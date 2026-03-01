from __future__ import annotations

from contextlib import suppress

import globalPluginHandler
import gui
import ui
import wx
import threading
import time
import os
import struct
import math
import re
import wave
import array
from dataclasses import dataclass
from typing import List, Optional, Tuple, Dict, Any

from scriptHandler import script

try:
    import tones
except Exception:
    tones = None


# =========================
# Utility
# =========================

A4_MIDI = 69
A4_FREQ = 440.0

NOTE_NAMES = ["C", "C sharp", "D", "D sharp", "E", "F", "F sharp", "G", "G sharp", "A", "A sharp", "B"]


def midi_to_freq(note: int) -> float:
    return A4_FREQ * (2.0 ** ((note - A4_MIDI) / 12.0))


def ticks_to_seconds(ticks: int, bpm: int, ppq: int) -> float:
    bpm = max(1, int(bpm))
    ppq = max(1, int(ppq))
    seconds_per_quarter = 60.0 / float(bpm)
    return (float(ticks) / float(ppq)) * seconds_per_quarter


def ticks_to_seconds_with_map(start_tick: int, ticks: int, tempo_map: list[tuple[int, int]] | None, default_bpm: int, ppq: int) -> float:
    """Convert a duration in ticks to seconds, honoring a tempo map if provided.

    tempo_map: list of (absolute_tick, bpm), sorted ascending.
    """
    ppq = max(1, int(ppq))
    start_tick = max(0, int(start_tick))
    ticks = max(0, int(ticks))
    if ticks == 0:
        return 0.0

    # Normalize map and ensure a point at tick 0.
    pts: list[tuple[int, int]] = []
    if tempo_map:
        for tk, bpm in tempo_map:
            try:
                pts.append((max(0, int(tk)), max(1, int(bpm))))
            except Exception:
                pass
    if not pts or pts[0][0] != 0:
        pts.append((0, max(1, int(default_bpm))))
    pts = sorted(set(pts), key=lambda x: x[0])

    end_tick = start_tick + ticks
    total = 0.0

    # Find the tempo in effect at start_tick (the last point at or before it).
    cur_bpm = pts[0][1]
    for tk, bpm in pts:
        if tk <= start_tick:
            cur_bpm = bpm
        else:
            break

    # Walk tempo segments.
    idx = 0
    while idx < len(pts) and pts[idx][0] <= start_tick:
        idx += 1

    cur_tick = start_tick
    while cur_tick < end_tick:
        next_change = end_tick
        if idx < len(pts):
            next_change = min(next_change, pts[idx][0])
        seg_end = min(end_tick, next_change)
        if seg_end > cur_tick:
            total += (seg_end - cur_tick) * (60.0 / float(cur_bpm)) / float(ppq)
            cur_tick = seg_end
        if idx < len(pts) and cur_tick >= pts[idx][0]:
            cur_bpm = pts[idx][1]
            idx += 1

    return total




def note_name(midi_note: int) -> str:
    n = int(midi_note) % 12
    octv = (int(midi_note) // 12) - 1
    return f"{NOTE_NAMES[n]} {octv}"


def pc_name(pc: int) -> str:
    return NOTE_NAMES[int(pc) % 12]


# =========================
# MIDI I/O (SMF format 0)
# =========================

def _vlq_encode(value: int) -> bytes:
    """Encode an int as MIDI variable-length quantity."""
    v = int(max(0, value))
    out = bytearray([v & 0x7F])
    v >>= 7
    while v:
        out.insert(0, 0x80 | (v & 0x7F))
        v >>= 7
    return bytes(out)

def _vlq_decode(data: bytes, idx: int) -> tuple[int, int]:
    """Decode MIDI VLQ starting at idx. Returns (value, new_idx)."""
    value = 0
    while True:
        if idx >= len(data):
            raise ValueError("Unexpected EOF while decoding VLQ")
        b = data[idx]
        idx += 1
        value = (value << 7) | (b & 0x7F)
        if not (b & 0x80):
            break
    return value, idx

def _write_midi_file(path: str, events: list["Event"], bpm: int, ppq: int, tempo_map: list[tuple[int, int]] | None = None) -> None:
    """Write a monophonic MIDI file (format 0, single track).

    If tempo_map is provided (list of (absolute_tick, bpm)), tempo changes are written as FF 51 events.
    """
    ppq = max(1, int(ppq))
    bpm = max(1, int(bpm))

    # Normalize tempo map and ensure a point at tick 0.
    pts: list[tuple[int, int]] = []
    if tempo_map:
        for tk, tbpm in tempo_map:
            try:
                pts.append((max(0, int(tk)), max(1, int(tbpm))))
            except Exception:
                pass
    if not pts:
        pts = [(0, bpm)]
    pts = sorted(set(pts), key=lambda x: x[0])
    if pts[0][0] != 0:
        pts.insert(0, (0, bpm))

    # Build a list of (abs_tick, order, raw_bytes) messages.
    msgs: list[tuple[int, int, bytes]] = []

    def tempo_msg(tbpm: int) -> bytes:
        tbpm = max(1, int(tbpm))
        us_per_quarter = int(round(60_000_000 / tbpm))
        us_per_quarter = max(1, min(us_per_quarter, 0xFFFFFF))
        return bytes([0xFF, 0x51, 0x03, (us_per_quarter >> 16) & 0xFF, (us_per_quarter >> 8) & 0xFF, us_per_quarter & 0xFF])

    for tk, tbpm in pts:
        # Order 1: tempo meta before note-ons at the same tick.
        msgs.append((int(tk), 1, tempo_msg(tbpm)))

    abs_tick = 0
    for ev in events:
        if ev.kind == "rest":
            abs_tick += int(ev.dur)
            continue
        note = int(ev.pitch) if ev.pitch is not None else None
        if note is None:
            abs_tick += int(ev.dur)
            continue
        dur = max(0, int(ev.dur))

        # Order 0 note-off first, order 2 note-on after, for same-tick boundaries.
        vel = clamp(int(getattr(ev, 'vel', 127) or 127), 1, 127)
        msgs.append((abs_tick, 2, bytes([0x90, note & 0x7F, vel & 0x7F])))
        msgs.append((abs_tick + dur, 0, bytes([0x80, note & 0x7F, 0x40])))
        abs_tick += dur

    # End-of-track
    msgs.append((abs_tick, 3, bytes([0xFF, 0x2F, 0x00])))

    msgs.sort(key=lambda x: (x[0], x[1]))

    track = bytearray()
    prev_tick = 0
    for tk, _order, raw in msgs:
        delta = max(0, int(tk) - int(prev_tick))
        track += _vlq_encode(delta)
        track += raw
        prev_tick = int(tk)

    # Header: MThd, length=6, format=0, ntrks=1, division=ppq
    header = bytearray()
    header += b"MThd" + struct.pack(">IHHH", 6, 0, 1, ppq)
    trk = bytearray()
    trk += b"MTrk" + struct.pack(">I", len(track)) + track

    with open(path, "wb") as f:
        f.write(header + trk)


def _write_wav_file(path: str, events: list["Event"], bpm: int, ppq: int, tempo_map: list[tuple[int, int]] | None = None, style: str = "sine") -> None:
    """Render the composition to a mono 16-bit PCM WAV file.

    style:
      - "sine": simple sine-wave preview
      - "nokia": pulse/square-ish beep with an envelope (retro phone-like)
    """
    bpm = max(1, int(bpm))
    ppq = max(1, int(ppq))
    style = (style or "sine").lower().strip()

    sample_rate = 22050 if style != "nokia" else 44100
    amp = 0.35 if style != "nokia" else 0.30
    duty = 0.5  # for pulse wave (nokia-style)

    # tiny fade to avoid clicks
    fade_ms = 6 if style != "nokia" else 4
    fade = max(1, int(sample_rate * (fade_ms / 1000.0)))

    def _poly_blep(t: float, dt: float) -> float:
        """PolyBLEP anti-aliasing helper (t in [0,1), dt=freq/sample_rate)."""
        if dt <= 0.0:
            return 0.0
        # Clamp dt to avoid pathological cases near Nyquist.
        if dt > 0.5:
            dt = 0.5
        if t < dt:
            x = t / dt
            return x + x - x * x - 1.0
        if t > 1.0 - dt:
            x = (t - 1.0) / dt
            return x * x + x + x + 1.0
        return 0.0

    def _write_silence(wf, n: int) -> None:
        if n <= 0:
            return
        chunk = array.array("h", [0]) * min(n, 4096)
        remaining = n
        while remaining > 0:
            k = min(remaining, 4096)
            wf.writeframes(chunk[:k].tobytes())
            remaining -= k

    with wave.open(path, "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)  # 16-bit
        wf.setframerate(sample_rate)

        abs_tick = 0
        phase = 0.0
        two_pi = 2.0 * math.pi

        for ev in events:
            dur_ticks = max(0, int(getattr(ev, "dur", 0)))
            secs = ticks_to_seconds_with_map(abs_tick, dur_ticks, tempo_map, bpm, ppq)
            abs_tick += dur_ticks
            n = int(round(secs * sample_rate))
            if n <= 0:
                continue

            if ev.kind == "rest" or getattr(ev, "pitch", None) is None:
                _write_silence(wf, n)
                continue

            freq = float(midi_to_freq(int(ev.pitch)))

            vel_factor = clamp(int(getattr(ev, 'vel', 127) or 127), 1, 127) / 127.0
            if freq <= 0.0:
                _write_silence(wf, n)
                continue

            # Envelope params
            if style == "nokia":
                attack = max(1, int(sample_rate * 0.005))
                decay = max(1, int(sample_rate * 0.018))
                release = max(1, int(sample_rate * 0.030))
                sustain = 0.70
            else:
                attack = fade
                decay = 1
                release = fade
                sustain = 1.0

            # Angular step per sample
            step = two_pi * freq / float(sample_rate)

            i = 0
            while i < n:
                k = min(4096, n - i)
                buf = array.array("h")
                buf_extend = buf.append

                for j in range(k):
                    idx = i + j

                    # Simple ADSR-ish envelope
                    if idx < attack:
                        env = idx / float(attack)
                    elif idx < attack + decay:
                        env = 1.0 - (1.0 - sustain) * ((idx - attack) / float(decay))
                    elif idx >= n - release:
                        env = sustain * max(0.0, 1.0 - ((idx - (n - release)) / float(release)))
                    else:
                        env = sustain

                    if style == "nokia":
                        # Retro phone beep: band-limited pulse using PolyBLEP to reduce aliasing.
                        # (Hard-edged pulse at low sample-rates sounds grungy/aliased.)
                        t01 = (phase / two_pi) % 1.0
                        dt = freq / float(sample_rate)
                        s = 1.0 if t01 < duty else -1.0
                        # Correct both discontinuities: rising edge at t=0, falling edge at t=duty.
                        s += _poly_blep(t01, dt)
                        s -= _poly_blep((t01 - duty) % 1.0, dt)
                    else:
                        s = math.sin(phase)

                    val = int(max(-1.0, min(1.0, s * amp * vel_factor * env)) * 32767.0)
                    buf_extend(val)

                    phase += step
                    if phase >= two_pi:
                        phase -= two_pi

                wf.writeframes(buf.tobytes())
                i += k


def _read_midi_file(path: str, target_ppq: int = 480) -> tuple[list["Event"], int, int, list[tuple[int, int]]]:
    """
    Read a MIDI file (format 0 or 1) and convert ALL tracks to a monophonic
    Event(note/rest) list. Returns (events, bpm, source_ppq, tempo_map).

    Import strategy:
      - Parse every MTrk chunk.
      - Collect all note on/off events with absolute tick times across tracks.
      - Merge them into a single stream and apply a "monophonic" rule:
        when a new note-on occurs, any currently-active note is cut off at that time.
    """
    with open(path, "rb") as f:
        data = f.read()

    if not data.startswith(b"MThd"):
        raise ValueError("Not a MIDI file (missing MThd)")

    idx = 4
    hdr_len = struct.unpack(">I", data[idx:idx + 4])[0]
    idx += 4
    if hdr_len < 6:
        raise ValueError("Invalid MIDI header length")

    fmt, ntrks, division = struct.unpack(">HHH", data[idx:idx + 6])
    idx += hdr_len

    source_ppq = int(division)
    if source_ppq <= 0:
        raise ValueError("Unsupported SMPTE timing in MIDI division")

    # Read all track chunks (robustly: skip unknown chunks)
    tracks: list[bytes] = []
    t = 0
    while t < int(ntrks) and idx + 8 <= len(data):
        cid = data[idx:idx + 4]
        clen = struct.unpack(">I", data[idx + 4:idx + 8])[0]
        chunk_data = data[idx + 8:idx + 8 + clen]
        idx = idx + 8 + clen
        if cid == b"MTrk":
            tracks.append(chunk_data)
            t += 1
        else:
            # Unknown chunk type; ignore
            continue

    if not tracks:
        raise ValueError("No MIDI track found")

    default_bpm = 120
    tempo_pts: list[tuple[int, int]] = []  # (tick, bpm) across all tracks
    # Collect note events: (time_ticks, kind, pitch, vel)
    # kind: 0=off, 1=on (so offs sort before ons at same time)
    note_events: list[tuple[int, int, int, int]] = []

    for track_bytes in tracks:
        time_ticks = 0
        running_status = None
        i = 0
        while i < len(track_bytes):
            delta, i = _vlq_decode(track_bytes, i)
            time_ticks += delta

            if i >= len(track_bytes):
                break

            status = track_bytes[i]
            if status & 0x80:
                i += 1
                running_status = status
            else:
                if running_status is None:
                    # Malformed; stop parsing this track
                    break
                status = running_status

            # Meta events
            if status == 0xFF:
                if i >= len(track_bytes):
                    break
                meta_type = track_bytes[i]
                i += 1
                mlen, i = _vlq_decode(track_bytes, i)
                mdata = track_bytes[i:i + mlen]
                i += mlen

                if meta_type == 0x51 and mlen == 3:
                    us = (mdata[0] << 16) | (mdata[1] << 8) | mdata[2]
                    if us > 0:
                        bpm = int(round(60_000_000 / us))
                        tempo_pts.append((int(time_ticks), int(bpm)))
                elif meta_type == 0x2F:
                    # End of track
                    break
                continue

            # SysEx events (skip)
            if status in (0xF0, 0xF7):
                slen, i = _vlq_decode(track_bytes, i)
                i += slen
                continue

            st = status & 0xF0

            # Note on / off
            if st in (0x80, 0x90):
                if i + 1 >= len(track_bytes):
                    break
                note = track_bytes[i] & 0x7F
                vel = track_bytes[i + 1] & 0x7F
                i += 2

                is_on = (st == 0x90 and vel > 0)
                is_off = (st == 0x80) or (st == 0x90 and vel == 0)

                if is_off:
                    note_events.append((time_ticks, 0, int(note), 0))
                elif is_on:
                    note_events.append((time_ticks, 1, int(note), int(vel)))
                continue

            # Other channel messages: skip their data bytes
            if st in (0xA0, 0xB0, 0xE0):  # 2 data bytes
                i += 2
            elif st in (0xC0, 0xD0):      # 1 data byte
                i += 1
            else:
                # Unknown/system message; bail out of this track
                break


    # Normalize tempo points into a tempo map.
    tempo_map: list[tuple[int, int]] = []
    try:
        # Normalize and sort tempo points; keep earliest BPM as default.
        if tempo_pts:
            tempo_pts_sorted = sorted(set((max(0, int(tk)), max(1, int(b))) for tk, b in tempo_pts), key=lambda x: x[0])
            tempo_map = tempo_pts_sorted
        if not tempo_map:
            tempo_map = [(0, int(default_bpm))]
        # Ensure tempo at tick 0; if first tempo point starts later, use that first BPM at tick 0.
        if tempo_map and tempo_map[0][0] != 0:
            tempo_map.insert(0, (0, int(tempo_map[0][1])))
    except Exception:
        tempo_map = [(0, int(default_bpm))]

    # Rescale tempo map tick positions to target_ppq so tempo changes align with converted events.
    try:
        target_ppq = max(1, int(target_ppq))
        scale = target_ppq / float(source_ppq)
        def _conv_tick(t: int) -> int:
            return int(round(int(t) * scale))
        tempo_map = sorted(set((max(0, _conv_tick(tk)), max(1, int(bpm))) for tk, bpm in tempo_map), key=lambda x: x[0])
        if tempo_map and tempo_map[0][0] != 0:
            tempo_map.insert(0, (0, int(tempo_map[0][1])))
    except Exception:
        pass

    # Pick a base tempo for UI/status: tempo in effect at tick 0.
    tempo_bpm = int(tempo_map[0][1]) if tempo_map else int(default_bpm)

    if not note_events:
        return [], int(max(1, tempo_bpm)), int(source_ppq), tempo_map

    # Sort by time; offs before ons; for simultaneous note-ons pick a deterministic winner:
    # process higher pitches first so the "last" note-on at a time becomes the lowest pitch.
    note_events.sort(key=lambda x: (x[0], x[1], -x[2] if x[1] == 1 else 0))

    # Build monophonic segments
    segments: list[tuple[int, int, int, int]] = []  # (start, end, pitch, vel)
    active_pitch: Optional[int] = None
    active_vel: int = 127
    active_start: int = 0
    last_time: int = 0

    for t, kind, pitch, vel in note_events:
        last_time = max(last_time, int(t))
        if kind == 1:  # note on
            if active_pitch is not None:
                if t > active_start:
                    segments.append((active_start, int(t), int(active_pitch), int(active_vel)))
            active_pitch = int(pitch)
            active_vel = clamp(int(vel), 1, 127) if int(vel) > 0 else 127
            active_start = int(t)
        else:  # note off
            if active_pitch is not None and int(pitch) == int(active_pitch):
                if t > active_start:
                    segments.append((active_start, int(t), int(active_pitch), int(active_vel)))
                active_pitch = None

    if active_pitch is not None:
        if last_time > active_start:
            segments.append((active_start, last_time, int(active_pitch), int(active_vel)))

    segments.sort(key=lambda x: x[0])

    # Convert to our ppq (target_ppq), preserving pitch.
    target_ppq = max(1, int(target_ppq))
    scale = target_ppq / float(source_ppq)

    def conv(t: int) -> int:
        return int(round(t * scale))

    out_events: list[Event] = []
    cur = 0
    for stime, etime, pitch, vel in segments:
        s = conv(stime)
        e = conv(etime)
        if e <= s:
            continue
        if s > cur:
            out_events.append(Event(kind="rest", pitch=None, dur=s - cur))
        out_events.append(Event(kind="note", pitch=int(pitch), dur=e - s, vel=clamp(int(vel),1,127)))
        cur = e

    return out_events, int(max(1, tempo_bpm)), int(source_ppq), tempo_map

def clamp(v: int, lo: int, hi: int) -> int:
    return max(lo, min(hi, v))


def _safe_filename_base(name: str, default: str = "composition") -> str:
    """Return a filesystem-safe base filename (no extension)."""
    base = (name or "").strip()
    if not base:
        base = default
    # Remove characters invalid on Windows and most filesystems.
    base = re.sub(r'[<>:"/\\|?*\x00-\x1F]', '', base)
    base = base.strip().strip('.')
    if not base:
        base = default
    # Keep it reasonably short for dialogs.
    return base[:80]


def dur_label(ticks: int, ppq: int) -> str:
    """Human-friendly duration labels for common note values.

    Supports dotted values (e.g., Dotted Quarter) when the tick count matches exactly.
    """
    if ppq <= 0:
        return f"{ticks} ticks"

    # Undotted common values
    common = [
        (ppq * 4, "Whole"),
        (ppq * 2, "Half"),
        (ppq, "Quarter"),
        (ppq // 2, "Eighth"),
        (ppq // 4, "Sixteenth"),
        (ppq // 8, "Thirty-second"),
    ]
    for t, name in common:
        if t == ticks:
            return name

    # Dotted values (3/2 of the undotted)
    dotted = []
    for t, name in common:
        # For integer tick math: dotted = undotted * 3 / 2
        dt = (int(t) * 3) // 2
        if (int(t) * 3) % 2 == 0:  # exact
            dotted.append((dt, f"Dotted {name}"))
    for t, name in dotted:
        if t == ticks:
            return name

    return f"{ticks} ticks"
    common = [
        (ppq * 4, "Whole"),
        (ppq * 2, "Half"),
        (ppq, "Quarter"),
        (ppq // 2, "Eighth"),
        (ppq // 4, "Sixteenth"),
        (ppq // 8, "Thirty-second"),
    ]
    for t, name in common:
        if t == ticks:
            return name
    return f"{ticks} ticks"


# =========================
# Model
# =========================

@dataclass
class Event:
    kind: str              # "note" or "rest"
    pitch: Optional[int]   # midi pitch for note, None for rest
    dur: int               # ticks
    vel: int = 127         # MIDI velocity/volume (1..127) for notes; ignored for rests


class Composition:
    def __init__(self):
        self.events: List[Event] = []

        # Cursor is now a DISPLAY POSITION including sentinels:
        # 0 = [BEGIN]
        # 1..len(events) = events
        # len(events)+1 = [END]
        self.cursor: int = 0

        self.tempo_bpm: int = 120
        # Tempo map: list of (absolute_tick, bpm). If present, playback and MIDI export honor it.
        # The UI currently edits a single tempo, so edits reset this to [(0, tempo_bpm)].
        self.tempo_map: List[Tuple[int, int]] = [(0, self.tempo_bpm)]
        self.ppq: int = 480
        self.step_ticks: int = 480

        self.base_note: int = 60
        self.input_transpose: int = 0
        self.input_velocity: int = 127  # velocity for new notes (1..127)

        self.chromatic_mode: bool = False
        self.scale_index: int = 0
        self.qwerty_layout: bool = False

        self.dirty: bool = False



        # Optional user metadata
        self.title: str = ""
        self.notes: str = ""

        # Marker ticks (absolute timeline ticks from start). Used for quick navigation.
        self.markers: List[int] = []

    def total_ticks(self) -> int:
        return sum(int(ev.dur) for ev in self.events)

    def tick_at_display_pos(self, pos: int) -> int:
        # pos is display position including sentinels.
        # 0 = Beginning, 1..len(events)=events, len(events)+1=End
        pos = int(pos)
        if pos <= 0:
            return 0
        if pos >= len(self.events) + 1:
            return self.total_ticks()
        tick = 0
        # sum durations of events strictly before this display position
        for ev in self.events[:pos-1]:
            tick += int(ev.dur)
        return tick

    def display_pos_from_tick(self, tick: int) -> int:
        tick = max(0, int(tick))
        acc = 0
        if tick <= 0:
            return 0
        for i, ev in enumerate(self.events):
            dur = int(ev.dur)
            if tick < acc + dur:
                return i + 1
            acc += dur
        return len(self.events) + 1
    def display_len(self) -> int:
        return len(self.events) + 2

    def is_begin(self, disp_index: int) -> bool:
        return disp_index == 0

    def is_end(self, disp_index: int) -> bool:
        return disp_index == len(self.events) + 1

    def disp_to_event_index(self, disp_index: int) -> Optional[int]:
        """Map displayed index to event index, or None for BEGIN/END."""
        if disp_index <= 0:
            return None
        if disp_index >= len(self.events) + 1:
            return None
        return disp_index - 1

    def insertion_event_index(self) -> int:
        """
        Insert between sentinels. If cursor on BEGIN, insert at 0.
        If cursor on END, insert at len(events).
        Otherwise cursor points at an event row; insert AFTER that row? No:
        cursor is a caret position on a row; we treat insertion as happening AT the caret position
        between rows, which is represented by the cursor row itself:
          - BEGIN row means before first event
          - event row i means between event (i-1) and event i? That’s confusing in listbox.
        Instead, we model cursor as selecting a ROW, but insertion is:
          - If on BEGIN -> insert at 0
          - If on END -> insert at len(events)
          - If on an event row -> insert AFTER that event (append-to-cursor behaviour)
        """
        if self.is_begin(self.cursor):
            return 0
        if self.is_end(self.cursor):
            return len(self.events)
        # on an event row: insert AFTER it
        ev_i = self.disp_to_event_index(self.cursor)
        if ev_i is None:
            return len(self.events)
        return clamp(ev_i + 1, 0, len(self.events))


# =========================
# Playback (DO NOT TOUCH AUDIO)
# =========================

class TonePlayer:
    def __init__(self):
        self._thread: Optional[threading.Thread] = None
        self._stop = threading.Event()
        self._lock = threading.Lock()

        # Playback position tracking (used for pause/follow cursor).
        self._statusLock = threading.Lock()
        self._is_playing: bool = False
        self._cur_event_index: Optional[int] = None  # event index (0..len(events))
        self._range_start: int = 0
        self._range_end: int = 0

    def stop(self) -> None:
        self._stop.set()

    def is_playing(self) -> bool:
        with self._statusLock:
            return bool(self._is_playing) and not self._stop.is_set()

    def current_event_index(self) -> Optional[int]:
        """Best-effort current event index during playback (0..len(events))."""
        with self._statusLock:
            return self._cur_event_index

    def current_range(self) -> Tuple[int, int]:
        with self._statusLock:
            return int(self._range_start), int(self._range_end)

    def _join(self) -> None:
        t = self._thread
        if t and t.is_alive():
            t.join(timeout=0.75)

    def _beep_chunked(self, freq: float, total_ms: int, max_chunk_ms: int = 5000, vol0_100: int = 100) -> None:
        if tones is None:
            return
        remaining = int(max(1, total_ms))
        while remaining > 0 and not self._stop.is_set():
            chunk = min(remaining, max_chunk_ms)
            try:
                # tones.beep usually accepts optional left/right volume (0..100).
                try:
                    tones.beep(freq, int(chunk), left=vol0_100, right=vol0_100)
                except TypeError:
                    tones.beep(freq, int(chunk))
            except Exception:
                pass
            remaining -= chunk

    def play_range(self, comp: Composition, start: int, end: int) -> None:
        with self._lock:
            self._stop.set()
            self._join()
            self._stop.clear()

            start = clamp(start, 0, len(comp.events))
            end = clamp(end, 0, len(comp.events))

            with self._statusLock:
                self._range_start = int(start)
                self._range_end = int(end)
                self._cur_event_index = int(start)
                self._is_playing = True

            def sleep_until(target: float) -> None:
                while not self._stop.is_set():
                    now = time.perf_counter()
                    remaining = target - now
                    if remaining <= 0:
                        return
                    if remaining > 0.004:
                        time.sleep(min(0.02, remaining - 0.002))
                    else:
                        while time.perf_counter() < target and not self._stop.is_set():
                            pass
                        return

            def run() -> None:
                try:
                    if tones is None:
                        self._stop.set()
                        return
                    cur_time = time.perf_counter()
                    BEEP_PORTION = 0.97

                    # Absolute tick position at the start of playback range, for tempo-map aware timing.
                    abs_tick = 0
                    try:
                        for j in range(0, start):
                            abs_tick += int(comp.events[j].dur)
                    except Exception:
                        abs_tick = 0

                    for i in range(start, end):
                        if self._stop.is_set():
                            break

                        with self._statusLock:
                            self._cur_event_index = int(i)

                        ev = comp.events[i]
                        step_s = max(0.001, ticks_to_seconds_with_map(abs_tick, ev.dur, getattr(comp, 'tempo_map', None), comp.tempo_bpm, comp.ppq))
                        abs_tick += int(ev.dur)
                        step_ms = int(step_s * 1000.0)
                        beep_ms = max(1, int(step_ms * BEEP_PORTION))

                        sleep_until(cur_time)
                        if self._stop.is_set():
                            break

                        if ev.kind == "note" and ev.pitch is not None:
                            # Map velocity (1..127) to NVDA tone volume (0..100).
                            try:
                                vel = int(getattr(ev, 'vel', getattr(ev, 'velocity', 127)) or 127)
                            except Exception:
                                vel = 127
                            vel = clamp(vel, 1, 127)
                            vol0_100 = int(round((vel / 127.0) * 100.0))
                            vol0_100 = clamp(vol0_100, 0, 100)
                            self._beep_chunked(midi_to_freq(int(ev.pitch)), beep_ms, vol0_100=vol0_100)

                        cur_time += step_s

                finally:
                    with self._statusLock:
                        # Best-effort: point to the end of the played range when stopping.
                        if self._cur_event_index is None:
                            self._cur_event_index = int(end)
                        self._is_playing = False
                    self._stop.set()

            self._thread = threading.Thread(target=run, daemon=True)
            self._thread.start()

    def play_all(self, comp: Composition) -> None:
        self.play_range(comp, 0, len(comp.events))


class PreviewBeep:
    def __init__(self):
        self._stop = threading.Event()
        self._lock = threading.Lock()
        self._pending: Optional[Tuple[float, int, int, int]] = None  # (freq, ms, vol0_100, token)
        self._token: int = 0
        self._t = threading.Thread(target=self._run, daemon=True)
        self._t.start()

    def stop(self) -> None:
        self._stop.set()

    def request(self, freq: float, ms: int, vol0_100: int = 100) -> None:
        """Queue a preview beep.

        vol0_100 is an approximate loudness (0..100) if supported by tones.beep.
        """
        if tones is None:
            return
        ms = int(max(1, ms))
        vol0_100 = int(clamp(int(vol0_100), 0, 100))
        with self._lock:
            self._token += 1
            self._pending = (float(freq), ms, vol0_100, self._token)

    def _beep_chunked_interruptible(self, freq: float, total_ms: int, vol0_100: int, token: int, max_chunk_ms: int = 300) -> None:
        remaining = int(max(1, total_ms))
        while remaining > 0 and not self._stop.is_set():
            with self._lock:
                if token != self._token:
                    return
            chunk = min(remaining, max_chunk_ms)
            try:
                # tones.beep usually accepts optional left/right volume (0..100).
                try:
                    tones.beep(freq, int(chunk), left=vol0_100, right=vol0_100)
                except TypeError:
                    tones.beep(freq, int(chunk))
            except Exception:
                pass
            remaining -= chunk

    def _run(self) -> None:
        while not self._stop.is_set():
            req = None
            with self._lock:
                req = self._pending
                self._pending = None
            if req is None:
                time.sleep(0.005)
                continue
            freq, ms, vol0_100, token = req
            self._beep_chunked_interruptible(freq, ms, vol0_100, token)


# =========================
# Input mapping / scales
# =========================

GRID_OFFSETS = {"j": 0, "k": 1, "l": 2, "u": 3, "i": 4, "o": 5, "7": 6, "8": 7}
GRID_DEGREES = GRID_OFFSETS.copy()

QWERTY_OFFSETS = {"a": 0, "w": 1, "s": 2, "e": 3, "d": 4, "f": 5, "t": 6, "g": 7, "y": 8, "h": 9, "u": 10, "j": 11, "k": 12}
QWERTY_DEGREES = {"a": 0, "s": 1, "d": 2, "f": 3, "g": 4, "h": 5, "j": 6, "k": 7}


def parse_scale_text(text: str, fallback_name: str) -> Tuple[str, List[int]]:
    raw = text.strip().replace(",", " ")
    name = fallback_name
    nums_part = raw
    if ":" in raw:
        left, right = raw.split(":", 1)
        if left.strip():
            name = left.strip()
        nums_part = right
    parts = [p for p in nums_part.split() if p.strip()]
    ints: List[int] = []
    for p in parts:
        try:
            ints.append(int(p))
        except Exception:
            pass
    ints = [x % 12 for x in ints if isinstance(x, int)]
    seen = set()
    out: List[int] = []
    for x in ints:
        if x not in seen:
            seen.add(x)
            out.append(x)
    if not out:
        out = [0, 2, 4, 5, 7, 9, 11]
    return name, out


def load_scales(addon_dir: str) -> List[Tuple[str, List[int]]]:
    scales: List[Tuple[str, List[int]]] = []
    scales.append(("Major", [0, 2, 4, 5, 7, 9, 11]))
    scales.append(("Minor", [0, 2, 3, 5, 7, 8, 10]))
    scales.append(("Pentatonic", [0, 2, 4, 7, 9]))
    scales.append(("Blues", [0, 3, 5, 6, 7, 10]))

    scales_dir = os.path.join(addon_dir, "Scales")
    if os.path.isdir(scales_dir):
        for fn in sorted(os.listdir(scales_dir)):
            if not fn.lower().endswith(".txt"):
                continue
            path = os.path.join(scales_dir, fn)
            try:
                with open(path, "r", encoding="utf-8") as f:
                    txt = f.read()
                name = os.path.splitext(fn)[0]
                sname, steps = parse_scale_text(txt, name)
                scales.append((sname, steps))
            except Exception:
                continue

    for i, (n, _) in enumerate(scales):
        if n.strip().lower() == "major":
            if i != 0:
                major = scales.pop(i)
                scales.insert(0, major)
            break
    return scales


def degree_to_semitone(scale_steps: List[int], degree: int) -> int:
    if not scale_steps:
        scale_steps = [0, 2, 4, 5, 7, 9, 11]
    deg = int(degree)
    octv = deg // len(scale_steps)
    idx = deg % len(scale_steps)
    return (octv * 12) + int(scale_steps[idx])


# =========================
# TXT Save/Load
# =========================

def comp_to_text(comp: Composition) -> str:
    key_pc = (comp.base_note + comp.input_transpose) % 12
    lines = []
    lines.append("NVDA_COMPOSER_TXT v6")
    lines.append(f"tempo {comp.tempo_bpm}")
    lines.append(f"ppq {comp.ppq}")
    lines.append(f"step {comp.step_ticks}")
    lines.append(f"base {comp.base_note}")
    lines.append(f"transpose {comp.input_transpose}")
    lines.append(f"keyPc {key_pc}")
    lines.append(f"keyName {pc_name(key_pc)}")
    lines.append(f"chromatic {1 if comp.chromatic_mode else 0}")
    lines.append(f"scale {comp.scale_index}")
    lines.append(f"qwerty {1 if comp.qwerty_layout else 0}")
    # Optional user metadata
    try:
        title = getattr(comp, "title", "") or ""
        title = title.replace("\n", " ").strip()
        if title:
            lines.append(f"title {title}")
    except Exception:
        pass

    try:
        notes = getattr(comp, "notes", "") or ""
        notes = str(notes)
        if notes.strip():
            lines.append("notes")
            for ln in notes.splitlines():
                lines.append(ln.rstrip("\n"))
            lines.append("endNotes")
    except Exception:
        pass

    # Optional tempo map (used for MIDI imports/exports with tempo changes).
    try:
        tm = getattr(comp, "tempo_map", None)
        if tm and len(tm) > 1:
            lines.append("tempoMap")
            for tk, bpm in tm:
                lines.append(f"tempoPoint {int(tk)} {int(bpm)}")
            lines.append("endTempoMap")
    except Exception:
        pass

    # Optional markers (absolute tick positions).
    try:
        mk = getattr(comp, "markers", None)
        if mk:
            mk2 = sorted(set(int(x) for x in mk if x is not None))
            if mk2:
                lines.append("markers")
                for tk in mk2:
                    lines.append(f"marker {int(tk)}")
                lines.append("endMarkers")
    except Exception:
        pass

    lines.append("events")
    for ev in comp.events:
        if ev.kind == "rest":
            lines.append(f"rest {int(ev.dur)}")
        else:
            vel = clamp(int(getattr(ev, "vel", 127) or 127), 1, 127)
            lines.append(f"note {int(ev.pitch)} {int(ev.dur)} {vel}")
    return "\n".join(lines) + "\n"


def comp_from_text(text: str) -> Composition:
    """Parse NVDA Composer text format (all supported versions) into a Composition.

    Notes:
    - Older files may omit velocity; default is 127.
    - We also merge adjacent identical events (same pitch/rest and velocity) to keep
      timelines tidy (useful for Nokia RNG round-trips that can split durations).
    """
    comp = Composition()
    raw_lines = text.splitlines()
    lines = [ln.rstrip("\n") for ln in raw_lines if ln.strip()]
    if not lines:
        return comp

    first = lines[0].strip()
    if first.startswith("NVDA_COMPOSER_TXT"):
        i = 1
        in_events = False
        in_tempomap = False
        tempo_pts: List[Tuple[int, int]] = []
        in_markers = False
        marker_ticks: List[int] = []
        in_notes = False
        notes_lines: List[str] = []
        while i < len(lines):
            ln = lines[i].strip()
            i += 1
            if ln.lower() == "events":
                in_events = True
                continue
            if ln.lower() == "tempomap":
                in_tempomap = True
                continue
            if ln.lower() == "endtempomap":
                in_tempomap = False
                continue
            if ln.lower() == "markers":
                in_markers = True
                continue
            if ln.lower() == "endmarkers":
                in_markers = False
                continue
            if ln.lower() == "notes":
                in_notes = True
                continue
            if ln.lower() == "endnotes":
                in_notes = False
                continue
            if in_tempomap:
                parts = ln.split()
                if parts and parts[0].lower() == "tempopoint" and len(parts) >= 3:
                    try:
                        tempo_pts.append((int(parts[1]), int(parts[2])))
                    except Exception:
                        pass
                continue

            if in_markers:
                parts = ln.split()
                if not parts:
                    continue
                try:
                    if parts[0].lower() == "marker" and len(parts) >= 2:
                        marker_ticks.append(int(parts[1]))
                    else:
                        # Allow bare integer lines
                        marker_ticks.append(int(parts[0]))
                except Exception:
                    pass
                continue

            if in_notes:
                notes_lines.append(ln)
                continue

            if not in_events:
                parts = ln.split()
                if not parts:
                    continue
                if parts[0].lower() == "title":
                    try:
                        comp.title = ln[len(parts[0]):].strip()
                    except Exception:
                        pass
                    continue
                if len(parts) < 2:
                    continue
                k = parts[0].lower()
                v = parts[1]
                try:
                    if k == "tempo":
                        comp.tempo_bpm = int(v)
                    elif k == "ppq":
                        comp.ppq = int(v)
                    elif k == "step":
                        comp.step_ticks = int(v)
                    elif k == "base":
                        comp.base_note = int(v)
                    elif k == "transpose":
                        comp.input_transpose = int(v)
                    elif k == "chromatic":
                        comp.chromatic_mode = (int(v) != 0)
                    elif k == "scale":
                        comp.scale_index = int(v)
                    elif k == "qwerty":
                        comp.qwerty_layout = (int(v) != 0)
                except Exception:
                    pass
                continue

            parts = ln.split()
            if not parts:
                continue
            kind = parts[0].lower()
            if kind == "rest" and len(parts) >= 2:
                try:
                    comp.events.append(Event(kind="rest", pitch=None, dur=int(parts[1])))
                except Exception:
                    pass
            elif kind == "note" and len(parts) >= 3:
                try:
                    vel = 127
                    if len(parts) >= 4:
                        vel = clamp(int(parts[3]), 1, 127)
                    comp.events.append(Event(kind="note", pitch=int(parts[1]), dur=int(parts[2]), vel=vel))
                except Exception:
                    pass

        # Apply tempo map if present (v5+).
        if tempo_pts:
            pts = []
            for tk, bpm in tempo_pts:
                try:
                    pts.append((max(0, int(tk)), clamp(int(bpm), 20, 999)))
                except Exception:
                    pass
            pts = sorted(set(pts), key=lambda x: x[0])
            if pts and pts[0][0] != 0:
                pts.insert(0, (0, int(comp.tempo_bpm)))
            if pts:
                try:
                    comp.tempo_map = pts
                    comp.tempo_bpm = int(pts[0][1])
                except Exception:
                    pass

        # Apply markers if present.
        try:
            if marker_ticks:
                comp.markers = sorted(set(max(0, int(t)) for t in marker_ticks))
            else:
                comp.markers = []
        except Exception:
            comp.markers = []

        else:
            # No explicit tempo map in the file: keep tempo_bpm but reset tempo_map to a single point at tick 0.
            try:
                comp.tempo_map = [(0, int(comp.tempo_bpm))]
            except Exception:
                pass


        # Apply collected notes (if any)
        try:
            comp.notes = "\n".join(notes_lines).rstrip("\n")
        except Exception:
            pass

        comp.cursor = 0
        comp.dirty = False
        return comp

    # legacy minimal parse
    for ln in lines:
        parts = ln.split()
        if not parts:
            continue
        tag = parts[0].upper()
        if tag == "N" and len(parts) >= 3:
            try:
                vel = 127
                if len(parts) >= 4:
                    vel = clamp(int(parts[3]), 1, 127)
                comp.events.append(Event(kind="note", pitch=int(parts[1]), dur=int(parts[2]), vel=vel))
            except Exception:
                pass
        elif tag == "R" and len(parts) >= 2:
            try:
                comp.events.append(Event(kind="rest", pitch=None, dur=int(parts[1])))
            except Exception:
                pass

    comp.cursor = 0
    comp.dirty = False
    
    # Merge adjacent identical events (same pitch/rest and velocity) to avoid "extra notes"
    # when an exported format encodes a duration as multiple consecutive instructions.
    merged: List[Event] = []
    for ev in comp.events:
        ev_vel = int(getattr(ev, "vel", 127))
        if merged:
            prev = merged[-1]
            prev_vel = int(getattr(prev, "vel", 127))
            if ev.kind == prev.kind and ev.pitch == prev.pitch and ev_vel == prev_vel:
                prev.dur = int(prev.dur) + int(ev.dur)
                continue
        merged.append(ev)
    comp.events = merged
    return comp


# =========================
# Dialog
# =========================


# -----------------------------------------------------------------------------
# Nokia Smart Messaging Ringing Tone (.rng) import
# -----------------------------------------------------------------------------
# Many legacy Nokia "Composer" ringtones were distributed as Smart Messaging
# "ringing tone" payloads, commonly stored with a .rng suffix.
#
# This is a compact bit-packed format (not MIDI, not RTTTL text). We implement
# a small decoder for the "basic song" / "temporary song" subset, and treat the
# result as monophonic events in the current project.

class _BitReader:
    __slots__ = ("_data", "_bitpos")

    def __init__(self, data: bytes):
        self._data = data
        self._bitpos = 0  # bit offset from start

    def bits_left(self) -> int:
        return len(self._data) * 8 - self._bitpos

    def read_bits(self, n: int) -> int:
        if n <= 0:
            return 0
        if self._bitpos + n > len(self._data) * 8:
            raise ValueError("Unexpected end of .rng data")
        out = 0
        for _ in range(n):
            byte_index = self._bitpos // 8
            bit_index = 7 - (self._bitpos % 8)
            bit = (self._data[byte_index] >> bit_index) & 1
            out = (out << 1) | bit
            self._bitpos += 1
        return out

    def align_byte(self) -> None:
        rem = self._bitpos % 8
        if rem:
            self._bitpos += (8 - rem)

# Command-part IDs (7-bit values) per Nokia Smart Messaging spec.
_RNG_CMD_CANCEL = 0b0000101
_RNG_CMD_RTPROG = 0b0100101
_RNG_CMD_SOUND  = 0b0011101
_RNG_CMD_UNICODE = 0b0100010

# Song types (3-bit values)
_RNG_SONG_BASIC = 0b001
_RNG_SONG_TEMP  = 0b010

# Instruction IDs (3-bit values)
_RNG_I_PATTERN = 0b000
_RNG_I_NOTE    = 0b001
_RNG_I_SCALE   = 0b010
_RNG_I_STYLE   = 0b011
_RNG_I_TEMPO   = 0b100
_RNG_I_VOLUME  = 0b101

# Note values (4-bit)
_RNG_NOTE_TO_SEMITONE = {
    0b0000: None,  # pause/rest
    0b0001: 0,   # C
    0b0010: 1,   # C#
    0b0011: 2,   # D
    0b0100: 3,   # D#
    0b0101: 4,   # E
    0b0110: 5,   # F
    0b0111: 6,   # F#
    0b1000: 7,   # G
    0b1001: 8,   # G#
    0b1010: 9,   # A
    0b1011: 10,  # A#
    0b1100: 11,  # B (H)
}

# Duration (3-bit) -> divisor of whole note (in PPQ=480 ticks, whole=1920)
_RNG_DUR_TICKS = {
    0b000: 1920,  # full
    0b001: 960,   # half
    0b010: 480,   # quarter
    0b011: 240,   # eighth
    0b100: 120,   # 16th
    0b101: 60,    # 32nd
}

# Duration specifier (2-bit)
def _rng_apply_dur_spec(base_ticks: int, spec: int) -> int:
    if spec == 0b00:
        return base_ticks
    if spec == 0b01:  # dotted
        return (base_ticks * 3) // 2
    if spec == 0b10:  # double dotted
        return (base_ticks * 7) // 4
    if spec == 0b11:  # 2/3 length
        return (base_ticks * 2) // 3
    return base_ticks

# BPM encoding (5-bit) -> bpm (Smart Messaging spec table 3.8-11)
_RNG_BPM_TABLE = [
    25, 28, 31, 35, 40, 45, 50, 56,
    63, 70, 80, 90, 100, 112, 125, 140,
    160, 180, 200, 225, 250, 285, 320, 355,
    400, 450, 500, 565, 635, 715, 800, 900,
]

def _rng_scale_to_c_midi(scale_code: int) -> int:
    """
    Map Nokia 'note-scale' to a MIDI note for C in that scale.
    Per spec: scale-1 => A4 (440Hz), scale-2 => A5 (880Hz) default, etc.
    Using MIDI A4=69 => C4=60, A5=81 => C5=72, A6=93 => C6=84, A7=105 => C7=96.
    """
    if scale_code == 0b00:  # scale-1
        return 60
    if scale_code == 0b01:  # scale-2 (default)
        return 72
    if scale_code == 0b10:  # scale-3
        return 84
    if scale_code == 0b11:  # scale-4
        return 96
    return 72

def _parse_rng_song(br: _BitReader) -> Tuple[str, List[Event], int, List[Tuple[int, int]]]:
    """
    Returns (title, events, tempo_bpm, tempo_map).
    Tempo map entries are (absolute_tick, bpm).
    """
    title = ""
    song_type = br.read_bits(3)
    if song_type == _RNG_SONG_BASIC:
        name_len = br.read_bits(4)
        # Default charset is ISO-8859-1 per spec; we decode bytes and replace unknowns.
        name_bytes = bytes(br.read_bits(8) for _ in range(name_len))
        try:
            title = name_bytes.decode("latin-1", errors="replace").strip()
        except Exception:
            title = ""
        # Basic song is title + temporary song
        events, tempo_bpm, tempo_map = _parse_rng_temporary_song(br)
        return title, events, tempo_bpm, tempo_map

    if song_type == _RNG_SONG_TEMP:
        events, tempo_bpm, tempo_map = _parse_rng_temporary_song(br)
        return title, events, tempo_bpm, tempo_map

    raise ValueError("Unsupported .rng song type")

def _parse_rng_temporary_song(br: _BitReader) -> Tuple[List[Event], int, List[Tuple[int, int]]]:
    # Defaults: scale-2, natural style, volume level-7, bpm=63.
    current_scale = 0b01
    c_midi = _rng_scale_to_c_midi(current_scale)
    tempo_bpm = 63
    tempo_map: List[Tuple[int, int]] = [(0, tempo_bpm)]
    current_volume = 0b0111  # 0..15

    patterns_defined: Dict[int, List[Tuple[str, Any]]] = {}  # pid -> instruction stream
    seq_len = br.read_bits(8)

    out_events: List[Event] = []
    cur_tick = 0

    def emit_note(note_val: int, dur_code: int, dur_spec: int) -> None:
        nonlocal cur_tick, c_midi, out_events, current_volume
        base = _RNG_DUR_TICKS.get(dur_code, 480)
        ticks = _rng_apply_dur_spec(base, dur_spec)
        semi = _RNG_NOTE_TO_SEMITONE.get(note_val, None)
        if semi is None:
            out_events.append(Event(kind="rest", pitch=None, dur=ticks))
        else:
            pitch = c_midi + semi
            vel = clamp(int(round((int(current_volume) / 15.0) * 127.0)), 1, 127)
            out_events.append(Event(kind="note", pitch=pitch, dur=ticks, vel=vel))
        cur_tick += ticks

    def apply_instruction_stream(instrs: List[Tuple[str, Any]], repeat_index: int = 0) -> None:
        nonlocal current_scale, c_midi, tempo_bpm, tempo_map, cur_tick, current_volume
        for kind, payload in instrs:
            if kind == "scale":
                current_scale = payload
                c_midi = _rng_scale_to_c_midi(current_scale)
            elif kind == "tempo":
                bpm = payload
                tempo_bpm = bpm
                # Avoid duplicates at same tick
                if not tempo_map or tempo_map[-1][0] != cur_tick or tempo_map[-1][1] != bpm:
                    tempo_map.append((cur_tick, bpm))
            elif kind == "note":
                note_val, dur_code, dur_spec = payload
                emit_note(note_val, dur_code, dur_spec)
            elif kind == "volume":
                try:
                    current_volume = int(payload) & 0x0F
                except Exception:
                    current_volume = 0b0111
            else:
                # style ignored for now
                pass

    for _ in range(seq_len):
        instr_id = br.read_bits(3)
        if instr_id != _RNG_I_PATTERN:
            raise ValueError("Expected pattern header in .rng stream")

        pat_id = br.read_bits(2)   # A/B/C/D => 0..3
        loop_val = br.read_bits(4) # repeats; 0 means no repeat, 15 infinite
        spec = br.read_bits(8)     # 0 => reuse pattern, else instruction count

        if spec == 0:
            instrs = patterns_defined.get(pat_id)
            if instrs is None:
                raise ValueError("Pattern referenced before definition")
        else:
            instrs = []
            for _pi in range(spec):
                if br.bits_left() < 3:
                    break
                iid = br.read_bits(3)
                if iid == _RNG_I_NOTE:
                    note_val = br.read_bits(4)
                    dur_code = br.read_bits(3)
                    dur_spec = br.read_bits(2)
                    instrs.append(("note", (note_val, dur_code, dur_spec)))
                elif iid == _RNG_I_SCALE:
                    scale = br.read_bits(2)
                    instrs.append(("scale", scale))
                elif iid == _RNG_I_TEMPO:
                    bpm_code = br.read_bits(5)
                    bpm = _RNG_BPM_TABLE[bpm_code] if 0 <= bpm_code < len(_RNG_BPM_TABLE) else 63
                    instrs.append(("tempo", bpm))
                elif iid == _RNG_I_STYLE:
                    _ = br.read_bits(2)  # ignore
                    instrs.append(("style", None))
                elif iid == _RNG_I_VOLUME:
                    vol = br.read_bits(4)
                    instrs.append(("volume", int(vol) & 0x0F))
                else:
                    # Some .rng files appear to over-report the pattern-instruction count.
                    # If we encounter a pattern-header id (000) where an instruction is expected,
                    # treat it as the start of the next pattern (or padding) and rewind 3 bits so
                    # the outer loop can consume it.
                    if iid == _RNG_I_PATTERN:
                        br._bitpos -= 3
                        break
                    # Unknown/unsupported instruction: stop parsing this pattern best-effort.
                    break
            patterns_defined[pat_id] = instrs

        # Apply pattern once, then repeat loop_val times (loop_val=0 => play once).
        repeats = 1
        if loop_val == 0b1111:
            # Avoid infinite loops; pick a sane cap.
            repeats = 8
        else:
            repeats = 1 + loop_val

        for _r in range(repeats):
            apply_instruction_stream(instrs, repeat_index=_r)

    # Normalize tempo map: keep the *last* bpm at any given tick, ensure tick 0, and sort.
    tick_to_bpm: Dict[int, int] = {}
    for t, bpm in tempo_map:
        tick_to_bpm[int(t)] = int(bpm)

    if 0 in tick_to_bpm:
        tempo_bpm = tick_to_bpm[0]

    tempo_map_sorted = sorted(tick_to_bpm.items(), key=lambda x: x[0])
    if not tempo_map_sorted:
        tempo_map_sorted = [(0, tempo_bpm)]
    elif tempo_map_sorted[0][0] != 0:
        tempo_map_sorted.insert(0, (0, tempo_bpm))

    return out_events, tempo_bpm, tempo_map_sorted

def comp_from_rng_bytes(data: bytes) -> Tuple[Composition, str]:
    """
    Parse a .rng file (Nokia Smart Messaging Ringing Tone) into a Composition.
    Returns (composition, title_from_file).
    """
    br = _BitReader(data)
    title = ""
    events: List[Event] = []
    tempo_bpm: int = 63
    tempo_map: List[Tuple[int, int]] = [(0, tempo_bpm)]

    # Commands: [command-length][command-part...], terminated by 0 length.
    while br.bits_left() >= 8:
        cmd_len = br.read_bits(8)
        if cmd_len == 0:
            break
        for _ in range(cmd_len):
            cmd = br.read_bits(7)
            if cmd == _RNG_CMD_RTPROG:
                # Marker only; payload is empty, then align.
                br.align_byte()
                continue
            if cmd == _RNG_CMD_UNICODE:
                # Not supported; skip by aligning to byte (best-effort).
                br.align_byte()
                continue
            if cmd == _RNG_CMD_SOUND:
                t, evs, bpm, tmap = _parse_rng_song(br)
                if t and not title:
                    title = t
                events = evs
                tempo_bpm = bpm
                tempo_map = tmap
                br.align_byte()
                continue
            if cmd == _RNG_CMD_CANCEL:
                # Cancel command: ignore.
                br.align_byte()
                continue
            # Unknown command part: align and continue best-effort.
            br.align_byte()

    comp = Composition()
    comp.events = events
    comp.cursor = 0
    comp.tempo_bpm = int(tempo_bpm) if tempo_bpm else 63
    comp.tempo_map = list(tempo_map) if tempo_map else [(0, comp.tempo_bpm)]
    comp.ppq = 480
    comp.step_ticks = 240  # a sensible edit default after import
    comp.base_note = 60
    comp.input_transpose = 0
    comp.chromatic_mode = False
    comp.scale_index = 0
    comp.qwerty_layout = False
    comp.dirty = True
    return comp, title



# -----------------------------------------------------------------------------
# Nokia Smart Messaging Ringing Tone (.rng) export
# -----------------------------------------------------------------------------
# We export a "basic song" which contains a short title and a single pattern.
# Notes are mapped to the 4 Nokia "scales" (octave bands). Durations are quantized
# to the closest representable Nokia duration + specifier.
#
# Spec reference: Smart Messaging Specification v2.0.0, section 3.8. 
#
# Notes:
# - The Smart Messaging tone format is monophonic; chords are flattened in export.
# - Pitches outside the supported C4..B7 range are folded by octaves into range.

class _BitWriter:
    __slots__ = ("_bits",)

    def __init__(self):
        self._bits: List[int] = []

    def write_bits(self, value: int, nbits: int) -> None:
        value = int(value)
        nbits = int(nbits)
        if nbits <= 0:
            return
        for i in range(nbits - 1, -1, -1):
            self._bits.append((value >> i) & 1)

    def write_bytes(self, data: bytes) -> None:
        for b in data:
            self.write_bits(int(b), 8)

    def align_byte(self) -> None:
        rem = len(self._bits) % 8
        if rem:
            for _ in range(8 - rem):
                self._bits.append(0)

    def to_bytes(self) -> bytes:
        self.align_byte()
        out = bytearray()
        for i in range(0, len(self._bits), 8):
            b = 0
            for j in range(8):
                b = (b << 1) | (self._bits[i + j] & 1)
            out.append(b)
        return bytes(out)

# Build semitone->note value lookup from the import table.
_RNG_SEMITONE_TO_NOTE: Dict[int, int] = {v: k for k, v in _RNG_NOTE_TO_SEMITONE.items()}

def _rng_nearest_bpm_code(bpm: int) -> int:
    bpm = int(bpm)
    best = 0
    best_err = 10**9
    for i, v in enumerate(_RNG_BPM_TABLE):
        err = abs(int(v) - bpm)
        if err < best_err:
            best_err = err
            best = i
    return best

# Representable duration candidates (ticks) for one instruction.
def _rng_duration_candidates(ppq: int = 480) -> List[Tuple[int, int, int]]:
    # returns list of (ticks, dur_code, dur_spec)
    out: List[Tuple[int, int, int]] = []
    for dur_code, base in _RNG_DUR_TICKS.items():
        if dur_code not in (0, 1, 2, 3, 4, 5):
            continue
        for dur_spec in (0, 1, 2, 3):
            ticks = int(_rng_apply_dur_spec(int(base), int(dur_spec)))
            out.append((ticks, int(dur_code), int(dur_spec)))
    out.sort(key=lambda t: t[0])
    return out

_RNG_DUR_CANDS = _rng_duration_candidates()

def _rng_pick_duration(ticks: int) -> Tuple[int, int, int]:
    """Pick the best representable duration that does not exceed `ticks`.
    Returns (qticks, dur_code, dur_spec). If `ticks` is smaller than the minimum representable duration,
    returns the minimum duration (caller may choose to merge small remainders instead of emitting a new note).
    """
    ticks = max(1, int(ticks))
    # Largest candidate <= ticks
    best = None
    for cand in _RNG_DUR_CANDS:
        if cand[0] <= ticks:
            best = cand
        else:
            break
    if best is None:
        best = _RNG_DUR_CANDS[0]
    return int(best[0]), int(best[1]), int(best[2])


def _rng_pick_duration_nearest(ticks: int) -> Tuple[int, int, int]:
    """Pick the closest representable duration. Returns (qticks, dur_code, dur_spec)."""
    ticks = max(1, int(ticks))
    best = _RNG_DUR_CANDS[0]
    best_err = abs(best[0] - ticks)
    for cand in _RNG_DUR_CANDS:
        err = abs(cand[0] - ticks)
        if err < best_err:
            best = cand
            best_err = err
            if best_err == 0:
                break
    return int(best[0]), int(best[1]), int(best[2])

def _rng_fold_pitch_to_range(pitch: int) -> int:
    # Supported: C4..B7 (60..107) across scales 1..4
    p = int(pitch)
    while p < 60:
        p += 12
    while p > 107:
        p -= 12
    return p

def _rng_scale_for_pitch(pitch: int) -> int:
    p = _rng_fold_pitch_to_range(pitch)
    if p < 72:
        return 0b00  # C4..B4
    if p < 84:
        return 0b01  # C5..B5
    if p < 96:
        return 0b10  # C6..B6
    return 0b11      # C7..B7

def _rng_note_value_for_pitch(pitch: int) -> int:
    p = _rng_fold_pitch_to_range(pitch)
    semi = p % 12  # C=0 .. B=11
    return int(_RNG_SEMITONE_TO_NOTE.get(semi, 0b0001))  # default C

def _write_rng_file(path: str, events: List[Event], tempo_bpm: int, ppq: int, title: str = "composition") -> None:
    """
    Write a Nokia Smart Messaging Ringing Tone (.rng) file.

    Export is monophonic; we write a single pattern with (tempo, style, volume, scale changes, notes).
    """
    bw = _BitWriter()

    # Command: [len=2][rtprog][sound ...][end=0]
    bw.write_bits(2, 8)

    # Part 1: Ringing-tone-programming: 7 bits, then align.
    bw.write_bits(_RNG_CMD_RTPROG, 7)
    bw.align_byte()

    # Part 2: Sound
    bw.write_bits(_RNG_CMD_SOUND, 7)

    # Song type: basic song (001)
    bw.write_bits(0b001, 3)

    # Title (ISO-8859-1 default charset, unicode disabled). Limit to 15 chars.
    safe_title = (title or "composition").strip()
    if not safe_title:
        safe_title = "composition"
    safe_title = safe_title[:15]
    raw_title = safe_title.encode("latin-1", errors="replace")
    bw.write_bits(len(raw_title) & 0x0F, 4)
    bw.write_bytes(raw_title)

    # Temporary song: 1 pattern
    bw.write_bits(1, 8)  # song-sequence-length

    # Pattern header
    bw.write_bits(_RNG_I_PATTERN, 3)  # pattern-header-id = 000
    bw.write_bits(0b00, 2)            # pattern-id: A-part
    bw.write_bits(0, 4)               # loop-value: 0 => play once

    # Build instruction stream.
    instrs: List[Tuple[str, Any]] = []

    # Tempo (nearest Nokia BPM)
    bpm_code = _rng_nearest_bpm_code(int(tempo_bpm) if tempo_bpm else 63)
    instrs.append(("tempo_code", int(bpm_code)))

    # Style: natural (00) is the Nokia default. Continuous can sound more "tied".
    # We keep natural to match most classic Composer tones.
    instrs.append(("style", 0b00))

    # Volume: default level-7 (0111)
    current_vol_code = 0b0111
    instrs.append(("volume", int(current_vol_code)))

    # Notes: scale changes + note instructions.
    current_scale = None

    def emit_note_or_rest(note_val: int, dur_code: int, dur_spec: int) -> None:
        instrs.append(("note", (int(note_val), int(dur_code), int(dur_spec))))

    # Flatten to monophonic: we use each event in sequence.
    for ev in events:
        dur = int(getattr(ev, "dur", 0) or 0)
        if dur <= 0:
            continue

        # Map per-note velocity to Nokia volume (0..15). If it changes, emit a volume instruction.
        try:
            vel = int(getattr(ev, 'vel', 127) or 127)
        except Exception:
            vel = 127
        vol_code = int(round((clamp(vel, 1, 127) / 127.0) * 15.0))
        vol_code = clamp(vol_code, 0, 15)
        if vol_code != current_vol_code:
            current_vol_code = vol_code
            instrs.append(("volume", int(current_vol_code)))

        # Split durations into representable chunks.
        # Nokia RNG supports only a discrete set of durations. We prefer to UNDER-shoot and, if a tiny
        # remainder remains (< minimum representable), we merge it into the previous chunk instead of
        # emitting an extra (spurious) note/rest on round-trip.
        remaining = dur
        last_note_instr_index: Optional[int] = None
        last_qticks: int = 0
        min_qticks = int(_RNG_DUR_CANDS[0][0]) if _RNG_DUR_CANDS else 40

        while remaining > 0:
            # If the remainder is too small to represent, merge it into the previous note/rest by bumping
            # that duration to the nearest representable value.
            if remaining < min_qticks and last_note_instr_index is not None:
                desired = int(last_qticks + remaining)
                nq, ndur_code, ndur_spec = _rng_pick_duration_nearest(desired)
                kind, payload = instrs[last_note_instr_index]
                if kind == "note":
                    note_val, _, _ = payload
                    instrs[last_note_instr_index] = ("note", (int(note_val), int(ndur_code), int(ndur_spec)))
                    last_qticks = int(nq)
                remaining = 0
                break

            qticks, dur_code, dur_spec = _rng_pick_duration(remaining)
            if ev.kind == "rest" or getattr(ev, "pitch", None) is None:
                emit_note_or_rest(0b0000, dur_code, dur_spec)  # pause
                last_note_instr_index = len(instrs) - 1
                last_qticks = int(qticks)
            else:
                pitch = int(ev.pitch)
                scale = _rng_scale_for_pitch(pitch)
                if current_scale is None or scale != current_scale:
                    current_scale = scale
                    instrs.append(("scale", int(scale)))
                note_val = _rng_note_value_for_pitch(pitch)
                emit_note_or_rest(note_val, dur_code, dur_spec)
                last_note_instr_index = len(instrs) - 1
                last_qticks = int(qticks)

            remaining -= qticks
            if qticks <= 0:
                break

    # Pattern specifier: number of following pattern instructions.
    bw.write_bits(len(instrs) & 0xFF, 8)

    # Write instructions.
    for kind, payload in instrs:
        if kind == "tempo_code":
            bw.write_bits(_RNG_I_TEMPO, 3)
            bw.write_bits(int(payload) & 0x1F, 5)
        elif kind == "scale":
            bw.write_bits(_RNG_I_SCALE, 3)
            bw.write_bits(int(payload) & 0x03, 2)
        elif kind == "style":
            bw.write_bits(_RNG_I_STYLE, 3)
            bw.write_bits(int(payload) & 0x03, 2)
        elif kind == "volume":
            bw.write_bits(_RNG_I_VOLUME, 3)
            bw.write_bits(int(payload) & 0x0F, 4)
        elif kind == "note":
            note_val, dur_code, dur_spec = payload
            bw.write_bits(_RNG_I_NOTE, 3)
            bw.write_bits(int(note_val) & 0x0F, 4)
            bw.write_bits(int(dur_code) & 0x07, 3)
            bw.write_bits(int(dur_spec) & 0x03, 2)

    # Align the sound command-part, then terminate the command stream.
    bw.align_byte()
    bw.write_bits(0, 8)  # command-end

    data = bw.to_bytes()
    with open(path, "wb") as f:
        f.write(data)


class ComposerDialog(wx.Dialog):
    def __init__(self, parent, comp: Composition, addon_dir: str):
        super().__init__(parent, title="NVDA Composer", style=wx.DEFAULT_DIALOG_STYLE | wx.RESIZE_BORDER)

        self.comp = comp
        # Step modifier state (kept separate from Composition so it does not affect file formats)
        self._step_mode = "normal"  # "normal", "dotted", or "triplet"
        self._step_base_ticks = int(getattr(self.comp, "step_ticks", 1) or 1)

        self.addon_dir = addon_dir
        self.scales = load_scales(addon_dir)

        self.player = TonePlayer()
        self.preview = PreviewBeep()

        # Playback follow/pause options
        # followPlayback: when enabled, the caret can track playback position (optional).
        # snapOnPause: when enabled, pausing snaps the caret to the pause position.
        self.followPlayback: bool = False
        self.snapOnPause: bool = True
        self._paused: bool = False
        self._paused_at: Optional[int] = None  # event index
        self._paused_end: Optional[int] = None  # event index (exclusive)
        self._play_range: Tuple[int, int] = (0, 0)

        self._followTimer = wx.Timer(self)
        self.Bind(wx.EVT_TIMER, self._onFollowTimer, self._followTimer)

        self._lastNavCursor: Optional[int] = None
        self._lastPath: Optional[str] = None

        self._selAnchor: Optional[int] = None

        # Undo/redo stacks (composition + UI state snapshots)
        self._undoStack: List[dict] = []
        self._redoStack: List[dict] = []
        self._maxUndo: int = 200
        self._isRestoring: bool = False

        # Last used MIDI path (for export defaults)
        self._lastMidiPath: Optional[str] = None

        self._build_ui()
        self.Bind(wx.EVT_CLOSE, self._onClose)

    def _onClose(self, evt):
        try:
            self.player.stop()
        except Exception:
            pass
        self.Hide()

    def _build_ui(self) -> None:
        main = wx.BoxSizer(wx.VERTICAL)

        self.lblStatus = wx.StaticText(self, label=self._status_label())
        main.Add(self.lblStatus, 0, wx.EXPAND | wx.LEFT | wx.RIGHT | wx.TOP, 8)

        self.list = wx.ListBox(self, style=wx.LB_EXTENDED)
        main.Add(self.list, 1, wx.EXPAND | wx.ALL, 8)

        row = wx.BoxSizer(wx.HORIZONTAL)
        self.btnPlay = wx.Button(self, label="Play\tEnter")
        self.btnStop = wx.Button(self, label="Stop\tEsc")
        self.btnClose = wx.Button(self, label="Close\tAlt+F4")
        row.Add(self.btnPlay, 0, wx.RIGHT, 6)
        row.Add(self.btnStop, 0, wx.RIGHT, 6)
        row.AddStretchSpacer(1)
        row.Add(self.btnClose, 0)
        main.Add(row, 0, wx.EXPAND | wx.ALL, 8)

        self.SetSizer(main)
        self.SetMinSize((720, 380))

        self.btnPlay.Bind(wx.EVT_BUTTON, self._onPlay)
        self.btnStop.Bind(wx.EVT_BUTTON, self._onStop)
        self.btnClose.Bind(wx.EVT_BUTTON, lambda e: self.Close())

        self.list.Bind(wx.EVT_CHAR_HOOK, self._onListCharHook)
        self.list.Bind(wx.EVT_LISTBOX, self._onListboxSelection)

        self.refreshList(setFocus=True)

    def _deselectAll(self) -> None:
        try:
            sels = list(self.list.GetSelections())
        except Exception:
            sels = []
        for i in sels:
            try:
                self.list.Deselect(int(i))
            except Exception:
                pass

    def _select_all_events(self) -> None:
        # Select all *events* (exclude the "Beginning" and "End" sentinels).
        if not self.comp.events:
            ui.message("Nothing to select")
            return
        self._deselectAll()
        # Display indices: 0=Beginning, 1..len(events)=events, last=End
        first = 1
        last = len(self.comp.events)
        for di in range(first, last + 1):
            try:
                self.list.Select(int(di))
            except Exception:
                pass
        # Place caret at end of the selection range (common editor behavior)
        self.comp.cursor = clamp(last, 0, self.comp.display_len() - 1)
        self._selAnchor = first
        self._lastNavCursor = self.comp.cursor
        try:
            self.list.SetFocus()
        except Exception:
            pass
        ui.message(f"Selected {len(self.comp.events)}")

    def _status_label(self) -> str:
        # This label doubles as the accessible label for the timeline listbox in wx,
        # so keep it informative but easy to listen to.
        proj = "Untitled"
        # Prefer an explicit track title (F2). If no title is set, fall back to the filename.
        title = ""
        try:
            title = str(getattr(self.comp, "title", "") or "").strip()
        except Exception:
            title = ""
        if title:
            proj = title
        else:
            src_path = self._lastPath or getattr(self, "_lastMidiPath", None)
            if src_path:
                try:
                    proj = os.path.splitext(os.path.basename(src_path))[0] or proj
                except Exception:
                    pass

        mode = "Chromatic" if self.comp.chromatic_mode else "Scale"
        sname = self.scales[self.comp.scale_index][0] if self.scales else "Major"
        root = note_name(self.comp.base_note + self.comp.input_transpose)
        layout = "QWERTY" if self.comp.qwerty_layout else "Grid"
        step_name = dur_label(self.comp.step_ticks, self.comp.ppq)
        dirty = " (modified)" if self.comp.dirty else ""

        return (
            f"Project: {proj}{dirty}. "
            f"Tempo: {self.comp.tempo_bpm} BPM. "
            f"Step: {step_name}. "
            f"Mode: {mode}. "
            f"Scale: {sname}. "
            f"Layout: {layout}. "
            f"Input: {root}."
        )


    def _update_status(self, announce: Optional[str] = None) -> None:
        self.lblStatus.SetLabel(self._status_label())
        self.Layout()
        if announce:
            ui.message(announce)

    def _mark_dirty(self):
        self.comp.dirty = True
        self._update_status()

    def _make_snapshot(self) -> dict:
        return {
            "events": [(e.kind, e.pitch, e.dur, getattr(e, "vel", getattr(e, "velocity", 127))) for e in self.comp.events],
            "cursor": int(self.comp.cursor),
            "tempo_bpm": int(self.comp.tempo_bpm),
            "ppq": int(self.comp.ppq),
            "step_ticks": int(self.comp.step_ticks),
            "base_note": int(self.comp.base_note),
            "input_transpose": int(self.comp.input_transpose),
            "input_velocity": int(getattr(self.comp, "input_velocity", 127)),
            "chromatic_mode": bool(self.comp.chromatic_mode),
            "scale_index": int(self.comp.scale_index),
            "qwerty_layout": bool(self.comp.qwerty_layout),
            "dirty": bool(self.comp.dirty),
            "lastPath": self._lastPath,
            "lastMidiPath": self._lastMidiPath,
            "selAnchor": self._selAnchor,
            "selEvents": list(self._selected_event_indices()),
        }

    def _restore_snapshot(self, snap: dict) -> None:
        self._isRestoring = True
        try:
            evs = []
            for tup in snap.get("events", []):
                try:
                    k, p, d, v = tup
                except ValueError:
                    # Backward-compat: older snapshots stored (kind, pitch, dur)
                    k, p, d = tup
                    v = 127
                evs.append(Event(kind=k, pitch=p, dur=d, vel=int(v)))
            self.comp.events = evs
            self.comp.cursor = int(snap.get("cursor", 0))
            self.comp.tempo_bpm = int(snap.get("tempo_bpm", 120))
            self.comp.ppq = int(snap.get("ppq", 480))
            self.comp.step_ticks = int(snap.get("step_ticks", 480))
            self.comp.base_note = int(snap.get("base_note", 60))
            self.comp.input_transpose = int(snap.get("input_transpose", 0))
            self.comp.input_velocity = int(snap.get("input_velocity", getattr(self.comp, "input_velocity", 127)))
            self.comp.chromatic_mode = bool(snap.get("chromatic_mode", False))
            self.comp.scale_index = int(snap.get("scale_index", 0))
            self.comp.qwerty_layout = bool(snap.get("qwerty_layout", False))
            self.comp.dirty = bool(snap.get("dirty", False))

            self._lastPath = snap.get("lastPath", self._lastPath)
            self._lastMidiPath = snap.get("lastMidiPath", self._lastMidiPath)
            self._selAnchor = snap.get("selAnchor", None)

            self.refreshList(setFocus=True)

            # Re-apply multi-selection (event indices -> display indices)
            sels = snap.get("selEvents", []) or []
            try:
                self._deselectAll()
                for ei in sels:
                    di = int(ei) + 1  # +1 for "Beginning" sentinel
                    if 0 <= di < self.comp.display_len():
                        self.list.SetSelection(di, True)
            except Exception:
                pass

            # Keep cursor visible and selected
            self.comp.cursor = clamp(self.comp.cursor, 0, self.comp.display_len() - 1)
            try:
                self.list.SetSelection(int(self.comp.cursor), True)
            except Exception:
                pass

            self._update_status()
        finally:
            self._isRestoring = False

    def _push_undo(self) -> None:
        if self._isRestoring:
            return
        self._undoStack.append(self._make_snapshot())
        if len(self._undoStack) > self._maxUndo:
            self._undoStack.pop(0)
        self._redoStack.clear()

    def _undo(self) -> None:
        if not self._undoStack:
            ui.message("Nothing to undo")
            return
        cur = self._make_snapshot()
        snap = self._undoStack.pop()
        self._redoStack.append(cur)
        self._restore_snapshot(snap)
        ui.message("Undo")

    def _redo(self) -> None:
        if not self._redoStack:
            ui.message("Nothing to redo")
            return
        cur = self._make_snapshot()
        snap = self._redoStack.pop()
        self._undoStack.append(cur)
        self._restore_snapshot(snap)
        ui.message("Redo")

    
    def _do_export_midi(self) -> None:
        """Export the current project.

        Ctrl+E opens a single export dialog that can write:
          - MIDI (.mid/.midi)
          - WAV (.wav) simple sine preview
          - WAV (.wav) Nokia-style beep render
          - Nokia ringing tone (.rng) for classic phones
        """
        # Stop playback while exporting to avoid timing/tempo confusion.
        self._stop_playback()

        # Base name suggestion
        base = "composition"
        try:
            if getattr(self, "_lastPath", None):
                b = os.path.splitext(os.path.basename(self._lastPath))[0]
                if b:
                    base = b
            elif getattr(self, "_lastMidiPath", None):
                b = os.path.splitext(os.path.basename(self._lastMidiPath))[0]
                if b:
                    base = b
        except Exception:
            pass

        wildcard = "MIDI files (*.mid;*.midi)|*.mid;*.midi|WAV audio (*.wav)|*.wav|Nokia WAV audio (*.wav)|*.wav|Nokia ringing tone (*.rng)|*.rng|All files (*.*)|*.*"
        with wx.FileDialog(
            self,
            message="Export",
            wildcard=wildcard,
            style=wx.FD_SAVE | wx.FD_OVERWRITE_PROMPT,
            defaultFile=base + ".mid",
        ) as fd:
            if fd.ShowModal() != wx.ID_OK:
                return
            path = fd.GetPath()
            filt = int(getattr(fd, "GetFilterIndex", lambda: 0)())

        ext = os.path.splitext(path)[1].lower()
        # Choose export type based on filter index; fall back to extension.
        export_kind = None
        if filt == 0:
            export_kind = "midi"
        elif filt == 1:
            export_kind = "wav"
        elif filt == 2:
            export_kind = "wav_nokia"
        elif filt == 3:
            export_kind = "rng"
        else:
            if ext in (".wav",):
                export_kind = "wav"
            elif ext in (".rng",):
                export_kind = "rng"
            else:
                export_kind = "midi"

        try:
            if export_kind == "midi":
                if ext not in (".mid", ".midi"):
                    path = path + ".mid"
                _write_midi_file(
                    path,
                    self.comp.events,
                    int(self.comp.tempo_bpm),
                    int(self.comp.ppq),
                    tempo_map=getattr(self.comp, "tempo_map", None),
                )
                self._lastMidiPath = path
                ui.message("Exported MIDI")
                return


            if export_kind == "rng":
                if ext != ".rng":
                    path = path + ".rng"
                title = "composition"
                try:
                    # Use the suggested base name (or last filename) as the ringtone title.
                    title = os.path.splitext(os.path.basename(path))[0] or title
                except Exception:
                    pass
                _write_rng_file(path, self.comp.events, int(self.comp.tempo_bpm), int(self.comp.ppq), title=title)
                ui.message("Exported Nokia .rng")
                return

            # WAV exports
            if ext != ".wav":
                path = path + ".wav"
            style = "sine" if export_kind == "wav" else "nokia"
            _write_wav_file(
                path,
                self.comp.events,
                int(self.comp.tempo_bpm),
                int(self.comp.ppq),
                tempo_map=getattr(self.comp, "tempo_map", None),
                style=style,
            )
            if style == "nokia":
                ui.message("Exported Nokia WAV")
            else:
                ui.message("Exported WAV")
        except Exception as e:
            ui.message(f"Export failed: {e}")

    def _do_import_midi(self, path: Optional[str] = None, confirm: bool = True) -> None:
        # Stop any ongoing playback before importing.
        self._stop_playback()

        # Import replaces the current project, so confirm unsaved work (unless caller already did).
        if confirm:
            res = self._confirm_unsaved()
            if res == wx.ID_CANCEL:
                return
            if res == wx.ID_YES:
                self._do_save()
                if self.comp.dirty:
                    return

        # If a path is provided (e.g. from Ctrl+O), do NOT show a second dialog.
        if path is None:
            with wx.FileDialog(
                self,
                message="Import MIDI",
                wildcard="MIDI files (*.mid;*.midi)|*.mid;*.midi|All files (*.*)|*.*",
                style=wx.FD_OPEN | wx.FD_FILE_MUST_EXIST
            ) as fd:
                if fd.ShowModal() != wx.ID_OK:
                    return
                path = fd.GetPath()

        events, bpm, src_ppq, tempo_map = _read_midi_file(path, target_ppq=480)
        if not events:
            ui.message("No note events found in MIDI")
            return

        # Clear undo/redo; treat this as a new loaded project (unsaved in txt).
        self._undoStack.clear()
        self._redoStack.clear()

        self.comp.events = events
        self.comp.cursor = 0
        self.comp.tempo_bpm = bpm
        try:
            self.comp.tempo_map = tempo_map or [(0, int(bpm))]
        except Exception:
            pass
        self.comp.ppq = 480
        self.comp.step_ticks = 480  # Quarter default (can be changed by user)
        self.comp.base_note = 60
        self.comp.input_transpose = 0
        self.comp.chromatic_mode = False
        self.comp.scale_index = 0
        self.comp.qwerty_layout = False

        self.comp.title = ""
        self.comp.notes = ""
        self.comp.markers = []

        self.comp.dirty = False
        self._lastPath = None
        self._lastMidiPath = None
        self._lastMidiPath = path
        self._selAnchor = None

        self.refreshList(setFocus=True)
        ui.message("Imported MIDI")

    def _do_import_rng(self, path: Optional[str] = None, confirm: bool = True) -> None:
        # Stop any ongoing playback before importing.
        self._stop_playback()

        # Import replaces the current project, so confirm unsaved work (unless caller already did).
        if confirm:
            res = self._confirm_unsaved()
            if res == wx.ID_CANCEL:
                return
            if res == wx.ID_YES:
                self._do_save()
                if self.comp.dirty:
                    return

        if path is None:
            with wx.FileDialog(
                self,
                message="Import Nokia ringtone (.rng)",
                wildcard="Nokia ringtones (*.rng)|*.rng|All files (*.*)|*.*",
                style=wx.FD_OPEN | wx.FD_FILE_MUST_EXIST
            ) as fd:
                if fd.ShowModal() != wx.ID_OK:
                    return
                path = fd.GetPath()

        try:
            with open(path, 'rb') as f:
                data = f.read()
            comp, title = comp_from_rng_bytes(data)
        except Exception as e:
            ui.message(f"Import .rng failed: {e}")
            return
        # Clear undo/redo; treat this as a new loaded project.
        self._undoStack.clear()
        self._redoStack.clear()


        # Replace current composition with imported data
        self.comp.events = comp.events
        self.comp.cursor = 0
        self.comp.tempo_bpm = comp.tempo_bpm
        self.comp.tempo_map = comp.tempo_map
        self.comp.step_ticks = comp.step_ticks
        self.comp.base_note = comp.base_note
        self.comp.input_transpose = comp.input_transpose
        self.comp.chromatic_mode = comp.chromatic_mode
        self.comp.scale_index = comp.scale_index
        self.comp.qwerty_layout = comp.qwerty_layout
        self.comp.title = str(title or "")
        self.comp.notes = ""
        self.comp.markers = []

        self.comp.dirty = False
        self._lastPath = None
        self._lastMidiPath = path  # used for suggesting default save name
        self._selAnchor = None

        self.refreshList(setFocus=True)
        ui.message("Imported .rng")


    def refreshList(self, setFocus: bool = False) -> None:
        items: List[str] = []
        items.append("Beginning")
        for i, ev in enumerate(self.comp.events):
            if ev.kind == "rest":
                items.append(f"{i+1}: Rest ({dur_label(ev.dur, self.comp.ppq)})")
            else:
                items.append(f"{i+1}: {note_name(ev.pitch)} ({dur_label(ev.dur, self.comp.ppq)})")
        items.append("End")

        self.list.Set(items)
        if setFocus:
            self.list.SetFocus()

        self._deselectAll()
        self.comp.cursor = clamp(self.comp.cursor, 0, self.comp.display_len() - 1)
        self.list.SetSelection(self.comp.cursor)

        self._update_status()

    def _set_tempo(self, bpm: int, announce: bool = True) -> None:
        bpm = clamp(int(bpm), 10, 999)
        self.comp.tempo_bpm = bpm
        # The UI edits a single global tempo; reset tempo map accordingly.
        try:
            self.comp.tempo_map = [(0, int(bpm))]
        except Exception:
            pass
        self._mark_dirty()
        if announce:
            self._update_status(f"{bpm} BPM")

    def _current_scale(self) -> Tuple[str, List[int]]:
        if not self.scales:
            return ("Major", [0, 2, 4, 5, 7, 9, 11])
        self.comp.scale_index = clamp(self.comp.scale_index, 0, len(self.scales) - 1)
        return self.scales[self.comp.scale_index]

    def _preview_pitch(self, pitch: int, dur_ticks: int, vel: Optional[int] = None) -> None:
        if tones is None:
            return
        ms = max(1, int(ticks_to_seconds(dur_ticks, self.comp.tempo_bpm, self.comp.ppq) * 1000.0))
        beep_ms = max(1, int(ms * 0.95))
        vol0_100 = 100
        try:
            if vel is not None:
                vol0_100 = int(round((clamp(int(vel), 1, 127) / 127.0) * 100.0))
        except Exception:
            vol0_100 = 100
        self.preview.request(midi_to_freq(int(pitch)), beep_ms, vol0_100=vol0_100)

    def _selected_display_indices(self) -> List[int]:
        try:
            sels = list(self.list.GetSelections())
        except Exception:
            sels = []
        return sorted(int(x) for x in sels)

    def _selected_event_indices(self) -> List[int]:
        out: List[int] = []
        for di in self._selected_display_indices():
            ei = self.comp.disp_to_event_index(di)
            if ei is not None:
                out.append(ei)
        return sorted(set(out))

    def _insert_event(self, ev: Event) -> None:
        self._push_undo()
        idx = self.comp.insertion_event_index()
        self.comp.events.insert(idx, ev)

        # Move cursor to the inserted event row (display index = event index + 1)
        self.comp.cursor = idx + 1
        self._selAnchor = None

        self._mark_dirty()
        self.refreshList(setFocus=True)

        if ev.kind == "note" and ev.pitch is not None:
            self._preview_pitch(ev.pitch, ev.dur, vel=getattr(ev,'vel',None))

    def _move_cursor(self, delta: int, extendSelection: bool = False) -> None:
        """Move caret along the timeline (Left/Right).

        If extendSelection is True (Shift+Left/Right), extend a contiguous selection range
        from an anchor to the new cursor position, and preview the note under the cursor.
        """
        old_cursor = int(self.comp.cursor)
        self.comp.cursor = clamp(self.comp.cursor + int(delta), 0, self.comp.display_len() - 1)

        # Avoid replay spam at edges on key-repeat
        if self._lastNavCursor == self.comp.cursor and not extendSelection:
            self._deselectAll()
            try:
                self.list.SetSelection(self.comp.cursor)
            except Exception:
                pass
            return
        self._lastNavCursor = self.comp.cursor

        if extendSelection:
            if self._selAnchor is None:
                self._selAnchor = old_cursor
            a = clamp(int(self._selAnchor), 0, self.comp.display_len() - 1)
            b = clamp(int(self.comp.cursor), 0, self.comp.display_len() - 1)
            lo, hi = (a, b) if a <= b else (b, a)
            self._deselectAll()
            for i in range(lo, hi + 1):
                try:
                    # In multi-select listboxes, SetSelection(i, True) adds to selection.
                    self.list.SetSelection(i, True)
                except TypeError:
                    try:
                        self.list.SetSelection(i)
                    except Exception:
                        pass
                except Exception:
                    pass
        else:
            self._selAnchor = None
            self._deselectAll()
            try:
                self.list.SetSelection(self.comp.cursor)
            except Exception:
                pass

        # For Beginning/End: let listbox speak label. Otherwise announce + preview.
        if self.comp.is_begin(self.comp.cursor) or self.comp.is_end(self.comp.cursor):
            return

        ei = self.comp.disp_to_event_index(self.comp.cursor)
        if ei is None or ei < 0 or ei >= len(self.comp.events):
            return
        ev = self.comp.events[ei]
        if ev.kind == "rest":
            ui.message("Rest")
        else:
            ui.message(f"{note_name(ev.pitch)}, velocity {clamp(int(getattr(ev,'vel',127) or 127),1,127)}")
            self._preview_pitch(ev.pitch, ev.dur, vel=getattr(ev,'vel',None))

    def _transpose_selected(self, semitones: int) -> None:
        self._push_undo()

        # Preserve display selections so transposition does not unexpectedly
        # deselect the user's range.
        sel_disp = self._selected_display_indices()
        sels = self._selected_event_indices()

        if not sels:
            # If cursor is on an event row, target it.
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is None:
                ui.message("Nothing selected")
                return
            sels = [ei]
            sel_disp = [self.comp.cursor]

        multi = len(sels) > 1
        changed = 0
        last_pitch: Optional[int] = None
        last_dur: Optional[int] = None

        for i in sels:
            if 0 <= i < len(self.comp.events):
                ev = self.comp.events[i]
                if ev.kind == "note" and ev.pitch is not None:
                    ev.pitch = int(ev.pitch) + int(semitones)
                    changed += 1
                    last_pitch = int(ev.pitch)
                    last_dur = int(ev.dur)

        if not changed:
            ui.message("Nothing to transpose")
            return

        self._mark_dirty()
        self.refreshList(setFocus=True)

        # Restore the user's selection range (transpose doesn't change list length).
        if sel_disp:
            self._deselectAll()
            max_di = self.comp.display_len() - 1
            for di in sorted(set(clamp(int(x), 0, max_di) for x in sel_disp)):
                try:
                    self.list.SetSelection(di, True)
                except TypeError:
                    # Fallback: some wx builds don't accept the "add" flag.
                    try:
                        self.list.SetSelection(di)
                    except Exception:
                        pass
                except Exception:
                    pass

        # Sound feedback only for single-note transpose.
        if not multi and last_pitch is not None:
            ui.message(note_name(last_pitch))
            self._preview_pitch(last_pitch, last_dur or self.comp.step_ticks)
        else:
            ui.message(f"Transposed {changed} notes")

    def _change_length_selected(self, direction: int) -> None:
        self._push_undo()

        # Preserve the user's selection so length changes don't unexpectedly
        # collapse multi-selections (same behavior as transpose).
        sel_disp = self._selected_display_indices()
        sels = self._selected_event_indices()
        if not sels:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is None:
                ui.message("Nothing selected")
                return
            sels = [ei]
            sel_disp = [self.comp.cursor]

        factor = 0.5 if direction < 0 else 2.0
        changed = 0
        last_pitch = None
        last_dur = None
        multi = len(sels) > 1

        for i in sels:
            if 0 <= i < len(self.comp.events):
                ev = self.comp.events[i]
                ev.dur = max(1, int(round(ev.dur * factor)))
                changed += 1
                if not multi and ev.kind == "note" and ev.pitch is not None:
                    last_pitch = int(ev.pitch)
                    last_dur = int(ev.dur)

        if not changed:
            ui.message("Nothing to change")
            return

        self._mark_dirty()
        self.refreshList(setFocus=True)

        # Restore the selection range (length edits don't change list length).
        if sel_disp:
            self._deselectAll()
            max_di = self.comp.display_len() - 1
            for di in sorted(set(clamp(int(x), 0, max_di) for x in sel_disp)):
                try:
                    self.list.SetSelection(di, True)
                except TypeError:
                    try:
                        self.list.SetSelection(di)
                    except Exception:
                        pass
                except Exception:
                    pass

        # Feedback: speak duration, and preview only for single-note edits.
        if not multi and sels and 0 <= sels[0] < len(self.comp.events):
            ui.message(dur_label(self.comp.events[sels[0]].dur, self.comp.ppq))
            if last_pitch is not None:
                self._preview_pitch(last_pitch, last_dur or self.comp.step_ticks)
        else:
            ui.message(f"Changed length of {changed}")


    def _common_duration_bases(self, extra: tuple[int, ...] = ()) -> set[int]:
        """Return a set of 'musical' base durations (in ticks) used for dotted/triplet detection.

        This avoids mis-detecting plain quarter notes (e.g. 480) as 'undotting' to triplet values (e.g. 320).
        """
        ppq = int(getattr(self.comp, "ppq", 480) or 480)
        bases = {
            max(1, ppq * 4),          # whole
            max(1, ppq * 2),          # half
            max(1, ppq),              # quarter
            max(1, ppq // 2),         # eighth
            max(1, ppq // 4),         # sixteenth
            max(1, ppq // 8),         # thirty-second
        }
        for b in extra:
            try:
                b = int(b)
            except Exception:
                continue
            if b > 0:
                bases.add(b)
        return bases

    def _toggle_dotted_ticks(self, ticks: int, base_hint: int | None = None) -> int:
        """Toggle dotted/undotted for a tick value.

        Undotting only happens if the current duration is a dotted form of a 'reasonable' base duration.
        Otherwise we treat the value as undotted and apply dotting (× 3/2).
        """
        ticks = int(max(1, ticks))
        bases = self._common_duration_bases(extra=(() if base_hint is None else (int(base_hint),)))
        # Dotted values satisfy: ticks = base * 3/2  => base = ticks * 2/3
        if (ticks * 2) % 3 == 0:
            base = (ticks * 2) // 3
            if base in bases:
                return int(max(1, base))
        # Otherwise make dotted (3/2), rounded to nearest tick
        return int(max(1, (ticks * 3 + 1) // 2))

    def _toggle_triplet_ticks(self, ticks: int, base_hint: int | None = None) -> int:
        """Toggle triplet/normal for a tick value.

        Normalizing back only happens if the current duration is a triplet form of a 'reasonable' base duration.
        Otherwise we treat the value as normal and apply triplet scaling (× 2/3).
        """
        ticks = int(max(1, ticks))
        bases = self._common_duration_bases(extra=(() if base_hint is None else (int(base_hint),)))
        # Triplet values satisfy: ticks = base * 2/3  => base = ticks * 3/2
        if (ticks * 3) % 2 == 0:
            base = (ticks * 3) // 2
            if base in bases:
                return int(max(1, base))
        # Otherwise make triplet (2/3), rounded to nearest tick
        return int(max(1, (ticks * 2 + 1) // 3))

    def _toggle_step_dotted(self) -> None:
        """Toggle dotted step for new notes/rests (mutually exclusive with triplet)."""
        self._push_undo()
        mode = getattr(self, "_step_mode", "normal") or "normal"
        base = int(getattr(self, "_step_base_ticks", int(self.comp.step_ticks) or 1) or 1)

        if mode == "dotted":
            # Back to normal
            self.comp.step_ticks = int(max(1, base))
            self._step_mode = "normal"
        else:
            # If we were in triplet mode, keep the same base and switch modifiers.
            if mode == "normal":
                base = int(self.comp.step_ticks) or 1
                self._step_base_ticks = int(max(1, base))
            self.comp.step_ticks = int(max(1, (base * 3 + 1) // 2))
            self._step_mode = "dotted"

        self._mark_dirty()
        label = dur_label(self.comp.step_ticks, self.comp.ppq)
        if self._step_mode == "dotted":
            self._update_status(f"Step dotted {label}")
        else:
            self._update_status(f"Step {label}")
        return

    def _toggle_step_triplet(self) -> None:
        """Toggle triplet step for new notes/rests (mutually exclusive with dotted)."""
        self._push_undo()
        mode = getattr(self, "_step_mode", "normal") or "normal"
        base = int(getattr(self, "_step_base_ticks", int(self.comp.step_ticks) or 1) or 1)

        if mode == "triplet":
            self.comp.step_ticks = int(max(1, base))
            self._step_mode = "normal"
        else:
            if mode == "normal":
                base = int(self.comp.step_ticks) or 1
                self._step_base_ticks = int(max(1, base))
            self.comp.step_ticks = int(max(1, (base * 2 + 1) // 3))
            self._step_mode = "triplet"

        self._mark_dirty()
        label = dur_label(self.comp.step_ticks, self.comp.ppq)
        if self._step_mode == "triplet":
            self._update_status(f"Step triplet {label}")
        else:
            self._update_status(f"Step {label}")
        return

    def _parse_custom_ticks_input(self, s: str) -> int:
        """Parse a user-entered duration into ticks.

        Accepted forms:
          - ticks: 333
          - ticks with suffix: 333t
          - beats (quarter notes): 1.5b
          - fraction of a whole note: 3/16
        """
        s = (s or "").strip().lower()
        if not s:
            raise ValueError("Empty value")

        # Explicit ticks suffix
        if s.endswith("t"):
            s = s[:-1].strip()
            v = int(s)
            if v <= 0:
                raise ValueError("Ticks must be > 0")
            return v

        # Beats (quarter notes). Supports:
        #   1.5b        (beats, using current PPQ)
        #   1.5b480     (beats, explicitly specifying PPQ)
        m = re.match(r'^([0-9]*\.?[0-9]+)\s*b\s*(\d+)?$', s)
        if m:
            beats = float(m.group(1))
            if beats <= 0:
                raise ValueError("Beats must be > 0")
            ppq = int(m.group(2)) if m.group(2) else int(self.comp.ppq)
            if ppq <= 0:
                raise ValueError("PPQ must be > 0")
            ticks = int(round(beats * ppq))
            return max(1, ticks)

        # Fraction of a whole note (whole = ppq * 4)
        if "/" in s:
            num_s, den_s = s.split("/", 1)
            num = int(num_s.strip())
            den = int(den_s.strip())
            if num <= 0 or den <= 0:
                raise ValueError("Bad fraction")
            whole = int(self.comp.ppq) * 4
            ticks = int(round(whole * (num / den)))
            return max(1, ticks)

        # Plain integer ticks
        v = int(s)
        if v <= 0:
            raise ValueError("Ticks must be > 0")
        return v

    def _prompt_custom_ticks(self, title: str, initial: str = "") -> Optional[int]:
        """Return ticks from user input or None if cancelled.

        The input field is pre-filled with *initial* and **select-all** is applied reliably,
        so the first character you type overwrites the previous value (prevents concatenation).
        """
        prompt = "Enter duration as ticks (e.g. 333 or 333t), beats (e.g. 1.5b or 1.5b480), or a fraction of a whole note (e.g. 3/16)."
        current_initial = str(initial or "")
        while True:
            dlg = wx.Dialog(self, title=title)
            try:
                sizer = wx.BoxSizer(wx.VERTICAL)
                sizer.Add(wx.StaticText(dlg, label=prompt), 0, wx.ALL, 10)

                tc = wx.TextCtrl(dlg, value=current_initial)
                sizer.Add(tc, 0, wx.EXPAND | wx.LEFT | wx.RIGHT, 10)

                btns = dlg.CreateButtonSizer(wx.OK | wx.CANCEL)
                if btns:
                    sizer.Add(btns, 0, wx.EXPAND | wx.ALL, 10)

                dlg.SetSizerAndFit(sizer)

                # Ensure focus + select-all happens after the dialog is actually shown.
                def _on_show(evt):
                    wx.CallAfter(lambda: (tc.SetFocus(), tc.SetSelection(-1, -1)))
                    evt.Skip()

                dlg.Bind(wx.EVT_SHOW, _on_show)

                if dlg.ShowModal() != wx.ID_OK:
                    return None

                raw = (tc.GetValue() or "").strip()

                try:
                    return self._parse_custom_ticks_input(raw)
                except Exception:
                    ui.message("Invalid value. Examples: 333, 333t, 1.5b, 1.5b480, 3/16.")
                    current_initial = raw or current_initial
                    continue
            finally:
                dlg.Destroy()
    def _prompt_int_range(self, title: str, prompt: str, initial: str, vmin: int, vmax: int, error_msg: str) -> Optional[int]:
        """Prompt for an integer in a range (inclusive)."""
        current_initial = str(initial or "")
        while True:
            dlg = wx.Dialog(self, title=title)
            try:
                sizer = wx.BoxSizer(wx.VERTICAL)
                sizer.Add(wx.StaticText(dlg, label=prompt), 0, wx.ALL, 10)

                tc = wx.TextCtrl(dlg, value=current_initial)
                sizer.Add(tc, 0, wx.EXPAND | wx.LEFT | wx.RIGHT, 10)

                btns = dlg.CreateButtonSizer(wx.OK | wx.CANCEL)
                if btns:
                    sizer.Add(btns, 0, wx.EXPAND | wx.ALL, 10)

                dlg.SetSizerAndFit(sizer)

                def _on_show(evt):
                    wx.CallAfter(lambda: (tc.SetFocus(), tc.SetSelection(-1, -1)))
                    evt.Skip()

                dlg.Bind(wx.EVT_SHOW, _on_show)

                if dlg.ShowModal() != wx.ID_OK:
                    return None

                raw = (tc.GetValue() or "").strip()
                try:
                    v = int(raw)
                    if v < int(vmin) or v > int(vmax):
                        raise ValueError()
                    return v
                except Exception:
                    ui.message(error_msg)
                    current_initial = raw or current_initial
                    continue
            finally:
                dlg.Destroy()

    def _prompt_velocity(self, title: str, initial: str = "") -> Optional[int]:
        """Prompt for a velocity value (1..127)."""
        return self._prompt_int_range(
            title=title,
            prompt="Enter velocity (1 to 127).",
            initial=initial,
            vmin=1,
            vmax=127,
            error_msg="Velocity must be a number from 1 to 127.",
        )

    def _prompt_tempo(self, title: str, initial: str = "") -> Optional[int]:
        """Prompt for a tempo value in BPM."""
        return self._prompt_int_range(
            title=title,
            prompt="Enter tempo in BPM (20 to 999).",
            initial=initial,
            vmin=20,
            vmax=999,
            error_msg="Tempo must be a number from 20 to 999.",
        )



    def _set_velocity_from_prompt(self) -> None:
        """Press V to set velocity: applies to selection if present, otherwise sets input velocity."""
        sels = self._selected_event_indices()
        initial = ""
        if sels:
            # Prefer the first selected note velocity for initial value.
            for ei in sels:
                if 0 <= ei < len(self.comp.events):
                    ev = self.comp.events[ei]
                    if getattr(ev, "kind", "") == "note":
                        initial = str(clamp(int(getattr(ev, "vel", 127) or 127), 1, 127))
                        break
        if not initial:
            initial = str(clamp(int(getattr(self.comp, "input_velocity", 127) or 127), 1, 127))

        v = self._prompt_velocity("Velocity", initial=initial)
        if v is None:
            return

        if sels:
            changed = False
            self._push_undo()
            for ei in sels:
                if 0 <= ei < len(self.comp.events):
                    ev = self.comp.events[ei]
                    if getattr(ev, "kind", "") == "note":
                        ev.vel = int(v)
                        changed = True
            if changed:
                self._mark_dirty()
                self.refreshList(setFocus=True)
            ui.message(f"Velocity {v}")
            # Preview the first selected note.
            for ei in sels:
                if 0 <= ei < len(self.comp.events):
                    ev = self.comp.events[ei]
                    if getattr(ev, "kind", "") == "note" and getattr(ev, "pitch", None) is not None:
                        self._preview_pitch(int(ev.pitch), int(ev.dur), vel=int(v))
                        break
        else:
            self.comp.input_velocity = int(v)
            ui.message(f"Velocity {v}")
            # Preview note under cursor if any.
            try:
                ei = self.comp.disp_to_event_index(self.comp.cursor)
                if ei is not None and 0 <= ei < len(self.comp.events):
                    ev = self.comp.events[ei]
                    if getattr(ev, "kind", "") == "note" and getattr(ev, "pitch", None) is not None:
                        self._preview_pitch(int(ev.pitch), int(ev.dur), vel=int(v))
            except Exception:
                pass
    def _set_tempo_from_prompt(self) -> None:
        bpm = self._prompt_tempo("Tempo", initial=str(int(getattr(self.comp, "tempo_bpm", 120) or 120)))
        if bpm is None:
            return
        self._set_tempo(int(bpm), announce=True)



    def _set_custom_step_from_prompt(self) -> None:
        ticks = self._prompt_custom_ticks("Custom step length", initial=str(int(getattr(self.comp, "step_ticks", 0) or 0)))
        if ticks is None:
            return
        self._set_step_ticks(int(ticks), announce=True)

    def _set_custom_duration_selected_from_prompt(self) -> None:
        ticks = self._prompt_custom_ticks("Custom duration", initial="")
        if ticks is None:
            return
        self._set_duration_selected_ticks(int(ticks))

    def _set_duration_selected_ticks(self, ticks: int) -> None:
        """Set duration for selected events (or current event) to a fixed tick value."""
        self._push_undo()

        sel_disp = self._selected_display_indices()
        sels = self._selected_event_indices()
        if not sels:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is None:
                ui.message("Nothing selected")
                return
            sels = [ei]
            sel_disp = [self.comp.cursor]

        ticks = int(max(1, ticks))
        multi = len(sels) > 1
        last_pitch = None
        last_dur = None

        for i in sels:
            if 0 <= i < len(self.comp.events):
                self.comp.events[i].dur = ticks
                if not multi and self.comp.events[i].kind == "note" and self.comp.events[i].pitch is not None:
                    last_pitch = int(self.comp.events[i].pitch)
                    last_dur = int(self.comp.events[i].dur)

        self._mark_dirty()
        self.refreshList(setFocus=True)

        # Restore selection.
        if sel_disp:
            self._deselectAll()
            max_di = self.comp.display_len() - 1
            for di in sorted(set(clamp(int(x), 0, max_di) for x in sel_disp)):
                try:
                    self.list.SetSelection(di, True)
                except TypeError:
                    try:
                        self.list.SetSelection(di)
                    except Exception:
                        pass
                except Exception:
                    pass

        # Feedback
        label = dur_label(ticks, self.comp.ppq)
        if not multi:
            ui.message(label)
            if last_pitch is not None:
                self._preview_pitch(last_pitch, last_dur or ticks)
        else:
            ui.message(f"Set length to {label} for {len(sels)}")

    def _toggle_dotted_duration_selected(self) -> None:
        """Toggle dotted/undotted for selected events (or current event)."""
        self._push_undo()

        sel_disp = self._selected_display_indices()
        sels = self._selected_event_indices()
        if not sels:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is None:
                ui.message("Nothing selected")
                return
            sels = [ei]
            sel_disp = [self.comp.cursor]

        multi = len(sels) > 1
        last_pitch = None
        last_dur = None

        for i in sels:
            if 0 <= i < len(self.comp.events):
                ev = self.comp.events[i]
                ev.dur = self._toggle_dotted_ticks(ev.dur)
                if not multi and ev.kind == "note" and ev.pitch is not None:
                    last_pitch = int(ev.pitch)
                    last_dur = int(ev.dur)

        self._mark_dirty()
        self.refreshList(setFocus=True)

        # Restore selection.
        if sel_disp:
            self._deselectAll()
            max_di = self.comp.display_len() - 1
            for di in sorted(set(clamp(int(x), 0, max_di) for x in sel_disp)):
                try:
                    self.list.SetSelection(di, True)
                except TypeError:
                    try:
                        self.list.SetSelection(di)
                    except Exception:
                        pass
                except Exception:
                    pass

        if not multi and sels and 0 <= sels[0] < len(self.comp.events):
            ui.message(dur_label(self.comp.events[sels[0]].dur, self.comp.ppq))
            if last_pitch is not None:
                self._preview_pitch(last_pitch, last_dur or self.comp.step_ticks)
        else:
            ui.message("Toggled dotted length")
    def _delete_selection_or_current(self, forward: bool) -> None:
        self._push_undo()
        if not self.comp.events:
            ui.message("Nothing to delete")
            return

        sels = self._selected_event_indices()
        if sels:
            count = 0
            for i in sorted(sels, reverse=True):
                if 0 <= i < len(self.comp.events):
                    del self.comp.events[i]
                    count += 1
            # keep cursor stable within bounds
            self.comp.cursor = clamp(self.comp.cursor, 0, self.comp.display_len() - 1)
            self._mark_dirty()
            self.refreshList(setFocus=True)
            ui.message(f"Deleted {count}")
            return

        # no selection: handle sentinels + cursor row
        if self.comp.is_end(self.comp.cursor) and not forward:
            # At End, Backspace should delete the previous event.
            target = len(self.comp.events) - 1
        elif self.comp.is_begin(self.comp.cursor) and forward:
            # At Beginning, Delete should delete the first event.
            target = 0
        else:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is None:
                ui.message("Nothing to delete")
                return
            target = ei + 1 if forward else ei

        if target < 0 or target >= len(self.comp.events):
            ui.message("Nothing to delete")
            return

        # Sound feedback for single deletions (not for multi-selection deletes).
        deleted_ev = self.comp.events[target]
        if deleted_ev.kind == "note" and deleted_ev.pitch is not None:
            self._preview_pitch(int(deleted_ev.pitch), int(deleted_ev.dur))
            deleted_label = note_name(int(deleted_ev.pitch))
        else:
            deleted_label = "Rest"

        del self.comp.events[target]
        self.comp.cursor = clamp(self.comp.cursor, 0, self.comp.display_len() - 1)
        self._mark_dirty()
        self.refreshList(setFocus=True)
        ui.message(f"Deleted {deleted_label}")

    def _toggle_triplet_duration_selected(self) -> None:
        """Toggle triplet/normal for selected events (or current event).

        Mirrors Ctrl+0 dotted toggle behavior: updates durations, restores selection consistently,
        announces the new duration, and previews pitch when possible.
        """
        self._push_undo()

        sel_disp = self._selected_display_indices()
        sels = self._selected_event_indices()
        if not sels:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is None:
                ui.message("Nothing selected")
                return
            sels = [ei]
            sel_disp = [self.comp.cursor]

        multi = len(sels) > 1
        last_pitch = None
        last_dur = None

        for i in sels:
            if 0 <= i < len(self.comp.events):
                ev = self.comp.events[i]
                ev.dur = self._toggle_triplet_ticks(ev.dur)
                if not multi and ev.kind == "note" and ev.pitch is not None:
                    last_pitch = int(ev.pitch)
                last_dur = int(ev.dur)

        self._mark_dirty()

        # Restore selection exactly like other duration operations so the list readout stays in sync.
        try:
            self._deselectAll()
            max_di = self.comp.display_len() - 1
            for di in sorted(set(clamp(int(x), 0, max_di) for x in sel_disp)):
                try:
                    self.list.SetSelection(di, True)
                except TypeError:
                    try:
                        self.list.SetSelection(di)
                    except Exception:
                        pass
                except Exception:
                    pass
        except Exception:
            # Fallback: best-effort restore
            try:
                self._restore_selection(sel_disp)
            except Exception:
                pass

        if not multi and sels and 0 <= sels[0] < len(self.comp.events):
            ui.message(dur_label(self.comp.events[sels[0]].dur, self.comp.ppq))
            if last_pitch is not None:
                self._preview_pitch(last_pitch, last_dur or self.comp.step_ticks)
        else:
            ui.message("Toggled triplet length")
        return
    def _confirm_unsaved(self) -> int:
        if not self.comp.dirty:
            return wx.ID_NO
        dlg = wx.MessageDialog(
            self,
            "You have unsaved changes. Save before loading a new file?",
            "NVDA Composer",
            style=wx.YES_NO | wx.CANCEL | wx.ICON_WARNING
        )
        try:
            res = dlg.ShowModal()
        finally:
            dlg.Destroy()
        return res

    def _new_project(self) -> None:
        # Stop playback when starting a new project.
        self._stop_playback()
        # Offer to save unsaved work first.
        res = self._confirm_unsaved()
        if res == wx.ID_CANCEL:
            return
        if res == wx.ID_YES:
            self._do_save()
            # If still dirty, the user canceled or save failed.
            if self.comp.dirty:
                return

        self._push_undo()

        # Reset to defaults.
        self.comp.events = []
        self.comp.cursor = 0
        self.comp.tempo_bpm = 120
        try:
            self.comp.tempo_map = [(0, 120)]
        except Exception:
            pass
        self.comp.ppq = 480
        self.comp.step_ticks = 480  # Quarter note default
        self.comp.base_note = 60    # C4
        self.comp.input_transpose = 0
        self.comp.chromatic_mode = False
        self.comp.scale_index = 0   # Major (index 0)
        self.comp.qwerty_layout = False
        # Reset track metadata
        self.comp.title = ""
        self.comp.notes = ""
        self.comp.markers = []
        self.comp.dirty = False

        self._lastPath = None
        self._lastMidiPath = None
        self._selAnchor = None
        self.refreshList(setFocus=True)
        ui.message("New project")


    def _save_text_to_path(self, path: str) -> bool:
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(comp_to_text(self.comp))
            self.comp.dirty = False
            self._lastPath = path
            self._update_status("Saved")
            return True
        except Exception as e:
            ui.message(f"Save failed: {e}")
            return False

    def _do_save(self) -> None:
        if self._lastPath and os.path.isfile(self._lastPath):
            self._save_text_to_path(self._lastPath)
            return

        default_name = _safe_filename_base(getattr(self.comp, 'title', '') or '', 'composition') + ".txt"
        try:
            src = self._lastPath or getattr(self, "_lastMidiPath", None)
            if src:
                base = os.path.splitext(os.path.basename(src))[0]
                if base and not (getattr(self.comp, 'title', '') or '').strip():
                    default_name = base + ".txt"
        except Exception:
            pass

        with wx.FileDialog(
            self,
            message="Save composition",
            wildcard="NVDA Composer projects (*.txt)|*.txt|All files (*.*)|*.*",
            style=wx.FD_SAVE | wx.FD_OVERWRITE_PROMPT,
            defaultFile=default_name,
        ) as fd:
            if fd.ShowModal() != wx.ID_OK:
                return
            path = fd.GetPath()
        self._save_text_to_path(path)

    def _do_save_as(self) -> None:
        """
        Save the current project to a new .txt file, always prompting for a path.
        After a successful save, the new path becomes the current save target.
        """
        default_name = _safe_filename_base(getattr(self.comp, 'title', '') or '', 'composition') + ".txt"
        default_dir = ""
        try:
            src = self._lastPath or getattr(self, "_lastMidiPath", None)
            if src:
                default_dir = os.path.dirname(src)
                base = os.path.splitext(os.path.basename(src))[0]
                if base and not (getattr(self.comp, 'title', '') or '').strip():
                    default_name = base + ".txt"
        except Exception:
            pass

        with wx.FileDialog(
            self,
            message="Save composition as",
            wildcard="NVDA Composer projects (*.txt)|*.txt|All files (*.*)|*.*",
            style=wx.FD_SAVE | wx.FD_OVERWRITE_PROMPT,
            defaultDir=default_dir,
            defaultFile=default_name,
        ) as fd:
            if fd.ShowModal() != wx.ID_OK:
                return
            path = fd.GetPath()

        # Ensure extension.
        root, ext = os.path.splitext(path)
        if not ext:
            path = root + ".txt"

        self._save_text_to_path(path)

    def _get_data_dir(self) -> str:
        """Return the add-on data directory."""
        # Packaged add-ons typically store assets under <addonRoot>/addon/data
        cand = os.path.join(self.addon_dir, "addon", "data")
        if os.path.isdir(cand):
            return cand
        cand2 = os.path.join(self.addon_dir, "data")
        if os.path.isdir(cand2):
            return cand2
        return cand  # best guess

    def _get_demos_dir(self) -> str:
        return os.path.join(self._get_data_dir(), "demos")

    def _do_open(self, initial_dir: Optional[str] = None) -> None:
        # Stop any ongoing playback before opening a file.
        self._stop_playback()
        res = self._confirm_unsaved()
        if res == wx.ID_CANCEL:
            return
        if res == wx.ID_YES:
            self._do_save()
            if self.comp.dirty:
                return

        with wx.FileDialog(
            self,
            message="Open composition",
            wildcard="NVDA Composer files (*.txt;*.mid;*.midi;*.rng)|*.txt;*.mid;*.midi;*.rng|Text projects (*.txt)|*.txt|MIDI files (*.mid;*.midi)|*.mid;*.midi|Nokia ringtones (*.rng)|*.rng|All files (*.*)|*.*",
            style=wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
            defaultDir=(initial_dir or ""),
        ) as fd:
            if fd.ShowModal() != wx.ID_OK:
                return
            path = fd.GetPath()

        # Ignore readme files shipped alongside demos.
        try:
            if 'readme' in os.path.basename(path).lower():
                ui.message("That looks like a readme file. Please choose a composition file.")
                return
        except Exception:
            pass

        # If the user picked a MIDI file, import it using the same Open command.
        ext = os.path.splitext(path)[1].lower()
        if ext in ('.mid', '.midi'):
            self._do_import_midi(path, confirm=False)
            return

        # Nokia Smart Messaging ringing tone files (.rng)
        if ext == '.rng':
            self._do_import_rng(path, confirm=False)
            return

        try:
            with open(path, "r", encoding="utf-8") as f:
                txt = f.read()
            loaded = comp_from_text(txt)
        except Exception as e:
            ui.message(f"Open failed: {e}")
            return

        self.comp.events = loaded.events
        self.comp.cursor = 0
        self.comp.tempo_bpm = loaded.tempo_bpm
        self.comp.tempo_map = getattr(loaded, 'tempo_map', None) or [(0, int(self.comp.tempo_bpm))]
        self.comp.ppq = loaded.ppq
        self.comp.step_ticks = loaded.step_ticks
        self.comp.base_note = loaded.base_note
        self.comp.input_transpose = loaded.input_transpose
        self.comp.chromatic_mode = loaded.chromatic_mode
        self.comp.scale_index = loaded.scale_index
        self.comp.qwerty_layout = loaded.qwerty_layout
        self.comp.title = str(getattr(loaded, "title", "") or "")
        self.comp.notes = str(getattr(loaded, "notes", "") or "")
        self.comp.markers = list(getattr(loaded, "markers", []) or [])
        self.comp.dirty = False
        self._lastPath = path

        self.refreshList(setFocus=True)
        ui.message("Loaded")

    def _toggle_layout(self) -> None:
        self.comp.qwerty_layout = not self.comp.qwerty_layout
        self._mark_dirty()
        ui.message("QWERTY layout" if self.comp.qwerty_layout else "Grid layout")



    def _onListboxSelection(self, evt) -> None:
        # Keep our internal cursor synced with the listbox selection (Home/End, mouse, type-ahead, etc.)
        try:
            sel = int(evt.GetSelection())
        except Exception:
            try:
                sel = int(self.list.GetSelection())
            except Exception:
                sel = -1
        if sel is None or sel == wx.NOT_FOUND or sel < 0:
            return
        self.comp.cursor = clamp(int(sel), 0, self.comp.display_len() - 1)
        self._lastNavCursor = self.comp.cursor

    def _sync_cursor_from_ui(self) -> None:
        # When the user is extending a selection via Shift+Left/Right, keep our
        # internally-tracked caret position. Otherwise wx will often report
        # selections in ascending order and we would snap the caret back to the
        # right-most selected item on every keypress, making Shift+Left feel
        # broken.
        if self._selAnchor is not None:
            return

        # For multiselect listboxes, prefer the last selected item as the caret.
        try:
            sels = list(self.list.GetSelections())
        except Exception:
            sels = []
        if sels:
            self.comp.cursor = clamp(int(sels[-1]), 0, self.comp.display_len() - 1)
            return
        try:
            sel = int(self.list.GetSelection())
        except Exception:
            sel = wx.NOT_FOUND
        if sel != wx.NOT_FOUND and sel >= 0:
            self.comp.cursor = clamp(int(sel), 0, self.comp.display_len() - 1)

    def _announce_cursor(self) -> None:
        # For Beginning/End, let the listbox speak the item label (avoids double speech).
        if self.comp.is_begin(self.comp.cursor) or self.comp.is_end(self.comp.cursor):
            return


        ei = self.comp.disp_to_event_index(self.comp.cursor)
        if ei is None or ei < 0 or ei >= len(self.comp.events):
            return
        ev = self.comp.events[ei]
        if ev.kind == "rest":
            ui.message("Rest")
        else:
            ui.message(f"{note_name(ev.pitch)}, velocity {clamp(int(getattr(ev,'vel',127) or 127),1,127)}")
            self._preview_pitch(ev.pitch, ev.dur, vel=getattr(ev,'vel',None))

    def _set_cursor_abs(self, disp_index: int, announce: bool = True) -> None:
        self._selAnchor = None
        self.comp.cursor = clamp(int(disp_index), 0, self.comp.display_len() - 1)
        self._lastNavCursor = self.comp.cursor
        self._deselectAll()
        try:
            self.list.SetSelection(self.comp.cursor)
        except Exception:
            pass
        if announce:
            self._announce_cursor()

    def _set_step_ticks(self, ticks: int, announce: bool = True) -> None:
        ticks = max(1, int(ticks))
        self.comp.step_ticks = ticks
        # Reset modifier state when an explicit step is set.
        self._step_mode = "normal"
        self._step_base_ticks = int(ticks)
        self._mark_dirty()
        if announce:
            ui.message(f"Step {dur_label(self.comp.step_ticks, self.comp.ppq)}")

    def _do_new(self) -> None:
        res = self._confirm_unsaved()
        if res == wx.ID_CANCEL:
            return
        if res == wx.ID_YES:
            self._do_save()
            if self.comp.dirty:
                return

        self.comp.events = []
        self.comp.cursor = 0
        self.comp.dirty = False
        self._lastPath = None
        self._lastMidiPath = None
        self.refreshList(setFocus=True)
        ui.message("New")

    def _set_clipboard_text(self, text: str) -> bool:
        try:
            if wx.TheClipboard.Open():
                try:
                    data = wx.TextDataObject()
                    data.SetText(text)
                    wx.TheClipboard.SetData(data)
                    return True
                finally:
                    wx.TheClipboard.Close()
        except Exception:
            pass
        return False

    def _get_clipboard_text(self) -> Optional[str]:
        try:
            if wx.TheClipboard.Open():
                try:
                    data = wx.TextDataObject()
                    if wx.TheClipboard.GetData(data):
                        return data.GetText()
                finally:
                    wx.TheClipboard.Close()
        except Exception:
            pass
        return None

    def _events_to_clip_text(self, events: List[Event]) -> str:
        # Clipboard format is intentionally plain text so it can be pasted between
        # Composer windows (and even edited in a text editor).
        lines = ["#NVDAComposer", "NVDA_COMPOSER_CLIP v2"]
        for ev in events:
            if ev.kind == "rest":
                lines.append(f"r t{int(ev.dur)}")
            else:
                vel = clamp(int(getattr(ev, "vel", 127) or 127), 1, 127)
                lines.append(f"n{int(ev.pitch)} t{int(ev.dur)} v{vel}")
        return "\n".join(lines) + "\n"
    def _events_to_share_clip_text(self, events: List[Event]) -> str:
        # Share-friendly clipboard text. Adds optional metadata as comment lines,
        # while keeping the core event format identical.
        lines = ["#NVDAComposer", "NVDA_COMPOSER_CLIP v2"]
        try:
            title = getattr(self.comp, "title", "") or ""
            title = str(title).replace("\n", " ").strip()
            if title:
                lines.append(f"# title: {title}")
        except Exception:
            pass
        try:
            bpm = int(getattr(self.comp, "tempo_bpm", 120))
            lines.append(f"# tempo: {bpm}")
        except Exception:
            pass
        try:
            notes = getattr(self.comp, "notes", "") or ""
            notes = str(notes)
            if notes.strip():
                lines.append("# notes:")
                for ln in notes.splitlines():
                    lines.append(f"# {ln}")
                lines.append("# endnotes")
        except Exception:
            pass

        for ev in events:
            if ev.kind == "rest":
                lines.append(f"r t{int(ev.dur)}")
            else:
                vel = clamp(int(getattr(ev, "vel", 127) or 127), 1, 127)
                lines.append(f"n{int(ev.pitch)} t{int(ev.dur)} v{vel}")
        return "\n".join(lines) + "\n"



    def _parse_clip_package(self, text: str):
        """Parse a clipboard/share clip.

        Returns (events, meta_dict). Meta may contain title(str), tempo(int), notes(str).
        Robustness goals:
          - tolerate extra text before/after the clip (social media posts)
          - tolerate comment lines and unknown lines
          - tolerate literal "\n" sequences
          - support both legacy v1 (note/rest) and compact v2 (n.. t.. v.. / r t..)
        """
        if not text:
            return None, {}

        # Tolerate literal "\n" sequences (common when clips are pasted through social media)
        if "\\n" in text and "\n" not in text:
            text = text.replace("\\r\\n", "\\n").replace("\\n", "\n")

        raw_lines = text.splitlines()
        # Keep original spacing for notes, but strip right-side newlines.
        raw_lines = [ln.rstrip("\r\n") for ln in raw_lines]

        # Find the clip header anywhere in the text.
        header_idx = None
        header = None
        for i, ln in enumerate(raw_lines):
            s = (ln or "").strip()
            if s in ("NVDA_COMPOSER_CLIP v2", "NVDA_COMPOSER_CLIP v1"):
                header_idx = i
                header = s
                break
        if header_idx is None:
            # If a hashtag is present, allow it to precede the header.
            for i, ln in enumerate(raw_lines):
                s = (ln or "").strip()
                if s.lower().startswith("#nvdacomposer"):
                    # look ahead a few lines for header
                    for j in range(i, min(i + 6, len(raw_lines))):
                        sj = (raw_lines[j] or "").strip()
                        if sj in ("NVDA_COMPOSER_CLIP v2", "NVDA_COMPOSER_CLIP v1"):
                            header_idx = j
                            header = sj
                            break
                if header_idx is not None:
                    break
        if header_idx is None:
            return None, {}

        lines = [ln.strip() for ln in raw_lines[header_idx + 1:] if ln.strip()]

        meta: Dict[str, Any] = {}
        notes_lines: List[str] = []
        in_notes = False
        out: List[Event] = []

        def parse_event_line(s: str) -> Optional[Event]:
            # Legacy: "note <pitch> <dur> [vel]" or "rest <dur>"
            parts = s.split()
            if not parts:
                return None
            k = parts[0].lower()

            if k == "rest" and len(parts) >= 2:
                with suppress(Exception):
                    return Event(kind="rest", pitch=None, dur=int(parts[1]))
                return None

            if k == "note" and len(parts) >= 3:
                with suppress(Exception):
                    vel = 127
                    if len(parts) >= 4:
                        vel = clamp(int(parts[3]), 1, 127)
                    return Event(kind="note", pitch=int(parts[1]), dur=int(parts[2]), vel=vel)
                return None

            # Compact v2:
            #   n84 t120 v127
            #   r t120
            # Also tolerate: n84 t120 (implies v127), r120 (dur directly), r t120, n84 120 127 (fallback)
            m = re.match(r"^n(\d+)\b", k, flags=re.IGNORECASE)
            if m:
                with suppress(Exception):
                    pitch = int(m.group(1))
                    dur = None
                    vel = 127
                    # scan tokens for t/v
                    for tok in parts[1:]:
                        tl = tok.lower().strip()
                        if tl.startswith("t"):
                            with suppress(Exception):
                                dur = int(tl[1:])
                        elif tl.startswith("v"):
                            with suppress(Exception):
                                vel = clamp(int(tl[1:]), 1, 127)
                    # fallback: if no t token, allow second token as dur
                    if dur is None and len(parts) >= 2:
                        with suppress(Exception):
                            dur = int(parts[1].lstrip("t"))
                    if dur is None:
                        return None
                    return Event(kind="note", pitch=pitch, dur=int(dur), vel=int(vel))

            m = re.match(r"^r(\d+)?\b", k, flags=re.IGNORECASE)
            if m:
                dur = None
                if m.group(1):
                    with suppress(Exception):
                        dur = int(m.group(1))
                for tok in parts[1:]:
                    tl = tok.lower().strip()
                    if tl.startswith("t"):
                        with suppress(Exception):
                            dur = int(tl[1:])
                    elif dur is None:
                        with suppress(Exception):
                            dur = int(tl)
                if dur is None:
                    return None
                return Event(kind="rest", pitch=None, dur=int(dur))

            # Extremely old compact: "N <pitch> <dur> [vel]" or "R <dur>"
            if parts[0].upper() == "R" and len(parts) >= 2:
                with suppress(Exception):
                    return Event(kind="rest", pitch=None, dur=int(parts[1]))
            if parts[0].upper() == "N" and len(parts) >= 3:
                with suppress(Exception):
                    vel = 127
                    if len(parts) >= 4:
                        vel = clamp(int(parts[3]), 1, 127)
                    return Event(kind="note", pitch=int(parts[1]), dur=int(parts[2]), vel=vel)

            return None

        for ln in lines:
            s = (ln or "").strip()
            if not s:
                continue

            # Legacy v1 metadata lines may not be commented.
            low_plain = s.lower()
            if low_plain.startswith("title:"):
                meta["title"] = s.split(":", 1)[1].strip()
                continue
            if low_plain.startswith("tempo:"):
                with suppress(Exception):
                    meta["tempo"] = int(s.split(":", 1)[1].strip())
                continue
            if low_plain in ("notes:", "notes"):
                in_notes = True
                continue
            if low_plain in ("endnotes", "end notes", "end_notes"):
                in_notes = False
                continue

            # Comment lines
            if s.startswith(("#", ";", "//")):
                # metadata
                low = s.lower()
                if low.startswith("# title:"):
                    meta["title"] = s.split(":", 1)[1].strip()
                elif low.startswith("# tempo:"):
                    with suppress(Exception):
                        meta["tempo"] = int(s.split(":", 1)[1].strip())
                elif low.startswith("# notes:"):
                    in_notes = True
                elif low.startswith("# endnotes"):
                    in_notes = False
                elif in_notes:
                    # "# ..." lines inside notes
                    notes_lines.append(s[1:].lstrip())
                # Ignore other comments (including #NVDAComposer)
                continue

            if in_notes:
                notes_lines.append(s)
                continue

            ev = parse_event_line(s)
            if ev is not None:
                out.append(ev)
            else:
                # Unknown/harmless line: ignore
                continue

        if notes_lines:
            meta["notes"] = "\n".join(notes_lines).rstrip("\n")

        return (out if out else None), meta

    def _parse_clip_text(self, text: str) -> Optional[List[Event]]:
        events, _meta = self._parse_clip_package(text)
        return events

    def _copy_selection(self) -> None:
        sels = self._selected_event_indices()
        if not sels:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is not None:
                sels = [ei]
        if not sels:
            ui.message("Nothing to copy")
            return

        events = [self.comp.events[i] for i in sels if 0 <= i < len(self.comp.events)]
        if not events:
            ui.message("Nothing to copy")
            return

        text = self._events_to_clip_text(events)
        if self._set_clipboard_text(text):
            ui.message(f"Copied {len(events)}")
        else:
            ui.message("Copy failed")

    def _copy_share_selection(self) -> None:
        sels = self._selected_event_indices()
        if not sels:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            if ei is not None:
                sels = [ei]
        if not sels:
            ui.message("Nothing to copy")
            return

        events = [self.comp.events[i] for i in sels if 0 <= i < len(self.comp.events)]
        if not events:
            ui.message("Nothing to copy")
            return

        text = self._events_to_share_clip_text(events)
        if self._set_clipboard_text(text):
            ui.message(f"Copied {len(events)} (share)")
        else:
            ui.message("Copy failed")

    def _paste_clipboard(self) -> None:
        self._push_undo()
        text = self._get_clipboard_text()
        events = self._parse_clip_text(text or "")
        if not events:
            ui.message("Clipboard has no NVDA Composer data")
            return

        idx = self.comp.insertion_event_index()
        self.comp.events[idx:idx] = [Event(kind=e.kind, pitch=e.pitch, dur=e.dur, vel=getattr(e, "vel", getattr(e, "velocity", 127))) for e in events]

        # Cursor to last pasted event row (display index = event index + 1)
        self.comp.cursor = idx + len(events)

        self._mark_dirty()
        self.refreshList(setFocus=True)
        ui.message(f"Pasted {len(events)}")

    def _paste_clipboard_with_meta(self) -> None:
        self._push_undo()
        text = self._get_clipboard_text() or ""
        events, meta = self._parse_clip_package(text)
        if not events:
            ui.message("Clipboard has no NVDA Composer data")
            return

        idx = self.comp.insertion_event_index()
        self.comp.events[idx:idx] = [Event(kind=e.kind, pitch=e.pitch, dur=e.dur, vel=getattr(e, "vel", getattr(e, "velocity", 127))) for e in events]
        self.comp.cursor = idx + len(events)

        # Offer to import metadata (tempo/title/notes) if present.
        has_meta = bool(meta.get("title") or meta.get("tempo") or meta.get("notes"))
        if has_meta:
            try:
                msg = "Import clip metadata (title/tempo/notes) into this project as well?"
                res = wx.MessageBox(msg, "Paste with metadata", wx.YES_NO | wx.ICON_QUESTION, parent=self)
                if res == wx.YES:
                    if meta.get("title") is not None:
                        self.comp.title = str(meta.get("title") or "").strip()
                    if meta.get("notes") is not None:
                        self.comp.notes = str(meta.get("notes") or "")
                    if meta.get("tempo") is not None:
                        try:
                            bpm = int(meta.get("tempo"))
                            self.comp.tempo_bpm = bpm
                            self.comp.tempo_map = [(0, bpm)]
                        except Exception:
                            pass
            except Exception:
                pass

        self._mark_dirty()
        self.refreshList(setFocus=True)
        ui.message(f"Pasted {len(events)}" + (" (with metadata)" if has_meta else ""))


    def _play_to_cursor(self) -> None:
        if not self.comp.events:
            ui.message("Nothing to play")
            return
        # Determine end index (exclusive)
        if self.comp.is_begin(self.comp.cursor):
            ui.message("Nothing to play")
            return
        if self.comp.is_end(self.comp.cursor):
            end = len(self.comp.events)
        else:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            end = clamp((ei + 1) if ei is not None else 0, 0, len(self.comp.events))
        if end <= 0:
            ui.message("Nothing to play")
            return
        self._start_playback_range(0, end, announce="Playing")

    def _play_from_cursor(self) -> None:
        if not self.comp.events:
            ui.message("Nothing to play")
            return
        if self.comp.is_end(self.comp.cursor):
            ui.message("Nothing to play")
            return
        if self.comp.is_begin(self.comp.cursor):
            start = 0
        else:
            ei = self.comp.disp_to_event_index(self.comp.cursor)
            start = clamp(ei if ei is not None else 0, 0, len(self.comp.events))
        if start >= len(self.comp.events):
            ui.message("Nothing to play")
            return
        self._start_playback_range(start, len(self.comp.events), announce="Playing")

    def _play_selection_range(self) -> None:
        sels = self._selected_event_indices()
        if not sels:
            ui.message("Nothing selected")
            return
        start = min(sels)
        end = max(sels) + 1
        start = clamp(start, 0, len(self.comp.events))
        end = clamp(end, 0, len(self.comp.events))
        if end <= start:
            ui.message("Nothing to play")
            return
        self._start_playback_range(start, end, announce="Playing selection")

    def _onPlay(self, evt) -> None:
        if not self.comp.events:
            ui.message("Nothing to play")
            return
        self._start_playback_range(0, len(self.comp.events), announce="Playing")

    def _stop_playback(self, announce: Optional[str] = None, clear_pause: bool = True) -> None:
        # Centralized stop so we consistently reset follow/pause state.
        try:
            self.player.stop()
        except Exception:
            pass
        try:
            if self._followTimer.IsRunning():
                self._followTimer.Stop()
        except Exception:
            pass
        if clear_pause:
            self._paused = False
            self._paused_at = None
            self._paused_end = None
        if announce:
            ui.message(announce)

    def _start_follow_timer(self) -> None:
        try:
            if self.followPlayback and not self._followTimer.IsRunning():
                # 20 Hz is plenty for a listbox highlight.
                self._followTimer.Start(50)
        except Exception:
            pass

    def _onFollowTimer(self, evt) -> None:
        # Track playback position in the UI (optional toggle).
        if not getattr(self, "followPlayback", False):
            try:
                if self._followTimer.IsRunning():
                    self._followTimer.Stop()
            except Exception:
                pass
            return

        try:
            if not self.player.is_playing():
                if self._followTimer.IsRunning():
                    self._followTimer.Stop()
                return
            pos = self.player.current_event_index()
            if pos is None:
                return
            pos = int(pos)

            # Don't destroy an active multi-selection while the user is selecting/copying.
            try:
                sels = list(self.list.GetSelections())
            except Exception:
                sels = []
            if len(sels) > 1:
                return

            if pos >= len(self.comp.events):
                di = self.comp.display_len() - 1  # End sentinel
            else:
                di = clamp(pos + 1, 0, self.comp.display_len() - 1)

            if di != self.comp.cursor:
                self.comp.cursor = di
                self._deselectAll()
                try:
                    self.list.SetSelection(int(di))
                except Exception:
                    pass
        except Exception:
            pass

    def _start_playback_range(self, start: int, end: int, announce: str = "Playing") -> None:
        # Starting playback should clear pause state.
        self._paused = False
        self._paused_at = None
        self._paused_end = None
        self._play_range = (int(start), int(end))
        self.player.play_range(self.comp, int(start), int(end))
        self._start_follow_timer()
        ui.message(announce)

    def _pause_or_resume(self) -> None:
        # Ctrl+Space toggles pause/resume for the *current* playback range.
        if self.player.is_playing():
            pos = self.player.current_event_index()
            if pos is None:
                pos = self._play_range[0]
            pos = clamp(int(pos), 0, len(self.comp.events))
            _, end = self.player.current_range()
            end = clamp(int(end), 0, len(self.comp.events))
            self._paused = True
            self._paused_at = pos
            self._paused_end = end
            self._stop_playback(clear_pause=False)
            # Optionally snap caret to pause point.
            if getattr(self, "snapOnPause", True):
                if pos >= len(self.comp.events):
                    self._set_cursor_abs(self.comp.display_len() - 1, announce=False)
                else:
                    self._set_cursor_abs(pos + 1, announce=False)
            ui.message("Paused")
            return

        if self._paused and self._paused_at is not None and self._paused_end is not None:
            start = clamp(int(self._paused_at), 0, len(self.comp.events))
            end = clamp(int(self._paused_end), 0, len(self.comp.events))
            self._paused = False
            self._start_playback_range(start, end, announce="Resumed")
            return

        ui.message("Nothing to pause")

    def _onStop(self, evt) -> None:
        self._stop_playback("Stop")

    # --- KEYHOOK ---

    def _find_readme_path(self) -> Optional[str]:
        # Try common NVDA add-on doc locations (English first).
        try:
            addon_root = os.path.dirname(os.path.dirname(__file__))  # ...\nvdaComposer
        except Exception:
            addon_root = os.path.dirname(__file__)
        candidates = [
            os.path.join(addon_root, "doc", "en", "readme.html"),
            os.path.join(addon_root, "doc", "en", "readme_0.8_table.html"),
            os.path.join(addon_root, "doc", "readme.html"),
            os.path.join(addon_root, "readme.html"),
        ]
        for p in candidates:
            try:
                if os.path.isfile(p):
                    return p
            except Exception:
                pass
        return None

    def _open_help(self) -> None:
        p = self._find_readme_path()
        if not p:
            ui.message("Help file not found.")
            return
        try:
            # On Windows this opens in default browser.
            os.startfile(p)  # type: ignore[attr-defined]
        except Exception:
            try:
                wx.LaunchDefaultBrowser("file:///" + p.replace("\\", "/"))
            except Exception:
                ui.message("Failed to open help.")

    def _show_tutorial(self) -> None:
        txt = '''NVDA Composer quick start

Open:
• NVDA+Alt+N opens NVDA Composer.

Step length (new notes and rests):
• 1–6 set the step length (whole → 32nd).
• 0 toggles dotted/undotted.
• Ctrl+9 toggles triplet step (new notes/rests).
• ` (grave; often ¬) lets you type a custom step length.

Editing durations (current note/selection):
• Ctrl+Left/Right shortens/lengthens by one step.
• Ctrl+1–6 sets duration to whole/half/quarter/eighth/16th/32nd.
• Ctrl+0 toggles dotted duration.
• Ctrl+9 toggles triplet duration.

Entering notes:
• Left/Right moves the timeline cursor by one step.
• Press a note key to insert a note at the cursor (then advance).
• Space inserts a rest.
• Up/Down shifts the input pitch by 1 semitone; Alt+Up/Down shifts by 1 octave.

Which keys enter notes?
• Ctrl+K chooses the layout:
  – Grid layout: J K L U I O 7 8 (low → high)
  – QWERTY layout: A W S E D F T G Y H U J K (low → high)
• In Scale mode (Ctrl+T), the keys act as scale degrees:
  – Grid: J=1, K=2, L=3, U=4, I=5, O=6, 7=7, 8=8
  – QWERTY: A=1, S=2, D=3, F=4, G=5, H=6, J=7, K=8

Layouts and scales:
• Ctrl+K toggles Grid vs QWERTY note-entry layout.
• Ctrl+T toggles Scale vs Chromatic; Alt+Left/Right cycles scales.

Playback:
• Enter plays from the start; Ctrl+Enter plays from the cursor; Shift+Enter plays up to the cursor.
• Esc stops; Ctrl+Space pauses/resumes.

Tip: Press F1 anytime to open the full documentation.
Esc closes this quick start tutorial window.'''
        try:
            ui.browseableMessage(txt, "NVDA Composer tutorial")
        except Exception:
            ui.message(txt)


    def _edit_track_metadata(self) -> None:
        # Lets the user enter a title and free-form notes/comments for the project.
        dlg = wx.Dialog(self, title="Track properties", style=wx.DEFAULT_DIALOG_STYLE | wx.RESIZE_BORDER)
        try:
            mainSizer = wx.BoxSizer(wx.VERTICAL)

            lblTitle = wx.StaticText(dlg, label="Title:")
            txtTitle = wx.TextCtrl(dlg)
            try:
                txtTitle.SetValue(str(getattr(self.comp, "title", "") or ""))
            except Exception:
                pass

            lblNotes = wx.StaticText(dlg, label="Notes:")
            txtNotes = wx.TextCtrl(dlg, style=wx.TE_MULTILINE)
            try:
                txtNotes.SetValue(str(getattr(self.comp, "notes", "") or ""))
            except Exception:
                pass

            btns = dlg.CreateButtonSizer(wx.OK | wx.CANCEL)

            mainSizer.Add(lblTitle, 0, wx.ALL, 6)
            mainSizer.Add(txtTitle, 0, wx.EXPAND | wx.LEFT | wx.RIGHT, 6)
            mainSizer.Add(lblNotes, 0, wx.ALL, 6)
            mainSizer.Add(txtNotes, 1, wx.EXPAND | wx.LEFT | wx.RIGHT, 6)
            if btns:
                mainSizer.Add(btns, 0, wx.EXPAND | wx.ALL, 6)

            dlg.SetSizer(mainSizer)
            dlg.SetSize((520, 380))
            dlg.Layout()

            # Ensure first keystroke overwrites existing title if user types immediately.
            def _focus_select():
                try:
                    txtTitle.SetFocus()
                    txtTitle.SelectAll()
                except Exception:
                    pass
            wx.CallAfter(_focus_select)

            if dlg.ShowModal() != wx.ID_OK:
                return

            try:
                self.comp.title = txtTitle.GetValue().strip()
            except Exception:
                self.comp.title = ""
            try:
                self.comp.notes = txtNotes.GetValue()
            except Exception:
                self.comp.notes = ""

            self._mark_dirty()
            self.refreshList(setFocus=True)
            ui.message("Track properties updated")
        finally:
            try:
                dlg.Destroy()
            except Exception:
                pass

    def _goto_prompt(self) -> None:
        # Accept either an event number (1..N), or ticks if you end with 't' (e.g. 960t).
        try:
            total_events = len(self.comp.events)
        except Exception:
            total_events = 0
        msg = f"Go to position. Enter event number 1 to {total_events}, or ticks ending with t (e.g. 960t)."
        dlg = wx.TextEntryDialog(self, msg, "Go to")
        try:
            if dlg.ShowModal() != wx.ID_OK:
                return
            val = (dlg.GetValue() or "").strip()
        finally:
            try:
                dlg.Destroy()
            except Exception:
                pass
        if not val:
            return
        try:
            if val.lower() in ("b", "begin", "beginning", "start"):
                self.comp.cursor = 0
            elif val.lower() in ("e", "end"):
                self.comp.cursor = len(self.comp.events) + 1
            elif val.lower().endswith("t"):
                tick = int(val[:-1].strip())
                self.comp.cursor = self.comp.display_pos_from_tick(tick)
            else:
                n = int(val)
                n = max(1, min(total_events, n))
                self.comp.cursor = n  # display position
            self.refreshList(setFocus=True)
            with suppress(Exception):
                self.list.EnsureVisible(self.comp.cursor)
            self._speakCurrentItem()
        except Exception:
            ui.message("Invalid position.")

    def _toggle_marker_at_cursor(self) -> None:
        """Toggle a marker at the current cursor position.

        Markers are stored as absolute tick positions in the project metadata.
        """
        # Core operation (don't let UI update errors masquerade as failure).
        tick = None
        try:
            tick = int(self.comp.tick_at_display_pos(self.comp.cursor))
            mk = getattr(self.comp, "markers", None)
            if mk is None:
                self.comp.markers = []
                mk = self.comp.markers

            existed = any(int(t) == tick for t in mk)
            if existed:
                self.comp.markers = [int(t) for t in mk if int(t) != tick]
                msg = "Marker cleared"
            else:
                self.comp.markers = sorted(set([int(t) for t in mk] + [tick]))
                msg = "Marker set"

            # Mark as modified only when the user changes markers.
            self.comp.dirty = True
        except Exception:
            ui.message("Marker failed.")
            return

        # Best-effort UI refresh/status (should never turn success into failure).
        with suppress(Exception):
            self._updateStatus()
        ui.message(msg)


    def _jump_marker(self, direction: int) -> None:
        """Jump to the previous (-1) or next (+1) marker."""
        # Core calculation/move first.
        try:
            mk = sorted(set(int(t) for t in getattr(self.comp, "markers", []) if t is not None))
            if not mk:
                ui.message("No markers.")
                return

            cur_tick = int(self.comp.tick_at_display_pos(self.comp.cursor))
            if direction < 0:
                choices = [t for t in mk if t < cur_tick]
                if not choices:
                    ui.message("No previous marker.")
                    return
                target = max(choices)
            else:
                choices = [t for t in mk if t > cur_tick]
                if not choices:
                    ui.message("No next marker.")
                    return
                target = min(choices)

            # Move cursor.
            self.comp.cursor = self.comp.display_pos_from_tick(target)
            idx = mk.index(target) + 1
            total = len(mk)
        except Exception:
            ui.message("Marker jump failed.")
            return

        # Best-effort UI updates.
        try:
            self.refreshList(setFocus=True)
            with suppress(Exception):
                self.list.EnsureVisible(self.comp.cursor)
            self._speakCurrentItem()
        except Exception:
            pass

        ui.message(f"Marker {idx} of {total}")


    def _reverse_project(self) -> None:
        """Easter egg: reverse timeline (events and markers). Keeps Begin/End sentinels."""
        # Stop playback first so the playback thread doesn't hold onto old timing.
        try:
            self._stop_playback()
        except Exception:
            pass

        try:
            old_cursor = int(self.comp.cursor)
            n = len(self.comp.events)
            total = self.comp.total_ticks()

            # Reverse events
            self.comp.events = list(reversed(self.comp.events))

            # Reverse markers (tick positions)
            mk = getattr(self.comp, "markers", [])
            self.comp.markers = sorted(set(max(0, total - int(t)) for t in mk))

            # Map cursor: for event positions 1..n map to n - pos + 1
            if old_cursor <= 0:
                self.comp.cursor = n + 1  # old begin -> end
            elif old_cursor >= n + 1:
                self.comp.cursor = 0      # old end -> begin
            else:
                self.comp.cursor = (n - old_cursor + 1)

            self.comp.dirty = True
            self.refreshList(setFocus=True)
            # Status updates are nice, but must never mask a successful reverse.
            with suppress(Exception):
                self._updateStatus()
            ui.message("Timeline reversed")
        except Exception as e:
            ui.message(f"Reverse failed: {e}")

    def _onListCharHook(self, evt) -> None:
        # Always sync internal cursor from UI first (Home/End, mouse selection, etc.)
        self._sync_cursor_from_ui()

        key = evt.GetKeyCode()
        mods = evt.GetModifiers()

        # Velocity / volume (for new notes, or for selected notes).
        # Uses punctuation present on most layouts: comma/period.
        # Comma = down, Period = up. Shift = larger steps.
        try:
            uni = int(evt.GetUnicodeKey())
        except Exception:
            uni = 0
        if not (mods & (wx.MOD_CONTROL | wx.MOD_ALT)):
            # Handle both unshifted (',' '.') and shifted ('<' '>') cases.
            if uni in (44, 46, 60, 62):
                # Shift jumps by 10s (more natural for 1..127).
                delta = 10 if (mods & wx.MOD_SHIFT) or uni in (60, 62) else 1
                direction = -1 if uni in (44, 60) else 1

                # If there is a selection, adjust velocity of selected notes; otherwise adjust input velocity.
                disp_sels = self._selected_display_indices()
                ev_idxs: List[int] = []
                for di in disp_sels:
                    ei = self.comp.disp_to_event_index(int(di))
                    if ei is not None:
                        ev_idxs.append(int(ei))

                # Helper: find the first selected note event to announce/preview.
                def _first_selected_note(eis: List[int]) -> Optional[Tuple[int, Any]]:
                    for _ei in eis:
                        if 0 <= _ei < len(self.comp.events):
                            _ev = self.comp.events[_ei]
                            if getattr(_ev, "kind", "") == "note" and getattr(_ev, "pitch", None) is not None:
                                return (_ei, _ev)
                    return None

                if ev_idxs:
                    changed = False
                    for ei in ev_idxs:
                        try:
                            ev = self.comp.events[ei]
                            if getattr(ev, "kind", "") != "note":
                                continue
                            curv = clamp(int(getattr(ev, "vel", 127) or 127), 1, 127)
                            newv = clamp(curv + direction * delta, 1, 127)
                            if newv != curv:
                                ev.vel = int(newv)
                                changed = True
                        except Exception:
                            continue

                    first_note = _first_selected_note(ev_idxs)
                    if first_note is None:
                        ui.message("No notes selected")
                        return

                    # Always announce the current velocity (even if unchanged at the ends).
                    ei0, ev0 = first_note
                    v0 = clamp(int(getattr(ev0, "vel", 127) or 127), 1, 127)

                    if changed:
                        self.comp.dirty = True
                        self.refreshList(setFocus=True)

                    ui.message(f"Velocity {v0}")
                    # Preview so the user hears *something* happened (tone loudness may vary if supported).
                    try:
                        self._preview_pitch(int(ev0.pitch), int(ev0.dur), vel=int(v0))
                    except Exception:
                        pass
                else:
                    curv = clamp(int(getattr(self.comp, "input_velocity", 127) or 127), 1, 127)
                    newv = clamp(curv + direction * delta, 1, 127)
                    self.comp.input_velocity = int(newv)

                    ui.message(f"Velocity {newv}")
                    # Preview the note under the cursor (if any) using the new input velocity.
                    try:
                        ei = self.comp.disp_to_event_index(self.comp.cursor)
                        if ei is not None and 0 <= ei < len(self.comp.events):
                            ev = self.comp.events[ei]
                            if getattr(ev, "kind", "") == "note" and getattr(ev, "pitch", None) is not None:
                                self._preview_pitch(int(ev.pitch), int(ev.dur), vel=int(newv))
                    except Exception:
                        pass

                return


        if key == wx.WXK_TAB:
            evt.Skip()
            return
        if (mods & wx.MOD_ALT) and key == wx.WXK_F4:
            evt.Skip()
            return

        # Help / tutorial
        if key == wx.WXK_F1:
            if (mods & wx.MOD_SHIFT) and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL)):
                self._show_tutorial()
                return
            if not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
                self._open_help()
                return

        # Track metadata (title / notes)
        if key == wx.WXK_F2 and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            self._edit_track_metadata()
            return

        # Go to
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT) and key in (ord("G"), ord("g")):
            self._goto_prompt()
            return

        # Markers
        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("M"), ord("m")):
            self._toggle_marker_at_cursor()
            return
        if not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)) and key in (ord("-"), wx.WXK_SUBTRACT, wx.WXK_NUMPAD_SUBTRACT, getattr(wx, "WXK_OEM_MINUS", -1)):
            self._jump_marker(-1)
            return
        if not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)) and key in (ord("="), wx.WXK_NUMPAD_EQUAL):
            self._jump_marker(+1)
            return

        # Easter egg: reverse timeline
        if (mods & wx.MOD_SHIFT) and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL)) and key == wx.WXK_BACK:
            self._reverse_project()
            return

        # ---- File / project ----
        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("N"), ord("n")):
            self._new_project()
            return

        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("O"), ord("o")):
            self._do_open()
            return
        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("S"), ord("s")):
            self._do_save()
            return
        # Ctrl+Shift+S = Save As
        if (mods & wx.MOD_CONTROL) and (mods & wx.MOD_SHIFT) and not (mods & wx.MOD_ALT) and key in (ord("S"), ord("s")):
            self._do_save_as()
            return


        # Ctrl+Shift+C = Copy share clip (includes optional title/tempo/notes as comments)
        if (mods & wx.MOD_CONTROL) and (mods & wx.MOD_SHIFT) and not (mods & wx.MOD_ALT) and key in (ord("C"), ord("c")):
            self._copy_share_selection()
            return
        # Ctrl+Shift+V = Paste and optionally import metadata (title/tempo/notes)
        if (mods & wx.MOD_CONTROL) and (mods & wx.MOD_SHIFT) and not (mods & wx.MOD_ALT) and key in (ord("V"), ord("v")):
            self._paste_clipboard_with_meta()
            return
        # F12 = Save As (common in some editors)
        if key == wx.WXK_F12 and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL | wx.MOD_SHIFT)):
            self._do_save_as()
            return

        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("A"), ord("a")):
            self._select_all_events()
            return

        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("E"), ord("e")):
            self._do_export_midi()
            return
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT) and key in (ord("Z"), ord("z")):
            if (mods & wx.MOD_SHIFT):
                self._redo()
            else:
                self._undo()
            return
        if (mods & wx.MOD_CONTROL) and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT)) and key in (ord("Y"), ord("y")):
            self._redo()
            return



        # ---- Transport ----
        if key == wx.WXK_ESCAPE:
            self._stop_playback("Stop")
            return

        if key in (wx.WXK_RETURN, wx.WXK_NUMPAD_ENTER):
            if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT):
                self._play_from_cursor()
                return
            if (mods & wx.MOD_SHIFT) and not (mods & wx.MOD_ALT):
                self._play_to_cursor()
                return
            self._onPlay(None)
            return

                # Ctrl+Space = pause/resume playback
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT) and key == wx.WXK_SPACE:
            self._pause_or_resume()
            return


        # Ctrl+Shift+O = Open/import starting in the demos folder
        if (mods & wx.MOD_CONTROL) and (mods & wx.MOD_SHIFT) and not (mods & wx.MOD_ALT) and key in (ord("O"), ord("o")):
            self._do_open(initial_dir=self._get_demos_dir())
            return

# ---- Ctrl shortcuts (non-Enter) ----
        if (mods & wx.MOD_CONTROL):
            if key in (ord("N"), ord("n")):
                self._do_new()
                return
            if (mods & wx.MOD_SHIFT) == 0 and key in (ord("O"), ord("o")):
                self._do_open()
                return
            if key in (ord("S"), ord("s")):
                self._do_save()
                return

            if (mods & wx.MOD_SHIFT) == 0 and key in (ord("P"), ord("p")):
                self._set_tempo_from_prompt()
                return
            if key in (ord("C"), ord("c")):
                self._copy_selection()
                return
            if key in (ord("V"), ord("v")):
                # Ctrl+Shift+V: Paste and optionally import metadata (title/tempo/notes)
                if (mods & wx.MOD_SHIFT):
                    self._paste_clipboard_with_meta()
                else:
                    self._paste_clipboard()
                return
            if key in (ord("K"), ord("k")):
                self._toggle_layout()
                return
            if key in (ord("T"), ord("t")):
                self.comp.chromatic_mode = not self.comp.chromatic_mode
                self._mark_dirty()
                ui.message("Chromatic mode" if self.comp.chromatic_mode else "Scale mode")
                return

            if key in (ord("F"), ord("f")):
                if (mods & wx.MOD_SHIFT):
                    self.snapOnPause = not getattr(self, "snapOnPause", True)
                    ui.message("Snap on pause " + ("on" if self.snapOnPause else "off"))
                else:
                    self.followPlayback = not getattr(self, "followPlayback", False)
                    ui.message("Follow playback " + ("on" if self.followPlayback else "off"))
                    # Apply immediately if currently playing.
                    if self.followPlayback and self.player.is_playing():
                        self._start_follow_timer()
                    elif not self.followPlayback:
                        try:
                            if self._followTimer.IsRunning():
                                self._followTimer.Stop()
                        except Exception:
                            pass
                return

        # ---- Cursor positioning ----
        if key == wx.WXK_HOME and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            self._set_cursor_abs(0, announce=False)
            return
        if key == wx.WXK_END and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            self._set_cursor_abs(self.comp.display_len() - 1, announce=False)
            return

        # ---- Tempo ----
        if key == wx.WXK_PAGEUP:
            step = 10 if (mods & wx.MOD_SHIFT) else 1
            self._set_tempo(self.comp.tempo_bpm + step, announce=True)
            return
        if key == wx.WXK_PAGEDOWN:
            step = 10 if (mods & wx.MOD_SHIFT) else 1
            self._set_tempo(self.comp.tempo_bpm - step, announce=True)
            return

        # ---- Delete ----
        if key == wx.WXK_BACK:
            self._delete_selection_or_current(forward=False)
            return
        if key == wx.WXK_DELETE:
            self._delete_selection_or_current(forward=True)
            return

        # ---- Existing note transpose ----
        # Shift Up/Down = semitone
        if (mods & wx.MOD_SHIFT) and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL)) and key == wx.WXK_UP:
            self._transpose_selected(+1)
            return
        if (mods & wx.MOD_SHIFT) and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL)) and key == wx.WXK_DOWN:
            self._transpose_selected(-1)
            return
        # Ctrl Up/Down = octave
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT) and key == wx.WXK_UP:
            self._transpose_selected(+12)
            return
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT) and key == wx.WXK_DOWN:
            self._transpose_selected(-12)
            return

        # ---- Selected length ----
        if (mods & wx.MOD_CONTROL) and key == wx.WXK_LEFT:
            self._change_length_selected(-1)
            return
        if (mods & wx.MOD_CONTROL) and key == wx.WXK_RIGHT:
            self._change_length_selected(+1)
            return

        # ---- Set selected duration by division (Ctrl+1..6), dotted (Ctrl+0), and triplet (Ctrl+9) ----
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT):
            uni = evt.GetUnicodeKey()
            # Some keyboard layouts/hosts do not provide a UnicodeKey for Ctrl+digits.
            # Fall back to keycode for ASCII digits and numpad digits.
            digit_key = None
            if uni is not None and uni != wx.WXK_NONE and 48 <= int(uni) <= 57:
                digit_key = int(uni)
            elif ord("0") <= int(key) <= ord("9"):
                digit_key = int(key)
            else:
                # Numpad digits (works whether NumLock is on or off, provided wx reports numpad keycodes)
                for n in range(10):
                    kc = getattr(wx, f"WXK_NUMPAD{n}", None)
                    if kc is not None and int(key) == int(kc):
                        digit_key = ord("0") + n
                        break
                if digit_key is None:
                    # Some builds expose numpad digits as a contiguous range.
                    np0 = getattr(wx, "WXK_NUMPAD0", None)
                    np9 = getattr(wx, "WXK_NUMPAD9", None)
                    if np0 is not None and np9 is not None and int(np0) <= int(key) <= int(np9):
                        digit_key = ord("0") + (int(key) - int(np0))
            if digit_key == ord("0") and not (mods & wx.MOD_SHIFT):
                self._toggle_dotted_duration_selected()
                return
            if digit_key == ord("9") and not (mods & wx.MOD_SHIFT):
                self._toggle_triplet_duration_selected()
                return

            if digit_key in (ord("1"), ord("2"), ord("3"), ord("4"), ord("5"), ord("6")):
                digit = int(chr(digit_key))
                mapping = {
                    1: self.comp.ppq * 4,
                    2: self.comp.ppq * 2,
                    3: self.comp.ppq,
                    4: max(1, self.comp.ppq // 2),
                    5: max(1, self.comp.ppq // 4),
                    6: max(1, self.comp.ppq // 8),
                }
                self._set_duration_selected_ticks(mapping[digit])
                return


        # ---- Input keyboard shift ----
        # Up/Down = semitone shift of input keyboard
        if key == wx.WXK_UP and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            self.comp.input_transpose += 1
            self._mark_dirty()
            root = note_name(self.comp.base_note + self.comp.input_transpose)
            self._update_status(f"Input transpose {root} +1 semitone")
            return
        if key == wx.WXK_DOWN and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            self.comp.input_transpose -= 1
            self._mark_dirty()
            root = note_name(self.comp.base_note + self.comp.input_transpose)
            self._update_status(f"Input transpose {root} -1 semitone")
            return
        # Alt Up/Down = octave shift of input keyboard
        if (mods & wx.MOD_ALT) and not (mods & (wx.MOD_SHIFT | wx.MOD_CONTROL)) and key == wx.WXK_UP:
            self.comp.input_transpose += 12
            self._mark_dirty()
            root = note_name(self.comp.base_note + self.comp.input_transpose)
            self._update_status(f"Input transpose {root} +1 octave")
            return
        if (mods & wx.MOD_ALT) and not (mods & (wx.MOD_SHIFT | wx.MOD_CONTROL)) and key == wx.WXK_DOWN:
            self.comp.input_transpose -= 12
            self._mark_dirty()
            root = note_name(self.comp.base_note + self.comp.input_transpose)
            self._update_status(f"Input transpose {root} -1 octave")
            return

        # ---- Scales ----
        if (mods & wx.MOD_ALT) and key == wx.WXK_LEFT:
            if self.scales:
                self.comp.scale_index = (self.comp.scale_index - 1) % len(self.scales)
                self._mark_dirty()
                name, _ = self._current_scale()
                self._update_status(f"Scale {name}")
            return
        if (mods & wx.MOD_ALT) and key == wx.WXK_RIGHT:
            if self.scales:
                self.comp.scale_index = (self.comp.scale_index + 1) % len(self.scales)
                self._mark_dirty()
                name, _ = self._current_scale()
                self._update_status(f"Scale {name}")
            return

        # ---- Selection play ----
        if (mods & wx.MOD_SHIFT) and key == wx.WXK_SPACE:
            self._play_selection_range()
            return

        # ---- Timeline navigation (Left/Right) ----
        if key == wx.WXK_LEFT and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL | wx.MOD_SHIFT)):
            self._move_cursor(-1, extendSelection=False)
            return
        if key == wx.WXK_RIGHT and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL | wx.MOD_SHIFT)):
            self._move_cursor(1, extendSelection=False)
            return

        # Shift+Left/Right extends selection range
        if (mods & wx.MOD_SHIFT) and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL)) and key == wx.WXK_LEFT:
            self._move_cursor(-1, extendSelection=True)
            return
        if (mods & wx.MOD_SHIFT) and not (mods & (wx.MOD_ALT | wx.MOD_CONTROL)) and key == wx.WXK_RIGHT:
            self._move_cursor(1, extendSelection=True)
            return

        # ---- Custom duration / step via ` key ----
        uni = evt.GetUnicodeKey()
        is_grave = (uni in (ord("`"), ord("¬"))) or (key == 192)
        # Ctrl+` : set duration of current note or selection
        if (mods & wx.MOD_CONTROL) and not (mods & wx.MOD_ALT) and is_grave:
            self._set_custom_duration_selected_from_prompt()
            return
        # ` : set a custom step length (for new notes/rests). Allow Shift+` on layouts where it produces ¬.
        if not (mods & wx.MOD_ALT) and not (mods & wx.MOD_CONTROL) and is_grave:
            self._set_custom_step_from_prompt()
            return

        # ---- Velocity direct entry (V) ----
        # Press V to type a velocity (1..127). If notes are selected, applies to selection.
        if not (mods & (wx.MOD_ALT | wx.MOD_CONTROL | wx.MOD_SHIFT)):
            uni = evt.GetUnicodeKey()
            if uni in (ord("v"), ord("V")):
                self._set_velocity_from_prompt()
                return


        #
        # (Triplet step is now on 9; Ctrl+9 is reserved for triplet duration.)

        # ---- Step length (1-6) and dotted (0) ----
        # 1 Whole, 2 Half, 3 Quarter, 4 Eighth, 5 Sixteenth, 6 Thirty-second
        if not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            uni = evt.GetUnicodeKey()
            if uni in (ord("1"), ord("2"), ord("3"), ord("4"), ord("5"), ord("6")):
                digit = int(chr(uni))
                mapping = {
                    1: self.comp.ppq * 4,
                    2: self.comp.ppq * 2,
                    3: self.comp.ppq,
                    4: max(1, self.comp.ppq // 2),
                    5: max(1, self.comp.ppq // 4),
                    6: max(1, self.comp.ppq // 8),
                }
                self._set_step_ticks(mapping[digit], announce=True)
                return
            if uni == ord("9"):
                self._toggle_step_triplet()
                return
            if uni == ord("0"):
                self._toggle_step_dotted()
                return

        # ---- Rest ----
        if key == wx.WXK_SPACE and not (mods & (wx.MOD_ALT | wx.MOD_SHIFT | wx.MOD_CONTROL)):
            self._insert_event(Event(kind="rest", pitch=None, dur=self.comp.step_ticks))
            ui.message("Rest")
            return

        # ---- Note entry ----
        # If Shift is held on digit keys, ignore (prevents Shift+9 etc from acting as note entry).
        # This keeps 9 reserved for triplet step, and avoids "note creep" from shifted digits.
        if (mods & wx.MOD_SHIFT) and (ord("0") <= int(key) <= ord("9")) and not (mods & (wx.MOD_CONTROL | wx.MOD_ALT)):
            return
        uni = evt.GetUnicodeKey()
        if uni != wx.WXK_NONE and uni >= 32:
            ch = chr(uni).lower()

            if self.comp.qwerty_layout:
                if self.comp.chromatic_mode and ch in QWERTY_OFFSETS:
                    offset = QWERTY_OFFSETS[ch]
                    pitch = self.comp.base_note + self.comp.input_transpose + offset
                    self._insert_event(Event(kind="note", pitch=pitch, dur=self.comp.step_ticks, vel=clamp(int(getattr(self.comp,'input_velocity',127) or 127),1,127)))
                    ui.message(note_name(pitch))
                    return
                if (not self.comp.chromatic_mode) and ch in QWERTY_DEGREES:
                    degree = QWERTY_DEGREES[ch]
                    sname, steps = self._current_scale()
                    offset = degree_to_semitone(steps, degree)
                    pitch = self.comp.base_note + self.comp.input_transpose + offset
                    self._insert_event(Event(kind="note", pitch=pitch, dur=self.comp.step_ticks, vel=clamp(int(getattr(self.comp,'input_velocity',127) or 127),1,127)))
                    ui.message(f"{note_name(pitch)} {sname}")
                    return
            else:
                if self.comp.chromatic_mode and ch in GRID_OFFSETS:
                    offset = GRID_OFFSETS[ch]
                    pitch = self.comp.base_note + self.comp.input_transpose + offset
                    self._insert_event(Event(kind="note", pitch=pitch, dur=self.comp.step_ticks, vel=clamp(int(getattr(self.comp,'input_velocity',127) or 127),1,127)))
                    ui.message(note_name(pitch))
                    return
                if (not self.comp.chromatic_mode) and ch in GRID_DEGREES:
                    degree = GRID_DEGREES[ch]
                    sname, steps = self._current_scale()
                    offset = degree_to_semitone(steps, degree)
                    pitch = self.comp.base_note + self.comp.input_transpose + offset
                    self._insert_event(Event(kind="note", pitch=pitch, dur=self.comp.step_ticks, vel=clamp(int(getattr(self.comp,'input_velocity',127) or 127),1,127)))
                    ui.message(f"{note_name(pitch)} {sname}")
                    return

        evt.Skip()


# =========================
# Global plugin
# =========================

class GlobalPlugin(globalPluginHandler.GlobalPlugin):
    scriptCategory = "NVDA Composer"
    __gestures = {"kb:NVDA+alt+n": "openComposer"}

    def __init__(self):
        super().__init__()
        self._comp = Composition()
        self._dlg: Optional[ComposerDialog] = None
        self._addon_dir = os.path.dirname(__file__)
        self._addon_root = os.path.dirname(self._addon_dir)

    @script(description="Open NVDA Composer", gesture="kb:NVDA+alt+n")
    def script_openComposer(self, gesture):
        try:
            if self._dlg:
                self._dlg.Show()
                self._dlg.Raise()
                self._dlg.refreshList(setFocus=True)
                return
            self._dlg = ComposerDialog(gui.mainFrame, self._comp, self._addon_root)
            self._dlg.Show()
        except Exception as e:
            ui.message(f"Failed to open Composer: {e}")