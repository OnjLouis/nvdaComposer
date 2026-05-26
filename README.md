# NVDA Composer

NVDA Composer is a keyboard-first, screen-reader-friendly music sketchpad for NVDA.

Non-NVDA users can try the web version at <https://onj.me/nc>.

## Quick Start

1. Install NVDA Composer from the [NVDA Add-on Store](https://addonstore.nvaccess.org/?addonId=nvdaComposer&apiVersion=2026.1.0&channel=stable&language=en).
2. Open Composer with `NVDA+Alt+N`.
3. Choose a step length with `1` to `6`.
4. Enter notes, use `Space` for a rest.
5. Press `Enter` to play/pause.
6. Save with `Ctrl+S`.

## Common Shortcuts

| Shortcut | Action |
| --- | --- |
| `NVDA+Alt+N` | Open NVDA Composer |
| `F1` | Open full help |
| `Shift+F1` | Open quick tutorial |
| `Ctrl+O` | Open project / import |
| `Ctrl+S` | Save project |
| `Ctrl+Shift+S` or `F12` | Save As |
| `Enter` | Play / pause |
| `Esc` | Stop playback |
| `Left` / `Right` | Move timeline cursor |
| `Shift+Left` / `Shift+Right` | Expand or shrink selection |
| `Space` | Insert rest |
| `Delete` / `Backspace` | Delete note(s) |
| `Ctrl+Z` / `Ctrl+Y` | Undo / Redo |
| `Ctrl+Up` / `Ctrl+Down` | Increase / decrease tempo |
| `Ctrl+P` | Set exact tempo (BPM) |

## Full Documentation

- Full shortcut reference and feature docs: [`source/doc/en/readme.html`](source/doc/en/readme.html)

## Source Code

- The source for this build is published in [`source/`](source/).
- Main plugin file: [`source/globalPlugins/nvdaComposer.py`](source/globalPlugins/nvdaComposer.py)
