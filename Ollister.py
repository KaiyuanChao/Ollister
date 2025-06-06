#!/usr/bin/env python3
"""
==================================================
Ollister - Ollama Model Lister and Explorer
        V 1.0: published on 2025-06-06 2:55am 
        v 1.0.1:
==================================================

A speedy GUI application for exploring and managing locally installed Ollama models.

Author: Coder Johan
GitHub: https://github.com/kaiyuanchao/ollister
License: MIT

Key Features:
- Model browsing with filtering
- Background Ollama info API caching for smooth performance
- Disk usage pie chart
- Cross-platform (Windows/macOS/Linux)
- Single file, zero external dependencies (pure Python standard library)

Usage:
    python Ollister.py

Requirements and Charter:
    - Python 3.+ with tkinter
    - Ollama installed and running locally
    - NO dependencies other than the Python Standard Library for python 3.9!
"""

import colorsys
import hashlib  # Moved hashlib here
import json
import math
import os
import platform
import queue  # For thread-safe communication
import random
import re
import struct
import subprocess
import sys
import threading
import time
import tkinter.font as tkFont
import tkinter.messagebox as msgbox
import tkinter.scrolledtext as st
import tkinter.ttk as ttk
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from tkinter import END, WORD, Canvas, Listbox, Menu, StringVar, Tk, TclError, Toplevel, PhotoImage
from typing import DefaultDict, Dict, List, Optional, cast, Set, Tuple


# Cache states for clearer cache management
CACHE_NONE = 0  # Not fetched yet
CACHE_FETCHING = 1  # Currently being fetched
CACHE_SUCCESS = 2  # Successfully fetched
CACHE_ERROR = 3  # Error occurred


CFG = {
    "api": "http://localhost:11434/api/show",
    "manifest": "manifests/registry.ollama.ai/library",
    "colors": {"sys": "#990000", "mp": "#0066CC", "ap": "#6A0DAD", "ai": "#000066", "sb": "#005300", "size": "#0010C4"},
    "urls": {"ollama": "https://ollama.com/library/", "hf": "https://huggingface.co/models?search="},
    "window": {
        "title": "Ollister v1.0",
        "main_app_geometry": "2100x960",
        "pie_chart_geometry": "1045x730",  # Default: (950*1.1)x(700*1.1)
        "model_internals_geometry": "1240x1320",  # Default size for Model Internals window
        "about_dialog_geometry": "406x496",  # About dialog
    },
    "flicker_color": "#D0D0D0",  # Light gray for copy feedback flicker
}


def copy_rgb_to_windows_clipboard_minimal(rgb_pixels_bytes: bytes, width: int, height: int) -> bool:
    """Copy raw 24-bit RGB pixel data to Windows clipboard as DIB format."""
    if sys.platform != "win32":
        return False

    # --- Windows API Constants and DLLs (minimal setup) ---
    CF_DIB = 8
    GHND = 0x0042  # GMEM_MOVEABLE | GMEM_ZEROINIT (ensures memory is zeroed)

    try:
        import ctypes

        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
    except (AttributeError, ImportError):
        return False

    # --- 1. Prepare DIB pixel data (BGR, bottom-up, padded) ---
    bytes_per_pixel = 3  # For RGB/BGR
    unpadded_row_size = width * bytes_per_pixel
    padded_row_size = (unpadded_row_size + 3) & ~3  # Each row rounded up to multiple of 4 bytes

    # Create a zeroed bytearray for the DIB pixel data
    dib_pixel_data_size = padded_row_size * height
    dib_pixels = bytearray(dib_pixel_data_size)  # Initialized to zeros, so padding is already zero

    for y_dest_row in range(height):  # y_dest_row is 0 for bottom-most DIB row
        y_src_row = height - 1 - y_dest_row  # Corresponding source image row (0 is top-most)

        src_row_offset = y_src_row * unpadded_row_size
        dest_row_offset = y_dest_row * padded_row_size

        for x in range(width):
            src_pixel_offset = src_row_offset + (x * bytes_per_pixel)
            dest_pixel_offset = dest_row_offset + (x * bytes_per_pixel)

            # Convert RGB from source to BGR for DIB
            dib_pixels[dest_pixel_offset + 0] = rgb_pixels_bytes[src_pixel_offset + 2]  # Blue
            dib_pixels[dest_pixel_offset + 1] = rgb_pixels_bytes[src_pixel_offset + 1]  # Green
            dib_pixels[dest_pixel_offset + 2] = rgb_pixels_bytes[src_pixel_offset + 0]  # Red

    final_dib_pixel_bytes = bytes(dib_pixels)

    # --- 2. Prepare BITMAPINFOHEADER ---
    # < little-endian; L: DWORD (uint32); l: LONG (int32); H: WORD (uint16)
    header_bytes = struct.pack(
        "<LllHHLLllLL",
        40,  # biSize (BITMAPINFOHEADER size)
        width,
        height,  # Positive for bottom-up DIB
        1,  # biPlanes (must be 1)
        24,  # biBitCount (24-bit)
        0,  # biCompression (BI_RGB, no compression)
        dib_pixel_data_size,  # biSizeImage
        0,  # biXPelsPerMeter (can be 0)
        0,  # biYPelsPerMeter (can be 0)
        0,  # biClrUsed (0 for 24-bit)
        0,  # biClrImportant (0 = all important)
    )

    dib_total_size = len(header_bytes) + dib_pixel_data_size

    # --- 3. Allocate global memory and copy DIB data ---
    h_global_mem = kernel32.GlobalAlloc(GHND, dib_total_size)
    if not h_global_mem:
        return False

    p_global_mem = kernel32.GlobalLock(h_global_mem)
    if not p_global_mem:
        kernel32.GlobalFree(h_global_mem)
        return False

    try:
        ctypes.memmove(p_global_mem, header_bytes, len(header_bytes))
        ctypes.memmove(p_global_mem + len(header_bytes), final_dib_pixel_bytes, dib_pixel_data_size)
    except Exception:
        kernel32.GlobalUnlock(h_global_mem)
        kernel32.GlobalFree(h_global_mem)
        return False
    finally:
        if p_global_mem:
            kernel32.GlobalUnlock(h_global_mem)

    # --- 4. Clipboard operations ---
    if not user32.OpenClipboard(None):
        kernel32.GlobalFree(h_global_mem)
        return False

    if not user32.EmptyClipboard():
        user32.CloseClipboard()
        kernel32.GlobalFree(h_global_mem)
        return False

    if not user32.SetClipboardData(CF_DIB, h_global_mem):
        user32.CloseClipboard()
        kernel32.GlobalFree(h_global_mem)
        return False

    user32.CloseClipboard()
    return True


def apply_pypy_tkinter_patches():
    """Apply PyPy compatibility patches to prevent Tkinter threading issues."""
    if hasattr(sys, "pypy_version_info") or "pypy" in sys.version.lower():
        print("PyPy detected - Applying comprehensive Tkinter compatibility patches")

        # Suppress PyPy warnings about patched __del__ methods
        import warnings

        warnings.filterwarnings("ignore", message="a __del__ method added to an existing type will not be called", category=RuntimeWarning)

        # Import tkinter modules
        import tkinter
        from tkinter import PhotoImage as OriginalPhotoImage

        # For PyPy, we'll monkey-patch the __del__ methods directly on the classes
        # instead of creating inheritance wrapper classes which cause issues
        # Store original __del__ methods in case we need them
        # _original_photoimage_del = getattr(OriginalPhotoImage, "__del__", None)

        # Monkey-patch PhotoImage __del__ method
        def safe_del(self):
            pass  # Do nothing - prevents threading issues

        OriginalPhotoImage.__del__ = safe_del

        # Monkey-patch Variable and its subclasses
        try:
            from tkinter import Variable

            Variable.__del__ = safe_del
        except (ImportError, AttributeError):
            pass

        # Monkey-patch specific Variable types
        for var_class_name in ["StringVar", "IntVar", "BooleanVar", "DoubleVar"]:
            try:
                var_class = getattr(tkinter, var_class_name, None)
                if var_class and hasattr(var_class, "__del__"):
                    var_class.__del__ = safe_del
            except (AttributeError, TypeError):
                pass

        # Also try to patch any other classes that might have __del__ issues
        try:
            # Check if there's a base Image class
            if hasattr(tkinter, "Image"):
                tkinter.Image.__del__ = safe_del
        except (AttributeError, TypeError):
            pass

        # Also replace in the main namespace for direct imports
        import builtins

        if not hasattr(builtins, "_pypy_tkinter_patched"):
            builtins._pypy_tkinter_patched = True  # type: ignore[attr-defined]

        return OriginalPhotoImage  # Return the original, now-patched class
    else:
        # On regular Python, just return the standard PhotoImage
        from tkinter import PhotoImage

        return PhotoImage


# Apply patches and get the appropriate PhotoImage class
PhotoImageClass = apply_pypy_tkinter_patches()  # Renamed to avoid redefinition


class AsyncTaskManager:
    """A reusable manager for running background tasks and delivering results to the UI thread."""

    def __init__(self, root):
        """Initialize the task manager with a root window."""
        self.root = root
        self.task_queue = queue.Queue()
        self.is_polling = False
        self._start_polling()

    def _start_polling(self):
        """Start the queue polling if not already active."""
        if not self.is_polling:
            self.is_polling = True
            self._poll_queue()

    def _poll_queue(self):
        """Process results from the queue in the main UI thread."""
        try:
            while True:
                callback, args, kwargs = self.task_queue.get_nowait()
                callback(*args, **kwargs)
        except queue.Empty:
            pass

        # Continue polling if root window still exists
        if self.is_polling and self.root.winfo_exists():
            self.root.after(50, self._poll_queue)
        else:
            self.is_polling = False

    def run(self, background_func, on_complete_callback, *args, **kwargs):
        """
        Run a function in a background thread and deliver results to UI thread.

        Args:
            background_func: The function to execute in the background
            on_complete_callback: The function to call in the UI thread with the result
            *args: Arguments for the background function
            **kwargs: Keyword arguments for the background function
        """

        def _worker():
            try:
                result = background_func(*args, **kwargs)
                self.task_queue.put((on_complete_callback, [result], {}))
            except Exception as e:
                # Pass errors to the callback with a special error marker
                error_result = ("ERROR", e)
                self.task_queue.put((on_complete_callback, [error_result], {}))

        threading.Thread(target=_worker, daemon=True).start()

    def run_with_progress(self, background_func, on_progress_callback, on_complete_callback, *args, **kwargs):
        """
        Run a function in a background thread with progress updates.

        Args:
            background_func: Function that yields progress updates and returns final result
            on_progress_callback: Function called for each progress update
            on_complete_callback: Function called with final result
            *args: Arguments for the background function
            **kwargs: Keyword arguments for the background function
        """

        def _worker():
            try:
                # Background function should yield progress and return final result
                result_generator = background_func(*args, **kwargs)
                final_result = None

                for progress_update in result_generator:
                    if isinstance(progress_update, tuple) and progress_update[0] == "PROGRESS":
                        self.task_queue.put((on_progress_callback, [progress_update[1]], {}))
                    else:
                        final_result = progress_update

                if final_result is not None:
                    self.task_queue.put((on_complete_callback, [final_result], {}))
            except Exception as e:
                error_result = ("ERROR", e)
                self.task_queue.put((on_complete_callback, [error_result], {}))

        threading.Thread(target=_worker, daemon=True).start()

    def schedule_ui_update(self, callback, *args, **kwargs):
        """
        Schedule a UI update to run on the next polling cycle.

        Args:
            callback: Function to call in the UI thread
            *args: Arguments for the callback
            **kwargs: Keyword arguments for the callback
        """
        self.task_queue.put((callback, args, kwargs))

    def stop(self):
        """Stop the task manager polling."""
        self.is_polling = False


# --- DPI Awareness (Windows Specific) ---
# The following block addresses rendering on high-DPI displays under Windows.
# By default, Windows may scale applications that are not DPI-aware, leading
# to blurry text and graphics as the OS upscales a lower-resolution render
# of the application. To achieve crisp, 1:1 pixel mapping for custom graphics
# and ensure all UI elements (text, widgets) are rendered at the native
# screen resolution, we use ctypes to call Windows API functions.
# `SetProcessDpiAwareness(2)` (for per-monitor v2) or its fallback
# `SetProcessDPIAware()` tells Windows that our application will handle its
# own scaling. This must be done *before* the main Tkinter window (Tk())
# is initialized. The result is significantly sharper visuals across the
# entire application on high-DPI setups.
# Attempt to set DPI awareness on Windows for 1:1 pixel mapping
if platform.system() == "Windows":
    try:
        import ctypes

        # Try for per-monitor DPI awareness v2 (Windows 10 Creators Update and later)
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except (ImportError, AttributeError, OSError):  # OSError for cases like trying to run on a non-GUI Windows Server Core
        try:
            # Fallback for older Windows versions
            ctypes.windll.user32.SetProcessDPIAware()
        except (ImportError, AttributeError, OSError):
            print("Warning: Could not set DPI awareness. Graphics may appear scaled/blurry.")


@dataclass
class Model:
    """Ollama model with metadata and file paths."""

    name_tag: str
    mod_time: float
    total_size: int
    manifest_path: Path
    blob_paths: List[Path]
    digests: List[str]

    def __post_init__(self):
        """Cache lowercase name for filtering."""
        self.name_lower = self.name_tag.lower()


class ModelManager:
    """Handles model discovery and management for Ollama models."""

    def __init__(self, models_dir: Path):
        """Initialize with models directory."""
        self.models_dir = models_dir
        self.models: List[Model] = []
        self.digest_map: Dict[str, Set[str]] = {}

    def refresh(self) -> Tuple[List[Model], dict]:
        """Scan models directory and return (models, digest_map)."""
        self.models, self.digest_map = self._find_models()
        return self.models, self.digest_map

    def get_model_by_tag(self, tag: str) -> Optional[Model]:
        """Get model by tag name, or None if not found."""
        return next((m for m in self.models if m.name_tag == tag), None)

    def _find_models(self) -> Tuple[List[Model], dict]:
        """Scan models directory and return (models, digest_map)."""
        models: List[Model] = []
        digest_map: DefaultDict[str, Set[str]] = defaultdict(set)
        manifest_base = self.models_dir / str(CFG["manifest"])

        if not manifest_base.is_dir():
            return models, dict(digest_map)

        for tag_file in manifest_base.glob("*/*"):
            if tag_file.is_file():
                name_tag = f"{tag_file.parent.name}:{tag_file.name}"
                try:
                    with open(tag_file, encoding="utf-8") as f:
                        data = json.load(f)

                    blobs, digests, size = [], [], 0
                    config_item = data.get("config")
                    items = list(filter(None, [config_item])) + data.get("layers", [])

                    for item in items:
                        if isinstance(item, dict) and (digest := item.get("digest")):
                            digests.append(digest)
                            # Track which models use this digest (for shared blob detection)
                            digest_map[digest].add(name_tag)
                            blob_path = self.models_dir / "blobs" / digest.replace(":", "-", 1)
                            if blob_path.is_file():
                                blobs.append(blob_path)
                                try:
                                    size += blob_path.stat().st_size
                                except OSError:
                                    pass

                    model = Model(name_tag, tag_file.stat().st_mtime, size, tag_file, blobs, digests)
                    models.append(model)
                except (FileNotFoundError, json.JSONDecodeError, PermissionError):
                    pass

        return sorted(models, key=lambda x: x.name_tag), dict(digest_map)

    @staticmethod
    def find_ollama_models_directory() -> Optional[Path]:
        """Find Ollama models directory from common locations."""
        paths = [os.getenv("OLLAMA_MODELS"), "~/.ollama/models", "/usr/share/ollama/.ollama/models"]
        for p in paths:
            if p and Path(p).expanduser().is_dir():
                return Path(p).expanduser()
        return None


def fmt_size(n):
    """Format bytes as human-readable string."""
    if n is None:
        return "N/A"
    n = float(n)
    for u in ["B", "KB", "MB", "GB", "TB"]:
        if n < 1024:
            return f"{n:.2f} {u}"
        n /= 1024
    return f"{n:.2f} PB"


class API:
    """Fetch and cache Ollama API model data asynchronously."""

    def __init__(self, task_manager=None):
        """Initialize with empty cache."""
        self._cache = {}
        self.task_manager = task_manager

    def cached(self, tag):
        """Return cached API data for tag, if available."""
        entry = self._cache.get(tag)
        if entry and entry["state"] == CACHE_SUCCESS:
            return entry["data"]
        return None

    def cache_state(self, tag):
        """Return cache state for tag."""
        return self._cache.get(tag, {}).get("state", CACHE_NONE)

    def fetch(self, tag, on_complete_callback=None):
        """Fetch model details from API in background thread."""
        self._cache[tag] = {"state": CACHE_FETCHING, "data": None}

        def _fetch():
            try:
                req = urllib.request.Request(CFG["api"], json.dumps({"name": tag}).encode("utf-8"), {"Content-Type": "application/json"})
                with urllib.request.urlopen(req, timeout=10) as resp:
                    if resp.status == 200:
                        data = json.loads(resp.read().decode("utf-8"))
                        formatted = self._format_response(data)
                        self._cache[tag] = {"state": CACHE_SUCCESS, "data": formatted}
                        return (tag, formatted)
                    else:
                        self._cache[tag] = {"state": CACHE_ERROR, "data": f"\n(HTTP {resp.status})\n"}
                        return (tag, None)
            except urllib.error.URLError as e:
                self._cache_error(tag, f"Connection failed: {getattr(e, 'reason', str(e))}")
                return (tag, None)
            except json.JSONDecodeError as e:
                self._cache_error(tag, f"Invalid API response: {e}")
                return (tag, None)
            except Exception as e:
                self._cache_error(tag, f"Error: {type(e).__name__}: {str(e)}")
                return (tag, None)

        if self.task_manager and on_complete_callback:
            self.task_manager.run(_fetch, on_complete_callback)
        else:
            # Fallback to old threading approach if no task manager
            threading.Thread(target=_fetch, daemon=True).start()

    def _cache_error(self, tag, message):
        """Set cache error state."""
        # Show a user-friendly message for connection errors
        if message.lower().startswith("connection failed"):
            user_msg = "\n(Connection failed: Please ensure Ollama is installed and running on your system.)\n"
        else:
            user_msg = f"\n({message})\n"
        self._cache[tag] = {"state": CACHE_ERROR, "data": user_msg}

    def _format_response(self, data) -> List[Tuple[str, Optional[str]]]:
        """Format API response data for display as (text, tag) segments."""
        segments: List[Tuple[str, Optional[str]]] = [("\n--- Ollama API info ---\n", None)]

        # Details section
        if details := data.get("details", {}):
            detail_fields = [("family", "Family"), ("parameter_size", "Size"), ("quantization_level", "Quant")]
            for k, lbl in detail_fields:
                if k in details:
                    segments.append((f"{lbl}: {details[k]}\n", "mp"))

        # Parameters section
        if params := data.get("parameters"):
            segments.append(("\nParameters:\n", None))
            for line in params.strip().split("\n"):
                parts = line.split(None, 1)
                if len(parts) == 2:
                    k, v = parts
                    tag = "ap" if k in ["num_ctx", "num_predict"] else "mp"
                    segments.append((f"  {k}: {v}\n", tag))

        # Template and System sections
        section_configs: List[Tuple[str, str, Optional[str]]] = [("template", "Template", "api_text"), ("system", "System", None)]
        for key, header, section_tag in section_configs:
            raw_content: Optional[str] = data.get(key)
            if raw_content is not None:
                content = cast(str, raw_content)
                segments.append((f"\n{header}:\n", None))
                for i, x in enumerate(content.strip().split("\n")):
                    line_tag = "sys" if section_tag is None and i == 0 else (section_tag if section_tag is not None else "api_text")
                    segments.append((f"  {x}\n", line_tag))

        return segments

    def clear(self, tag=None):
        """Clear cached data for a tag or all tags."""
        if tag:
            self._cache.pop(tag, None)
        else:
            self._cache.clear()


def is_system_prompt(text):
    """Check if text contains system prompt markers."""
    text_lower = text.lower().strip()
    # Only check for 4 keywords for system prompt detection
    keywords = [
        "system:",
        "you are",
        "role",
        "instruction",
    ]
    return any(k in text_lower for k in keywords)


class TemplateFormatter:
    """Formats Jinja-like templates with indentation for display."""

    def __init__(self, template):
        self.template = template if template else ""
        self.indent = 0
        self.lines = []
        self.jinja_re = re.compile(r"({%.*?%}|\{\{.*?\}\}|{#.*?#})", re.DOTALL)
        self.indent_patterns = {
            "increase": re.compile(r"{%-?\s*(if|for|elif|else).*?%}", re.DOTALL),
            "decrease_before": re.compile(r"{%-?\s*(elif|else|endif|endfor).*?%}", re.DOTALL),
        }

    def format(self):
        """Format template into indented lines."""
        tokens = self.jinja_re.split(self.template)
        for token in tokens:
            if not token:
                continue

            is_block = token.startswith("{%")
            is_expr = token.startswith("{{")
            is_comment = token.startswith("{#")

            if is_block:
                self._process_control_block(token)
            elif is_expr:
                self._process_output_block(token)
            elif is_comment:
                if token.strip():
                    self.lines.append(("comment", self._get_indent_str() + token.strip() + "\n"))
            elif token.strip():
                self._process_plain_text(token)
        return self.lines

    def _get_indent_str(self):
        return "    " * self.indent

    def _process_output_block(self, token):
        content = token.replace("\\n", "↵").replace("\n", "↵")
        self.lines.append(("text", self._get_indent_str() + content.strip() + "\n"))

    def _process_control_block(self, token):
        def replace_newlines_in_strings(match):
            return match.group(0).replace("\n", "↵")

        token_display = re.sub(r'("[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\')', replace_newlines_in_strings, token)

        if self.indent_patterns["decrease_before"].match(token_display):
            if not (token_display.startswith("{%- if") or token_display.startswith("{%- for")):
                self.indent = max(0, self.indent - 1)

        self.lines.append(("block", self._get_indent_str() + token_display.strip() + "\n"))

        if self.indent_patterns["increase"].match(token_display):
            self.indent += 1

    def _process_plain_text(self, token):
        """Processes plain text segments, indenting non-empty lines."""
        for _, line in enumerate(token.splitlines()):
            stripped_line = line.strip()
            if stripped_line:
                self.lines.append(("text", self._get_indent_str() + stripped_line + "\n"))

    def apply_syntax_highlighting(self, stxt_widget):
        text_content = stxt_widget.get("1.0", "end-1c")

        # Patterns to highlight (simpler approach from OllisterIntegrity.py)
        patterns = [
            (r"(\{\{.*?\}\}|#.*$)", ["var", "comment"]),  # {{ }} and comments
            (r"(['\"])(?:(?=(\\?))\2.)*?\1", ["str"]),  # Quoted strings
            (r"(?<!\w)(-?\d+(?:\.\d+)?)(?!\w)", ["num"]),  # Numbers
            (r"↵", ["newline"]),  # Newline placeholders
        ]

        for pattern, tags in patterns:
            for match in re.finditer(pattern, text_content, re.MULTILINE):
                start = f"1.0+{match.start()}c"
                end = f"1.0+{match.end()}c"

                # Determine which tag to apply
                if len(tags) > 1:
                    # Special case for {{ }} vs comments
                    tag = tags[0] if match.group(0).startswith("{{") else tags[1]
                else:
                    tag = tags[0]

                stxt_widget.tag_add(tag, start, end)


class App:
    """Main application class for the Ollister GUI."""

    def __init__(self, root):
        """Initialize with Tkinter root window."""
        self.root = root
        self.root.title(CFG["window"]["title"])
        self.root.geometry(CFG["window"]["main_app_geometry"])

        self.models_dir = ModelManager.find_ollama_models_directory()
        if not self.models_dir:
            msgbox.showerror("Error", "No models dir")
            self.root.destroy()
            return

        # Initialize ModelManager
        self.model_manager = ModelManager(self.models_dir)
        self.models, self.digest_map = self.model_manager.refresh()

        # Initialize AsyncTaskManager for all background operations FIRST
        self.task_manager = AsyncTaskManager(self.root)

        self.sort_key = "name"
        self.sort_reverse = defaultdict(bool)
        self.current_tag = None
        self.api = API(self.task_manager)
        self._running = True
        self._cache_idx = 0
        self._cache_job = None  # Tkinter after job ID is a string
        self._fetching_current = False

        # Set custom icon (pastel blue to white gradient, 32x32)
        self._icon = self._create_icon()
        try:
            self.root.iconphoto(True, self._icon)
        except Exception:
            pass  # Not all platforms support iconphoto

        # Setup fonts first
        self._setup_fonts()

        # Create UI factory
        self.ui = UIFactory(self.root, self.fonts)

        self._setup_ui()
        self._refresh()

        self.pie_window = None
        self.about_window = None

        if self._running and self.models:
            self._background_cache()

        # Clean shutdown handler
        def on_close():
            self._running = False
            if self._cache_job:
                self.root.after_cancel(self._cache_job)
            self.task_manager.stop()
            self.root.destroy()

        self.root.protocol("WM_DELETE_WINDOW", on_close)

    def _setup_fonts(self):
        """Setup DPI-scaled fonts."""
        # Determine DPI scaling factor
        self.scaling_factor = 1.0
        try:
            # update_idletasks ensures winfo_pixels returns a value based on the current state
            self.root.update_idletasks()
            if platform.system() == "Windows":
                # On Windows, after DPI awareness is set, calculate scaling from reported DPI
                dpi = self.root.winfo_pixels("1i")  # Pixels per logical inch
                self.scaling_factor = dpi / 96.0  # 96 DPI is the standard baseline
                # Clamp to a reasonable range (e.g., 100% to 300%)
                if not 1.0 <= self.scaling_factor <= 4.0:  # Allow up to 400% (Removed superfluous-parens)
                    self.scaling_factor = 1.0
            else:
                # For macOS/Linux, Tk's scaling factor might be more relevant
                tk_scale = self.root.tk.call("tk", "scaling")
                if isinstance(tk_scale, (float, int)) and (1.0 <= tk_scale <= 4.0):
                    self.scaling_factor = tk_scale
                else:  # If tk_scale is not sensible, try DPI calculation as a fallback
                    dpi = self.root.winfo_pixels("1i")
                    self.scaling_factor = dpi / 96.0
                    if not 1.0 <= self.scaling_factor <= 4.0:  # Removed superfluous-parens
                        self.scaling_factor = 1.0
        except Exception:
            self.scaling_factor = 1.0  # Default if any error

        # Font setup
        default_font = tkFont.nametofont("TkDefaultFont")
        size = default_font.cget("size")  # Base size from system's default font

        # Revert scaling for general fonts, let Tkinter handle base scaling with DPI awareness
        # Specific adjustments can be made elsewhere if needed.
        font_size_list = size + 2
        font_size_title = size + 2
        font_size_details = size + 3  # Consolas for details might need to be a bit larger by default
        font_size_bold = size + 3
        font_size_api_small = size + 1
        font_size_small = size  # Consolas for small/treeview

        self.fonts = {
            "list": tkFont.Font(size=font_size_list),
            "title": tkFont.Font(size=font_size_title),
            "details": tkFont.Font(family="Consolas", size=font_size_details),
            "bold": tkFont.Font(family="Consolas", size=font_size_bold, weight="bold"),
            "api_small": tkFont.Font(family="Consolas", size=font_size_api_small),
            "small": tkFont.Font(family="Consolas", size=font_size_small),
            # New font for blob paths, one point smaller than "details"
            "blob_font": tkFont.Font(family="Consolas", size=font_size_details - 1 if font_size_details > 7 else font_size_details),
            # New font for chat template text, one point smaller than "details"
            "chat_template_font": tkFont.Font(family="Consolas", size=font_size_details - 1 if font_size_details > 7 else font_size_details),
            # Dedicated italic font based on "details"
            "italic_details_font": tkFont.Font(family="Consolas", size=font_size_details, slant="italic"),
        }

    def _handle_api_result(self, result):
        """Handle API fetch result from AsyncTaskManager."""
        if isinstance(result, tuple) and len(result) == 2:
            tag, data = result
            if tag == self.current_tag:
                self._fetching_current = False
                if data:
                    self.details.config(state="normal")
                    self._update_item_data(data)
                    self.details.config(state="disabled")
                else:
                    self._error()
        elif isinstance(result, tuple) and result[0] == "ERROR":
            self._error()

    def _create_icon(self, base_rgb=None):
        """Create a 32x32 gradient icon from base_rgb to white."""
        size = 32
        icon = PhotoImageClass(width=size, height=size)
        if base_rgb is None:
            r, g, b = 170, 204, 255  # pastel blue default
        else:
            r, g, b = base_rgb
        for y in range(size):
            rr = int(r + (255 - r) * y / (size - 1))
            gg = int(g + (255 - g) * y / (size - 1))
            bb = int(b + (255 - b) * y / (size - 1))
            color = f"#{rr:02x}{gg:02x}{bb:02x}"
            for x in range(size):
                icon.put(color, (x, y))
        return icon

    def _setup_ui(self):
        """Create and configure the complete user interface."""
        # Grid configuration for main layout panels
        # Left panel (model list, filters, etc.) gets a fixed minsize and a smaller weight.
        # self.root.grid_columnconfigure(0, weight=1, minsize=200)
        # Right panel (details) gets a larger weight to claim more horizontal space.
        # self.root.grid_columnconfigure(1, weight=3.5)
        # Use integer weights that approximate the desired 1:3.5 ratio (e.g., 2:7)
        self.root.grid_columnconfigure(0, weight=2, minsize=200)
        self.root.grid_columnconfigure(1, weight=7)
        self.root.grid_rowconfigure(0, weight=1)  # Allow row to expand vertically

        # Left panel setup using UI factory
        left = self.ui.create_frame(self.root)
        left.grid(row=0, column=0, sticky="nsew")

        # Header panel with title and buttons
        buttons_config = [("?", self._about, 2), ("Pie Chart", self._pie, None)]
        self.ui.create_header_panel(left, "Ollama Models", buttons_config)

        # Search panel
        self.search_var = StringVar()
        self.filter_entry = self.ui.create_search_panel(left, self.search_var, self._update_list)

        # Sort panel
        sort_options = [("name", "Name"), ("date", "Date"), ("size", "Size")]
        self.sort_buttons = self.ui.create_sort_panel(left, sort_options, self._sort, self._refresh)

        # Listbox with scrollbar
        self.listbox, scrollbar = self.ui.create_listbox_with_scrollbar(left, "list", row=3, column=0, columnspan=3, sticky="nsew", padx=8, pady=4)

        self.listbox.bind("<<ListboxSelect>>", self._on_select)
        self.listbox.bind("<Button-3>", self._context_menu)

        # Context menu setup
        self.menu = Menu(self.root, tearoff=0)
        menu_items = ["Ready in Terminal", "Pull Updates", None, "Check Integrity", None, "Delete Model..."]
        for lbl in menu_items:
            if lbl is None:
                self.menu.add_separator()
            else:
                self.menu.add_command(label=lbl)  # Command is configured later

        # Right panel setup using UI factory
        right = self.ui.create_frame(self.root)
        right.grid(row=0, column=1, sticky="nsew", padx=8, pady=4)
        right.grid_rowconfigure(1, weight=1)
        right.grid_columnconfigure(0, weight=1)

        # Header with buttons
        header = self.ui.create_frame(right, padding="0")
        header.grid(row=0, column=0, sticky="ew", pady=(0, 4), padx=8)
        header.grid_columnconfigure(0, weight=1)

        # Details title
        self.ui.create_label(header, "Details:", "title", row=0, column=0, sticky="w", padx=4, pady=4)

        # Action buttons
        button_configs = [
            ("inspect", "Inspect Model Internals", "disabled", lambda: None),
            ("web", "Model Page", "disabled", lambda: None),
            ("hf", "Search HF", "disabled", lambda: None),
            ("copy", "[Copy Text]", "normal", self._copy),
        ]
        self.buttons = self.ui.create_button_panel(header, button_configs, extra_spacing_after=["inspect"])

        # Details text area using UI factory
        self.details = self.ui.create_scrolled_text(right, "details", wrap=WORD, state="disabled", row=1, column=0, sticky="nsew", padx=8, pady=4)

        # Configure text tags using UI factory
        self.ui.setup_text_tags(self.details, CFG["colors"])

        # Status bar at the bottom
        self.status_var = StringVar(value="Ready")
        self.status_bar = ttk.Label(self.root, textvariable=self.status_var, anchor="w", relief="sunken")
        self.status_bar.grid(row=1, column=0, columnspan=2, sticky="ew")

        # Keyboard shortcuts
        self.root.bind_all("<Control-f>", lambda e: self._focus_filter())
        self.root.bind_all("<Control-F>", lambda e: self._focus_filter())
        self.root.bind_all("<Control-r>", lambda e: self._refresh())
        self.root.bind_all("<Control-R>", lambda e: self._refresh())
        self.root.bind_all("<Control-c>", lambda e: self._copy())
        self.root.bind_all("<Control-C>", lambda e: self._copy())

    def _refresh(self):
        """Refresh model list by rescanning directory."""
        self.models, self.digest_map = self.model_manager.refresh()
        self._update_list()
        self._cache_idx = 0  # Reset cache index to start from the beginning

        if self._cache_job:
            self.root.after_cancel(self._cache_job)
            self._cache_job = None  # Ensure it's cleared

        if self._running and self.models:
            # Don't call _background_cache directly, let it be scheduled or triggered
            # by a subsequent event or if the existing job was cancelled and needs restart.
            # For an explicit refresh, we want to restart the caching process cleanly.
            self.set_status("Models refreshed. Initializing cache...")  # Indicate refresh action
            self._cache_job = self.root.after(100, self._background_cache)  # Start caching shortly after refresh
        elif not self.models:
            self.set_status("No models found.")
        else:
            self.set_status("Ready")

    def _background_cache(self):
        """Cache API data for models in background, prioritizing uncached models."""
        if not self._running or not self.models:
            self.set_status("Ready")  # Ensure Ready if nothing to do or not running
            if self._cache_job:  # Clear any pending job if we are stopping or no models
                self.root.after_cancel(self._cache_job)  # Corrected variable name self.cache_job to self._cache_job
                self._cache_job = None
            return

        found_model_to_fetch_this_iteration = False
        for i in range(len(self.models)):
            # Cycle through models starting from _cache_idx to ensure all are checked over time
            current_model_index = (self._cache_idx + i) % len(self.models)
            m = self.models[current_model_index]
            state = self.api.cache_state(m.name_tag)

            if state in [CACHE_SUCCESS, CACHE_FETCHING]:
                continue

            if state == CACHE_ERROR:
                cached_data = self.api._cache.get(m.name_tag, {})
                # Make check case-insensitive and ensure data is a string
                error_data_str = str(cached_data.get("data", "")).lower()
                if "connection failed" in error_data_str:
                    continue

            # Found a model to cache in this iteration
            found_model_to_fetch_this_iteration = True
            # Important: Update self._cache_idx to the *next* model to check in the *next* full iteration
            # This was being updated too eagerly before. It should point to where the next full scan starts.
            # For this iteration, we process m (model at current_model_index)
            # The _cache_idx update for the *next full scan* is handled outside the loop if nothing is found,
            # or implicitly by how `idx` cycles if something *is* found and we return.
            # Let's refine the _cache_idx update: only advance if we truly fetched this specific one and will return.

            base_rgb = (random.randint(128, 220), random.randint(128, 220), random.randint(180, 255))
            self._icon = self._create_icon(base_rgb)
            try:
                self.root.iconphoto(True, self._icon)
            except Exception:
                pass  # Platform support for icon may vary

            self.set_status(f"Caching: {m.name_tag}")  # Status indicates active caching
            self.api.fetch(m.name_tag, self._handle_api_result)
            # After dispatching a fetch, update _cache_idx to start the *next* scan from the model *after* the current one.
            self._cache_idx = (current_model_index + 1) % len(self.models)
            self._cache_job = self.root.after(500, self._background_cache)  # Check for next model soon
            return

        # If the loop completes without finding any model to fetch *in this iteration*:
        if not found_model_to_fetch_this_iteration:
            self.set_status("Ready")
            self._cache_idx = 0  # Reset to start from the beginning on the next long-wait cycle
            self._cache_job = self.root.after(30000, self._background_cache)  # Long wait if all seem settled
        # If found_model_to_fetch_this_iteration was true, we would have returned inside the loop.

    def _sort(self, k):
        """Change sort key and update display."""
        if k == self.sort_key:
            self.sort_reverse[k] = not self.sort_reverse[k]
        else:
            self.sort_key = k
        self._update_list()

    def _update_list(self):
        """Update listbox with filtered and sorted models."""
        if not self.models:
            return

        # Sort models
        field_map = {"name": "name_tag", "date": "mod_time", "size": "total_size"}
        f = field_map[self.sort_key]
        self.models.sort(key=lambda x: getattr(x, f), reverse=self.sort_reverse[self.sort_key])

        # Filter models
        flt = self.search_var.get().strip().lower()
        if flt:
            ms = [m for m in self.models if flt in m.name_lower]
        else:
            ms = self.models

        # Update listbox
        self.listbox.delete(0, END)
        for m in ms:
            self.listbox.insert(END, f"  {m.name_tag}")

        # Update sort button indicators
        for k, b in self.sort_buttons.items():
            if k == self.sort_key:
                indicator = " ▼" if self.sort_reverse[k] else " ▲"
            else:
                indicator = ""
            b.config(text=f"{k.capitalize()}{indicator}")

    def _on_select(self, _):
        """Handle listbox selection."""
        if s := self.listbox.curselection():
            self._show_item(self.listbox.get(s[0]).strip())

    def _show_item(self, t):
        """Display detailed information for the selected model."""
        self.current_tag = t
        self._fetching_current = False

        m = self.model_manager.get_model_by_tag(t)
        if not m:
            return

        # Clear and populate details
        self.details.config(state="normal")
        self.details.delete("1.0", END)

        # Basic info
        self.details.insert("1.0", f"Model: {t}\n\n", "bold")
        self.details.insert(END, f"Size: {fmt_size(m.total_size)}\n", "size")
        mod_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(m.mod_time))
        self.details.insert(END, f"Modified: {mod_time}\n\n")

        # File paths - prepare for sorting
        self.details.insert(END, f"Manifest: {m.manifest_path}\n\nBlobs:\n")

        blobs_to_display = []
        for b, dg in zip(m.blob_paths, m.digests):
            try:
                blob_size = b.stat().st_size if b.is_file() else 0
            except OSError:
                blob_size = -1  # Treat errored blobs as smallest for sorting, or handle differently

            shared_count = len(self.digest_map.get(dg, []))
            is_shared = shared_count > 1
            blobs_to_display.append({"path": b, "size": blob_size, "is_shared": is_shared, "digest": dg})  # Keep digest if needed for other logic, not directly for sorting here

        # Sort blobs: unique first (is_shared=False=0), then shared (is_shared=True=1).
        # Within each category, sort by size descending (-size).
        blobs_to_display.sort(key=lambda x: (x["is_shared"], -x["size"]))

        for blob_info in blobs_to_display:
            b_path = blob_info["path"]
            sz_str = fmt_size(blob_info["size"]) if blob_info["size"] >= 0 else "Error"
            status = "shared" if blob_info["is_shared"] else "unique"

            current_tags = ["blob_path_font"]
            if blob_info["is_shared"]:
                current_tags.append("sb")

            self.details.insert(END, f" {b_path} ({sz_str}) [{status}]\n", tuple(current_tags))

        self.details.insert(END, "\n(Loading...)")

        # Always scroll to top on new selection
        self.details.yview_moveto(0)

        # Configure buttons for the selected model
        self.buttons["web"].config(state="normal", command=lambda: self._open_web(t))
        self.buttons["hf"].config(state="normal", command=lambda: self._search_hf(t))
        self.buttons["inspect"].config(state="normal", command=lambda: self._llm_analysis(t))

        # Try to get cached API data
        ai = self.api.cached(t)
        if ai:
            self._update_item_data(ai)
        else:
            # Fetch API data
            self._fetching_current = True
            self.api.fetch(t, self._handle_api_result)
        self.details.config(state="disabled")

    def _error(self):
        """Handle API fetch errors."""
        self.details.config(state="normal")
        s = self.details.search("(Loading...)", "1.0", END)
        if s:
            self.details.delete(s, f"{s}+12c")
            if self.current_tag:
                entry = self.api._cache.get(self.current_tag, {})
                if entry.get("state") == CACHE_ERROR:
                    self.details.insert(s, entry.get("data", ""))
        self.set_status("API error", timeout=3)
        self.details.config(state="disabled")

    def _update_item_data(self, segments):
        """Update details display with API response data."""
        s = self.details.search("(Loading...)", "1.0", END)
        if s:
            self.details.delete(s, f"{s}+12c")
        else:
            # Don't add duplicate API sections
            if self.details.search("--- API", "1.0", END):
                return

        # Add formatted segments
        for text, tag in segments:
            if tag:
                # Highlight system prompt lines with 'sys' tag (red)
                if tag == "str" and is_system_prompt(text):
                    self.details.insert(END, text, "sys")
                else:
                    self.details.insert(END, text, tag)
            else:
                self.details.insert(END, text)

    def _context_menu(self, e):
        """Show context menu for model under cursor."""
        self.listbox.selection_clear(0, END)
        idx = self.listbox.nearest(e.y)
        if idx == -1:
            return
        self.listbox.selection_set(idx)
        tag = self.listbox.get(idx).strip()
        self._on_select(None)  # To update main view

        # Configure menu commands for the selected tag
        self.menu.entryconfigure("Ready in Terminal", command=lambda: self._run_command("run", tag))
        self.menu.entryconfigure("Pull Updates", command=lambda: self._run_command("pull", tag))
        self.menu.entryconfigure("Check Integrity", command=lambda: self._check_integrity(tag))
        self.menu.entryconfigure("Delete Model...", command=lambda: self._delete(tag))

        self.menu.tk_popup(e.x_root, e.y_root)

    def _get_selected_tag(self):
        """Get selected model tag from listbox."""
        if s := self.listbox.curselection():
            return self.listbox.get(s[0]).strip()
        return None

    def _run_command(self, c, t):
        """Open terminal with ollama command for selected model."""
        if not t:
            return

        try:
            s = platform.system()
            if s == "Windows":
                cmd = f'start "Ollama" cmd /k "echo. && echo # Copy and run this command: && echo ollama {c} "{t}" && echo."'
                os.system(cmd)
            elif s == "Darwin":
                script = f'tell app "Terminal" to do script "echo; echo \\"# Copy and run this command:\\"; echo \\"ollama {c} \\\\"{t}\\\\"\\"; echo"'
                subprocess.Popen(["osascript", "-e", script])
            else:
                cmd = f'echo; echo "# Copy and run this command:"; echo "ollama {c} \\"{t}\\""; echo; bash'
                subprocess.Popen(["gnome-terminal", "--", "bash", "-c", cmd])
        except (OSError, subprocess.SubprocessError):
            msgbox.showerror("Error", "Cannot open terminal")

    def _delete(self, t):
        """Delete selected model after confirmation."""
        if not t:
            return

        if msgbox.askyesno("Confirm", f"Delete '{t}'?"):
            try:
                subprocess.run(["ollama", "rm", t], check=True, capture_output=True, text=True)
                msgbox.showinfo("Success", f"'{t}' deleted.")
                self.api.clear(t)
                self._refresh()
            except subprocess.SubprocessError:
                msgbox.showerror("Error", "Failed to delete")

    def _open_web(self, t):
        """Open model page on Ollama website."""
        if t:
            model_name = t.split(":")[0]
            webbrowser.open_new_tab(f"{CFG['urls']['ollama']}{model_name}")

    def _search_hf(self, t):
        """Search for model on Hugging Face."""
        if t:
            model_name = t.split(":")[0]
            search_url = f"{CFG['urls']['hf']}{urllib.parse.quote_plus(model_name)}"
            webbrowser.open_new_tab(search_url)

    def _check_integrity(self, t):
        """Launch the integrity check window for the selected model."""
        if not t:
            msgbox.showinfo("No Model", "Please select a model first.")
            return

        # App's only job is to instantiate the window. That's it.
        IntegrityCheckWindow(self.root, t, self.model_manager, self.fonts)

    def _pie(self):
        """Launch the pie chart window, only if not already open."""
        try:
            if self.pie_window and self.pie_window.winfo_exists():
                return
        except (AttributeError, TclError):
            self.pie_window = None

        pie_chart = PieChartWindow(self.root, self.models, self.fonts)
        self.pie_window = pie_chart.root

    def _copy(self):
        """Copy details panel contents to clipboard."""
        try:
            text = self.details.get("1.0", END).strip()
            if not text:
                return
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            # Flicker feedback
            orig_bg = self.details.cget("background")
            self.details.config(background=CFG["flicker_color"])
            self.details.after(30, lambda: self.details.config(background=orig_bg))
        except Exception:
            pass

    def _about(self):
        """Launch the About dialog, only if not already open."""
        try:
            if self.about_window and self.about_window.winfo_exists():
                return
        except (AttributeError, TclError):
            self.about_window = None

        about_dialog = AboutWindow(self.root, self.fonts, getattr(self, "scaling_factor", 1.0))
        self.about_window = about_dialog.root

    def set_status(self, text, timeout=None):
        """Set status bar text with optional timeout."""
        self.status_var.set(text)
        if timeout:
            self.root.after(int(timeout * 1000), lambda: self.status_var.set("Ready"))

    def _focus_filter(self):
        """Focus filter entry box."""
        if hasattr(self, "filter_entry"):
            self.filter_entry.focus_set()

    def _llm_analysis(self, selected_model_tag):
        """Show GGUF metadata and tensor info window."""
        if not selected_model_tag:
            msgbox.showinfo("No Model", "Please select a model first.")
            return

        # Just create an instance of the new window class.
        # It will manage its own lifecycle.
        ModelInternalsWindow(self.root, selected_model_tag, self.model_manager, self.fonts, self.scaling_factor, self.task_manager)


class UIFactory:
    """Factory for creating UI components with consistent patterns."""

    def __init__(self, root, fonts):
        self.root = root
        self.fonts = fonts

    def create_frame(self, parent, **kwargs):
        """Create frame with default padding."""
        if "padding" not in kwargs:
            kwargs["padding"] = "10"
        frame = ttk.Frame(parent, **kwargs)
        return frame

    def create_label(self, parent, text, font_key=None, **layout_kwargs):
        """Create and position label."""
        font = self.fonts.get(font_key) if font_key else None
        label_kwargs = {"text": text}
        if font:
            label_kwargs["font"] = font
        label = ttk.Label(parent, **label_kwargs)
        if layout_kwargs:
            # Check if we have pack options (expand, fill, side) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                label.pack(**layout_kwargs)
            else:
                label.grid(**layout_kwargs)
        return label

    def create_button(self, parent, text, command, width=None, state="normal", **layout_kwargs):
        """Create and position button."""
        btn_kwargs = {"text": text, "command": command, "state": state}
        if width:
            btn_kwargs["width"] = width
        button = ttk.Button(parent, **btn_kwargs)
        if layout_kwargs:
            # Check if we have pack options (expand, fill, side) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                button.pack(**layout_kwargs)
            else:
                button.grid(**layout_kwargs)
        return button

    def create_entry(self, parent, textvariable=None, **layout_kwargs):
        """Create and position entry."""
        entry_kwargs = {}
        if textvariable:
            entry_kwargs["textvariable"] = textvariable
        entry = ttk.Entry(parent, **entry_kwargs)
        if layout_kwargs:
            # Check if we have pack options (expand, fill, side) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                entry.pack(**layout_kwargs)
            else:
                entry.grid(**layout_kwargs)
        return entry

    def create_listbox_with_scrollbar(self, parent, font_key=None, **grid_kwargs):
        """Create listbox with scrollbar."""
        font = self.fonts.get(font_key) if font_key else None
        if font:
            listbox = Listbox(parent, font=font, exportselection=False)
        else:
            listbox = Listbox(parent, exportselection=False)
        scrollbar = ttk.Scrollbar(parent, command=listbox.yview)
        listbox.config(yscrollcommand=scrollbar.set)

        if grid_kwargs:
            # Extract grid parameters for listbox and scrollbar
            listbox_grid = dict(grid_kwargs)
            scrollbar_grid = {"row": listbox_grid.get("row", 0), "column": listbox_grid.get("column", 0) + listbox_grid.get("columnspan", 1), "sticky": "ns"}
            if "pady" in listbox_grid:
                scrollbar_grid["pady"] = listbox_grid["pady"]

            listbox.grid(**listbox_grid)
            scrollbar.grid(**scrollbar_grid)

        return listbox, scrollbar

    def create_header_panel(self, parent, title, buttons_config):
        """Create a header panel with title and buttons.

        Args:
            parent: Parent widget
            title: Header title text
            buttons_config: List of (text, command, width) tuples
        """
        # Main frame setup
        parent.grid_rowconfigure(3, weight=1)
        parent.grid_columnconfigure(0, weight=1)
        parent.grid_columnconfigure(1, weight=0)

        # Create title label
        self.create_label(parent, title, "title", row=0, column=0, sticky="w", padx=8, pady=4)

        # Create buttons
        for i, (text, command, width) in enumerate(buttons_config, 1):
            self.create_button(parent, text, command, width=width, row=0, column=i, sticky="e", padx=(0, 4) if i == 1 else (10, 8), pady=4)

    def create_search_panel(self, parent, search_var, update_callback):
        """Create a search panel with filter entry and clear button."""
        search_frame = self.create_frame(parent, padding="0")
        search_frame.grid(row=1, column=0, columnspan=3, sticky="ew", pady=4, padx=8)
        search_frame.grid_columnconfigure(1, weight=1)

        # Filter label
        self.create_label(search_frame, "Filter:", row=0, column=0, padx=(0, 5), pady=4)

        # Setup search variable callback
        search_var.trace_add("write", lambda *_: update_callback())

        # Filter entry
        filter_entry = self.create_entry(search_frame, textvariable=search_var, row=0, column=1, sticky="ew", padx=4, pady=4)

        # Clear button
        self.create_button(search_frame, "×", lambda: search_var.set(""), width=2, row=0, column=2, padx=4, pady=4)

        return filter_entry

    def create_sort_panel(self, parent, sort_options, sort_callback, refresh_callback):
        """Create a sort panel with sort buttons and refresh button.

        Args:
            parent: Parent widget
            sort_options: List of (key, label) tuples
            sort_callback: Function to call when sort button clicked
            refresh_callback: Function to call when refresh clicked
        """
        sort_frame = self.create_frame(parent, padding="0")
        sort_frame.grid(row=2, column=0, columnspan=3, sticky="ew", pady=4, padx=8)

        sort_buttons = {}
        for i, (k, lbl) in enumerate(sort_options):
            btn = self.create_button(sort_frame, lbl, lambda key=k: sort_callback(key), row=0, column=i, sticky="ew", padx=4, pady=4)
            sort_frame.grid_columnconfigure(i, weight=1)
            sort_buttons[k] = btn

        # Refresh button
        self.create_button(sort_frame, "⟳", refresh_callback, width=3, row=0, column=len(sort_options), padx=(5, 8), pady=4)

        return sort_buttons

    def create_dialog_window(self, title, geometry="400x220", modal=True, resizable=False):
        """Create standardized dialog window, returns (window, frame)."""
        window = Toplevel(self.root)
        window.title(title)
        window.geometry(geometry)
        window.resizable(resizable, resizable)
        window.transient(self.root)

        if modal:
            window.grab_set()

        frame = self.create_frame(window, padding="16")
        frame.pack(fill="both", expand=True)

        return window, frame

    def create_button_panel(self, parent, button_configs, extra_spacing_after=None, **grid_kwargs):
        """Create a panel with multiple buttons.

        Args:
            parent: Parent widget
            button_configs: List of (key, text, state, command) tuples
            extra_spacing_after: List of button keys that should have extra right padding

        Returns:
            dict: Dictionary mapping keys to button widgets
        """
        extra_spacing_after = extra_spacing_after or []
        buttons = {}
        for i, (k, text, state, command) in enumerate(button_configs, 1):
            # Add extra padding if this button is in the extra_spacing_after list
            padx = (4, 45) if k in extra_spacing_after else 4
            btn = self.create_button(parent, text, command, state=state, row=0, column=i, padx=padx, pady=4)
            buttons[k] = btn
        return buttons

    def create_scrolled_text(self, parent, font_key=None, wrap=WORD, state="normal", height=None, **layout_kwargs):
        """Create a ScrolledText widget.

        Args:
            parent: Parent widget
            font_key: Font key from self.fonts
            wrap: Text wrapping mode
            state: Initial state of the text widget
            height: Height in lines (widget parameter, not layout parameter)
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            ScrolledText widget
        """
        font = self.fonts.get(font_key) if font_key else None
        text_kwargs = {"wrap": wrap, "state": state}
        if font:
            text_kwargs["font"] = font
        if height is not None:
            text_kwargs["height"] = height

        text_widget = st.ScrolledText(parent, **text_kwargs)
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                text_widget.pack(**layout_kwargs)
            else:
                text_widget.grid(**layout_kwargs)
        return text_widget

    def setup_text_tags(self, text_widget, color_config):
        """Setup text tags for a text widget.

        Args:
            text_widget: The text widget to configure
            color_config: Dictionary mapping tag names to colors
        """
        text_widget.tag_configure("api_text", font=self.fonts["api_small"])
        for tag, color in color_config.items():
            text_widget.tag_configure(tag, foreground=color, font=self.fonts["details"])
        text_widget.tag_configure("bold", font=self.fonts["bold"])
        text_widget.tag_configure("blob_path_font", font=self.fonts["blob_font"])

    def create_progressbar(self, parent, mode="determinate", maximum=100, **pack_kwargs):
        """Create a progress bar.

        Args:
            parent: Parent widget
            mode: Progress bar mode ('determinate' or 'indeterminate')
            maximum: Maximum value for determinate mode
            **pack_kwargs: Pack options

        Returns:
            Progressbar widget
        """
        progress = ttk.Progressbar(parent, mode=mode, maximum=maximum)  # type: ignore[arg-type]
        if pack_kwargs:
            progress.pack(**pack_kwargs)
        return progress

    def setup_integrity_check_tags(self, text_widget):
        """Setup specialized text tags for integrity check results.

        Args:
            text_widget: The text widget to configure
        """
        text_widget.tag_configure("ok", foreground="#008800", font=self.fonts["bold"])
        text_widget.tag_configure("fail", foreground="#CC0000", font=self.fonts["bold"])
        text_widget.tag_configure("info", foreground="#666666")
        text_widget.tag_configure("header", font=self.fonts["bold"])

    def create_canvas(self, parent, width=None, height=None, bg="white", **layout_kwargs):
        """Create a Canvas widget.

        Args:
            parent: Parent widget
            width: Canvas width
            height: Canvas height
            bg: Background color
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            Canvas widget
        """
        canvas_kwargs = {"bg": bg}
        if width is not None:
            canvas_kwargs["width"] = width
        if height is not None:
            canvas_kwargs["height"] = height

        canvas = Canvas(parent, **canvas_kwargs)  # type: ignore[arg-type]
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                canvas.pack(**layout_kwargs)
            else:
                canvas.grid(**layout_kwargs)
        return canvas

    def create_notebook(self, parent, **layout_kwargs):
        """Create a Notebook widget.

        Args:
            parent: Parent widget
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            Notebook widget
        """
        notebook = ttk.Notebook(parent)
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                notebook.pack(**layout_kwargs)
            else:
                notebook.grid(**layout_kwargs)
        return notebook

    def create_treeview(self, parent, columns=None, show="headings", **layout_kwargs):
        """Create a Treeview widget.

        Args:
            parent: Parent widget
            columns: Column identifiers
            show: What to show ('tree', 'headings', or both)
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            Treeview widget
        """
        treeview_kwargs = {"show": show}
        if columns:
            treeview_kwargs["columns"] = columns

        treeview = ttk.Treeview(parent, **treeview_kwargs)  # type: ignore[arg-type]
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                treeview.pack(**layout_kwargs)
            else:
                treeview.grid(**layout_kwargs)
        return treeview

    def create_scrollbar(self, parent, orient="vertical", command=None, **layout_kwargs):
        """Create a Scrollbar widget.

        Args:
            parent: Parent widget
            orient: Orientation ('vertical' or 'horizontal')
            command: Command to execute on scroll
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            Scrollbar widget
        """
        scrollbar_kwargs = {"orient": orient}
        if command:
            scrollbar_kwargs["command"] = command

        scrollbar = ttk.Scrollbar(parent, **scrollbar_kwargs)  # type: ignore[arg-type]
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                scrollbar.pack(**layout_kwargs)
            else:
                scrollbar.grid(**layout_kwargs)
        return scrollbar

    def create_radiobutton(self, parent, text, variable, value, command=None, **layout_kwargs):
        """Create a Radiobutton widget.

        Args:
            parent: Parent widget
            text: Button text
            variable: Associated variable
            value: Value when selected
            command: Command to execute
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            Radiobutton widget
        """
        radio_kwargs = {"text": text, "variable": variable, "value": value}
        if command:
            radio_kwargs["command"] = command

        radiobutton = ttk.Radiobutton(parent, **radio_kwargs)
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                radiobutton.pack(**layout_kwargs)
            else:
                radiobutton.grid(**layout_kwargs)
        return radiobutton

    def create_separator(self, parent, orient="horizontal", **layout_kwargs):
        """Create a Separator widget.

        Args:
            parent: Parent widget
            orient: Orientation ('horizontal' or 'vertical')
            **layout_kwargs: Layout options (pack or grid)

        Returns:
            Separator widget
        """
        separator = ttk.Separator(parent, orient=orient)  # type: ignore[arg-type]
        if layout_kwargs:
            # Check if we have pack options (expand, fill) or grid options (row, column)
            if any(key in layout_kwargs for key in ["expand", "fill", "side"]):
                separator.pack(**layout_kwargs)
            else:
                separator.grid(**layout_kwargs)
        return separator


class GGUFParser:
    """GGUF file parser for metadata and tensor extraction."""

    # Type mappings as class constants
    GGUF_TYPE_MAP = {
        0: "F32",
        1: "F16",
        2: "Q4_0",
        3: "Q4_1",
        4: "Q5_0",
        5: "Q5_1",
        6: "Q8_0",
        7: "Q8_1",
        8: "Q2_K",
        9: "Q3_K",
        10: "Q4_K",
        11: "Q5_K",
        12: "Q6_K",
        13: "Q8_K",
        14: "I8",
        15: "I16",
        16: "I32",
        17: "COUNT",
    }

    @staticmethod
    def gguf_type_size(type_code):
        """Get size in bytes for GGUF type code."""
        return {0: 1, 1: 1, 2: 2, 3: 2, 4: 4, 5: 4, 6: 4, 7: 1, 10: 8, 11: 8, 12: 8}.get(type_code, 0)

    @staticmethod
    def gguf_type_name(type_code):
        """Get human-readable name for GGUF type code."""
        return {
            0: "uint8",
            1: "int8",
            2: "uint16",
            3: "int16",
            4: "uint32",
            5: "int32",
            6: "float32",
            7: "bool",
            8: "string",
            9: "array",
            10: "uint64",
            11: "int64",
            12: "float64",
        }.get(type_code, str(type_code))

    @staticmethod
    def skip_array(f, subtype, count):
        """Skip array in GGUF file stream."""
        element_size = GGUFParser.gguf_type_size(subtype)
        if element_size > 0:
            f.seek(element_size * count, 1)
        elif subtype == 8:  # String array
            for _ in range(count):
                slen = struct.unpack("<Q", f.read(8))[0]
                f.seek(slen, 1)
        elif subtype == 9:  # Nested array
            for _ in range(count):
                st, sc = struct.unpack("<IQ", f.read(12))
                GGUFParser.skip_array(f, st, sc)

    @staticmethod
    def gguf_type_bytes_per_param_estimate(type_str: str) -> float:
        """Estimate bytes per parameter for GGUF quantization types."""
        estimates = {
            "F32": 4.0,
            "F16": 2.0,
            "Q8_0": 1.0 + (2 / 32),
            "Q8_1": 1.0 + (4 / 32),
            "Q8_K": 1.0 + (2 / 256 + 2 / 256),
            "Q6_K": 6 / 8 + (2 / 256 + 2 / 256 + 1 / 256 * 128 / 2),
            "Q5_0": 5 / 8 + (2 / 32),
            "Q5_1": 5 / 8 + (4 / 32),
            "Q5_K": 5 / 8 + (2 / 256 + 2 / 256 + 1 / 256 * 128 / 2),
            "Q4_0": 0.5 + (2 / 32),
            "Q4_1": 0.5 + (4 / 32),
            "Q4_K": 0.5 + (2 / 256 + 2 / 256 + 1 / 256 * 128 / 2),
            "Q3_K": 3 / 8 + (2 / 256 + 1 / 256 * 128 / 2 + 1 / 256 * 64 / 4),
            "Q2_K": 2 / 8 + (2 / 256 + 2 / 256 * 16 / 2 + 2 / 256 * 16 / 2),
            "I32": 4.0,
            "I16": 2.0,
            "I8": 1.0,
            "IQ1_S": 0.2225,
            "IQ2_XXS": 0.275,
            "IQ2_XS": 0.30375,
            "IQ2_S": 0.31875,
            "IQ2_M": 0.345,
            "IQ3_XXS": 0.40125,
            "IQ3_XS": 0.415,
            "IQ3_S": 0.44,
            "IQ3_M": 0.45375,
            "IQ4_XS": 0.54,
            "IQ4_NL": 0.57,
        }
        return estimates.get(type_str, 0.0)

    @staticmethod
    def parse_gguf(blob_path, chat_template_text_list_ref=None):
        """Parse GGUF file and extract metadata and tensor information."""
        # Categorized field lists
        overview_fields = []
        general_fields = []
        tokenizer_fields = []
        rope_fields = []
        architecture_fields = []
        other_fields = []

        tensor_infos = []
        found_template = False
        metadata_dict = {}  # Store all metadata for analysis

        OVERVIEW_KEYS = [
            "general.name",
            "general.architecture",
            "general.type",
            "general.version",
            "general.basename",
            "general.size_label",
            "general.finetune",
            "general.organization",
            "general.license",
            "general.license.name",
            "general.license.link",
            "general.author",
            "general.description",
            "general.tags",
            "general.languages",
        ]

        SPECIAL_TOKEN_KEY_MAP = {
            "tokenizer.ggml.bos_token_id": "BOS Token ID",
            "tokenizer.ggml.eos_token_id": "EOS Token ID",
            "tokenizer.ggml.unknown_token_id": "UNK Token ID",
            "tokenizer.ggml.padding_token_id": "PAD Token ID",
            "tokenizer.ggml.add_bos_token": "Auto-add BOS Token",
            "tokenizer.ggml.add_eos_token": "Auto-add EOS Token",
            "tokenizer.ggml.add_space_prefix": "Auto-add Space Prefix",
            "tokenizer.ggml.remove_extra_whitespaces": "Remove Extra Whitespaces",
            # FIM token keys
            "tokenizer.ggml.fim_prefix_token_id": "FIM Prefix Token ID",
            "tokenizer.ggml.fim_middle_token_id": "FIM Middle Token ID",
            "tokenizer.ggml.fim_suffix_token_id": "FIM Suffix Token ID",
            "tokenizer.ggml.prefix_token_id": "Prefix Token ID (Legacy FIM)",
            "tokenizer.ggml.suffix_token_id": "Suffix Token ID (Legacy FIM)",
            "tokenizer.ggml.middle_token_id": "Middle Token ID (Legacy FIM)",
        }

        BOOLEAN_FLAG_KEYS = [
            "tokenizer.ggml.add_bos_token",
            "tokenizer.ggml.add_eos_token",
            "tokenizer.ggml.add_space_prefix",
            "tokenizer.ggml.remove_extra_whitespaces",
        ]

        try:
            with open(blob_path, "rb") as f:
                magic = f.read(4)
                if magic != b"GGUF":
                    return [("plain", f"Blob is not GGUF. Magic: {magic!r}")], [], [], [], [], [], [], [], False

                version, tensor_count, kv_count = struct.unpack("<IQQ", f.read(20))
                gguf_header_info = ("header", f"GGUF v{version}, Tensors: {tensor_count}, Meta KVs: {kv_count}\n\n")

                if chat_template_text_list_ref:
                    chat_template_text_list_ref[0] = ""

                # Enhanced type mapping with better formatting
                type_map = {
                    0: ("<B", "num", 1),
                    1: ("<b", "num", 1),
                    2: ("<H", "num", 2),
                    3: ("<h", "num", 2),
                    4: ("<I", "num", 4),
                    5: ("<i", "num", 4),
                    6: ("<f", "num", 4),
                    7: ("<B", "bool", 1),
                    10: ("<Q", "num", 8),
                    11: ("<q", "num", 8),
                    12: ("<d", "num", 8),
                }

                # Parse metadata key-value pairs
                for i in range(kv_count):
                    key_len = struct.unpack("<Q", f.read(8))[0]
                    key = f.read(key_len).decode("utf-8", errors="replace")
                    type_code = struct.unpack("<I", f.read(4))[0]
                    val_str, tag_str = "", "italic"
                    original_key_for_categorization = key

                    if type_code in type_map:
                        fmt, tag_str, size = type_map[type_code]
                        val = struct.unpack(fmt, f.read(size))[0]

                        # Format numeric values
                        if tag_str == "num" and isinstance(val, float):
                            if 9.999999e-6 < val < 1.0000001e-5:
                                val_str = "0.00001"
                            elif 0.00000001 < abs(val) < 0.9:
                                formatted_val = f"{val:.8f}"
                                val_str = formatted_val.rstrip("0").rstrip(".")
                                if val_str == ".":
                                    val_str = "0"
                                elif val_str.startswith("-."):
                                    val_str = "-0" + val_str[1:]
                                elif val_str.startswith("."):
                                    val_str = "0" + val_str
                            else:
                                val_str = str(val)
                        else:
                            val_str = str(val)
                        metadata_dict[key] = val

                        # Override for special token keys
                        if key in SPECIAL_TOKEN_KEY_MAP:
                            display_key = SPECIAL_TOKEN_KEY_MAP[key]
                            if key in BOOLEAN_FLAG_KEYS:
                                val_str = "Yes" if val == 1 else "No"
                        else:
                            display_key = key

                    elif type_code == 8:  # String
                        slen = struct.unpack("<Q", f.read(8))[0]
                        sval = f.read(slen).decode("utf-8", errors="replace")
                        metadata_dict[key] = sval
                        val_str = f'"{sval}"'
                        tag_str = "longstr" if len(sval) > 40 else "str"
                        display_key = key

                        if key in SPECIAL_TOKEN_KEY_MAP:
                            display_key = SPECIAL_TOKEN_KEY_MAP[key]

                        # Specific overrides for certain string fields
                        if key == "general.tags":
                            val_str = sval
                            tag_str = "tags_info"
                        elif key == "general.languages":
                            val_str = sval
                            tag_str = "languages_info"
                        elif key == "general.license":
                            val_str = sval
                            tag_str = "license_type"
                        elif key == "general.license.name":
                            val_str = sval
                            tag_str = "license_name_info"
                        elif key == "general.license.link":
                            val_str = sval
                            tag_str = "license_link"
                        elif key == "general.author":
                            val_str = sval
                            tag_str = "author_info"
                        elif key == "general.description":
                            val_str = sval
                            tag_str = "description_info"
                        elif "chat_template" in key and chat_template_text_list_ref:
                            val_str = f"[Present. {len(sval)} chars - see Chat Template tab.]"
                            tag_str = "italic"
                            display_key = SPECIAL_TOKEN_KEY_MAP.get(key, key)
                            if not found_template:
                                chat_template_text_list_ref[0] = sval
                                found_template = True
                        elif is_system_prompt(sval):
                            tag_str = "sys"

                    elif type_code == 9:  # Array
                        subtype, count = struct.unpack("<IQ", f.read(12))
                        display_key = key
                        tag_str = "italic"

                        if subtype == 8 and count < 100:  # String arrays
                            try:
                                array_values = []
                                for _ in range(count):
                                    item_len = struct.unpack("<Q", f.read(8))[0]
                                    item_val = f.read(item_len).decode("utf-8", errors="replace")
                                    array_values.append(item_val)
                                metadata_dict[key] = array_values

                                if key == "general.tags":
                                    val_str = ", ".join(array_values) if array_values else "[No Tags]"
                                    tag_str = "tags_info"
                                elif key == "general.languages":
                                    val_str = ", ".join(array_values) if array_values else "[No Languages]"
                                    tag_str = "languages_info"
                                elif key == "general.datasets":
                                    val_str = ", ".join(array_values) if array_values else "[No Datasets]"
                                    tag_str = "datasets_info"
                                elif any(is_system_prompt(item) for item in array_values):
                                    val_str = f"[{GGUFParser.gguf_type_name(subtype)} x {count}] - Contains system prompts!"
                                    tag_str = "sys"
                                else:
                                    # Generic string array: show sample
                                    sample_display = ", ".join(f'"{v}"' for v in array_values[:3])
                                    if count > 3:
                                        sample_display += ", ..."
                                    val_str = f"[Array of {GGUFParser.gguf_type_name(subtype)}, Count: {count}] (Sample: {sample_display})"
                            except Exception:
                                GGUFParser.skip_array(f, subtype, count)
                                val_str = f"[{GGUFParser.gguf_type_name(subtype)} x {count}] - Error reading content"
                        else:
                            GGUFParser.skip_array(f, subtype, count)
                            val_str = f"[{GGUFParser.gguf_type_name(subtype)} x {count}]"
                    else:
                        val_str = f"(unknown type {type_code})"
                        display_key = key

                    # Categorize field
                    field_entry = (display_key, val_str, tag_str)

                    # Determine architecture prefix for RoPE check
                    arch_prefix_for_rope = ""
                    for arch_p in ["llama.", "falcon.", "gpt.", "mpt.", "bloom.", "qwen2.", "qwen3moe.", "deepseek2.", "exaone."]:
                        if original_key_for_categorization.startswith(arch_p):
                            arch_prefix_for_rope = arch_p
                            break

                    if original_key_for_categorization in OVERVIEW_KEYS:
                        overview_fields.append(field_entry)
                    elif original_key_for_categorization.startswith("general.rope.") or (arch_prefix_for_rope and original_key_for_categorization.startswith(arch_prefix_for_rope + "rope.")):
                        rope_fields.append(field_entry)
                    elif original_key_for_categorization.startswith("general."):
                        general_fields.append(field_entry)
                    elif original_key_for_categorization.startswith("tokenizer."):
                        tokenizer_fields.append(field_entry)
                    elif any(original_key_for_categorization.startswith(arch) for arch in ["llama.", "falcon.", "gpt.", "mpt.", "bloom."]):
                        architecture_fields.append(field_entry)
                    else:
                        other_fields.append(field_entry)

                # Parse tensors
                for i in range(tensor_count):
                    name_len = struct.unpack("<Q", f.read(8))[0]
                    name = f.read(name_len).decode("utf-8", errors="replace")
                    n_dims = struct.unpack("<I", f.read(4))[0]
                    shape = [struct.unpack("<Q", f.read(8))[0] for _ in range(n_dims)]
                    ggml_type, offset = struct.unpack("<IQ", f.read(12))
                    param_count = math.prod(shape) if shape else 0
                    tensor_infos.append(
                        {
                            "id": i + 1,
                            "name": name,
                            "n_dims": n_dims,
                            "shape": shape,
                            "type_code": ggml_type,
                            "type_str": GGUFParser.GGUF_TYPE_MAP.get(ggml_type, f"UNK_{ggml_type}"),
                            "offset": offset,
                            "param_count": param_count,
                        }
                    )

        except FileNotFoundError:
            return [("plain", "Error: Blob file not found.")], [], [], [], [], [], [], [], False
        except struct.error as e:
            return [("plain", f"GGUF Struct Error: {type(e).__name__}: {e}")], [], [], [], [], [], [], [], False
        except Exception as e:
            return [("plain", f"GGUF Read Error: {type(e).__name__}: {e}")], [], [], [], [], [], [], [], False

        return gguf_header_info, overview_fields, general_fields, tokenizer_fields, rope_fields, architecture_fields, other_fields, tensor_infos, found_template


class ModelInternalsWindow:
    """Manages the 'Model Internals' window, encapsulating its UI, state, and logic."""

    def __init__(self, parent_root, model_tag, model_manager, fonts, scaling_factor, task_manager):
        """Initialize the Model Internals window."""
        self.parent = parent_root
        self.model_tag = model_tag
        self.model_manager = model_manager
        self.fonts = fonts
        self.scaling_factor = scaling_factor
        self.task_manager = task_manager  # From App for async operations

        internals_geom = CFG["window"].get("model_internals_geometry", "1000x750")
        self.root = Toplevel(parent_root)
        self.root.title(f"Model Internals: {self.model_tag}")
        self.root.geometry(internals_geom)
        self.root.resizable(True, True)
        self.root.transient(parent_root)

        self.ui = UIFactory(self.root, self.fonts)

        # Window-specific variables
        self.plot_mode = StringVar(value="count")
        self.plot_images: List[PhotoImage] = []  # type: ignore
        self.is_plot_generating = False  # Track if plot generation is active
        self.plot_canvas_ref: Optional[Canvas] = None  # type: ignore
        self.tensor_data_for_resize = []
        self.resize_timer: Dict[str, Optional[str]] = {"timer": None}  # type: ignore
        self.meta_text: Optional[st.ScrolledText] = None  # type: ignore
        self.template_text: Optional[st.ScrolledText] = None  # type: ignore
        self.tensor_tree: Optional[ttk.Treeview] = None  # type: ignore
        self.notebook: Optional[ttk.Notebook] = None  # type: ignore
        self.copy_btn = None
        self.chat_template_text_holder = [""]

        # Threading and state management
        self.plot_queue = queue.Queue()
        self.is_plotting = {"active": False}
        self.plot_cache_state = {
            "is_rendered": False,
            "last_mode": None,
            "last_canvas_size": (0, 0),
            "last_data_hash": None,
        }

        # Setup UI and load data
        self._setup_ui()
        self._load_data()
        self._check_plot_queue()

    def _setup_ui(self):
        """Create and configure the UI for the Model Internals window."""
        main_frame = self.ui.create_frame(self.root, padding="10")
        main_frame.pack(expand=True, fill="both")

        self.notebook = self.ui.create_notebook(main_frame, expand=True, fill="both")
        style = ttk.Style()
        style.configure("TNotebook.Tab", padding=[12, 8])

        # Metadata Tab
        meta_frame = self.ui.create_frame(self.notebook, padding="10")
        self.notebook.add(meta_frame, text="Metadata")
        self.meta_text = self.ui.create_scrolled_text(meta_frame, "details", wrap=WORD, expand=True, fill="both")
        self._configure_metadata_tags()
        self.meta_text.config(state="normal")
        self.meta_text.insert("end", "Loading GGUF metadata...")
        self.meta_text.config(state="disabled")

        # Chat Template Tab
        template_frame = self.ui.create_frame(self.notebook, padding="10")
        self.notebook.add(template_frame, text="Chat Template", state="disabled")
        self.template_text = self.ui.create_scrolled_text(template_frame, "details", wrap=WORD, expand=True, fill="both")
        self._configure_chat_template_tags()
        self.template_text.config(state="normal")
        self.template_text.insert("end", "No chat template available for this model.")
        self.template_text.config(state="disabled")

        # Tensors Tab
        tensor_frame = self.ui.create_frame(self.notebook, padding="10")
        self.notebook.add(tensor_frame, text="Tensors")
        tensor_tree_frame = self.ui.create_frame(tensor_frame)
        tensor_tree_frame.pack(expand=True, fill="both")
        self.tensor_tree_columns = ("id", "name", "shape", "type", "params", "offset")
        self.tensor_tree = self.ui.create_treeview(tensor_tree_frame, columns=self.tensor_tree_columns, show="headings")
        self._style_tensor_treeview()
        vsb = self.ui.create_scrollbar(tensor_tree_frame, orient="vertical", command=self.tensor_tree.yview, side="right", fill="y")
        hsb = self.ui.create_scrollbar(tensor_tree_frame, orient="horizontal", command=self.tensor_tree.xview, side="bottom", fill="x")
        self.tensor_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.tensor_tree.pack(side="left", fill="both", expand=True)
        self.tensor_tree.insert("", "end", values=("Loading...", "", "", "", "", ""))

        # TensorPlot Tab
        plot_frame = self.ui.create_frame(self.notebook, padding="10")
        self.notebook.add(plot_frame, text="TensorPlot")
        plot_controls_frame = self.ui.create_frame(plot_frame)
        plot_controls_frame.pack(side="top", fill="x", pady=(0, 5))
        self.ui.create_label(plot_controls_frame, "Plot by:", side="left", padx=(0, 5))
        self.ui.create_radiobutton(
            plot_controls_frame, "Size (Bytes)", self.plot_mode, "size_bytes", command=lambda: (self.plot_cache_state.update({"is_rendered": False}), self._on_canvas_resize(None)), side="left", padx=5
        )
        self.ui.create_radiobutton(
            plot_controls_frame, "Tensor Count", self.plot_mode, "count", command=lambda: (self.plot_cache_state.update({"is_rendered": False}), self._on_canvas_resize(None)), side="left", padx=5
        )
        self.plot_canvas_ref = self.ui.create_canvas(plot_frame, bg="#2A2A2A", width=800, height=600, expand=True, fill="both")
        self.plot_canvas_ref.bind("<Configure>", self._on_canvas_resize)

        # Buttons
        btn_frame = self.ui.create_frame(main_frame)
        btn_frame.pack(fill="x", pady=(10, 0))
        self.copy_btn = self.ui.create_button(btn_frame, "Copy Tab Content", self._copy_active_tab_text, side="left", padx=(0, 8))
        self.notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)
        self._on_tab_changed()

    def _configure_metadata_tags(self):
        if not self.meta_text:
            return
        self.meta_text.tag_configure("key", font=self.fonts["details"])
        self.meta_text.tag_configure("num", foreground="#007700", font=self.fonts["details"])
        self.meta_text.tag_configure("longstr", foreground="#003366", font=self.fonts["api_small"])
        self.meta_text.tag_configure("str", foreground="#003366", font=self.fonts["details"])
        self.meta_text.tag_configure("bool", foreground="#700070", font=self.fonts["details"])
        self.meta_text.tag_configure("array", foreground="#444444", font=self.fonts["details"])
        self.meta_text.tag_configure("header", font=self.fonts["bold"])
        self.meta_text.tag_configure("italic", font=(self.fonts["details"].actual("family"), self.fonts["details"].actual("size"), "italic"))
        self.meta_text.tag_configure("newline", foreground="#6B0E6B", font=self.fonts["bold"])
        self.meta_text.tag_configure("license_type", font=self.fonts["bold"])
        self.meta_text.tag_configure("license_link", foreground="#0000EE", font=self.fonts["details"])
        self.meta_text.tag_configure("license_name_info", font=self.fonts["details"])
        self.meta_text.tag_configure("author_info", font=self.fonts["details"])
        self.meta_text.tag_configure("description_info", font=self.fonts["italic_details_font"])
        self.meta_text.tag_configure("tags_info", foreground="#005300", font=self.fonts["italic_details_font"])
        self.meta_text.tag_configure("languages_info", foreground="#005300", font=self.fonts["italic_details_font"])

    def _configure_chat_template_tags(self):
        if not self.template_text:
            return
        tag_config = {
            "var": {"foreground": "#286CB0"},
            "block": {},
            "text": {},
            "str": {"foreground": "#00008B"},
            "comment": {"foreground": "#666666"},
            "bold": {"font": self.fonts["bold"]},
            "num": {"foreground": "#007700"},
            "sys": {"foreground": "#990000"},
            "newline": {"foreground": "#6B0E6B", "font": self.fonts["bold"]},
        }
        base_chat_font = self.fonts["chat_template_font"]
        for tag, config in tag_config.items():
            if "font" not in config:
                config["font"] = base_chat_font
            elif not config:
                config["font"] = base_chat_font
            self.template_text.tag_configure(tag, **config)

    def _style_tensor_treeview(self):
        if not self.tensor_tree:
            return
        style = ttk.Style()
        base_small_font_size = self.fonts["small"].cget("size")

        # For treeview, use a smaller font size to fit more content
        # Apply scaling factor first, then reduce size more aggressively for compactness
        scaled_base_size = max(int(base_small_font_size * self.scaling_factor), 8)
        treeview_content_font_size = max(int(scaled_base_size * 0.75), 6)

        tree_font = tkFont.Font(family=self.fonts["small"].cget("family"), size=treeview_content_font_size)
        tree_heading_font = tkFont.Font(family=self.fonts["small"].cget("family"), size=treeview_content_font_size, weight="bold")

        # Calculate row height with generous padding to prevent descender cutoff
        font_ascent = tree_font.metrics("ascent")
        font_descent = tree_font.metrics("descent")
        font_linespace = tree_font.metrics("linespace")

        # Use the larger of calculated height or linespace, plus extra padding for descenders
        calculated_height = font_ascent + font_descent + 16  # Generous padding for descenders like g, q, p, j, y
        scaled_row_height = max(calculated_height, font_linespace + 16, 24)

        style.configure("Treeview", font=tree_font, rowheight=scaled_row_height)
        style.configure("Treeview.Heading", font=tree_heading_font)
        col_widths = {
            "id": int(40 * self.scaling_factor),
            "name": int(350 * self.scaling_factor),
            "shape": int(150 * self.scaling_factor),
            "type": int(100 * self.scaling_factor),
            "params": int(100 * self.scaling_factor),
            "offset": int(100 * self.scaling_factor),
        }
        for col in self.tensor_tree_columns:
            self.tensor_tree.heading(col, text=col.capitalize(), command=lambda c=col: self._sort_treeview(self.tensor_tree, c, False))
            self.tensor_tree.column(col, stretch=True, width=col_widths.get(col, int(120 * self.scaling_factor)), minwidth=col_widths.get(col, int(120 * self.scaling_factor)))

    def _load_data(self):
        """Loads GGUF data asynchronously via the Task Manager."""
        m = self.model_manager.get_model_by_tag(self.model_tag)
        if not m or not m.blob_paths:
            msgbox.showinfo("No GGUF", "No blob files found for this model.", parent=self.root)
            self.root.destroy()
            return

        largest_blob_path = max(m.blob_paths, key=lambda p: p.stat().st_size if p.is_file() else 0)

        # Use the task manager to run the parser in the background and call _on_data_loaded on completion
        self.task_manager.run(self._gguf_parser_worker, self._on_data_loaded, largest_blob_path)

    def _gguf_parser_worker(self, blob_path):
        """
        Background worker function.
        This runs in a separate thread and MUST NOT touch any Tkinter UI elements.
        It returns the parsed data.
        """
        return GGUFParser.parse_gguf(blob_path, self.chat_template_text_holder)

    def _on_data_loaded(self, result):
        """
        UI callback function.
        This runs in the main UI thread and receives the result from the worker.
        """
        if not self.root.winfo_exists():
            return

        # Check if the worker returned an error tuple
        if isinstance(result, tuple) and result[0] == "ERROR":
            # Handle the error, e.g., show a message box
            msgbox.showerror("Parsing Error", f"Failed to parse GGUF file: {result[1]}", parent=self.root)
            return

        # Unpack the successful result
        (gguf_header, overview_fields, general_meta_fields, tokenizer_meta_fields, rope_meta_fields, architecture_meta_fields, other_meta_fields, tensor_data_list, found_template_flag) = result

        # Update UI components
        self._update_metadata_tab(gguf_header, overview_fields, general_meta_fields, tokenizer_meta_fields, rope_meta_fields, architecture_meta_fields, other_meta_fields)
        self._update_tensor_tab(tensor_data_list)
        if found_template_flag:
            self._update_chat_template_tab()

        # Schedule the plot generation
        def delayed_plot():
            if not self.root.winfo_exists() or not self.plot_canvas_ref or not self.plot_canvas_ref.winfo_exists():
                return
            self.plot_canvas_ref.update_idletasks()
            if self.plot_canvas_ref.winfo_width() > 100 and self.plot_canvas_ref.winfo_height() > 100:
                self.tensor_data_for_resize.clear()
                self.tensor_data_for_resize.extend(tensor_data_list)
                if not self.is_plot_generating:
                    self._on_canvas_resize(None)
            else:
                self.root.after(100, delayed_plot)

        self.root.after(100, delayed_plot)

    def _update_metadata_tab(self, header, *field_lists):
        if not self.meta_text:
            return
        self.meta_text.config(state="normal")
        self.meta_text.delete("1.0", "end")
        if header and isinstance(header, tuple) and len(header) == 2:
            self.meta_text.insert("end", header[1], header[0])
        elif isinstance(header, list) and header:
            for tag_err, txt_err in header:
                self.meta_text.insert("end", txt_err, tag_err)
            if header[0][0] == "plain":
                self.meta_text.config(state="disabled")
                return
        sections = [
            ("=== Model Overview ===\n", field_lists[0]),
            ("=== General Information ===\n", field_lists[1]),
            ("=== Tokenizer Information ===\n", field_lists[2]),
            ("=== RoPE Configuration ===\n", field_lists[3]),
            ("=== Architecture Specific ===\n", field_lists[4]),
            ("=== Other Metadata ===\n", field_lists[5]),
        ]
        for title, fields in sections:
            if fields:
                self.meta_text.insert("end", title, "header")
                for key, val, tag in fields:
                    self.meta_text.insert("end", f"{key}: ", "key")
                    self.meta_text.insert("end", f"{val}\n", tag)
                self.meta_text.insert("end", "\n", "plain")
        self.meta_text.config(state="disabled")

    def _update_tensor_tab(self, tensor_data_list):
        if not self.tensor_tree:
            return
        self.tensor_tree.delete(*self.tensor_tree.get_children())
        for info in tensor_data_list:
            shape_str = "(" + ",".join(str(d) for d in info["shape"]) + ")"
            self.tensor_tree.insert("", "end", values=(info["id"], info["name"], shape_str, info["type_str"], f"{info['param_count']:,}", f"{info['offset']:,}"))

    def _update_chat_template_tab(self):
        if not self.notebook or not self.template_text:
            return
        self.notebook.tab(1, state="normal")
        self.template_text.config(state="normal")
        self.template_text.delete("1.0", "end")
        raw_template = self.chat_template_text_holder[0]
        formatter = TemplateFormatter(raw_template)
        lines = formatter.format()
        if not lines:
            self.template_text.insert("end", raw_template, "text")
        else:
            for tag, val in lines:
                if tag == "text" and ("[SYSTEM_PROMPT]" in val or "<|im_start|>system" in val):
                    self.template_text.insert("end", val, "sys")
                else:
                    self.template_text.insert("end", val, tag)
        formatter.apply_syntax_highlighting(self.template_text)
        self.template_text.config(state="disabled")

    def _check_plot_queue(self):
        try:
            while True:
                msg_type, data = self.plot_queue.get_nowait()
                if msg_type == "PLOT_DATA":
                    canvas_w, canvas_h, plot_mode = data["canvas_dims"]
                    self._update_plot_on_canvas(data["plot_items"], canvas_w, canvas_h, plot_mode)
                    self.plot_cache_state["is_rendered"] = True
                elif msg_type == "ERROR":
                    canvas_w, canvas_h = data["canvas_dims"]
                    self._update_plot_on_canvas(None, canvas_w, canvas_h, data["message"])
                elif msg_type == "DONE":
                    self.is_plotting["active"] = False
        except queue.Empty:
            pass
        if self.is_plotting["active"] and self.root.winfo_exists():
            self.root.after(50, self._check_plot_queue)

    def _on_canvas_resize(self, _event):
        if self.resize_timer["timer"]:
            self.root.after_cancel(self.resize_timer["timer"])

        def do_resize():
            self.resize_timer["timer"] = None
            if self.is_plot_generating or not self.plot_canvas_ref or not self.plot_canvas_ref.winfo_exists() or self.plot_canvas_ref.winfo_width() <= 1 or self.plot_canvas_ref.winfo_height() <= 1:
                return
            self.plot_canvas_ref.delete("all")
            self.plot_cache_state["is_rendered"] = False
            canvas_w, canvas_h = self.plot_canvas_ref.winfo_width(), self.plot_canvas_ref.winfo_height()
            if canvas_w > 1 and canvas_h > 1:
                self.plot_canvas_ref.create_text(canvas_w / 2, canvas_h / 2, text="Generating tensor plot...", font=self.fonts["details"], fill="#AAAAAA", justify="center")
            self.is_plotting["active"] = True
            self._check_plot_queue()
            self.plot_cache_state["last_mode"] = self.plot_mode.get()
            self.plot_cache_state["last_canvas_size"] = (canvas_w, canvas_h)
            self.plot_cache_state["last_data_hash"] = hash(tuple((d["name"], d["type_str"]) for d in self.tensor_data_for_resize[:10]))
            plot_mode_value = self.plot_mode.get()
            self.is_plot_generating = True
            self.task_manager.run(lambda: self._generate_plot_data_with_queue(list(self.tensor_data_for_resize), canvas_w, canvas_h, plot_mode_value, self.plot_queue), self._on_plot_generated)

        self.resize_timer["timer"] = self.root.after(100, do_resize)

    def _on_plot_generated(self, _):
        self.is_plot_generating = False

    def _copy_active_tab_text(self):
        try:
            if not self.notebook:
                return
            selected_tab_index = self.notebook.index(self.notebook.select())
            content_to_copy, flicker_widget = None, None
            if selected_tab_index == 0 and self.meta_text:
                content_to_copy, flicker_widget = self.meta_text.get("1.0", "end").strip(), self.meta_text
            elif selected_tab_index == 1 and self.template_text:
                content_to_copy, flicker_widget = self.chat_template_text_holder[0] or self.template_text.get("1.0", "end").strip(), self.template_text
            elif selected_tab_index == 2 and self.tensor_tree:
                lines = ["\t".join(self.tensor_tree_columns)]
                lines.extend("\t".join(map(str, self.tensor_tree.item(item_id, "values"))) for item_id in self.tensor_tree.get_children())
                content_to_copy, flicker_widget = "\n".join(lines), self.tensor_tree
            elif selected_tab_index == 3 and self.plot_canvas_ref:
                if self._copy_tensor_plot_to_clipboard(self.plot_canvas_ref):
                    orig_bg = self.plot_canvas_ref.cget("bg")
                    self.plot_canvas_ref.config(bg=CFG["flicker_color"])
                    self.plot_canvas_ref.after(30, lambda: self.plot_canvas_ref.config(bg=orig_bg) if self.plot_canvas_ref else None)
                return
            if content_to_copy and flicker_widget:
                self.parent.clipboard_clear()
                self.parent.clipboard_append(content_to_copy)
                if isinstance(flicker_widget, st.ScrolledText):
                    orig_bg = flicker_widget.cget("background")
                    flicker_widget.config(background=CFG["flicker_color"])
                    flicker_widget.after(30, lambda: flicker_widget.config(background=orig_bg))
                elif isinstance(flicker_widget, ttk.Treeview):
                    style = ttk.Style()
                    orig_bg = style.lookup("Treeview", "background")
                    style.configure("Treeview", background=CFG["flicker_color"])
                    flicker_widget.after(30, lambda: style.configure("Treeview", background=orig_bg))
        except Exception:
            pass

    def _on_tab_changed(self, _event=None):
        if not self.notebook or not self.copy_btn:
            return
        selected_tab_index = self.notebook.index(self.notebook.select())
        if selected_tab_index == 3:
            self.copy_btn.state(["!disabled"])
            if self.tensor_data_for_resize and self.plot_canvas_ref and self.plot_canvas_ref.winfo_exists():
                current_mode, current_size = self.plot_mode.get(), (self.plot_canvas_ref.winfo_width(), self.plot_canvas_ref.winfo_height())
                data_hash = hash(tuple((d["name"], d["type_str"]) for d in self.tensor_data_for_resize[:10]))
                if (
                    not self.plot_cache_state["is_rendered"]
                    or self.plot_cache_state["last_mode"] != current_mode
                    or self.plot_cache_state["last_canvas_size"] != current_size
                    or self.plot_cache_state["last_data_hash"] != data_hash
                ):
                    self.plot_canvas_ref.event_generate("<Configure>")
        else:
            self.copy_btn.state(["!disabled"])

    def _generate_plot_data_with_queue(self, current_tensor_data, canvas_w, canvas_h, plot_mode, plot_queue):
        try:
            if not current_tensor_data:
                plot_queue.put(("ERROR", {"canvas_dims": (canvas_w, canvas_h), "message": "Tensor data not loaded."}))
                return
            prepared_plot_data = self._prepare_tensor_plot_data(current_tensor_data)
            if not prepared_plot_data:
                plot_queue.put(("ERROR", {"canvas_dims": (canvas_w, canvas_h), "message": "No data to plot."}))
                return
            layouts = self._calculate_treemap_layout(prepared_plot_data, 0, 0, canvas_w, canvas_h, mode=plot_mode)
            if not layouts:
                plot_queue.put(("ERROR", {"canvas_dims": (canvas_w, canvas_h), "message": "Layout calculation failed."}))
                return
            plot_items_for_ui = []
            for i, item_layout in enumerate(layouts):
                rect, color_tuple = item_layout["rect"], item_layout["color"]
                _x0, _y0, w, h = rect
                if w > 0 and h > 0:
                    try:
                        pixel_rows, img_width, img_height = self._create_pillow_image(w, h, color_tuple, _x0, _y0, (canvas_w * 0.3, canvas_h * 0.25), (canvas_w, canvas_h))
                        plot_items_for_ui.append(
                            {
                                "rect": rect,
                                "pixel_rows": pixel_rows,
                                "dimensions": (img_width, img_height),
                                "label_text_parts": (item_layout["type_str"], item_layout["layer_idx"], item_layout.get(plot_mode, 0)),
                                "base_color": color_tuple,
                            }
                        )
                        if (i + 1) % 10 == 0:
                            plot_queue.put(("PROGRESS", {"percent": int((i + 1) * 100 / len(layouts))}))
                    except Exception:
                        continue
            plot_queue.put(("PLOT_DATA", {"canvas_dims": (canvas_w, canvas_h, plot_mode), "plot_items": plot_items_for_ui}))
        except Exception as e:
            plot_queue.put(("ERROR", {"canvas_dims": (canvas_w, canvas_h), "message": f"Error generating plot: {e}"}))
        finally:
            plot_queue.put(("DONE", None))

    def _update_plot_on_canvas(self, plot_items_data, canvas_w, canvas_h, plot_mode_or_message):
        if not self.plot_canvas_ref or not self.plot_canvas_ref.winfo_exists():
            return
        self.plot_canvas_ref.delete("all")
        if plot_items_data is None:
            self.plot_canvas_ref.create_text(canvas_w / 2, canvas_h / 2, text=str(plot_mode_or_message), font=self.fonts["details"], fill="#AAAAAA", justify="center")
            return
        if not plot_items_data:
            self.plot_canvas_ref.create_text(canvas_w / 2, canvas_h / 2, text="No items to plot.", font=self.fonts["details"], fill="#AAAAAA", justify="center")
            return
        self.plot_images.clear()
        cached_rgb = bytearray(canvas_w * canvas_h * 3)
        bg_r, bg_g, bg_b = 42, 42, 42
        for i in range(0, len(cached_rgb), 3):
            cached_rgb[i], cached_rgb[i + 1], cached_rgb[i + 2] = bg_r, bg_g, bg_b
        hover_data = []
        for item_data in plot_items_data:
            x0, y0, w, h = item_data["rect"]
            hover_data.append(
                {
                    "rect": item_data["rect"],
                    "type_str": item_data["label_text_parts"][0],
                    "layer_idx": item_data["label_text_parts"][1],
                    "value": item_data["label_text_parts"][2],
                    "base_color": item_data["base_color"],
                    "plot_mode": plot_mode_or_message,
                }
            )
            width, height = item_data["dimensions"]
            pillow_image = PhotoImageClass(width=width, height=height)
            for y, row_data in enumerate(item_data["pixel_rows"]):
                pillow_image.put(row_data, to=(0, y))
                if y0 + y < canvas_h:
                    for x, hex_color in enumerate(row_data.strip("{}").split()):
                        if x0 + x < canvas_w and len(hex_color) == 7:
                            try:
                                r, g, b = int(hex_color[1:3], 16), int(hex_color[3:5], 16), int(hex_color[5:7], 16)
                                pixel_idx = ((y0 + y) * canvas_w + (x0 + x)) * 3
                                cached_rgb[pixel_idx], cached_rgb[pixel_idx + 1], cached_rgb[pixel_idx + 2] = r, g, b
                            except (ValueError, IndexError):
                                continue
            self.plot_images.append(pillow_image)
            self.plot_canvas_ref.create_image(x0, y0, image=pillow_image, anchor="nw")
        setattr(self.root, "_cached_plot_rgb", cached_rgb)
        setattr(self.plot_canvas_ref, "_hover_data", hover_data)
        setattr(self.plot_canvas_ref, "_tooltip_label", None)
        setattr(self.plot_canvas_ref, "_tooltip_widget", None)
        setattr(self.plot_canvas_ref, "_current_hover_block", None)
        self.plot_canvas_ref.bind("<Motion>", lambda e: self._on_canvas_hover(e, self.plot_canvas_ref))
        self.plot_canvas_ref.bind("<Leave>", lambda e: self._hide_canvas_tooltip(self.plot_canvas_ref))

    def _on_canvas_hover(self, event, canvas):
        if not hasattr(canvas, "_hover_data") or not canvas._hover_data:
            return
        mouse_x, mouse_y = event.x, event.y
        for i, hover_info in enumerate(canvas._hover_data):
            x, y, w, h = hover_info["rect"]
            if x <= mouse_x <= x + w and y <= mouse_y <= y + h:
                if canvas._current_hover_block != i:
                    canvas._current_hover_block = i
                    self._show_canvas_tooltip(canvas, event, hover_info)
                else:
                    self._update_tooltip_position(canvas, event)
                return
        if canvas._current_hover_block is not None:
            canvas._current_hover_block = None
            self._hide_canvas_tooltip(canvas)

    def _update_tooltip_position(self, canvas, event):
        if not hasattr(canvas, "_tooltip_label") or not canvas._tooltip_label or not canvas._tooltip_widget:
            return
        try:
            x, y = event.x + 10, event.y - 30
            canvas_w, canvas_h = canvas.winfo_width(), canvas.winfo_height()
            tooltip_w, tooltip_h = canvas._tooltip_widget.winfo_reqwidth(), canvas._tooltip_widget.winfo_reqheight()
            if x + tooltip_w > canvas_w:
                x = event.x - tooltip_w - 10
            if y < 0:
                y = event.y + 20
            if y + tooltip_h > canvas_h:
                y = canvas_h - tooltip_h - 5
            canvas.coords(canvas._tooltip_label, x, y)
        except Exception:
            pass

    def _show_canvas_tooltip(self, canvas, event, hover_info):
        self._hide_canvas_tooltip(canvas)
        layer_names = {-10: "Token Embedding", 10000: "Output Layer", -5: "Layer Norm"}
        layer_text = layer_names.get(hover_info["layer_idx"], f"Layer {hover_info['layer_idx']}" if hover_info["layer_idx"] >= 0 else "Special Layer")
        value_text = f"Size: {fmt_size(hover_info['value'])}" if hover_info.get("plot_mode") == "size_bytes" else f"Tensors: {hover_info['value']}"
        tooltip_text = f"{hover_info['type_str']}\n{layer_text}\n{value_text}"
        tooltip = ttk.Label(canvas, text=tooltip_text, background="#FFFACD", relief="solid", borderwidth=1, font=self.fonts["small"])
        tooltip.update_idletasks()
        x, y = event.x + 10, event.y - 30
        canvas_w, canvas_h = canvas.winfo_width(), canvas.winfo_height()
        tooltip_w, tooltip_h = tooltip.winfo_reqwidth(), tooltip.winfo_reqheight()
        if x + tooltip_w > canvas_w:
            x = event.x - tooltip_w - 10
        if y < 0:
            y = event.y + 20
        if y + tooltip_h > canvas_h:
            y = canvas_h - tooltip_h - 5
        canvas._tooltip_label = canvas.create_window(x, y, window=tooltip, anchor="nw")
        canvas._tooltip_widget = tooltip

    def _hide_canvas_tooltip(self, canvas):
        if hasattr(canvas, "_tooltip_label") and canvas._tooltip_label:
            try:
                canvas.delete(canvas._tooltip_label)
            except Exception:
                pass
            canvas._tooltip_label = None
            canvas._tooltip_widget = None

    def _prepare_tensor_plot_data(self, tensor_data_list):
        if not tensor_data_list:
            return []
        grouped_data = defaultdict(lambda: {"count": 0, "total_param_count": 0, "estimated_total_bytes": 0.0})
        for tensor_info in tensor_data_list:
            type_str, param_count, layer_idx = tensor_info["type_str"], tensor_info["param_count"], self._extract_layer_number(tensor_info["name"])
            group_key = (type_str, layer_idx)
            grouped_data[group_key]["count"] += 1
            grouped_data[group_key]["total_param_count"] += param_count
            grouped_data[group_key]["estimated_total_bytes"] += param_count * GGUFParser.gguf_type_bytes_per_param_estimate(type_str)
        plot_data, TYPE_BASE_HUES = [], {
            "Q4_K": 0.55,
            "Q6_K": 0.45,
            "Q8_0": 0.35,
            "Q5_K": 0.65,
            "Q3_K": 0.75,
            "Q2_K": 0.85,
            "F32": 0.05,
            "F16": 0.15,
            "Q4_0": 0.25,
            "Q4_1": 0.30,
            "Q5_0": 0.40,
            "Q5_1": 0.42,
            "Q8_1": 0.38,
            "Q8_K": 0.33,
            "I8": 0.90,
            "I16": 0.92,
            "I32": 0.95,
            "IQ1_S": 0.2225,
            "IQ2_XXS": 0.275,
            "IQ2_XS": 0.30375,
            "IQ2_S": 0.31875,
            "IQ2_M": 0.345,
            "IQ3_XXS": 0.40125,
            "IQ3_XS": 0.415,
            "IQ3_S": 0.44,
            "IQ3_M": 0.45375,
            "IQ4_XS": 0.54,
            "IQ4_NL": 0.57,
        }
        all_layer_indices = [idx for _, idx in grouped_data.keys()]
        min_layer, max_layer = (min(all_layer_indices), max(all_layer_indices)) if all_layer_indices else (0, 0)
        layer_range = max(1, max_layer - min_layer)
        color_idx = 0
        for (type_str, layer_idx), data in sorted(grouped_data.items(), key=lambda x: (x[0][0], x[0][1])):
            if type_str not in TYPE_BASE_HUES:
                TYPE_BASE_HUES[type_str] = (color_idx * 0.137) % 1.0
                color_idx += 1
            base_hue, layer_normalized = TYPE_BASE_HUES[type_str], (layer_idx - min_layer) / layer_range if layer_idx >= 0 else 0
            final_hue, saturation, value = (base_hue + (layer_normalized - 0.5) * 0.1) % 1.0, 0.7 - (layer_normalized * 0.15), 0.85 - (layer_normalized * 0.1)
            r, g, b = colorsys.hsv_to_rgb(final_hue, saturation, value)
            plot_data.append(
                {
                    "type_str": type_str,
                    "layer_idx": layer_idx,
                    "count": data["count"],
                    "total_params": data["total_param_count"],
                    "size_bytes": data["estimated_total_bytes"],
                    "color": (int(r * 255), int(g * 255), int(b * 255)),
                }
            )
        return plot_data

    def _calculate_treemap_layout(self, data_items, x, y, width, height, mode="size_bytes"):
        if not data_items or width <= 0.5 or height <= 0.5:
            return []
        items = [dict(item) for item in data_items if item.get(mode, 0) > 0]
        if not items:
            return []
        total_value = sum(item.get(mode, 0) for item in items)
        if total_value == 0:
            return []
        total_area = float(width * height)
        for item in items:
            item["_scaled_value"] = max(0.0001, (item.get(mode, 0) / total_value) * total_area)
        items.sort(key=lambda item: item["_scaled_value"], reverse=True)
        final_layouts = []

        def worst_aspect_ratio(row, row_sum, length):
            if row_sum == 0 or length == 0:
                return float("inf")
            strip_thickness = row_sum / length
            if strip_thickness == 0:
                return float("inf")
            max_r = 0.0
            for item in row:
                item_length = (item["_scaled_value"] / row_sum) * length
                if item_length > 0:
                    max_r = max(max_r, max(item_length / strip_thickness, strip_thickness / item_length))
            return max_r

        def layout_row(row, row_sum, x_r, y_r, w_r, h_r, is_horizontal):
            offset = 0.0
            num_items = len(row)
            for i, item in enumerate(row):
                proportion = item["_scaled_value"] / row_sum if row_sum > 0 else 0
                if is_horizontal:
                    item_w = w_r * proportion if i < num_items - 1 else w_r - offset
                    final_layouts.append({**item, "rect": (int(round(x_r + offset)), int(round(y_r)), max(1, int(item_w)), max(1, int(h_r)))})
                    offset += item_w
                else:
                    item_h = h_r * proportion if i < num_items - 1 else h_r - offset
                    final_layouts.append({**item, "rect": (int(round(x_r)), int(round(y_r + offset)), max(1, int(w_r)), max(1, int(item_h)))})
                    offset += item_h

        def squarify(items_to_tile, current_x, current_y, current_w, current_h):
            if not items_to_tile or current_w <= 0.5 or current_h <= 0.5:
                return
            is_horizontal, length = current_w >= current_h, current_w if current_w >= current_h else current_h
            row, row_sum, idx = [], 0.0, 0
            while idx < len(items_to_tile):
                item = items_to_tile[idx]
                potential_row, potential_sum = row + [item], row_sum + item["_scaled_value"]
                if not row or worst_aspect_ratio(potential_row, potential_sum, length) <= worst_aspect_ratio(row, row_sum, length):
                    row, row_sum, idx = potential_row, potential_sum, idx + 1
                else:
                    break
            if not row:
                row, row_sum, idx = [items_to_tile[0]], items_to_tile[0]["_scaled_value"], 1
            strip_thickness = row_sum / length if length > 0 else (current_h if is_horizontal else current_w)
            if is_horizontal:
                layout_row(row, row_sum, current_x, current_y, current_w, strip_thickness, True)
                squarify(items_to_tile[idx:], current_x, current_y + strip_thickness, current_w, current_h - strip_thickness)
            else:
                layout_row(row, row_sum, current_x, current_y, strip_thickness, current_h, False)
                squarify(items_to_tile[idx:], current_x + strip_thickness, current_y, current_w - strip_thickness, current_h)

        squarify(items, float(x), float(y), float(width), float(height))
        return final_layouts

    def _sort_treeview(self, treeview, col, reverse):
        def sort_key(item):
            try:
                return float(item[0].replace(",", ""))
            except ValueError:
                return str(item[0]).lower()

        data = sorted([(treeview.set(child, col), child) for child in treeview.get_children("")], key=sort_key, reverse=reverse)
        for index, (_, child) in enumerate(data):
            treeview.move(child, "", index)
        treeview.heading(col, command=lambda c=col: self._sort_treeview(treeview, c, not reverse))

    def _extract_layer_number(self, tensor_name):
        if match := re.search(r"blk\.(\d+)\.", tensor_name):
            return int(match.group(1))
        if "token_embd" in tensor_name or "embed" in tensor_name:
            return -10
        if "output.weight" in tensor_name:
            return 10000
        if "norm" in tensor_name and "blk." not in tensor_name:
            return -5
        return -2

    def _create_pillow_image(self, width, height, base_color_tuple, canvas_rect_x, canvas_rect_y, global_light_source_xy, canvas_dims):
        width, height = max(1, int(width)), max(1, int(height))
        canvas_w, canvas_h = canvas_dims
        light_cx, light_cy = global_light_source_xy
        pillow_center_x, pillow_center_y = canvas_rect_x + width / 2, canvas_rect_y + height / 2
        dist_to_light = math.sqrt((pillow_center_x - light_cx) ** 2 + (pillow_center_y - light_cy) ** 2)
        max_dist = math.sqrt((canvas_w / 2) ** 2 + (canvas_h / 2) ** 2) or 1
        global_light_modulator = 1.0 + (0.3 * (1.0 - min(1.0, dist_to_light / max_dist)))
        cushion_height_scale = 0.8 if min(width, height) < 20 else 1.0
        lx, ly, lz = canvas_w * 0.35 - pillow_center_x, canvas_h * 0.05 - pillow_center_y, 12.0
        l_len = math.sqrt(lx * lx + ly * ly + lz * lz) or 1.0
        light_x, light_y, light_z = lx / l_len, ly / l_len, lz / l_len
        r, g, b = base_color_tuple
        h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
        all_rows = []
        for y_px in range(height):
            row_pixels_hex = []
            for x_px in range(width):
                nx, ny = 2 * x_px / width - 1, 2 * y_px / height - 1
                z = max(0, 1 - (abs(nx / 1.25) ** 4 + abs(ny / 1.25) ** 4) ** 0.25) * cushion_height_scale
                if z > 0:
                    dzdx, dzdy = -2.5 * nx - 1.5 * nx / width, -2.5 * ny - 1.5 * ny / height
                    normal_len = math.sqrt(dzdx * dzdx + dzdy * dzdy + 1)
                    normal_x, normal_y, normal_z = -dzdx / normal_len, -dzdy / normal_len, 1 / normal_len
                    diffuse = max(0, normal_x * light_x + normal_y * light_y + normal_z * light_z)
                    reflect_z = 2 * diffuse * normal_z - light_z
                    specular = max(0, reflect_z) ** 25
                    lighting = diffuse * 0.75 + (diffuse * 0.7 + specular * 0.3) * 0.25
                    lit_v = v * (0.45 + 0.55 * lighting) * global_light_modulator
                else:
                    lit_v = v * 0.3
                lit_v = max(0, min(1.15, lit_v))
                lit_r, lit_g, lit_b = colorsys.hsv_to_rgb(h, s, lit_v)
                temp_shift = (dist_to_light / max_dist) * 0.03
                r_f, g_f, b_f = int(lit_r * 255 * (1 + temp_shift)), int(lit_g * 255), int(lit_b * 255 * (1 - temp_shift * 0.5))
                row_pixels_hex.append(f"#{max(0,min(255,r_f)):02x}{max(0,min(255,g_f)):02x}{max(0,min(255,b_f)):02x}")
            all_rows.append("{" + " ".join(row_pixels_hex) + "}")
        return all_rows, width, height

    def _copy_tensor_plot_to_clipboard(self, plot_canvas_ref):
        try:
            if not plot_canvas_ref or not plot_canvas_ref.winfo_exists():
                return False
            canvas_width, canvas_height = plot_canvas_ref.winfo_width(), plot_canvas_ref.winfo_height()
            if canvas_width <= 1 or canvas_height <= 1:
                return False
            cached_plot_data = getattr(self.root, "_cached_plot_rgb", None)
            if cached_plot_data and len(cached_plot_data) == canvas_width * canvas_height * 3:
                if platform.system() == "Windows":
                    return copy_rgb_to_windows_clipboard_minimal(bytes(cached_plot_data), canvas_width, canvas_height)
            return False
        except Exception:
            return False


class IntegrityCheckWindow:
    """Manages the model integrity check dialog, including its UI and worker thread."""

    def __init__(self, parent_root, model_tag, model_manager, fonts):
        """Initialize the integrity check window."""
        self.parent = parent_root
        self.model_tag = model_tag
        self.model_manager = model_manager
        self.fonts = fonts

        # Get model data
        self.model = self.model_manager.get_model_by_tag(model_tag)
        if not self.model:
            return

        if not self.model.blob_paths:
            msgbox.showinfo("No Files", "No blob files found for this model.", parent=parent_root)
            return

        # Create window
        self.root = Toplevel(parent_root)
        self.root.title(f"Integrity Check: {model_tag}")
        self.root.geometry("840x520")
        self.root.resizable(True, True)
        self.root.transient(parent_root)

        self.ui = UIFactory(self.root, self.fonts)

        # Worker thread state
        self.worker_state = {"should_stop": False}

        # Use the global task manager from App
        self.task_manager = AsyncTaskManager(self.root)

        self._setup_ui()
        self._start_check()

    def _setup_ui(self):
        """Create the integrity check UI."""
        main_frame = self.ui.create_frame(self.root, padding="16")
        main_frame.pack(fill="both", expand=True)

        # Results text area
        self.text = self.ui.create_scrolled_text(main_frame, "details", wrap=WORD, height=15, state="normal")
        self.text.pack(expand=True, fill="both")

        # Configure tags for coloring
        self.ui.setup_integrity_check_tags(self.text)

        self.text.insert("end", f"Checking integrity of {len(self.model.blob_paths)} file(s)...\n\n", "header")
        self.text.config(state="disabled")

        # Progress bar
        self.progress = self.ui.create_progressbar(main_frame, mode="determinate", maximum=len(self.model.blob_paths), fill="x", pady=(10, 10))

        # Close button
        self.close_btn = self.ui.create_button(main_frame, "Close", self._close_window)
        self.close_btn.pack()

        # Setup close handling
        self.root.protocol("WM_DELETE_WINDOW", self._close_window)

    def _close_window(self):
        """Enhanced close function that signals worker to stop."""
        self.worker_state["should_stop"] = True
        self.root.destroy()

    def _start_check(self):
        """Start the integrity check process."""
        self.task_manager.run_with_progress(self._worker_generator, self._handle_progress, self._handle_completion)

    def _handle_progress(self, progress_value):
        """Handle progress updates from worker thread."""
        if self.root.winfo_exists() and not self.worker_state["should_stop"]:
            self.progress.config(value=progress_value)

    def _handle_completion(self, results):
        """Handle completion of integrity check."""
        if isinstance(results, tuple) and results[0] == "ERROR":
            # Handle error case
            return
        if self.root.winfo_exists() and not self.worker_state["should_stop"]:
            self._display_results(results)

    def _display_results(self, results):
        """Display integrity check results."""
        self.text.config(state="normal")
        self.text.delete("1.0", "end")

        # Summary
        passed = sum(1 for _, match, _, _ in results if match is True)
        failed = sum(1 for _, match, _, _ in results if match is False)
        unknown = sum(1 for _, match, _, _ in results if match is None)

        self.text.insert("end", f"Integrity Check Results for {self.model_tag}\n", "header")
        self.text.insert("end", f"{'=' * 60}\n\n", "info")

        if failed == 0 and unknown == 0:
            self.text.insert("end", f"✓ All {passed} file(s) passed integrity check!\n\n", "ok")
        else:
            if passed > 0:
                self.text.insert("end", f"✓ {passed} file(s) passed\n", "ok")
            if failed > 0:
                self.text.insert("end", f"✗ {failed} file(s) FAILED\n", "fail")
            if unknown > 0:
                self.text.insert("end", f"? {unknown} file(s) have no reference digest\n", "info")
            self.text.insert("end", "\n")

            # Detailed results
            self.text.insert("end", "Details:\n", "header")
            self.text.insert("end", f"{'-' * 60}\n", "info")

        for name, match, expected, actual in results:
            if match is True:
                self.text.insert("end", f"✓ {name}: ", "ok")
                self.text.insert("end", "PASSED\n", "ok")
                self.text.insert("end", f"   SHA256: {actual}\n", "info")
            elif match is False:
                self.text.insert("end", f"✗ {name}: ", "fail")
                self.text.insert("end", "FAILED\n", "fail")
                if actual.startswith("Error:"):
                    self.text.insert("end", f"   {actual}\n", "fail")
                else:
                    self.text.insert("end", f"   Expected: {expected}\n", "info")
                    self.text.insert("end", f"   Found:    {actual}\n", "fail")
            else:
                self.text.insert("end", f"? {name}: No reference digest\n")
                self.text.insert("end", f"   SHA256: {actual}\n", "info")
            self.text.insert("end", "\n")

        self.text.config(state="disabled")
        self.progress.config(value=len(self.model.blob_paths))

    def _worker_generator(self):
        """Worker generator for hash computation with progress updates."""
        results = []

        for i, (blob_path, expected_digest) in enumerate(zip(self.model.blob_paths, self.model.digests)):
            # Check if we should stop (window closed)
            if self.worker_state["should_stop"]:
                return results

            # Yield progress update
            yield ("PROGRESS", i + 1)

            try:
                # Compute SHA-256 with larger chunks and periodic stop checks
                hasher = hashlib.sha256()
                with open(blob_path, "rb") as f:
                    chunk_count = 0
                    # Read in 1MB chunks (16x larger than before for better performance)
                    for chunk in iter(lambda: f.read(1048576), b""):
                        if self.worker_state["should_stop"]:  # Check every chunk
                            return results
                        hasher.update(chunk)
                        chunk_count += 1
                        # Check stop condition every 10 chunks (10MB processed)
                        if chunk_count % 10 == 0 and self.worker_state["should_stop"]:
                            return results

                calc_digest = hasher.hexdigest()

                # Compare with expected (if available)
                if expected_digest:
                    # Extract just the hex part from "sha256:hexdigest" format
                    expected_hex = expected_digest.split(":")[-1] if ":" in expected_digest else expected_digest
                    match = calc_digest.lower() == expected_hex.lower()
                    results.append((blob_path.name, match, expected_hex, calc_digest))
                else:
                    results.append((blob_path.name, None, None, calc_digest))

            except Exception as e:
                if not self.worker_state["should_stop"]:  # Only add error if not stopping
                    results.append((blob_path.name, False, expected_digest, f"Error: {e}"))

        # Return final results
        return results


class PieChartWindow:
    """Manages the disk usage pie chart dialog."""

    def __init__(self, parent_root, models: List[Model], fonts):
        """Initialize the pie chart window."""
        self.parent = parent_root
        self.models = models
        self.fonts = fonts

        if not self.models:
            return

        # Create window
        self.root = Toplevel(parent_root)
        self.root.title("Space Usage")
        self.root.geometry("1045x770")
        self.root.resizable(True, True)
        self.root.transient(parent_root)

        self.ui = UIFactory(self.root, self.fonts)

        self._prepare_data()
        self._setup_ui()
        self._draw_chart()

    def _prepare_data(self):
        """Prepare data for pie chart."""
        # Sort models by size
        sorted_models = sorted(self.models, key=lambda x: x.total_size, reverse=True)
        self.data = [(m.name_tag, m.total_size) for m in sorted_models[:22]]

        if sorted_models[22:]:
            others_size = sum(m.total_size for m in sorted_models[22:])
            self.data.append(("all others", others_size))

        self.total = sum(s for _, s in self.data)

    def _setup_ui(self):
        """Create the pie chart UI."""
        main_frame = self.ui.create_frame(self.root, padding="16")
        main_frame.pack(fill="both", expand=True)

        # Total size label
        total_label = ttk.Label(main_frame, text=f"Total: {self.total / (1024**3):.2f} GB", font=("Arial", 12, "bold"))
        total_label.pack(pady=(0, 10))

        # Canvas
        self.canvas = self.ui.create_canvas(main_frame, width=900, height=600, bg="white", fill="both", expand=True)

        # Close button
        self.ui.create_button(main_frame, "Close", self.root.destroy).pack(pady=(10, 0))

    def _draw_chart(self):
        """Draw the pie chart and legend."""
        # Draw pie chart
        cx, cy, radius = 250, 300, 211
        random.seed(46)  # Consistent colors

        colors = []
        for i in range(len(self.data)):
            if i < len(self.data) - 1 or self.data[-1][0] != "all others":
                # Generate bright colors
                r = random.randint(180, 255)
                g = random.randint(180, 255)
                b = random.randint(180, 255)
                colors.append(f"#{r:02x}{g:02x}{b:02x}")
            else:
                colors.append("#BCBCBC")  # Medium-gray for "all others"

        angle = 0
        for (label, size), color in zip(self.data, colors):
            extent = size / self.total * 360
            self.canvas.create_arc(cx - radius, cy - radius, cx + radius, cy + radius, start=angle, extent=extent, fill=color, style="pieslice")
            angle += extent

        # Legend
        self.canvas.create_text(500, 30, text="Models", anchor="w", font=("Arial", 12, "bold"))
        for i, ((label, size), color) in enumerate(zip(self.data, colors)):
            y = 50 + i * 24
            self.canvas.create_rectangle(500, y, 515, y + 15, fill=color, outline="black")
            percentage = size / self.total * 100
            text = f"{label} ({fmt_size(size)}, {percentage:.1f}%)"
            self.canvas.create_text(525, y + 7, anchor="w", text=text)


class AboutWindow:
    """Manages the About dialog."""

    def __init__(self, parent_root, fonts, scaling_factor=1.0):
        """Initialize the About window."""
        self.parent = parent_root
        self.fonts = fonts
        self.scaling_factor = scaling_factor

        # Create window
        self.root = Toplevel(parent_root)
        self.root.title("About Ollister")
        self.root.geometry(CFG["window"]["about_dialog_geometry"])
        self.root.resizable(False, False)
        self.root.transient(parent_root)

        self.ui = UIFactory(self.root, self.fonts)

        self._setup_ui()

    def _setup_ui(self):
        """Create the About dialog UI."""
        main_frame = self.ui.create_frame(self.root, padding="16")
        main_frame.pack(fill="both", expand=True)

        # App info section
        info_widgets = [
            ("Ollister v1.0", "title", (0, 8)),
            ("Speedy insights for local Ollama models.", None, None),
            ("Author: Coder Johan 开源 超", None, (8, 0)),
            ("GitHub:", None, (8, 0)),
        ]

        for text, font_key, pady in info_widgets:
            label = ttk.Label(main_frame, text=text)
            if font_key:
                label.config(font=self.fonts[font_key])
            if pady:
                label.pack(anchor="w", pady=pady)
            else:
                label.pack(anchor="w")

        # URL entry with copy functionality
        self.url = "https://github.com/kaiyuanchao/ollister"
        url_entry = ttk.Entry(main_frame, width=40)
        url_entry.insert(0, self.url)
        url_entry.config(state="readonly")
        url_entry.pack(anchor="w", pady=(0, 8))

        ttk.Button(main_frame, text="Copy URL", command=self._copy_url).pack(anchor="w", pady=(0, 8))
        ttk.Label(main_frame, text="(c) 2025 - MIT License.").pack(anchor="w", pady=(8, 0))

        # Add a separator
        ttk.Separator(main_frame, orient="horizontal").pack(fill="x", pady=10, padx=5)

        # System Information
        self._create_system_info(main_frame)

    def _copy_url(self):
        """Copy URL to clipboard."""
        self.parent.clipboard_clear()
        self.parent.clipboard_append(self.url)

    def _create_system_info(self, parent):
        """Create system information section."""
        info_frame = ttk.Frame(parent)
        info_frame.pack(anchor="w", pady=(5, 0))

        # Gather system info
        os_name = platform.system()
        os_release = platform.release()
        os_info = f"{os_name} {os_release}" if os_name and os_release else os_name or "N/A"
        py_ver = platform.python_version() or "N/A"

        try:
            scaling = f"{self.scaling_factor:.2f}x"
        except Exception:
            scaling = "N/A"

        # Interpreter detection
        def get_interpreter_info():
            implementation = platform.python_implementation()
            version = platform.python_version()
            if implementation == "PyPy":
                jit = getattr(sys, "pypy_translation_info", {}).get("translation.jit", False)
                if jit:
                    return "Running on: PyPy (JIT active) " + version, "#008800"
                else:
                    return "Running on: PyPy (JIT not active) " + version, "#008800"
            else:
                return f"Running on: {implementation} {version}", None

        interp_line, interp_color = get_interpreter_info()

        # Create system info labels
        system_labels = [
            (f"OS: {os_info}", None),
            (f"Python: {py_ver}", None),
            (interp_line, interp_color),
            (f"UI Scaling: {scaling}", None),
        ]

        for text, color in system_labels:
            label = ttk.Label(info_frame, text=text)
            if color:
                label.config(foreground=color)
            label.pack(anchor="w")

        # Padding and close button
        ttk.Frame(info_frame, height=10).pack()
        ttk.Button(info_frame, text="Close", command=self.root.destroy).pack(pady=5)


if __name__ == "__main__":
    root = Tk()
    app = App(root)
    if app and root.winfo_exists():
        root.mainloop()
