#!/usr/bin/env python3
"""
Runtime ML-backend detection for neural/ — the code-side mirror of
setup.sh's install-time choice (Apple Silicon → mlx, CUDA host → torch).

Whatever `setup.sh`/`uv sync --extra …` installed, this picks it up so the
neural models don't hard-code one backend.  Honors `$ML_BACKEND`
(mlx|torch) as an override.

    from backend import detect_backend
    bk = detect_backend()        # "mlx" or "torch"
"""
from __future__ import annotations

import importlib.util
import os


def _installed(mod: str) -> bool:
    return importlib.util.find_spec(mod) is not None


def detect_backend(prefer: str | None = None) -> str:
    """Return the available ML backend: "mlx" or "torch".

    Order: explicit `prefer` arg, then `$ML_BACKEND`, then platform
    preference (mlx before torch), restricted to what's actually
    importable.  Raises if neither is installed."""
    pref = prefer or os.environ.get("ML_BACKEND")
    order: list[str] = []
    if pref and pref not in ("auto", "none"):
        order.append(pref)
    order += ["mlx", "torch"]
    for name in dict.fromkeys(order):          # dedup, preserve order
        if name == "mlx" and _installed("mlx.core"):
            return "mlx"
        if name == "torch" and _installed("torch"):
            return "torch"
    raise RuntimeError(
        "no ML backend installed — run ./setup.sh (auto-selects), or "
        "`uv sync --extra mlx` (Apple Silicon) / `--extra torch` (CUDA).")


if __name__ == "__main__":
    try:
        print(detect_backend())
    except RuntimeError as e:
        import sys
        print(f"none ({e})", file=sys.stderr)
        sys.exit(1)
