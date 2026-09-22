#!/usr/bin/env python3
"""Layering check: the generic `NCG` library must never import `RenewalGeometry`,
and every `.lean` file must be reachable from its library's root module.

    python scripts/check_layering.py
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.']+)", re.M)


def modules(lib: str) -> dict[str, Path]:
    return {".".join(p.relative_to(ROOT).with_suffix("").parts): p
            for p in (ROOT / lib).rglob("*.lean")}


def main() -> int:
    errors: list[str] = []
    for lib in ("NCG", "RenewalGeometry"):
        mods = modules(lib)
        root = ROOT / f"{lib}.lean"
        registered = set(IMPORT_RE.findall(root.read_text("utf-8")))
        for name, path in sorted(mods.items()):
            text = path.read_text("utf-8")
            if name not in registered:
                errors.append(f"{path.relative_to(ROOT)}: not imported by {lib}.lean")
            for imp in IMPORT_RE.findall(text):
                if lib == "NCG" and imp.startswith("RenewalGeometry"):
                    errors.append(f"{path.relative_to(ROOT)}: NCG must not import {imp}")
                if imp.startswith(("NCG.", "RenewalGeometry.")):
                    target = ROOT / (imp.replace(".", "/") + ".lean")
                    if not target.exists():
                        errors.append(f"{path.relative_to(ROOT)}: import of missing module {imp}")
        for name in sorted(registered):
            if name.startswith(lib + ".") and name not in mods:
                errors.append(f"{lib}.lean imports missing module {name}")
    if errors:
        print("Layering check FAILED:")
        for e in errors:
            print("  -", e)
        return 1
    print("Layering check passed: NCG is independent of RenewalGeometry; "
          "all modules registered.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
