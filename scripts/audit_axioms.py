#!/usr/bin/env python3
"""Axiom audit for every Lean declaration cited by a ``proved`` or
``computer_certified`` ledger record.

Generates a temporary Lean file that imports the cited modules and runs
``#print axioms`` on every cited declaration, compiles it with
``lake env lean``, and fails if any declaration depends on an axiom outside
Lean's standard three (``propext``, ``Classical.choice``, ``Quot.sound``) —
in particular ``sorryAx`` and ``Lean.ofReduceBool`` (``native_decide``).

    python scripts/audit_axioms.py            # all papers
    python scripts/audit_axioms.py <paper>    # one paper
    python scripts/audit_axioms.py --keep     # keep the generated file
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "papers"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDITED = ("proved", "computer_certified")


def lake() -> str:
    for cand in (shutil.which("lake"),
                 str(Path.home() / ".elan" / "bin" / "lake")):
        if cand and Path(cand).exists():
            return cand
    return "lake"


def cited(paper: str) -> list[tuple[str, str]]:
    ledger = json.loads((PAPERS_DIR / paper / "statements.json").read_text("utf-8"))
    out: list[tuple[str, str]] = []
    for rec in ledger.values():
        if rec.get("status") not in AUDITED:
            continue
        for ref in rec.get("lean", []):
            path, _, decl = ref.partition(":")
            if decl:
                out.append((path.replace("\\", "/"), decl))
    return out


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    keep = "--keep" in sys.argv
    papers = args or sorted(p.parent.name for p in PAPERS_DIR.glob("*/paper.json"))
    refs = sorted({r for p in papers for r in cited(p)})
    if not refs:
        print("No proved/certified records cite Lean declarations; nothing to audit.")
        return 0
    modules = sorted({p[:-5].replace("/", ".") for p, _ in refs})
    decls = sorted({d for _, d in refs})
    src = "".join(f"import {m}\n" for m in modules)
    src += "\n" + "".join(f"#print axioms {d}\n" for d in decls)
    tmp = ROOT / "AxiomAudit.lean"
    tmp.write_text(src, encoding="utf-8")
    try:
        proc = subprocess.run([lake(), "env", "lean", str(tmp)], cwd=ROOT,
                              capture_output=True, text=True, encoding="utf-8")
    finally:
        if not keep:
            tmp.unlink(missing_ok=True)
    output = proc.stdout + proc.stderr
    bad: list[str] = []
    seen = 0
    for line in output.splitlines():
        m = re.match(r"'(.+?)' depends on axioms: \[(.*)\]", line.strip())
        if m:
            seen += 1
            axioms = {a.strip() for a in m.group(2).split(",") if a.strip()}
            extra = axioms - ALLOWED
            if extra:
                bad.append(f"{m.group(1)}: {sorted(extra)}")
        elif "does not depend on any axioms" in line:
            seen += 1
    if proc.returncode != 0:
        print(output[-4000:])
        print("Axiom audit FAILED: Lean reported errors (see above).")
        return 1
    if bad:
        print("Axiom audit FAILED: non-standard axioms found:")
        for b in bad:
            print("  -", b)
        return 1
    print(f"Axiom audit passed: {seen} declarations across {len(modules)} modules "
          f"use only {sorted(ALLOWED)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
