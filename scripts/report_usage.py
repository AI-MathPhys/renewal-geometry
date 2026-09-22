#!/usr/bin/env python3
"""Which library modules do the papers actually use?

Import closure says which files must be *compiled*; this script asks the finer
question: which declarations are *used* (transitively, through the proof terms)
by the Lean declarations cited in the paper ledgers.  It generates a Lean
meta-program that walks `Expr.getUsedConstants` from every cited declaration,
staying inside the `NCG`/`RenewalGeometry` modules, and reports

* per paper: the modules and folders it depends on;
* library-wide: modules never used by any cited declaration, split into
  "structurally required" (imported by a used module) and "removable"
  (nothing used imports them).

Needs a completed `lake build`.

    python scripts/report_usage.py                 # markdown report on stdout
    python scripts/report_usage.py --json out.json # machine-readable
    python scripts/report_usage.py --keep          # keep UsageAudit.lean
"""
from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "papers"
LIBS = ("NCG", "RenewalGeometry")
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.']+)", re.M)

LEAN_PROGRAM = r'''
import Lean
open Lean Elab Command

/-- Module name of a constant, if it lives in one of our libraries. -/
def ourModule? (env : Environment) (c : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? c
  let m := env.header.moduleNames[idx.toNat]!
  let s := m.toString
  if s.startsWith "NCG." || s == "NCG" || s.startsWith "RenewalGeometry." || s == "RenewalGeometry"
  then some m else none

partial def collect (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | c :: rest, seen =>
    if seen.contains c then collect env rest seen else
    match env.find? c with
    | none => collect env rest seen
    | some ci =>
      let seen := seen.insert c
      match ourModule? env c with
      | none => collect env rest seen        -- Mathlib/core: do not descend
      | some _ =>
        let deps := ci.type.getUsedConstants ++ ((ci.value?.map Expr.getUsedConstants).getD #[])
        collect env (deps.toList ++ rest) seen

elab "#usage_roots " roots:str* : command => do
  let env ← getEnv
  for r in roots do
    let n := r.getString.toName
    if !env.contains n then
      IO.println s!"MISSING {n}"
    else
      let used := collect env [n] {}
      let mut mods : NameSet := {}
      for c in used.toList do
        if let some m := ourModule? env c then
          mods := mods.insert m
      for m in mods.toList do
        IO.println s!"DEP {n} {m}"
'''


def lake() -> str:
    for cand in (shutil.which("lake"), str(Path.home() / ".elan" / "bin" / "lake")):
        if cand and Path(cand).exists():
            return cand
    return "lake"


def all_modules() -> dict[str, list[str]]:
    """module -> list of imported modules (only our libraries)."""
    mods: dict[str, list[str]] = {}
    for lib in LIBS:
        for p in (ROOT / lib).rglob("*.lean"):
            name = ".".join(p.relative_to(ROOT).with_suffix("").parts)
            imps = [i for i in IMPORT_RE.findall(p.read_text("utf-8")) if i.startswith(LIBS)]
            mods[name] = imps
    return mods


def folder_of(module: str) -> str:
    parts = module.split(".")
    if len(parts) <= 2:
        return parts[0]
    if parts[1] == "Topology":
        return "/".join(parts[:3])
    return "/".join(parts[:2])


def main() -> int:
    keep = "--keep" in sys.argv
    json_out = None
    if "--json" in sys.argv:
        json_out = Path(sys.argv[sys.argv.index("--json") + 1])

    # ---- roots per paper
    roots_by_paper: dict[str, dict[str, str]] = {}   # paper -> decl -> module
    for pj in sorted(PAPERS_DIR.glob("*/paper.json")):
        paper = pj.parent.name
        ledger = json.loads((pj.parent / "statements.json").read_text("utf-8"))
        roots: dict[str, str] = {}
        for rec in ledger.values():
            for ref in rec.get("lean", []):
                path, _, decl = ref.partition(":")
                if decl:
                    roots[decl] = path[:-5].replace("/", ".")
        roots_by_paper[paper] = roots
    all_roots = {d: m for r in roots_by_paper.values() for d, m in r.items()}
    modules = all_modules()

    # ---- run Lean
    src = "".join(f"import {m}\n" for m in sorted(set(all_roots.values())))
    src += LEAN_PROGRAM + "\n#usage_roots " + " ".join(f'"{d}"' for d in sorted(all_roots)) + "\n"
    tmp = ROOT / "UsageAudit.lean"
    tmp.write_text(src, encoding="utf-8")
    try:
        proc = subprocess.run([lake(), "env", "lean", str(tmp)], cwd=ROOT,
                              capture_output=True, text=True, encoding="utf-8")
    finally:
        if not keep:
            tmp.unlink(missing_ok=True)
    if proc.returncode != 0:
        print(proc.stdout[-3000:], proc.stderr[-3000:])
        print("Lean failed; is the library built?")
        return 1
    deps: dict[str, set[str]] = defaultdict(set)
    missing: list[str] = []
    for line in proc.stdout.splitlines():
        if line.startswith("DEP "):
            _, decl, mod = line.split(" ", 2)
            deps[decl].add(mod)
        elif line.startswith("MISSING "):
            missing.append(line.split(" ", 1)[1])

    # ---- aggregate
    used_by_paper: dict[str, set[str]] = {}
    for paper, roots in roots_by_paper.items():
        s: set[str] = set()
        for d in roots:
            s |= deps.get(d, set())
        used_by_paper[paper] = s
    used_all = set().union(*used_by_paper.values()) if used_by_paper else set()
    # structural closure: modules imported (transitively) by used modules
    structural: set[str] = set()
    stack = list(used_all)
    while stack:
        m = stack.pop()
        for i in modules.get(m, []):
            if i not in structural and i not in used_all:
                structural.add(i)
                stack.append(i)
    never_used = set(modules) - used_all
    removable = never_used - structural
    root_modules = {m for m in modules if m in LIBS}  # NCG.lean / RenewalGeometry.lean roots
    removable -= root_modules

    def by_folder(mods: set[str]) -> dict[str, int]:
        out: dict[str, int] = defaultdict(int)
        for m in mods:
            out[folder_of(m)] += 1
        return dict(sorted(out.items(), key=lambda kv: -kv[1]))

    total_by_folder = by_folder(set(modules) - root_modules)

    if json_out:
        json_out.write_text(json.dumps({
            "used_by_paper": {p: sorted(s) for p, s in used_by_paper.items()},
            "used_all": sorted(used_all),
            "structural_only": sorted(structural),
            "removable": sorted(removable),
            "missing_roots": missing,
        }, indent=1), encoding="utf-8")

    print("# Library usage by the papers\n")
    print(f"Roots: {len(all_roots)} cited declarations"
          + (f" ({len(missing)} not found: {missing[:5]})" if missing else "") + ".\n")
    print("| Paper | Cited decls | Modules used | Folders used |")
    print("|---|---:|---:|---|")
    for paper, roots in roots_by_paper.items():
        f = by_folder(used_by_paper[paper])
        print(f"| {paper} | {len(roots)} | {len(used_by_paper[paper])} | "
              + ", ".join(f"{k} ({v})" for k, v in f.items()) + " |")
    print()
    print("| Folder | Modules | Used by a paper | Import-only | Unused & removable |")
    print("|---|---:|---:|---:|---:|")
    ub, sb, rb = by_folder(used_all), by_folder(structural), by_folder(removable)
    for folder, n in total_by_folder.items():
        print(f"| {folder} | {n} | {ub.get(folder, 0)} | {sb.get(folder, 0)} | {rb.get(folder, 0)} |")
    print(f"| **Total** | {sum(total_by_folder.values())} | {len(used_all)} | "
          f"{len(structural)} | {len(removable)} |\n")
    if removable:
        print("## Modules no cited declaration uses and no used module imports\n")
        for m in sorted(removable):
            print(f"- `{m}`")
    return 0


if __name__ == "__main__":
    sys.exit(main())
