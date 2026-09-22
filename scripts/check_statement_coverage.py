#!/usr/bin/env python3
"""Statement-coverage checker for the Renewal Geometry formalization.

Every paper under ``papers/<name>/`` carries a small ``paper.json`` manifest
(title, LaTeX source, extra theorem-like environments) and a curated ledger
``statements.json``.  This script parses every named statement environment
out of the LaTeX source and checks it against the ledger:

* every manuscript statement has a ledger record (no gaps);
* no stale records (labels that no longer exist in the manuscript);
* the ledger's ``env``/``title`` agree with the manuscript;
* every Lean reference is of the form ``<path>.lean:<declaration>`` and the
  declaration is really declared in that file.

Ledger record format
--------------------
    "thm:foo": {
      "env": "theorem",
      "title": "Short title as in the manuscript",
      "status": "proved",
      "lean": ["RenewalGeometry/Lorentz/Foo.lean:RenewalGeometry.foo_theorem"],
      "note": "Honest disclosure of any scoped hypothesis or gap."
    }

Statuses
--------
- ``proved``               : the mathematical content is proved sorry-free in
                             Lean (the note records any explicitly scoped
                             hypothesis);
- ``computer_certified``   : verified by a finite kernel-checked enumeration
                             (``decide``-style certificate);
- ``statement_encoded``    : the object or statement is faithfully formalized
                             as a Lean definition/structure but its proof
                             content (if any) is not machine-checked; also
                             used for declaration/bookkeeping environments
                             (assumptions, constructions) whose formal
                             counterparts are hypothesis arguments of the
                             proved theorems referencing them;
- ``conditional_interface``: open — no Lean counterpart yet;
- ``not_started``          : untriaged (kept at zero).

Usage
-----
    python scripts/check_statement_coverage.py                 # all papers
    python scripts/check_statement_coverage.py emergent_spacetime
    python scripts/check_statement_coverage.py emergent_spacetime --list proved
    python scripts/check_statement_coverage.py --summary       # markdown table
    python scripts/check_statement_coverage.py <paper> --init  # seed records
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "papers"
LEAN_DIRS = (ROOT / "NCG", ROOT / "RenewalGeometry")

ENVS = ("theorem", "proposition", "lemma", "corollary", "definition")

STATUSES = (
    "proved",
    "computer_certified",
    "statement_encoded",
    "conditional_interface",
    "not_started",
)

# Environments whose mathematical content must eventually be backed by Lean.
PROOF_ENVS = {
    "theorem", "proposition", "lemma", "corollary",
    "mastertheorem", "countertheorem", "conditionalresult",
}

# Environments that define an object: ``statement_encoded`` requires a Lean
# definition/structure reference (a definition with no Lean counterpart is
# ``conditional_interface``).
DEFINITION_ENVS = {"definition", "construction"}

# Every record that is not proved carries an estimate of how far the existing
# library is from proving it, plus a one-line plan.
DIFFICULTIES = ("easy", "medium", "hard")

BOOKKEEPING_NOTE = (
    "Non-theorem environment (declaration/bookkeeping); formal counterparts "
    "are the hypothesis arguments of the proved theorems referencing it."
)

LABEL_RE = re.compile(r"\s*\\label\{([^}]+)\}")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)"
    r"\s+((?:[A-Za-z0-9_'.]|[^\x00-\x7F])+)",
    re.M,
)
NAMESPACE_RE = re.compile(r"^\s*(namespace|end)\s+([A-Za-z0-9_.]+)?", re.M)


# --------------------------------------------------------------------------
# papers
# --------------------------------------------------------------------------

def paper_names() -> list[str]:
    return sorted(p.parent.name for p in PAPERS_DIR.glob("*/paper.json"))


def load_manifest(name: str) -> dict:
    return json.loads((PAPERS_DIR / name / "paper.json").read_text("utf-8"))


def paper_paths(name: str) -> tuple[Path, Path, dict]:
    manifest = load_manifest(name)
    folder = PAPERS_DIR / name
    return folder / manifest["tex"], folder / "statements.json", manifest


def begin_re(envs: tuple[str, ...]) -> "re.Pattern[str]":
    return re.compile(
        r"\\begin\{(" + "|".join(envs) + r")\}(?:\[([^\]]*)\])?"
    )


def strip_comments(text: str) -> str:
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def slugify(title: str) -> str:
    slug = re.sub(r"\\[a-zA-Z@]+", "", title)
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", slug).strip("-").lower()
    return slug or "untitled"


def parse_manuscript(tex_file: Path, envs: tuple[str, ...]) -> list[dict]:
    text = strip_comments(tex_file.read_text(encoding="utf-8"))
    records = []
    seen_keys: set[str] = set()
    for m in begin_re(envs).finditer(text):
        env, title = m.group(1), (m.group(2) or "").strip()
        labels = []
        pos = m.end()
        while True:
            lm = LABEL_RE.match(text, pos)
            if not lm:
                break
            labels.append(lm.group(1))
            pos = lm.end()
        key = labels[0] if labels else f"{env}:{slugify(title)}"
        base, k = key, 2
        while key in seen_keys:
            key, k = f"{base}--{k}", k + 1
        seen_keys.add(key)
        records.append({"key": key, "env": env, "title": title,
                        "labels": labels})
    return records


# --------------------------------------------------------------------------
# Lean declaration index: file -> set of declared names (full and short)
# --------------------------------------------------------------------------

def declarations_in(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    names: set[str] = set()
    stack: list[str] = []
    # walk namespaces and declarations in source order
    events = []
    for m in NAMESPACE_RE.finditer(text):
        events.append((m.start(), "ns", m.group(1), m.group(2)))
    for m in DECL_RE.finditer(text):
        events.append((m.start(), "decl", m.group(1), None))
    for _, kind, a, b in sorted(events):
        if kind == "ns":
            if a == "namespace" and b:
                stack.extend(b.split("."))
            elif a == "end" and b:
                parts = b.split(".")
                if stack[-len(parts):] == parts:
                    del stack[-len(parts):]
        elif a.startswith("_root_."):
            names.add(a[len("_root_."):])
            names.add(a.split(".")[-1])
        else:
            names.add(a)
            names.add(a.split(".")[-1])
            if stack:
                names.add(".".join(stack + [a]))
    return names


def lean_index() -> dict[str, set[str]]:
    index: dict[str, set[str]] = {}
    for d in LEAN_DIRS:
        if not d.exists():
            continue
        for path in d.rglob("*.lean"):
            rel = path.relative_to(ROOT).as_posix()
            index[rel] = declarations_in(path)
    return index


# --------------------------------------------------------------------------
# checking
# --------------------------------------------------------------------------

def check_paper(name: str, index: dict[str, set[str]]) -> int:
    tex_file, status_file, manifest = paper_paths(name)
    envs = ENVS + tuple(manifest.get("extra_envs", ()))
    records = parse_manuscript(tex_file, envs)
    status_map: dict[str, dict] = {}
    if status_file.exists():
        status_map = json.loads(status_file.read_text(encoding="utf-8"))

    errors: list[str] = []
    keys = {r["key"] for r in records}
    for rec in records:
        entry = status_map.get(rec["key"])
        if entry is None:
            errors.append(f"missing status record: {rec['key']} "
                          f"({rec['env']} \"{rec['title']}\")")
            continue
        if entry.get("env") != rec["env"]:
            errors.append(f"environment mismatch for {rec['key']}: "
                          f"manuscript={rec['env']}, ledger={entry.get('env')}")
        if entry.get("title") != rec["title"]:
            errors.append(f"title mismatch for {rec['key']}: "
                          f"manuscript={rec['title']!r}, "
                          f"ledger={entry.get('title')!r}")
    for key, entry in status_map.items():
        if key not in keys:
            errors.append(f"stale status record (not in manuscript): {key}")
        if entry.get("status") not in STATUSES:
            errors.append(f"invalid status for {key}: {entry.get('status')}")

    for key, entry in status_map.items():
        lean = entry.get("lean", [])
        status = entry.get("status")
        if not isinstance(lean, list):
            errors.append(f"{key}: lean evidence must be a list")
            continue
        if status in ("proved", "computer_certified") and not lean:
            errors.append(f"{key}: status {status} requires at least one "
                          "Lean reference")
        if (status == "statement_encoded"
                and entry.get("env") in PROOF_ENVS | DEFINITION_ENVS
                and not lean):
            errors.append(f"{key}: status statement_encoded on a "
                          f"{entry.get('env')} requires at least one Lean "
                          "reference")
        if status in ("statement_encoded", "conditional_interface", "not_started"):
            diff = entry.get("difficulty")
            if diff is not None and diff not in DIFFICULTIES:
                errors.append(f"{key}: invalid difficulty {diff!r} "
                              f"(expected one of {DIFFICULTIES})")
            if "--require-difficulty" in sys.argv and diff is None \
                    and entry.get("env") not in ("assumption",):
                errors.append(f"{key}: non-proved record without a difficulty estimate")
        for ident in lean:
            module, sep, decl = ident.partition(":")
            if not sep or not module.endswith(".lean") or not decl:
                errors.append(f"{key}: Lean reference must be "
                              f"'<path>.lean:<declaration>', got {ident!r}")
                continue
            module = module.replace("\\", "/")
            if module not in index:
                errors.append(f"{key}: Lean module not found: {module}")
                continue
            names = index[module]
            if decl not in names and decl.split(".")[-1] not in names:
                errors.append(f"{key}: declaration {decl} not found in "
                              f"{module}")

    counts = Counter(e["status"] for e in status_map.values())
    for s in STATUSES:
        counts.setdefault(s, 0)
    summary = ", ".join(f"{s}={counts[s]}" for s in STATUSES)

    if errors:
        print(f"Statement coverage FAILED for {name} "
              f"({len(records)} statements): {summary}")
        for err in errors:
            print(f"  - {err}")
        return 1
    print(f"Statement coverage passed for {name} "
          f"({len(records)} statements): {summary}")
    return 0


def init_paper(name: str) -> int:
    tex_file, status_file, manifest = paper_paths(name)
    envs = ENVS + tuple(manifest.get("extra_envs", ()))
    records = parse_manuscript(tex_file, envs)
    status_map: dict[str, dict] = {}
    if status_file.exists():
        status_map = json.loads(status_file.read_text(encoding="utf-8"))
    added = 0
    for rec in records:
        if rec["key"] not in status_map:
            proof_bearing = rec["env"] in PROOF_ENVS | DEFINITION_ENVS
            status_map[rec["key"]] = {
                "env": rec["env"],
                "title": rec["title"],
                "status": ("conditional_interface" if proof_bearing
                           else "statement_encoded"),
                "lean": [],
                "note": "" if proof_bearing else BOOKKEEPING_NOTE,
            }
            added += 1
    ordered = {r["key"]: status_map[r["key"]] for r in records}
    status_file.write_text(
        json.dumps(ordered, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8", newline="\n",
    )
    print(f"Initialized {name}/statements.json: {added} records added, "
          f"{len(ordered)} total.")
    return 0


def list_paper(name: str, wanted: str) -> int:
    _, status_file, _ = paper_paths(name)
    status_map: dict[str, dict] = {}
    if status_file.exists():
        status_map = json.loads(status_file.read_text(encoding="utf-8"))
    for key, entry in status_map.items():
        if entry["status"] == wanted:
            lean = ", ".join(entry.get("lean", []))
            print(f"  {key}  [{entry['env']}]  {entry['title']}"
                  + (f"  ->  {lean}" if lean else ""))
    return 0


def summary_table(names: list[str]) -> int:
    print("| Paper | Statements | Proved | Encoded | Open (partial Lean) | Open (none) | "
          "Easy | Medium | Hard |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    tot = Counter()
    for name in names:
        _, status_file, manifest = paper_paths(name)
        if not status_file.exists():
            continue
        status_map = json.loads(status_file.read_text(encoding="utf-8"))
        c = Counter(e["status"] for e in status_map.values())
        partial = sum(1 for e in status_map.values()
                      if e["status"] == "conditional_interface" and e.get("lean"))
        none = c["conditional_interface"] + c["not_started"] - partial
        d = Counter(e.get("difficulty") for e in status_map.values()
                    if e["status"] not in ("proved", "computer_certified"))
        row = {"n": len(status_map), "proved": c["proved"] + c["computer_certified"],
               "enc": c["statement_encoded"], "partial": partial, "none": none,
               "easy": d["easy"], "medium": d["medium"], "hard": d["hard"]}
        tot.update(row)
        print(f"| {manifest['short']} | {row['n']} | {row['proved']} | {row['enc']} | "
              f"{row['partial']} | {row['none']} | {row['easy']} | {row['medium']} | "
              f"{row['hard']} |")
    print(f"| **Total** | **{tot['n']}** | **{tot['proved']}** | **{tot['enc']}** | "
          f"**{tot['partial']}** | **{tot['none']}** | **{tot['easy']}** | "
          f"**{tot['medium']}** | **{tot['hard']}** |")
    return 0


def main() -> int:
    args = sys.argv[1:]
    positional: list[str] = []
    skip_next = False
    for a in args:
        if skip_next:
            skip_next = False
            continue
        if a == "--list":
            skip_next = True
            continue
        if a.startswith("--"):
            continue
        positional.append(a)
    known = paper_names()
    unknown = [a for a in positional if a not in known]
    if unknown:
        print(f"Unknown paper(s): {', '.join(unknown)}. "
              f"Expected one of: {', '.join(known)}.")
        return 2
    targets = positional or known

    if "--init" in args:
        return max(init_paper(name) for name in targets)
    if "--list" in args:
        wanted = args[args.index("--list") + 1]
        rc = 0
        for name in targets:
            if len(targets) > 1:
                print(f"== {name} ==")
            rc = max(rc, list_paper(name, wanted))
        return rc
    if "--summary" in args:
        return summary_table(targets)

    index = lean_index()
    return max(check_paper(name, index) for name in targets)


if __name__ == "__main__":
    sys.exit(main())
