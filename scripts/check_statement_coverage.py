#!/usr/bin/env python3
"""Statement-coverage checker for the NCG formalization.

Parses every named statement environment (theorem / proposition / lemma /
corollary / definition) out of the manuscript ``.tex`` sources under ``manuscripts/`` and checks it against
the curated status map ``statements.json`` next to each manuscript:

* every manuscript statement must have a status record (no gaps);
* no stale records (entries whose label no longer exists in the manuscript);
* every Lean identifier referenced by a record must exist in ``NCG/``.

Statuses
--------
- ``proved``               : the statement's mathematical content is proved
                             sorry-free in Lean (notes record any explicitly
                             scoped hypotheses, e.g. Archimedean order);
- ``computer_certified``   : verified by a finite kernel-checked enumeration
                             (``decide``-style certificate);
- ``statement_encoded``    : the object/statement is faithfully formalized as
                             a Lean definition/structure (nothing to prove);
- ``conditional_interface``: not formalized (currently unused: zero
                             records carry this status);
- ``not_started``          : untriaged (kept at zero).

Usage
-----
    python scripts/check_statement_coverage.py          # check + summary
    python scripts/check_statement_coverage.py --init   # add missing records
                                                        # as conditional_interface
    python scripts/check_statement_coverage.py --list proved   # list a status
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANUSCRIPT = ROOT / "manuscripts" / "lorentzian_emergence" / "lorentzian_emergence.tex"
STATUS_FILE = ROOT / "manuscripts" / "lorentzian_emergence" / "statements.json"
LEAN_DIR = ROOT / "NCG"

ENVS = ("theorem", "proposition", "lemma", "corollary", "definition")
STATUSES = (
    "proved",
    "computer_certified",
    "statement_encoded",
    "conditional_interface",
    "not_started",
)

BEGIN_RE = re.compile(
    r"\\begin\{(" + "|".join(ENVS) + r")\}(?:\[([^\]]*)\])?"
)
LABEL_RE = re.compile(r"\s*\\label\{([^}]+)\}")


def slugify(title: str) -> str:
    slug = re.sub(r"\\[a-zA-Z@]+", "", title)
    slug = re.sub(r"[^a-zA-Z0-9]+", "-", slug).strip("-").lower()
    return slug or "untitled"


def parse_manuscript() -> list[dict]:
    text = MANUSCRIPT.read_text(encoding="utf-8")
    records = []
    seen_keys: set[str] = set()
    for m in BEGIN_RE.finditer(text):
        env, title = m.group(1), (m.group(2) or "").strip()
        # collect the labels immediately following \begin{env}[title]
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
        records.append(
            {"key": key, "env": env, "title": title, "labels": labels}
        )
    return records


def lean_identifiers() -> set[str]:
    decl_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+"
        r"([A-Za-z0-9_'.]+)",
        re.M,
    )
    names: set[str] = set()
    for path in LEAN_DIR.rglob("*.lean"):
        for m in decl_re.finditer(path.read_text(encoding="utf-8")):
            full = m.group(1)
            names.add(full)
            names.add(full.split(".")[-1])
    return names


def main() -> int:
    global MANUSCRIPT, STATUS_FILE
    args = sys.argv[1:]
    if "--notes" in args:
        # Track the upstream-program companion document instead of the
        # main manuscript
        # (renewal_emergence.tex <-> its statements.json).
        MANUSCRIPT = ROOT / "manuscripts" / "renewal_emergence" / "renewal_emergence.tex"
        STATUS_FILE = ROOT / "manuscripts" / "renewal_emergence" / "statements.json"
    records = parse_manuscript()
    status_map: dict[str, dict] = {}
    if STATUS_FILE.exists():
        status_map = json.loads(STATUS_FILE.read_text(encoding="utf-8"))

    if "--init" in args:
        added = 0
        for rec in records:
            if rec["key"] not in status_map:
                status_map[rec["key"]] = {
                    "env": rec["env"],
                    "title": rec["title"],
                    "status": "conditional_interface",
                    "lean": [],
                    "note": "",
                }
                added += 1
        ordered = {r["key"]: status_map[r["key"]] for r in records}
        STATUS_FILE.write_text(
            json.dumps(ordered, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        print(f"Initialized {STATUS_FILE.name}: {added} records added, "
              f"{len(ordered)} total.")
        return 0

    if "--list" in args:
        wanted = args[args.index("--list") + 1]
        for key, entry in status_map.items():
            if entry["status"] == wanted:
                lean = ", ".join(entry.get("lean", []))
                print(f"  {key}  [{entry['env']}]  {entry['title']}"
                      + (f"  ->  {lean}" if lean else ""))
        return 0

    errors: list[str] = []
    keys = {r["key"] for r in records}
    for rec in records:
        if rec["key"] not in status_map:
            errors.append(f"missing status record: {rec['key']} "
                          f"({rec['env']} \"{rec['title']}\")")
    for key, entry in status_map.items():
        if key not in keys:
            errors.append(f"stale status record (not in manuscript): {key}")
        if entry.get("status") not in STATUSES:
            errors.append(f"invalid status for {key}: {entry.get('status')}")

    names = lean_identifiers()
    for key, entry in status_map.items():
        if entry.get("status") in ("proved", "computer_certified",
                                   "statement_encoded"):
            if not entry.get("lean"):
                errors.append(f"{key}: status {entry['status']} requires at "
                              "least one Lean identifier")
            for ident in entry.get("lean", []):
                if ident.split(".")[-1] not in names:
                    errors.append(f"{key}: Lean identifier not found in NCG/: "
                                  f"{ident}")

    counts = Counter(e["status"] for e in status_map.values())
    for s in STATUSES:
        counts.setdefault(s, 0)
    summary = ", ".join(f"{s}={counts[s]}" for s in sorted(counts))

    if errors:
        print(f"Statement coverage FAILED ({len(records)} records): {summary}")
        for err in errors:
            print(f"  - {err}")
        return 1

    print(f"Statement coverage passed ({len(records)} records): {summary}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
