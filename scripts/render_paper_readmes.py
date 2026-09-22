#!/usr/bin/env python3
"""Regenerate ``papers/<name>/README.md`` from ``paper.json`` + ``statements.json``.

The README is derived data: never edit it by hand, edit the ledger and rerun

    python scripts/render_paper_readmes.py
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "papers"

STATUS_LABEL = {
    "proved": "Proved",
    "computer_certified": "Computer-certified",
    "statement_encoded": "Statement encoded",
    "conditional_interface": "Open",
}


def md_escape(s: str) -> str:
    return s.replace("|", "\\|").replace("\n", " ")


def lean_links(refs: list[str]) -> str:
    out = []
    for r in refs:
        path, _, decl = r.partition(":")
        out.append(f"[`{decl}`](../../{path})")
    return "<br>".join(out)


def render(name: str) -> str:
    folder = PAPERS_DIR / name
    manifest = json.loads((folder / "paper.json").read_text("utf-8"))
    ledger = json.loads((folder / "statements.json").read_text("utf-8"))
    counts = Counter(r["status"] for r in ledger.values())
    partial = [(k, r) for k, r in ledger.items()
               if r["status"] == "conditional_interface" and r["lean"]]
    open_only = [(k, r) for k, r in ledger.items()
                 if r["status"] == "conditional_interface" and not r["lean"]]
    proved = [(k, r) for k, r in ledger.items()
              if r["status"] in ("proved", "computer_certified")]
    encoded = [(k, r) for k, r in ledger.items() if r["status"] == "statement_encoded"]

    lines: list[str] = []
    lines.append(f"# {manifest['title']}\n")
    lines.append(f"Source: [`{manifest['tex']}`]({manifest['tex']}) · "
                 f"PDF: [`{manifest['pdf']}`]({manifest['pdf']}) · "
                 f"Ledger: [`statements.json`](statements.json)\n")
    lines.append("This file is generated from the ledger by "
                 "`scripts/render_paper_readmes.py`; edit the ledger, not this file.\n")
    lines.append("## Verification summary\n")
    lines.append("| Status | Count | Meaning |")
    lines.append("|---|---:|---|")
    lines.append(f"| Proved | {counts['proved'] + counts['computer_certified']} | "
                 "the statement's content is proved in Lean, sorry-free, standard axioms only "
                 "(scoped hypotheses disclosed in the note) |")
    lines.append(f"| Statement encoded | {counts['statement_encoded']} | "
                 "the object/statement is faithfully defined in Lean; no proof content claimed |")
    lines.append(f"| Open, with partial Lean | {len(partial)} | "
                 "a special case, one direction, or a finite model is proved; the note says what is missing |")
    lines.append(f"| Open, no Lean counterpart | {len(open_only)} | "
                 "nothing in the library formalizes this statement yet |")
    lines.append(f"| **Total tracked statements** | **{len(ledger)}** | "
                 "every theorem/proposition/lemma/corollary/definition environment of the paper |\n")
    lines.append("Every cited declaration is checked to exist by "
                 "`scripts/check_statement_coverage.py` and audited for axioms by "
                 "`scripts/audit_axioms.py` (CI).\n")

    unproved = [(k, r) for k, r in ledger.items()
                if r["status"] not in ("proved", "computer_certified")]
    diff_counts = Counter(r.get("difficulty", "unrated") for _, r in unproved)
    if unproved:
        lines.append("## How far is the library from the rest?\n")
        lines.append("Every unproved record carries an estimate of the effort needed with the "
                     "existing machinery: **easy** (≤ 1 day: assembly of existing lemmas or a "
                     "direct definition), **medium** (days: new lemmas inside the existing "
                     "finite/algebraic framework), **hard** (research or infrastructure level: "
                     "function-space analysis, unbounded operators, continuum PDE, or the "
                     "statement needs reformulation).\n")
        lines.append("| Easy | Medium | Hard | Unrated |")
        lines.append("|---:|---:|---:|---:|")
        lines.append(f"| {diff_counts['easy']} | {diff_counts['medium']} | "
                     f"{diff_counts['hard']} | {diff_counts['unrated']} |\n")

    def table(title: str, rows: list[tuple[str, dict]], with_note: bool,
              with_plan: bool = False) -> None:
        if not rows:
            return
        lines.append(f"## {title} ({len(rows)})\n")
        hdr = "| Label | Env | Title | Lean |" + (" Note |" if with_note else "") \
            + (" Difficulty | What is missing |" if with_plan else "")
        lines.append(hdr)
        lines.append("|---|---|---|---|" + ("---|" if with_note else "")
                     + ("---|---|" if with_plan else ""))
        for k, r in rows:
            row = (f"| `{md_escape(k)}` | {r['env']} | {md_escape(r['title']) or '—'} | "
                   f"{lean_links(r['lean'])} |")
            if with_note:
                row += f" {md_escape(r.get('note', ''))} |"
            if with_plan:
                row += (f" {r.get('difficulty', '—')} | "
                        f"{md_escape(r.get('plan', ''))} |")
            lines.append(row)
        lines.append("")

    table("Proved statements", proved, with_note=True)
    table("Encoded definitions and statements", encoded, with_note=True, with_plan=True)
    table("Open statements with partial Lean support", partial, with_note=True, with_plan=True)
    if open_only:
        lines.append(f"## Open statements without a Lean counterpart ({len(open_only)})\n")
        lines.append("| Label | Env | Title | Difficulty | What is missing |")
        lines.append("|---|---|---|---|---|")
        for k, r in open_only:
            lines.append(f"| `{md_escape(k)}` | {r['env']} | {md_escape(r['title']) or '—'} | "
                         f"{r.get('difficulty', '—')} | {md_escape(r.get('plan', ''))} |")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    names = sorted(p.parent.name for p in PAPERS_DIR.glob("*/paper.json"))
    for name in names:
        (PAPERS_DIR / name / "README.md").write_text(render(name), encoding="utf-8",
                                                     newline="\n")
        print(f"rendered papers/{name}/README.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
