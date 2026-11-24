#!/usr/bin/env python3
"""Check that guide cheatsheets quote proof states the guide examples actually produce.

For every lean/guide/**/<ID>_*.md with a sibling <ID>_*.lean:
  * every inline code span containing `⊢` in a table row (cells such as `i j : Fin 2 ⊢ M i j = N i j`) must
    match one goal Lean reaches: the text after `⊢` equals that goal, and each hypothesis written
    before `⊢` (separated by `, `) is one of that goal's hypothesis lines;
  * every non-blank line inside a ```lean-goal block must be a goal line Lean reaches.

The guide .lean file holds plain examples. To learn the states, this script copies it to a temporary
file, inserts `trace_state` before the first tactic of every `:= by` proof and after each top-level
tactic, compiles the copy with `lake env lean --json`, and reads the printed goals. Those are the states
the infoview shows. The guide file itself is never changed. Any error in the copy fails the check.

    tools/guide_sync.py
Exit status 1 on any mismatch or compile error. Stdlib only.
"""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GUIDE = ROOT / "lean" / "guide"
GOAL_BLOCK = re.compile(r"^```lean-goal\n(.*?)^```", re.S | re.M)
CODE_SPAN = re.compile(r"`([^`]*⊢[^`]*)`")
DECL = re.compile(r"^(example|theorem|lemma)\b")


def indent(line: str) -> int:
    return len(line) - len(line.lstrip())


def instrument(src: str) -> str:
    """Insert `trace_state` around each top-level tactic of every multi-line `:= by` proof."""
    lines = src.split("\n")
    out, i = [], 0
    while i < len(lines):
        out.append(lines[i])
        if not DECL.match(lines[i]):
            i += 1
            continue
        # the statement may span lines; the proof starts after the line ending in `:= by`
        while i < len(lines) and not lines[i].rstrip().endswith(":= by") and lines[i].strip():
            i += 1
            if i < len(lines):
                out.append(lines[i])
        i += 1
        if i >= len(lines) or not lines[i].strip() or indent(lines[i]) == 0:
            continue  # one-line proof such as `:= by norm_num`, or no proof here
        base = indent(lines[i])
        pad = " " * base
        out.append(pad + "trace_state")
        while i < len(lines) and lines[i].strip() and indent(lines[i]) >= base:
            out.append(lines[i])
            nxt = lines[i + 1] if i + 1 < len(lines) else ""
            if not (nxt.strip() and indent(nxt) > base):  # end of this tactic (and its nested block)
                out.append(pad + "trace_state")
            i += 1
    return "\n".join(out)


def reached_goals(lean: Path) -> tuple[list[tuple[set[str], str]], list[str]]:
    """(hypothesis lines, goal) for every goal the instrumented copy prints, plus any errors."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(instrument(lean.read_text()))
        tmp = Path(f.name)
    try:
        r = subprocess.run(["lake", "env", "lean", "--json", str(tmp)], cwd=ROOT / "lean",
                           capture_output=True, text=True)
    finally:
        tmp.unlink()
    msgs = [json.loads(l) for l in r.stdout.splitlines() if l.startswith("{")]
    errors = [f"{m['pos']['line']}: {m['data']}" for m in msgs if m["severity"] == "error"]
    if r.returncode != 0 and not errors:
        errors.append(r.stderr.strip() or "lean failed")
    goals = []
    for m in msgs:
        if m["severity"] != "information":
            continue
        for g in re.split(r"\n\s*\n", m["data"].strip()):  # goals are separated by blank lines
            ls = [l.rstrip() for l in g.splitlines() if l.strip() and not l.startswith("case ")]
            k = next((j for j, l in enumerate(ls) if l.startswith("⊢")), None)
            if k is None:
                continue
            goal = " ".join([ls[k][1:].strip()] + [l.strip() for l in ls[k + 1:]])
            goals.append((set(ls[:k]), goal))
    return goals, errors


def check_span(span: str, goals) -> bool:
    left, _, right = span.partition("⊢")
    want_hyps = [h.strip() for h in left.split(", ") if h.strip()]
    goal = right.strip()
    return any(g == goal and all(h in hs for h in want_hyps) for hs, g in goals)


def main() -> int:
    failures = 0
    for md in sorted(GUIDE.rglob("*.md")):
        lean = md.with_suffix(".lean")
        if not lean.exists():
            continue  # shared sheets such as TACTIC_STATES.md
        rel = md.relative_to(ROOT)
        goals, errors = reached_goals(lean)
        for e in errors:
            print(f"{lean.relative_to(ROOT)}: error at {e}")
        failures += len(errors)
        goal_texts = {g for _, g in goals}
        text = md.read_text()
        table_rows = [l for l in GOAL_BLOCK.sub("", text).splitlines() if l.lstrip().startswith("|")]
        spans = [s for row in table_rows for s in CODE_SPAN.findall(row)]
        block_lines = [l.strip() for b in GOAL_BLOCK.findall(text) for l in b.splitlines() if l.strip()]
        bad = [s for s in spans if not check_span(s, goals)]
        bad += [l for l in block_lines if l.lstrip("⊢ ").strip() not in goal_texts]
        for s in bad:
            print(f"{rel}: not reached in {lean.name}: {s}")
        failures += len(bad)
        if not bad and not errors:
            print(f"{rel}: {len(spans)} table states and {len(block_lines)} goal lines, all reached in Lean")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
