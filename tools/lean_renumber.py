#!/usr/bin/env python3
"""Renumber or move Lean problem folders.

Usage: tools/lean_renumber.py MAPPING.json [--apply]
MAPPING.json: {"OLD_ID": "tier/topic_folder/NEW_ID", ...} (topic may be "" for easy).
Moves each problem folder lean/<tier>/[<topic>/]<OLD_ID>_<name>/ (problem.lean, solution.lean,
guide.lean, cheatsheet.md), then rewrites every whole-word OLD_ID token in lean/**/*.lean,
lean/**/*.md (headers, namespaces, cross-references). Without --apply it only prints the plan.
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "lean"
mapping = json.loads(Path(sys.argv[1]).read_text())
apply = "--apply" in sys.argv

moves, ids = [], {}
for old, dest in mapping.items():
    tier, topic, new = dest.split("/")
    ids[old] = new
    src = [d for t in ("easy", "medium", "hard") for d in
           list((ROOT / t).glob(f"{old}_*/")) + list((ROOT / t).glob(f"*/{old}_*/")) if d.is_dir()]
    assert len(src) == 1, (old, src)
    name = src[0].name.replace(old, new, 1)
    moves.append((src[0], ROOT / tier / topic / name if topic else ROOT / tier / name))

tok = re.compile(r"(?<![A-Za-z0-9_])(" + "|".join(map(re.escape, sorted(ids, key=len, reverse=True))) + r")(?![0-9])")
for a, b in moves:
    print(f"{a.relative_to(ROOT)} -> {b.relative_to(ROOT)}")
if not apply:
    sys.exit(0)
for a, b in moves:
    b.parent.mkdir(parents=True, exist_ok=True)
    a.rename(b)
changed = 0
for f in list(ROOT.rglob("*.lean")) + list(ROOT.rglob("*.md")):
    if ".lake" in f.parts:
        continue
    s = f.read_text()
    t = tok.sub(lambda m: ids[m[1]], s)
    if t != s:
        f.write_text(t); changed += 1
print(f"rewrote ids in {changed} files")
