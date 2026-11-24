#!/usr/bin/env python3
"""Check each Lean problem folder's guide.lean and cheatsheet.md against Lean and the problem.

A Lean problem folder is lean/<tier>/[<topic>/]<ID>_<name>/ holding problem.lean, solution.lean,
guide.lean and cheatsheet.md. For every folder (or only the IDs given):

  * shape: all four files exist; problem.lean has a GUIDE block, no REFERENCE card, and a SKELETON
    comment before each spec theorem/lemma;
  * guide.lean compiles with no errors, warnings or `sorry`;
  * every inline code span containing `⊢` in a cheatsheet table row (cells such as
    `i j : Fin 2 ⊢ M i j = N i j`) matches one goal Lean reaches in guide.lean: the text after `⊢`
    equals that goal, and each hypothesis written before `⊢` (separated by `, `) is one of that
    goal's hypothesis lines; every non-blank line in a ```lean-goal block is a goal Lean reaches;
  * guide.lean uses none of the problem's BANNED names (same matching as ./check);
  * guide.lean copies no line of the problem's spec regions (no spoilers: the guide teaches on
    other objects).

States are read without changing guide.lean: a temporary copy gets `trace_state` before the first
tactic of every multi-line `:= by` proof and after each top-level tactic, and is compiled with
`lake env lean --json`. Those are the states the infoview shows.

    tools/guide_sync.py                 # every folder
    tools/guide_sync.py M126 E003       # only these IDs
    tools/guide_sync.py -j 8            # parallel compiles (default 4)
Exit status 1 on any problem. Stdlib only.
"""
import concurrent.futures as cf
import importlib.util
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
_spec = importlib.util.spec_from_file_location("fvcheck", ROOT / "tools" / "check.py")
check = importlib.util.module_from_spec(_spec)
sys.modules["fvcheck"] = check  # dataclasses look the module up while it loads
_spec.loader.exec_module(check)

GOAL_BLOCK = re.compile(r"^```lean-goal\n(.*?)^```", re.S | re.M)
CODE_SPAN = re.compile(r"`([^`]*⊢[^`]*)`")
DECL = re.compile(r"^(example|theorem|lemma)\b")
SPEC_THEOREM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)*(theorem|lemma)\s+\S+")
MIN_SPOILER_LEN = 30  # spec lines shorter than this (`| 0 => 0`, `end Foo`) are too generic to flag


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


def lean_json(src: str) -> tuple[list[dict], int, str]:
    tmpdir = LEAN / ".lake" / "fvcheck"
    tmpdir.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=tmpdir, delete=False) as f:
        f.write(src)
        tmp = Path(f.name)
    try:
        r = subprocess.run([check.lake(), "env", "lean", "--json", str(tmp)], cwd=LEAN,
                           capture_output=True, text=True, timeout=1800)
    finally:
        tmp.unlink()
    msgs = [json.loads(l) for l in r.stdout.splitlines() if l.startswith("{")]
    return msgs, r.returncode, r.stderr


def goals_of(msgs: list[dict]) -> list[tuple[set[str], str]]:
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
    return goals


def check_span(span: str, goals) -> bool:
    left, _, right = span.partition("⊢")
    want_hyps = [h.strip() for h in left.split(", ") if h.strip()]
    goal = right.strip()
    return any(g == goal and all(h in hs for h in want_hyps) for hs, g in goals)


def shape_issues(folder: Path) -> list[str]:
    issues = [f"missing {n}" for n in ("problem.lean", "solution.lean", "guide.lean", "cheatsheet.md")
              if not (folder / n).exists()]
    if issues:
        return issues
    src = (folder / "problem.lean").read_text()
    header = src.split("-/", 1)[0]
    if not re.search(r"^GUIDE\s*$", header, re.M):
        issues.append("problem.lean: no GUIDE block in the header comment")
    if re.search(r"^REFERENCE\s*$", header, re.M):
        issues.append("problem.lean: still has a REFERENCE card")
    lines = src.splitlines()
    for i, line in enumerate(lines):
        if not check.SPEC_BEGIN_RE.match(line):
            continue
        body = next((l for l in lines[i + 1:] if l.strip() and not l.strip().startswith("--")), "")
        if not SPEC_THEOREM.match(body):
            continue
        before = "\n".join(lines[max(0, i - 40):i])
        last_skel, last_spec = before.rfind("SKELETON"), before.rfind("END SPEC")
        if last_skel < 0 or last_skel < last_spec:
            issues.append(f"problem.lean line {i + 1}: no SKELETON comment before this spec theorem")
    return issues


def spoiler_issues(problem: str, guide: str) -> list[str]:
    norm = lambda s: re.sub(r"\s+", " ", s).strip()
    code = norm(check.strip_comments(guide, check.LANGS["lean"]))
    out = []
    for _, region in check.spec_regions(problem):
        for line in region.splitlines():
            n = norm(line)
            if len(n) >= MIN_SPOILER_LEN and n in code:
                out.append(f"guide.lean copies a spec line of problem.lean: {n}")
                continue
            # the same statement restated as `example …` or under another name
            m = re.match(r"(?:theorem|lemma|def|abbrev)\s+\S+\s+(.*?)\s*(?::=)?$", n)
            if m and len(m[1]) >= MIN_SPOILER_LEN - 10 and m[1] in code:
                out.append(f"guide.lean restates a spec declaration of problem.lean: {n}")
    return out


def check_folder(folder: Path, frozen: dict) -> list[str]:
    rel = folder.relative_to(ROOT)
    issues = shape_issues(folder)
    if any(i.startswith("missing ") for i in issues):
        return [f"{rel}: {i}" for i in issues]
    problem = (folder / "problem.lean").read_text()
    guide = (folder / "guide.lean").read_text()
    pid = re.match(r"([EMH]\d{2,3})_", folder.name)[1]
    banned = frozen.get(pid, {}).get("banned") or check.banned_names(problem)
    issues += [f"guide.lean {h}" for h in check.banned_hits(guide, check.LANGS["lean"], banned)]
    issues += spoiler_issues(problem, guide)
    if re.search(r"(?<![\w.])sorry(?![\w'])", check.strip_comments(guide, check.LANGS["lean"])):
        issues.append("guide.lean contains sorry")
    msgs, code, stderr = lean_json(instrument(guide))
    for m in msgs:
        if m["severity"] in ("error", "warning"):
            issues.append(f"guide.lean {m['severity']} (instrumented line {m['pos']['line']}): "
                          f"{m['data'].strip()[:400]}")
    if code != 0 and not any(m["severity"] == "error" for m in msgs):
        issues.append(f"guide.lean: lean failed: {stderr.strip()[:400]}")
    goals = goals_of(msgs)
    goal_texts = {g for _, g in goals}
    text = (folder / "cheatsheet.md").read_text()
    rows = [l for l in GOAL_BLOCK.sub("", text).splitlines() if l.lstrip().startswith("|")]
    spans = [s for row in rows for s in CODE_SPAN.findall(row)]
    block_lines = [l.strip() for b in GOAL_BLOCK.findall(text) for l in b.splitlines() if l.strip()]
    issues += [f"cheatsheet.md state not reached in guide.lean: {s}" for s in spans if not check_span(s, goals)]
    issues += [f"cheatsheet.md goal line not reached in guide.lean: {l}" for l in block_lines
               if l.lstrip("⊢ ").strip() not in goal_texts]
    if not issues:
        return [f"OK {rel}: {len(spans)} table states, {len(block_lines)} goal lines"]
    return [f"{rel}: {i}" for i in issues]


def folders(ids: set) -> list[Path]:
    out = []
    for p in check.problems(check.LANGS["lean"], solutions=False):
        if not ids or check.id_key(p.pid) in ids:
            out.append(p.path.parent)
    return out


def main() -> int:
    args = sys.argv[1:]
    jobs = 4
    if "-j" in args:
        k = args.index("-j")
        jobs = int(args[k + 1])
        del args[k:k + 2]
    ids = {check.id_key(a) for a in args}
    todo = folders(ids)
    if not todo:
        print("no matching problem folders")
        return 1
    frozen = check.load_specs(check.LANGS["lean"])
    bad = 0
    with cf.ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
        for lines in ex.map(lambda f: check_folder(f, frozen), todo):
            for l in lines:
                print(l)
            bad += not lines[0].startswith("OK ")
    if len(todo) > 1:
        print(f"\n{len(todo) - bad}/{len(todo)} folders OK")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
