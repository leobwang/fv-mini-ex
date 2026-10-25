#!/usr/bin/env python3
"""fv-mini-ex checker (stdlib only; runs on Linux and macOS).

Learner use:
  ./check                       check every problem in every language
  ./check dafny                 check every Dafny problem
  ./check lean E07 M12          check specific problems
  ./check -v verus E03          also print the verifier output

Author use:
  ./check --freeze [lang]       record spec hashes of the stubs in <lang>/specs.json
  ./check --stubs [lang] [ID]   stubs: header parses, spec frozen, well-formed, NOT already passing
  ./check --solutions [lang]    solutions: spec identical to stub, passes at the strict limit
  ./check --index               regenerate <lang>/INDEX.md from the problem headers

A problem PASSES when the verifier accepts the file, nothing forbidden appears
in the code, and every BEGIN SPEC ... END SPEC region is byte-identical
(modulo trailing whitespace) to the frozen stub.
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TIERS = ("easy", "medium", "hard")

# Resource limits. The learner limit is what ./check uses; reference solutions
# must pass at the strict limit (half), leaving headroom for solver variance
# across platforms. Both are deterministic counters, not wall-clock timeouts.
DAFNY_RLIMIT = {"learner": 10_000_000, "strict": 5_000_000}
VERUS_RLIMIT = {"learner": 10, "strict": 5}
LEAN_ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

HEADER_RE = re.compile(
    r"^\s*(?:/-!?|--|//|/\*!?)\s*([EMH]\d{2})\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.*?)\s*(?:-/|\*/)?\s*$"
)
# A marker is a line holding only the marker in a line comment, so prose that
# mentions "BEGIN SPEC" (cards, hints) is not mistaken for one.
SPEC_BEGIN_RE = re.compile(r"^\s*(?:--|//)\s*BEGIN SPEC\s*$")
SPEC_END_RE = re.compile(r"^\s*(?:--|//)\s*END SPEC\s*$")


@dataclass
class Lang:
    name: str
    ext: str
    line_comment: str
    block_open: str
    block_close: str
    nested_blocks: bool
    forbidden: list[tuple[str, str]] = field(default_factory=list)  # (regex, reason)


LANGS = {
    "lean": Lang(
        "lean", ".lean", "--", "/-", "-/", True,
        [
            (r"\baxiom\b", "axiom declaration"),
            (r"\bnative_decide\b", "native_decide (trusts the compiler)"),
            (r"\bimplemented_by\b", "implemented_by"),
            (r"@\[\s*extern\b", "extern"),
            (r"\bunsafe\b", "unsafe"),
            (r"debug\.skipKernelTC", "skipKernelTC"),
        ],
    ),
    "dafny": Lang(
        "dafny", ".dfy", "//", "/*", "*/", True,
        [
            (r"\bassume\b", "assume"),
            (r"\bexpect\b", "expect (the verifier assumes it)"),
            (r"\{:\s*axiom\b", "{:axiom}"),
            (r"\{:\s*extern\b", "{:extern}"),
            (r"\{:\s*verify\s+false", "{:verify false}"),
            (r"\{:\s*(only|focus)\b", "{:only}/{:focus}"),
        ],
    ),
    "verus": Lang(
        "verus", ".rs", "//", "/*", "*/", True,
        [
            (r"\bassume\s*\(", "assume"),
            (r"\badmit\s*\(", "admit"),
            (r"verifier\s*::\s*external", "verifier::external*"),
            (r"verifier\s*\(\s*external", "verifier(external*)"),
            (r"assume_specification", "assume_specification"),
            (r"#\s*!?\[\s*cfg", "#[cfg]"),
            (r"exec_allows_no_decreases_clause", "exec_allows_no_decreases_clause"),
            (r"\bunsafe\b", "unsafe"),
        ],
    ),
}


# ---------------------------------------------------------------- toolchain


def tool(name: str) -> str:
    env = {"dafny": "FV_DAFNY", "verus": "FV_VERUS"}[name]
    if os.environ.get(env):
        return os.environ[env]
    p = ROOT / ".toolchain" / name / name
    if p.exists():
        return str(p)
    found = shutil.which(name)
    if found:
        return found
    sys.exit(f"error: {name} not found. Run tools/setup.sh, or set {env}=/path/to/{name}.")


def lake() -> str:
    found = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if not Path(found).exists():
        sys.exit("error: lake not found. Install elan: https://github.com/leanprover/elan")
    return found


def run(cmd: list[str], cwd: Path | None = None, timeout: int = 1800) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           text=True, timeout=timeout)
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired as e:
        return 124, (e.stdout or "") + f"\n[timed out after {timeout}s]"


# ---------------------------------------------------------------- source scanning


def strip_comments(src: str, lang: Lang) -> str:
    """Blank out comments (keeping newlines, so line numbers survive) and string bodies."""
    out, i, n, depth = [], 0, len(src), 0
    lc, bo, bc = lang.line_comment, lang.block_open, lang.block_close
    while i < n:
        if depth:
            if src.startswith(bc, i):
                depth -= 1; i += len(bc); continue
            if lang.nested_blocks and src.startswith(bo, i):
                depth += 1; i += len(bo); continue
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith(bo, i):
            depth = 1; i += len(bo); continue
        if src.startswith(lc, i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""'); out.extend("\n" for c in src[i:j] if c == "\n"); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def spec_regions(src: str) -> list[tuple[int, str]]:
    """[(start line, normalized text)] for each BEGIN SPEC ... END SPEC region."""
    regions, cur, start = [], None, 0
    for ln, line in enumerate(src.splitlines(), 1):
        if SPEC_BEGIN_RE.match(line):
            if cur is not None:
                raise ValueError(f"line {ln}: nested BEGIN SPEC")
            cur, start = [], ln
        elif SPEC_END_RE.match(line):
            if cur is None:
                raise ValueError(f"line {ln}: END SPEC without BEGIN SPEC")
            regions.append((start, "\n".join(l.rstrip() for l in cur).strip("\n")))
            cur = None
        elif cur is not None:
            cur.append(line)
    if cur is not None:
        raise ValueError(f"line {start}: BEGIN SPEC without END SPEC")
    return regions


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()[:16]


def parse_header(src: str) -> dict | None:
    for line in src.splitlines():
        if line.strip():
            m = HEADER_RE.match(line)
            if not m:
                return None
            return {"id": m[1], "title": m[2], "time": m[3], "tags": m[4]}
    return None


# ---------------------------------------------------------------- problems


@dataclass
class Problem:
    lang: Lang
    pid: str
    tier: str
    path: Path

    @property
    def rel(self) -> str:
        return str(self.path.relative_to(ROOT))


def problems(lang: Lang, solutions: bool) -> list[Problem]:
    base = ROOT / lang.name / ("solutions" if solutions else "")
    out = []
    for tier in TIERS:
        d = base / tier
        if not d.is_dir():
            continue
        for p in sorted(d.glob(f"*{lang.ext}")):
            m = re.match(r"([EMH]\d{2})_", p.name)
            if m:
                out.append(Problem(lang, m[1], tier, p))
    return out


def load_specs(lang: Lang) -> dict:
    p = ROOT / lang.name / "specs.json"
    return json.loads(p.read_text()) if p.exists() else {}


def forbidden_hits(src: str, lang: Lang) -> list[str]:
    code = strip_comments(src, lang)
    hits = []
    for rx, why in lang.forbidden:
        for m in re.finditer(rx, code):
            ln = code.count("\n", 0, m.start()) + 1
            hits.append(f"line {ln}: {why}")
    return hits


BANNED_RE = re.compile(r"^\s*(?:--|//)?\s*BANNED:\s*(.+?)\s*$", re.M)


def banned_names(src: str) -> list[str]:
    """Library names a problem forbids (declared on a `BANNED: a, b` line of the card)."""
    return [n.strip() for m in BANNED_RE.finditer(src) for n in m[1].split(",") if n.strip()]


def banned_hits(src: str, lang: Lang, banned: list[str]) -> list[str]:
    """Match on the last name component, so `open Nat` + `foo` is caught like `Nat.foo`.
    Spec regions are skipped: the frozen statement may itself use the banned name."""
    code = strip_comments(blank_spec_regions(src), lang)
    hits = []
    for name in banned:
        last = name.rsplit(".", 1)[-1]
        for m in re.finditer(rf"(?<![\w']){re.escape(last)}(?![\w'])", code):
            hits.append(f"line {code.count(chr(10), 0, m.start()) + 1}: banned for this problem: {name}")
    return hits


def blank_spec_regions(src: str) -> str:
    out, inside = [], False
    for line in src.split("\n"):
        if SPEC_BEGIN_RE.match(line):
            inside = True
        elif SPEC_END_RE.match(line):
            inside = False
        out.append("" if inside else line)
    return "\n".join(out)


def spec_problems(src: str, pid: str, frozen: dict) -> list[str]:
    if pid not in frozen:
        return [f"no frozen spec for {pid} (author: run ./check --freeze)"]
    try:
        regs = spec_regions(src)
    except ValueError as e:
        return [f"spec markers: {e}"]
    want = frozen[pid]["spec"]
    if len(regs) != len(want):
        return [f"expected {len(want)} BEGIN/END SPEC regions, found {len(regs)}"]
    return [f"spec region at line {ln} was modified" for (ln, txt), h in zip(regs, want) if sha(txt) != h]


# ---------------------------------------------------------------- verifiers


def lean_decl_names(src: str) -> list[str]:
    """Fully qualified names of the declarations inside spec regions."""
    names, stack, in_spec = [], [], False
    decl = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial)\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[]+)"
    )
    for line in src.splitlines():
        if SPEC_BEGIN_RE.match(line):
            in_spec = True; continue
        if SPEC_END_RE.match(line):
            in_spec = False; continue
        s = line.strip()
        if m := re.match(r"namespace\s+(\S+)", s):
            stack.append(m[1])
        elif re.match(r"section\b", s):
            stack.append(None)
        elif re.match(r"end\b", s) and stack and not in_spec:
            stack.pop()
        elif in_spec and (m := decl.match(line)):
            prefix = ".".join(x for x in stack if x)
            names.append(f"{prefix}.{m[1]}" if prefix else m[1])
    return names


def verify_lean(p: Problem, mode: str) -> tuple[str, str]:
    src = p.path.read_text()
    names = lean_decl_names(src)
    tmpdir = ROOT / "lean" / ".lake" / "fvcheck"
    tmpdir.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=tmpdir, delete=False) as f:
        f.write(src + "\n\n" + "".join(f"#print axioms {n}\n" for n in names))
        tmp = f.name
    try:
        code, out = run([lake(), "env", "lean", tmp], cwd=ROOT / "lean")
    finally:
        os.unlink(tmp)
    out = out.replace(tmp, p.rel)
    if code != 0 or re.search(r"(^|\n)\S*:\d+:\d+: error", out):
        return "FAIL", out
    used = {}
    for m in re.finditer(r"'(\S+)' depends on axioms: \[(.*?)\]", out, re.S):
        used[m[1]] = {a.strip() for a in m[2].split(",") if a.strip()}
    for m in re.finditer(r"'(\S+)' does not depend on any axioms", out):
        used[m[1]] = set()
    missing = [n for n in names if n not in used]
    if missing:
        return "FAIL", out + f"\n[checker] could not read axioms for: {missing}"
    holes = [n for n, ax in used.items() if "sorryAx" in ax]
    bad = {n: ax - LEAN_ALLOWED_AXIOMS - {"sorryAx"} for n, ax in used.items()}
    bad = {n: ax for n, ax in bad.items() if ax}
    if bad:
        return "FAIL", out + f"\n[checker] non-standard axioms: {bad}"
    if holes:
        done = len(names) - len(holes)
        return "TODO", out + f"\n[checker] {done}/{len(names)} spec declarations sorry-free; still open: {holes}"
    return "PASS", out


def verify_dafny(p: Problem, mode: str) -> tuple[str, str]:
    cmd = [tool("dafny"), "verify", "--resource-limit", str(DAFNY_RLIMIT[mode]), "--cores", "2", p.rel]
    code, out = run(cmd, cwd=ROOT)
    if code == 0:
        return "PASS", out
    if "verified" in out and "error" in out and "resolution/type errors" not in out:
        return "TODO", out
    return "FAIL", out


def verify_verus(p: Problem, mode: str) -> tuple[str, str]:
    cmd = [tool("verus"), "--crate-type=lib", "--no-cheating", "--rlimit", str(VERUS_RLIMIT[mode]),
           "--num-threads", "2", p.rel]
    code, out = run(cmd, cwd=ROOT)
    m = re.search(r"verification results::\s*(\d+) verified,\s*(\d+) errors", out)
    if code == 0 and m and int(m[1]) > 0 and int(m[2]) == 0:
        return "PASS", out
    if m:
        return "TODO", out
    return "FAIL", out


VERIFY = {"lean": verify_lean, "dafny": verify_dafny, "verus": verify_verus}


def wellformed(p: Problem) -> tuple[bool, str]:
    """Stub must type-check (holes allowed)."""
    if p.lang.name == "lean":
        st, out = verify_lean(p, "learner")
        return st in ("TODO", "PASS"), out
    if p.lang.name == "dafny":
        code, out = run([tool("dafny"), "resolve", p.rel], cwd=ROOT)
        return code == 0, out
    code, out = run([tool("verus"), "--crate-type=lib", "--no-verify", p.rel], cwd=ROOT)
    return code == 0, out


# ---------------------------------------------------------------- commands


def check_one(p: Problem, mode: str, frozen: dict) -> tuple[str, list[str], str]:
    src = p.path.read_text()
    issues = [f"forbidden: {h}" for h in forbidden_hits(src, p.lang)]
    issues += spec_problems(src, p.pid, frozen)
    issues += banned_hits(src, p.lang, frozen.get(p.pid, {}).get("banned", []))
    status, out = VERIFY[p.lang.name](p, mode)
    if issues:
        status = "FAIL"
    return status, issues, out


def check_stub(p: Problem, frozen: dict) -> tuple[str, list[str], str]:
    src = p.path.read_text()
    issues = []
    h = parse_header(src)
    if not h:
        issues.append("first line is not a valid header `ID | title | time | tags`")
    elif h["id"] != p.pid:
        issues.append(f"header id {h['id']} != filename id {p.pid}")
    issues += spec_problems(src, p.pid, frozen)
    if "HINTS" not in src:
        issues.append("no HINTS section")
    ok, out = wellformed(p)
    if not ok:
        issues.append("stub does not type-check")
    else:
        st, out2 = VERIFY[p.lang.name](p, "learner")
        if st == "PASS":
            issues.append("stub already passes (nothing to do)")
        out += "\n" + out2
    return ("PASS" if not issues else "FAIL"), issues, out


def freeze(langs: list[Lang]) -> None:
    for lang in langs:
        specs = {}
        for p in problems(lang, solutions=False):
            src = p.path.read_text()
            try:
                regs = spec_regions(src)
            except ValueError as e:
                sys.exit(f"error: {p.rel}: {e}")
            if not regs:
                print(f"warning: {p.rel} has no spec regions")
            specs[p.pid] = {"spec": [sha(t) for _, t in regs], "banned": banned_names(src)}
        out = ROOT / lang.name / "specs.json"
        out.write_text(json.dumps(specs, indent=1, sort_keys=True) + "\n")
        print(f"froze {len(specs)} specs -> {out.relative_to(ROOT)}")


def index(langs: list[Lang]) -> None:
    for lang in langs:
        rows = {t: [] for t in TIERS}
        for p in problems(lang, solutions=False):
            h = parse_header(p.path.read_text()) or {"title": "?", "time": "?", "tags": "?"}
            rows[p.tier].append(f"| {p.pid} | [{h['title']}]({p.tier}/{p.path.name}) | {h['time']} | {h['tags']} |")
        md = [f"# {lang.name.capitalize()} problems", "",
              "Generated by `./check --index`. `[Rnn]` marks a problem that also appears in the other languages.", ""]
        for t in TIERS:
            md += [f"## {t.capitalize()} ({len(rows[t])})", "", "| ID | Problem | Time | Tags |", "|---|---|---|---|", *rows[t], ""]
        (ROOT / lang.name / "INDEX.md").write_text("\n".join(md))
        print(f"wrote {lang.name}/INDEX.md")


_TTY = sys.stdout.isatty()
ICON = {k: (f"\033[{c}m{k}\033[0m" if _TTY else k) for k, c in (("PASS", 32), ("TODO", 33), ("FAIL", 31))}


def tail(out: str, n: int = 25) -> str:
    lines = [l for l in out.strip().splitlines() if l.strip()]
    return "\n".join(("    " + l) for l in lines[-n:])


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("targets", nargs="*", help="[lang] [ID ...]")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--solutions", action="store_true")
    g.add_argument("--stubs", action="store_true")
    g.add_argument("--freeze", action="store_true")
    g.add_argument("--index", action="store_true")
    ap.add_argument("-j", "--jobs", type=int, default=4)
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args()

    targets = list(a.targets)
    langs = list(LANGS.values())
    if targets and targets[0] in LANGS:
        langs = [LANGS[targets.pop(0)]]
    ids = {t.upper() for t in targets}

    if a.freeze:
        return freeze(langs)
    if a.index:
        return index(langs)

    jobs = []
    for lang in langs:
        frozen = load_specs(lang)
        for p in problems(lang, solutions=a.solutions):
            if not ids or p.pid in ids:
                jobs.append((p, frozen))
    if not jobs:
        sys.exit("no matching problems")

    def work(job):
        p, frozen = job
        if a.stubs:
            return p, check_stub(p, frozen)
        return p, check_one(p, "strict" if a.solutions else "learner", frozen)

    tally: dict[tuple[str, str], dict[str, int]] = {}
    failed = 0
    with cf.ThreadPoolExecutor(max_workers=max(1, a.jobs)) as ex:
        for p, (status, issues, out) in ex.map(work, jobs):
            t = tally.setdefault((p.lang.name, p.tier), {"PASS": 0, "TODO": 0, "FAIL": 0})
            t[status] += 1
            failed += status != "PASS"
            print(f"{ICON[status]}  {p.rel}")
            for i in issues:
                print(f"    ! {i}")
            if a.verbose or (status != "PASS" and len(jobs) <= 3):
                print(tail(out, 1000 if a.verbose else 25))
    if len(jobs) > 1:
        print("\nsummary")
        for (lang, tier), t in tally.items():
            print(f"  {lang:6} {tier:7} pass {t['PASS']:3}  todo {t['TODO']:3}  fail {t['FAIL']:3}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
