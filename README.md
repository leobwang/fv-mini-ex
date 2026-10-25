# fv-mini-ex

Short hands-on exercises for writing proofs and verified programs in **Lean 4**, **Dafny** and **Verus**:
100 problems per language (45 easy, 45 medium, 10 hard), every one machine-checked.

| Tier | Budget | Feels like |
|---|---|---|
| easy (E01–E45) | 1–3 min | one new construct or tactic; a guided tour of the syntax, in order |
| medium (M01–M45) | 5–20 min | a loop invariant, an induction with a helper lemma, a data-structure invariant |
| hard (H01–H10) | 30 min–2 h | a classic verified algorithm or a real theorem, with optional milestones |

About 20 problems tagged `[Rnn]` appear in all three languages (abs, binary search, insertion sort,
merge sort…), so you can compare how each language handles the same problem.

## Setup

```sh
tools/setup.sh          # Linux x86-64 or macOS (Apple Silicon / Intel); idempotent
tools/setup.sh --check  # show what's installed
```

Pins (see `VERSIONS.md`): Lean 4.32.0 + Mathlib v4.32.0, Dafny 4.11.0, Verus 0.2026.09.27.3cf1832.
You need `elan` (Lean), `rustup` (Verus needs Rust 1.98.1, which setup installs), `python3`, `curl` and `unzip`.
On a fresh Mac the first Lean setup downloads the Mathlib cache (a few GB).

**Editors.**
- Lean: VS Code + the `lean4` extension, opening the `lean/` folder (it holds the Lake project).
- Dafny: the Dafny VS Code extension, with "Dafny: Cli Path" set to `.toolchain/dafny/dafny`.
- Verus: `./check` gives the errors; verus-analyzer is optional.

## Workflow

1. Open a problem, e.g. `dafny/easy/E07_….dfy`. The top comment is the card: **GOAL** and a
   **REFERENCE** with only the syntax and library names that problem needs.
2. Fill the holes (`sorry` in Lean; `{ }` bodies or `0 // TODO` placeholders in Dafny/Verus). Add any
   helper lemmas you like.
3. Run `./check dafny E07`. Stuck? Hints are at the bottom of the file under `HINTS`, in three
   levels: a nudge, the strategy, the key line.
4. Compare with `dafny/solutions/easy/E07_….dfy`.

```sh
./check lean E05 E06       # check specific problems
./check verus              # a whole track, with a pass/todo/fail summary
./check                    # everything
./check -v dafny M12       # show the full verifier output
```

Status: **PASS** (verified, nothing forbidden, spec untouched), **TODO** (holes or verification
errors remain; Lean also reports how many spec theorems are sorry-free), **FAIL** (doesn't compile,
spec edited, or a forbidden construct).

## Rules the checker enforces

- Code between `BEGIN SPEC` and `END SPEC` is frozen: signatures, contracts, theorem statements. Editing
  it fails the check, so you can't solve a problem by weakening the spec.
- No cheating constructs. Lean: no `axiom`/`native_decide`, and spec theorems may depend only on
  `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`). Dafny: no `assume`,
  `expect`, `{:axiom}`, `{:verify false}`. Verus: runs with `--no-cheating`; no `verifier::external*`.
- Some problems ban a library lemma that would solve them in one line (listed under `BANNED:`).
- Resource limits are deterministic counters (Dafny `--resource-limit`, Verus `--rlimit`), so a pass
  means the same thing on every machine. Reference solutions pass at half the limit.

## Map

- `<lang>/INDEX.md`: every problem with time and tags
- `<lang>/REFERENCE.md`: a cumulative cheat sheet per language, ending in a one-screen `Cheatsheet`
- `<lang>/SYLLABUS.md`: the order constructs are introduced in
- `DESIGN.md`: how the problems are built (for adding your own)
