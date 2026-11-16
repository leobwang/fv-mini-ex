# fv-mini-ex

Short hands-on exercises for writing proofs and verified programs in **Lean 4**, **Dafny** and **Verus**,
every one machine-checked:

| Track | Easy | Medium | Hard | Libraries |
|---|---|---|---|---|
| Lean 4 | 127 | 192 | 115 | core, Mathlib, physlib (PhysLean + QuantumInfo) |
| Dafny | 45 | 45 | 10 | standard library |
| Verus | 45 | 45 | 10 | vstd |

| Tier | Budget | Feels like |
|---|---|---|
| easy | 1–3 min | one new construct or tactic; a guided tour of the syntax, in order |
| medium | 5–20 min | a loop invariant, an induction with a helper lemma, a data-structure invariant |
| hard | 30 min–2 h | a classic verified algorithm or a real theorem, with optional milestones |

Dafny and Verus IDs have two digits (`E07`); Lean IDs have three (`E007`).

**Lean topics.** Medium and hard Lean problems are grouped in topic folders
(`lean/medium/06_probability_and_statistics/`, …):

| # | Topic | Medium | Hard | Main libraries |
|---|---|---|---|---|
| 01 | Logic and types | 14 | 9 | core |
| 02 | Verified programs | 23 | 9 | core (`Std.Do`/`mvcgen` in two) |
| 03 | Semantics (IMP, STLC, Hoare logic, abstract interpretation) | 13 | 10 | core |
| 04 | Algebra and number theory | 15 | 10 | Mathlib |
| 05 | Analysis and sets | 13 | 11 | Mathlib |
| 06 | Probability and statistics | 23 | 12 | Mathlib `ProbabilityTheory`, `MeasureTheory`, `PMF` |
| 07 | Numerical analysis | 24 | 14 | Mathlib analysis, linear algebra, polynomials |
| 08 | Quantum computing | 24 | 13 | Mathlib matrices + physlib `QuantumInfo` |
| 09 | Condensed matter and stat mech | 24 | 14 | physlib `StatisticalMechanics`, `CondensedMatter` + Mathlib |
| 10 | Physics with PhysLean | 19 | 13 | physlib (relativity, EM, oscillators, units, anomaly cancellation) |

Easy Lean problems E001–E094 are the syntax/tactics tour; E095–E127 are warm-ups for the five domain
libraries (probability, numerics, quantum, condensed matter, PhysLean).

About 20 problems tagged `[Rnn]` appear in all three languages (abs, binary search, insertion sort,
merge sort…), so you can compare how each language handles the same problem.

## Setup

```sh
tools/setup.sh          # Linux x86-64 or macOS (Apple Silicon / Intel); idempotent
tools/setup.sh --check  # show what's installed
```

Pins (see `VERSIONS.md`): Lean 4.32.0 + Mathlib v4.32.0 + physlib (commit `ba2a946`), Dafny 4.11.0,
Verus 0.2026.09.27.3cf1832.
You need `elan` (Lean), `rustup` (Verus needs Rust 1.98.1, which setup installs), `python3`, `curl` and `unzip`.
On a fresh Mac the first Lean setup downloads the Mathlib cache (a few GB) and compiles the physlib
modules the exercises use (physlib has no prebuilt cache; about 10–20 minutes, once).

**Editors.** Open the repo root in VS Code and accept the recommended extensions (`lean4`, Dafny);
`.vscode/` configures the rest.
- Lean and Dafny report errors as you type. Dafny uses `.toolchain/dafny` at the `./check` resource limit.
  Two catches: the extension won't start unless `dotnet` is on PATH (`brew install dotnet`), though Dafny
  itself doesn't use it, and `dafny.cliPath` in `.vscode/settings.json` assumes the repo is at
  `~/code/learn/fv-mini-ex`. If it's elsewhere, change that path. Reload the window after either change.
- Verus only reads saved files, so `.rs` files auto-save and the "Watch Verus" task re-checks them; errors
  update about a second after you stop typing. The task starts with the folder only if automatic tasks are
  allowed, and VS Code's "Allow" turns that on for every trusted folder. Otherwise start it from "Run Task".
- Cmd+Shift+B (Ctrl+Shift+B on Linux) runs `./check` on the active file in any language.
- "Run Task → Check whole track" runs a whole language. Solutions are excluded from search and Cmd+P.

## Workflow

1. Open a problem, e.g. `dafny/easy/E07_….dfy` or `lean/medium/08_quantum_computing/M131_….lean`. The top comment is the card: **GOAL** and a
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
  it fails the check, so you can't solve a problem by weakening the spec. In Lean the checker also
  freezes the *elaborated* statement, so a `variable`, `open`, instance or notation added elsewhere that
  changes its meaning fails too.
- No cheating constructs. Lean: no `axiom`/`native_decide`, and spec theorems may depend only on
  `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`). Dafny: no `assume`,
  `expect`, `{:axiom}`, `{:verify false}`. Verus: runs with `--no-cheating`; no `verifier::external*`.
- Some problems ban a library lemma or an automation tactic that would solve them in one line (listed
  under `BANNED:`); a few constructive Lean problems restrict axioms (`AXIOMS:`).
- Resource limits are deterministic counters (Dafny `--resource-limit`, Verus `--rlimit`), so a pass
  means the same thing on every machine. Reference solutions pass at half the limit.

## Map

- `<lang>/INDEX.md`: every problem with time and tags
- `<lang>/REFERENCE.md`: a cumulative cheat sheet per language, ending in a one-screen `Cheatsheet`
- `<lang>/SYLLABUS.md`: the order constructs are introduced in
- `DESIGN.md`: how the problems are built (for adding your own)
