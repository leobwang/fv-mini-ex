/- M013 | Type-safe sprintf | 15-20 min | dependent types, type-level functions, learner-written definition, accumulator generalisation
GOAL
  `Fmt.type fs` computes the type of `sprintf fs` from the format list, so passing the wrong number or
  type of arguments is a type error. Write `sprintfAux fs acc` (`acc` is the text produced so far) and
  prove that `sprintf` agrees with the piece-by-piece spec `render` on every argument tuple.

GUIDE
  Entries R1–R15: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M013

-- BEGIN SPEC
/-- A format directive: literal text, a `Nat` hole, or a `String` hole. -/
inductive Fmt where
  | lit (s : String)
  | nat
  | str

/-- The type of `sprintf fs`: one argument per hole, then the result. -/
def Fmt.type : List Fmt → Type
  | [] => String
  | .lit _ :: fs => Fmt.type fs
  | .nat :: fs => Nat → Fmt.type fs
  | .str :: fs => String → Fmt.type fs

/-- The arguments of `fs`, collected in a tuple. -/
def Fmt.Args : List Fmt → Type
  | [] => Unit
  | .lit _ :: fs => Fmt.Args fs
  | .nat :: fs => Nat × Fmt.Args fs
  | .str :: fs => String × Fmt.Args fs

/-- Feed a tuple of arguments to a curried function of type `Fmt.type fs`. -/
def Fmt.apply : (fs : List Fmt) → Fmt.type fs → Fmt.Args fs → String
  | [], r, () => r
  | .lit _ :: fs, f, a => Fmt.apply fs f a
  | .nat :: fs, f, (n, a) => Fmt.apply fs (f n) a
  | .str :: fs, f, (s, a) => Fmt.apply fs (f s) a

/-- Specification: the rendered string, piece by piece. -/
def render : (fs : List Fmt) → Fmt.Args fs → String
  | [], () => ""
  | .lit s :: fs, a => s ++ render fs a
  | .nat :: fs, (n, a) => toString n ++ render fs a
  | .str :: fs, (s, a) => s ++ render fs a
-- END SPEC

/- SKELETON · sprintfAux
  1. The body is a term after the frozen `:=`: a `fun` with one arm per
     shape of the list, matching `fs` and `acc` together:                  R1
       | [], acc => …  | .lit s :: fs, acc => …  | .nat :: fs, acc => …  | .str :: fs, acc => …
  2. Each arm's type is `Fmt.type` of its list; reduce it to see what the
     arm must produce (`String`, `Fmt.type fs`, `Nat → Fmt.type fs`, …):   R2
  3. `[]`: nothing is left to fill in; return the accumulator:             R3
  4. `.lit s`: call `sprintfAux` on the tail `fs`, with `s` appended:      R3, R5
  5. `.nat` / `.str`: take the argument, then the recursive call with it
     appended (`toString` for the `Nat`):                                  R4 → R5
  6. Test it by `rfl` on a concrete format, in an `example` placed after
     `sprintf` (below the theorem, before `end M013`), e.g.
     `example : sprintf [.lit "x=", .nat] 3 = "x=3" := rfl`:               W1
-/
-- BEGIN SPEC
/-- Write this: `acc` is the text produced so far; holes become function arguments. -/
def sprintfAux : (fs : List Fmt) → String → Fmt.type fs :=
-- END SPEC
  sorry

/- SKELETON · sprintf_correct
  1. MILESTONE first, as a `have` (with `acc = ""` the statement is not
     inductive); step 5 uses it:                                           R6
       key : ∀ (fs : List Fmt) (acc : String) (args : Fmt.Args fs),
               Fmt.apply fs (sprintfAux fs acc) args = acc ++ render fs args
  2. Proof of `key`: introduce only `fs` and induct on it, so `ih` keeps
     `∀ acc args`; in each case `intro acc args`:                          R7
  3. `nil`: split `args : Fmt.Args []` into `()`, unfold the definitions;
     `simp` closes `acc = acc ++ ""` by itself:                            R8 → R11, R14
  4. `cons f fs ih`: split the head directive:                             R9
       `lit s`:       unfold, use `ih` at `acc ++ s`, regroup `++`:        R11 → R12 → R13
       `nat`, `str`:  split `args` into the argument and the rest first:   R10 → R11 → R12 → R13 (R15)
  5. The theorem: unfold `sprintf`, rewrite with `key` at `acc = ""`,
     then `"" ++ s = s`:                                                   R11, R12, R14
-/
-- BEGIN SPEC
def sprintf (fs : List Fmt) : Fmt.type fs := sprintfAux fs ""

theorem sprintf_correct (fs : List Fmt) (args : Fmt.Args fs) :
    Fmt.apply fs (sprintf fs) args = render fs args :=
-- END SPEC
  sorry

end M013

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `sprintfAux`: a `fun` matching `fs` and `acc` together (R1). `[]` returns `acc`, a literal appends to
    `acc`, a hole returns a function that appends its argument (R4, R5). `sprintf_correct` is not
    inductive as stated: the accumulator `""` does not survive one step (R6).
H2. Prove the milestone `key : ∀ fs acc args, Fmt.apply fs (sprintfAux fs acc) args = acc ++ render fs args`
    by `intro fs; induction fs` (so `ih` stays `∀ acc args`), split `args` and the head directive, and
    `simp` with the three definitions (R7–R13). The theorem is then `simp [sprintf, key]`.
H3. The hole arm: `| .nat :: fs, acc => fun n => sprintfAux fs (acc ++ toString n)`. In `key`, after
    `intro acc args` and `cases f`, each `cons` case is `simp [sprintfAux, Fmt.apply, render, ih, String.append_assoc]`
    (after `obtain ⟨n, a⟩ := args` for holes; `cases args` in `nil`).
-/
