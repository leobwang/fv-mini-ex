/- M013 | Type-safe sprintf | 15-20 min | dependent types, type-level functions, learner-written definition, accumulator generalisation
GOAL
  `Fmt.type fs` computes the type of `sprintf fs` from the format list, so passing the wrong number or
  type of arguments is a type error. Write `sprintfAux fs acc` (`acc` is the text produced so far) and
  prove that `sprintf` agrees with the piece-by-piece spec `render` on every argument tuple.

REFERENCE
  example : Fmt.type [.lit "x=", .nat] = (Nat → String) := rfl   -- a type computed by recursion
  -- once `sprintfAux` is written:  sprintf [.lit "x=", .nat, .lit ", s=", .str] 3 "ab" = "x=3, s=ab"
  -- in `fun | .nat :: fs, acc => _` the arm must have type `Fmt.type (.nat :: fs)`, which
  -- reduces to `Nat → Fmt.type fs`, so the arm itself can be `fun n => …`
  example : toString (42 : Nat) = "42" := rfl
  #check String.append_assoc  -- s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃)
  -- `cases args` on `args : Fmt.Args []` (that type is `Unit`); `obtain ⟨n, a⟩ := args` on a pair
NOTE: The body goes after the frozen `:=`, so write it as `fun | [], acc => … | .lit s :: fs, acc => … | …`.
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

-- BEGIN SPEC
/-- Write this: `acc` is the text produced so far; holes become function arguments. -/
def sprintfAux : (fs : List Fmt) → String → Fmt.type fs :=
-- END SPEC
  fun
  | [], acc => acc
  | .lit s :: fs, acc => sprintfAux fs (acc ++ s)
  | .nat :: fs, acc => fun n => sprintfAux fs (acc ++ toString n)
  | .str :: fs, acc => fun s => sprintfAux fs (acc ++ s)

-- BEGIN SPEC
def sprintf (fs : List Fmt) : Fmt.type fs := sprintfAux fs ""

theorem sprintf_correct (fs : List Fmt) (args : Fmt.Args fs) :
    Fmt.apply fs (sprintf fs) args = render fs args :=
-- END SPEC
  by
    -- WHY: generalise the accumulator; the statement with `acc = ""` is not inductive.
    have key : ∀ (fs : List Fmt) (acc : String) (args : Fmt.Args fs),
        Fmt.apply fs (sprintfAux fs acc) args = acc ++ render fs args := by
      intro fs
      induction fs with
      | nil => intro acc args; cases args; simp [sprintfAux, Fmt.apply, render]
      | cons f fs ih =>
        intro acc args
        cases f with
        | lit s => simp [sprintfAux, Fmt.apply, render, ih, String.append_assoc]
        | nat =>
          obtain ⟨n, a⟩ := args
          simp [sprintfAux, Fmt.apply, render, ih, String.append_assoc]
        | str =>
          obtain ⟨s, a⟩ := args
          simp [sprintfAux, Fmt.apply, render, ih, String.append_assoc]
    simp [sprintf, key]

end M013

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Define `sprintfAux` by matching on `fs` (with `acc` as a second pattern): `[]` returns `acc`, a literal
    appends to `acc`, a hole returns a function that appends its argument.
H2. `sprintf_correct` is not inductive as stated (`acc = ""` does not survive one step). Prove the general
    `∀ fs acc args, Fmt.apply fs (sprintfAux fs acc) args = acc ++ render fs args` first.
H3. The hole arm: `| .nat :: fs, acc => fun n => sprintfAux fs (acc ++ toString n)`. For the helper:
    `intro fs; induction fs with …`, then `cases f` on the head directive; each case is
    `simp [sprintfAux, Fmt.apply, render, ih, String.append_assoc]` (after `obtain ⟨n, a⟩ := args` for holes).
-/
