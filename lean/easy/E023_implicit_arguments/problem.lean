/- E023 | Implicit arguments | 3 min | implicit arguments, @, named arguments
GOAL
  Use a lemma whose arguments are implicit: let Lean infer them, name them, or pass all with `@`.
BANNED: omega, grind, simp

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · my_le_trans
  Given (already proved, nothing to fill). Read its signature: `{a b c}` are implicit,
  `h1`, `h2` explicit. The next three theorems use it in three different ways.
-/
-- BEGIN SPEC
theorem my_le_trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := Nat.le_trans h1 h2
-- END SPEC

/- SKELETON · use_inferred
  1. Apply `my_le_trans` to the two proofs only; `a b c` are read off
     the types of `h1` and `h2` (term mode, or `exact` in tactic mode):   R1
-/
-- BEGIN SPEC
theorem use_inferred (x : Nat) (h1 : x ≤ 5) (h2 : 5 ≤ 7) : x ≤ 7 :=
-- END SPEC
  sorry

/- SKELETON · use_named
  1. Apply `my_le_trans`, giving its middle implicit argument by its
     binder name (look the name up in the signature), then the proofs:   R2
     (all-explicit alternative with `@` and `_` for the rest:            R3)
-/
-- BEGIN SPEC
theorem use_named (h1 : 2 ≤ 4) (h2 : 4 ≤ 9) : 2 ≤ 9 :=
-- END SPEC
  sorry

/- SKELETON · use_explicit
  1. The goal is `my_le_trans`'s statement with `(…)` binders instead of
     `{…}`: that is the type of the lemma with `@` in front.              R4
     (`intro` everything first, then R1, also works.)
-/
-- BEGIN SPEC
theorem use_explicit : ∀ (a b c : Nat), a ≤ b → b ≤ c → a ≤ c :=
-- END SPEC
  sorry

/- SKELETON · hyp_implicit
  1. Instantiate `h` at `3`:       `f 3 = 3`                               R5
  2. Apply `f` to both sides:      `f (f 3) = f 3`                         R6
  3. Chain 2 and 1:                `f (f 3) = 3`                           R7
  (Tactic route instead: rewrite with `h` at `3`, then again: the inner
   `f 3` first, then the `f 3` that is left.                              R8, R8)
-/
-- BEGIN SPEC
theorem hyp_implicit (f : Nat → Nat) (h : ∀ {n : Nat}, f n = n) : f (f 3) = 3 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. You never prove anything new about `≤`: every hole is `my_le_trans` (or `h`) applied the right way.
    Decide per theorem what Lean can infer and what you must pass (R1–R4), and how to use a hypothesis
    with an implicit binder (R5).
H2. `use_inferred`: the two proofs only (R1). `use_named`: name the middle binder `b` (R2).
    `use_explicit`: the statement is the type of `@my_le_trans` (R4). `hyp_implicit`: `@h 3 : f 3 = 3`,
    push `f` through it with `congrArg`, chain with `.trans` (R5 → R6 → R7), or `rw` twice (R8).
H3. `my_le_trans h1 h2`; `my_le_trans (b := 4) h1 h2`; `@my_le_trans`;
    `(congrArg f (@h 3)).trans (@h 3)` (or `by rw [@h 3, @h 3]`).
-/
