/- M036 | Hoare triples for a for-loop (mvcgen warm-up) | 10-15 min | Std.Do, Hoare triple, mvcgen, loop invariant, Id.run
GOAL
  `maxLoop` computes a running maximum with a `for` loop. State its correctness as a Hoare triple,
  prove it with `mvcgen` and a loop invariant, then turn the triple into a fact about `.run`.

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false

namespace M036

-- BEGIN SPEC
/-- Running maximum with a `for` loop (0 for the empty list). -/
def maxLoop (xs : List Nat) : Id Nat := do
  let mut m := 0
  for x in xs do
    if m < x then
      m := x
  return m
-- END SPEC

/- SKELETON · maxLoop_spec
  1. Choose the invariant on (cursor `cur`, loop variable `m`): the postcondition with `xs`
     replaced by `cur.prefix` and `r` by `m`. It must hold for `[]` and `m = 0`.        R2
  2. Triple → VCs, giving that invariant:                                               R1, R3
       mvcgen [maxLoop] invariants
         · ⇓⟨cur, m⟩ => ⌜…⌝
     Three VCs remain: `vc1.step.isTrue` (m < x, new value x), `vc2.step.isFalse`
     (value kept), `vc3.pre` (entry, `[]` and 0). The exit VC is closed by `mvcgen`.
  3. Close every VC: membership in `pref ++ [x]` and in `[]`, then arithmetic:        R7 (uses R4–R6)
       all_goals …
-/
-- BEGIN SPEC
theorem maxLoop_spec (xs : List Nat) :
    ⦃⌜True⌝⦄ maxLoop xs ⦃⇓ r => ⌜(∀ x ∈ xs, x ≤ r) ∧ (r = 0 ∨ r ∈ xs)⌝⦄ :=
-- END SPEC
  sorry

/- SKELETON · maxLoop_run
  1. Do not reason about the loop again: `maxLoop_spec xs` is a triple about `maxLoop xs`.
  2. Turn it into the postcondition of `(maxLoop xs).run`, with `_` for the predicate:   R8, R9
  3. Take the first conjunct (the upper bound):                                          R10
  4. Apply it to `x` and `hx`:                                                           R11
     Steps 2–4 fit in one term (no `by`), as in W2 of the guide.
-/
-- BEGIN SPEC
theorem maxLoop_run (xs : List Nat) (x : Nat) (hx : x ∈ xs) : x ≤ (maxLoop xs).run :=
-- END SPEC
  sorry

end M036

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The invariant is the postcondition with `xs` replaced by `cur.prefix` (what the loop has seen)
    and `r` by the loop variable. `mvcgen [maxLoop] invariants?` prints the syntax (its body is too
    weak). For `maxLoop_run`, do not touch the loop: reuse `maxLoop_spec`.
H2. `mvcgen [maxLoop] invariants` with the line `· ⇓⟨cur, m⟩ => ⌜…⌝` leaves three VCs about
    `pref✝ ++ [cur✝]` and `[]`; `all_goals grind` closes them. For `maxLoop_run`,
    `Id.of_wp_run_eq rfl _ (maxLoop_spec xs)` proves the whole postcondition of `(maxLoop xs).run`.
H3. Invariant: `⌜(∀ x ∈ cur.prefix, x ≤ m) ∧ (m = 0 ∨ m ∈ cur.prefix)⌝`.
    `maxLoop_run`: take `.1` of `Id.of_wp_run_eq rfl _ (maxLoop_spec xs)` and apply it to `x hx`.
-/
