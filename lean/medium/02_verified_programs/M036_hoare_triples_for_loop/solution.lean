/- M036 | Hoare triples for a for-loop (mvcgen warm-up) | 10-15 min | Std.Do, Hoare triple, mvcgen, loop invariant, Id.run
GOAL
  `maxLoop` computes a running maximum with a `for` loop. State its correctness as a Hoare triple,
  prove it with `mvcgen` and a loop invariant, then turn the triple into a fact about `.run`.

REFERENCE
  -- ⦃P⦄ prog ⦃⇓ r => Q⦄ : started where P holds, `prog` returns some `r` satisfying Q
  -- ⌜φ⌝ lifts a plain Prop φ to an assertion. Type ⦃ ⦄ ⌜ ⌝ ⇓ as \{{ \}} \ulc \urc \d=
  example : ⦃⌜True⌝⦄ (pure 3 : Id Nat) ⦃⇓ r => ⌜r = 3⌝⦄ := by mvcgen
  -- A `for` loop needs an invariant over the cursor `cur` (`cur.prefix` = elements already
  -- processed, `cur.suffix` = still to go) and the loop's mutable variable. A sum loop would use
  --   mvcgen [sumLoop] invariants
  --   · ⇓⟨cur, s⟩ => ⌜s = cur.prefix.sum⌝
  --   all_goals grind        -- closes the verification conditions mvcgen leaves
  #check @Id.of_wp_run_eq  -- prog.run = x → ∀ P, ⦃⌜True⌝⦄ prog ⦃⇓ r => ⌜P r⌝⦄ → P x
NOTE: M018 proves a similar loop by unfolding it to `List.foldl`; here you reason in Hoare logic.
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

-- BEGIN SPEC
theorem maxLoop_spec (xs : List Nat) :
    ⦃⌜True⌝⦄ maxLoop xs ⦃⇓ r => ⌜(∀ x ∈ xs, x ≤ r) ∧ (r = 0 ∨ r ∈ xs)⌝⦄ :=
-- END SPEC
  by
    mvcgen [maxLoop] invariants
    · ⇓⟨cur, m⟩ => ⌜(∀ x ∈ cur.prefix, x ≤ m) ∧ (m = 0 ∨ m ∈ cur.prefix)⌝
    all_goals grind

-- BEGIN SPEC
theorem maxLoop_run (xs : List Nat) (x : Nat) (hx : x ∈ xs) : x ≤ (maxLoop xs).run :=
-- END SPEC
  (Id.of_wp_run_eq rfl _ (maxLoop_spec xs)).1 x hx

end M036

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The invariant is the postcondition with `xs` replaced by `cur.prefix` (what the loop has seen).
    `mvcgen [maxLoop] invariants?` prints a skeleton (too weak, but it shows the shape).
H2. After `mvcgen [maxLoop] invariants · ⇓⟨cur, m⟩ => ⌜…⌝`, every remaining goal is first-order
    list/arithmetic reasoning: `all_goals grind`. For `maxLoop_run`, reuse `maxLoop_spec`.
H3. Invariant: `⌜(∀ x ∈ cur.prefix, x ≤ m) ∧ (m = 0 ∨ m ∈ cur.prefix)⌝`;
    `maxLoop_run`: apply `Id.of_wp_run_eq rfl` to `maxLoop_spec xs` and take the first conjunct.
-/
