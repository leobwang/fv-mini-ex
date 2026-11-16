/- H012 | Boyer-Moore majority vote with mvcgen | 45-75 min | Std.Do, Hoare triples, mvcgen, loop invariants, imperative for-loop, composing specs
GOAL
  Verify the one-pass, O(1)-space majority vote (an imperative `Id` program with a `for` loop) with
  Hoare triples and `mvcgen`: if some `m` fills more than half of `xs`, the vote returns `m`. Then
  verify the two-pass checked version, and turn the triple into a plain equation about `.run`.

REFERENCE
  example : ⦃⌜True⌝⦄ (pure 3 : Id Nat) ⦃⇓ r => ⌜r = 3⌝⦄ := by mvcgen  -- ⦃pre⦄ prog ⦃post⦄; ⌜p⌝ lifts a Prop
  -- `⇓ r => Q r`: postcondition on the returned value r. `mvcgen [f]` unfolds f, emits the VCs.
  -- Loop invariant (cur.prefix = elements already processed; st = the `let mut`s, st.1, st.2 in order):
  --   mvcgen [f] invariants
  --   · ⇓⟨cur, st⟩ => ⌜... cur.prefix ... st.1 ... st.2 ...⌝
  -- `mvcgen [f] invariants?` prints a (non-inductive) invariant skeleton showing the shape.
  -- `invariants | inv1 c _ => ⇓⟨cur, n⟩ => ⌜...c...⌝` names a variable bound earlier (c ← ...).
  -- `mvcgen [g, f_spec]`: unfold g, use the proved triple `f_spec` where g calls f.
  #check @Id.of_wp_run_eq   -- prog.run = x → ∀ P, (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x
  -- wp⟦prog⟧ Q: weakest precondition; a proved triple ⦃⌜True⌝⦄ prog ⦃Q⦄ fits the `⊢ₛ wp⟦prog⟧ Q` argument.
  #check @List.count_append -- (l₁ ++ l₂).count a = l₁.count a + l₂.count a  (a grind lemma)
NOTE: `List.count m xs` is the number of occurrences of `m` in `xs`; "strict majority" is `xs.length < 2 * xs.count m`.
-/
import Std.Tactic.Do
open Std.Do
set_option mvcgen.warning false

namespace H012

-- BEGIN SPEC
/-- Boyer-Moore majority vote: one pass, O(1) extra space. -/
def majority (xs : List Nat) : Id Nat := do
  let mut cand := 0
  let mut k := 0
  for x in xs do
    if k = 0 then
      cand := x
      k := 1
    else if x = cand then
      k := k + 1
    else
      k := k - 1
  return cand

/-- Second pass: count the candidate and accept it only if it is a strict majority. -/
def majorityChecked (xs : List Nat) : Id (Option Nat) := do
  let c ← majority xs
  let mut n := 0
  for x in xs do
    if x = c then
      n := n + 1
  if xs.length < 2 * n then
    return some c
  else
    return none
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- The loop invariant of `majority`, after processing the prefix `p` with candidate `c` and counter `k`. -/
def MajInv (p : List Nat) (c k : Nat) : Prop :=
  (∀ y, y ≠ c → 2 * p.count y + k ≤ p.length) ∧ 2 * p.count c ≤ p.length + k

-- MILESTONE (optional: change or delete)
theorem majInv_nil : MajInv [] 0 0 := by
  simp [MajInv]

-- MILESTONE (optional: change or delete)
theorem majInv_reset (p : List Nat) (c x : Nat) (h : MajInv p c 0) : MajInv (p ++ [x]) x 1 := by
  unfold MajInv at *; grind

-- MILESTONE (optional: change or delete)
theorem majInv_match (p : List Nat) (c k : Nat) (h : MajInv p c k) : MajInv (p ++ [c]) c (k + 1) := by
  unfold MajInv at *; grind

-- MILESTONE (optional: change or delete)
theorem majInv_cancel (p : List Nat) (c k x : Nat) (hk : k ≠ 0) (hx : x ≠ c) (h : MajInv p c k) :
    MajInv (p ++ [x]) c (k - 1) := by
  unfold MajInv at *; grind

-- MILESTONE (optional: change or delete)
theorem majInv_final (xs : List Nat) (c k m : Nat) (h : MajInv xs c k)
    (hm : xs.length < 2 * xs.count m) : c = m := by
  unfold MajInv at *; grind

-- BEGIN SPEC
theorem majority_spec (xs : List Nat) :
    ⦃⌜True⌝⦄ majority xs ⦃⇓ r => ⌜∀ m, xs.length < 2 * xs.count m → r = m⌝⦄ :=
-- END SPEC
  by
    mvcgen [majority] invariants
    · ⇓⟨cur, st⟩ => ⌜MajInv cur.prefix st.1 st.2⌝
    -- one VC per branch of the loop body, plus entry and exit: exactly the milestones
    all_goals grind [majInv_nil, majInv_reset, majInv_match, majInv_cancel, majInv_final]

-- BEGIN SPEC
theorem majorityChecked_spec (xs : List Nat) :
    ⦃⌜True⌝⦄ majorityChecked xs ⦃⇓ r => ⌜∀ m, r = some m ↔ xs.length < 2 * xs.count m⌝⦄ :=
-- END SPEC
  by
    -- WHY: the label `inv1 c _` names the result `c` of the call to `majority`, which is not in scope here.
    mvcgen [majorityChecked, majority_spec] invariants
    | inv1 c _ => ⇓⟨cur, n⟩ => ⌜n = cur.prefix.count c⌝
    all_goals grind

-- BEGIN SPEC
theorem majority_run (xs : List Nat) (m : Nat) (hm : xs.length < 2 * xs.count m) :
    (majority xs).run = m :=
-- END SPEC
  Id.of_wp_run_eq rfl (fun r => ∀ m, xs.length < 2 * xs.count m → r = m) (majority_spec xs) m hm

end H012

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read `(cand, k)` as "k copies of cand are still unpaired"; every other element seen so far was
    cancelled against a different one. The invariant bounds counts in the prefix, not just `cand`.
H2. Two clauses: every `y ≠ c` is far from a majority of the prefix (even after adding `k`), and `c`
    itself is not too frequent. Each VC of `mvcgen` is one milestone; prove them by
    `unfold MajInv at *; grind`, then `mvcgen [majority] invariants · ⇓⟨cur, st⟩ => ⌜MajInv cur.prefix st.1 st.2⌝`
    and `all_goals grind [majInv_nil, majInv_reset, ...]`.
H3. `MajInv p c k := (∀ y, y ≠ c → 2 * p.count y + k ≤ p.length) ∧ 2 * p.count c ≤ p.length + k`.
    Checked version: `mvcgen [majorityChecked, majority_spec] invariants | inv1 c _ => ⇓⟨cur, n⟩ => ⌜n = cur.prefix.count c⌝`.
    `majority_run`: apply `Id.of_wp_run_eq rfl` with `P` := the postcondition of `majority_spec`.
-/
