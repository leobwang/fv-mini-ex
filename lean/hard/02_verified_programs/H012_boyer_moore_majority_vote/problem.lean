/- H012 | Boyer-Moore majority vote with mvcgen | 45-75 min | Std.Do, Hoare triples, mvcgen, loop invariants, imperative for-loop, composing specs
GOAL
  Verify the one-pass, O(1)-space majority vote (an imperative `Id` program with a `for` loop) with
  Hoare triples and `mvcgen`: if some `m` fills more than half of `xs`, the vote returns `m`. Then
  verify the two-pass checked version, and turn the triple into a plain equation about `.run`.

GUIDE
  Entries R1–R18: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · MajInv and the milestones (prove these FIRST; `majority_spec` uses all five)
  1. `MajInv p c k`: two `Nat` inequalities, no division, no `-` (cheatsheet Part 1):
       every `y ≠ c` occurs in `p` at most half of the `p.length - k` paired slots;
       `c` occurs at most `k` + half of them.
  2. majInv_nil:                                          simp [MajInv]   (R1, R2)
  3. majInv_reset, majInv_match, majInv_cancel, majInv_final, each:
       unfold the invariant in goal and hypotheses        R8
       close it (count/length of `p ++ [x]` inside)       R9 (uses R3–R7)
     They are used in majority_spec as: reset = VC `k = 0`, match = VC `x = cand`,
     cancel = VC `x ≠ cand`, nil = loop entry, final = loop exit.
-/
-- MILESTONE (optional: change or delete)
/-- The loop invariant of `majority`, after processing the prefix `p` with candidate `c` and counter `k`. -/
def MajInv (p : List Nat) (c k : Nat) : Prop :=
  sorry

-- MILESTONE (optional: change or delete)
theorem majInv_nil : MajInv [] 0 0 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem majInv_reset (p : List Nat) (c x : Nat) (h : MajInv p c 0) : MajInv (p ++ [x]) x 1 := by
  sorry

-- MILESTONE (optional: change or delete)
theorem majInv_match (p : List Nat) (c k : Nat) (h : MajInv p c k) : MajInv (p ++ [c]) c (k + 1) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem majInv_cancel (p : List Nat) (c k x : Nat) (hk : k ≠ 0) (hx : x ≠ c) (h : MajInv p c k) :
    MajInv (p ++ [x]) c (k - 1) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem majInv_final (xs : List Nat) (c k m : Nat) (h : MajInv xs c k)
    (hm : xs.length < 2 * xs.count m) : c = m := by
  sorry

/- SKELETON · majority_spec
  1. Prove the six MILESTONE declarations above first.
  2. Turn the triple into VCs, unfolding `majority`, with the loop invariant
       `MajInv` of the processed prefix and the two `let mut`s (cand, k)    R11, R12, R13, R14
  3. Five VCs: three loop branches, entry, exit = reset, match, cancel, nil, final.
     Close all of them at once with the five milestones                     all_goals, R10
-/
-- BEGIN SPEC
theorem majority_spec (xs : List Nat) :
    ⦃⌜True⌝⦄ majority xs ⦃⇓ r => ⌜∀ m, xs.length < 2 * xs.count m → r = m⌝⦄ :=
-- END SPEC
  sorry

/- SKELETON · majorityChecked_spec
  1. Turn the triple into VCs, unfolding `majorityChecked` and using the proved
     `majority_spec` at the call `let c ← majority xs`                      R15
  2. Invariant of the counting loop: `n` is the count of `c` in the processed
     prefix. It must name the candidate `c`, so use the labelled form       R16 (R12, R13)
  3. Four VCs: two loop steps (`x = c`, `x ≠ c`) and two exits (`some c`, `none`);
     `majority_spec`'s postcondition is in context. Close all at once      all_goals, R9 (R3–R5)
-/
-- BEGIN SPEC
theorem majorityChecked_spec (xs : List Nat) :
    ⦃⌜True⌝⦄ majorityChecked xs ⦃⇓ r => ⌜∀ m, r = some m ↔ xs.length < 2 * xs.count m⌝⦄ :=
-- END SPEC
  sorry

/- SKELETON · majority_run
  1. `Id.of_wp_run_eq` with `x := (majority xs).run` (proved by `rfl`) and `P` := the
     predicate inside `majority_spec`'s postcondition                       R17
  2. Its `wp` argument is the triple `majority_spec xs`                       R18
  3. The result is `P (majority xs).run`, a `∀ m, … → …`: apply it to `m` and `hm`
     (one term, as in guide W2)
-/
-- BEGIN SPEC
theorem majority_run (xs : List Nat) (m : Nat) (hm : xs.length < 2 * xs.count m) :
    (majority xs).run = m :=
-- END SPEC
  sorry

end H012

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Read `(cand, k)` as "k copies of cand are still unpaired"; every other element processed so far was
    cancelled against a different one. So the invariant bounds the count of EVERY value in the prefix,
    not just `cand`. Each VC that `mvcgen` produces is exactly one milestone.
H2. `MajInv` has two clauses: every `y ≠ c` is far from a majority of the prefix (even after adding `k`),
    and `c` itself is at most half plus `k`. Milestones: `unfold MajInv at *; grind` (`majInv_nil`:
    `simp [MajInv]`). Then `mvcgen [majority] invariants` with `· ⇓⟨cur, st⟩ => ⌜MajInv cur.prefix st.1 st.2⌝`
    and `all_goals grind [majInv_nil, majInv_reset, majInv_match, majInv_cancel, majInv_final]`.
    Checked version: `mvcgen [majorityChecked, majority_spec]` with a labelled counting invariant (R16).
H3. `MajInv p c k := (∀ y, y ≠ c → 2 * p.count y + k ≤ p.length) ∧ 2 * p.count c ≤ p.length + k`.
    Checked: `invariants | inv1 c _ => ⇓⟨cur, n⟩ => ⌜n = cur.prefix.count c⌝`, then `all_goals grind`.
    `majority_run`: `Id.of_wp_run_eq rfl P (majority_spec xs) m hm`, `P` the postcondition predicate `fun r => …`.
-/
