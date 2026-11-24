/- M148 | Three-qubit bit-flip code | 20 min | quantum error correction, syndromes, projectors, linearity, fin_cases, mathlib
GOAL
  Encode `α|000⟩ + β|111⟩`. Measuring the two parities (syndrome) and flipping the indicated qubit undoes
  any single bit flip; by linearity it also undoes any superposition of such errors ("errors are digitised").

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M148

-- BEGIN SPEC
abbrev Q3 := Fin 2 × Fin 2 × Fin 2

/-- the code state `α|000⟩ + β|111⟩` -/
def enc (α β : ℂ) : Q3 → ℂ := fun p => if p = (0, 0, 0) then α else if p = (1, 1, 1) then β else 0

/-- a bit flip on qubit `k` (`none` = no error), as a map on basis labels -/
def flip : Option (Fin 3) → Q3 → Q3
  | none, p => p
  | some 0, p => (p.1 + 1, p.2.1, p.2.2)
  | some 1, p => (p.1, p.2.1 + 1, p.2.2)
  | some 2, p => (p.1, p.2.1, p.2.2 + 1)

/-- apply the error `e` to a state -/
def err (e : Option (Fin 3)) (v : Q3 → ℂ) : Q3 → ℂ := fun p => v (flip e p)

/-- the syndrome: the parities `(q₀ ⊕ q₁, q₁ ⊕ q₂)` -/
def synd (p : Q3) : Fin 2 × Fin 2 := (p.1 + p.2.1, p.2.1 + p.2.2)

/-- projector onto the syndrome-`σ` subspace -/
def proj (σ : Fin 2 × Fin 2) (v : Q3 → ℂ) : Q3 → ℂ := fun p => if synd p = σ then v p else 0

/-- which flip to undo for each syndrome -/
def guess (σ : Fin 2 × Fin 2) : Option (Fin 3) :=
  if σ = (0, 0) then none else if σ = (1, 0) then some 0 else if σ = (1, 1) then some 1 else some 2

/-- measure the syndrome, then correct: `∑ σ, C_σ P_σ` -/
def decode (v : Q3 → ℂ) : Q3 → ℂ := ∑ σ, err (guess σ) (proj σ v)
-- END SPEC

/- SKELETON · corrects
  1. Function equation → one label, its three bits named:                   R1
  2. Split the error: `none` / `some e`, then `e : Fin 3` only where it
     exists (the `none` goal has no `e`):                                   R2, R4 (fin_cases: R3)
  3. In every goal split the three bits (`<;>`, TACTIC_STATES):             fin_cases a, b, c
  4. Close each of the 4 × 8 = 32 cases with ONE `simp`: all seven
     definition names plus the two sum lemmas, so that the sum over the
     4 syndromes σ is expanded (simp applies R7–R9 by itself):             R5, R6
-/
-- BEGIN SPEC
theorem corrects (α β : ℂ) (e : Option (Fin 3)) : decode (err e (enc α β)) = enc α β :=
-- END SPEC
  by
    funext ⟨a, b, c⟩
    rcases e with _ | e
    all_goals (try fin_cases e)
    all_goals (fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [decode, err, flip, enc, proj, synd, guess, Fintype.sum_prod_type, Fin.sum_univ_two])

/-- syndrome measurement + correction is a linear map -/
theorem decode_lin {ι : Type} [Fintype ι] (c : ι → ℂ) (v : ι → Q3 → ℂ) :
    decode (∑ e, c e • v e) = ∑ e, c e • decode (v e) := by
  funext p
  simp only [decode, err, proj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp

/- SKELETON · corrects_superposition
  1. MILESTONE first: a helper lemma placed above this SKELETON, outside the spec regions:
       decode_lin {ι : Type} [Fintype ι] (c : ι → ℂ) (v : ι → Q3 → ℂ) :
         decode (∑ e, c e • v e) = ∑ e, c e • decode (v e)
     a. pointwise:                                                          R1 (as `funext p`)
     b. unfold decode, err, proj and push the point inside the sums:        R7, R10, R11
     c. scalar into the inner sum and through the `if`:                     R13 with R12, R14, R15
     d. swap the two sums:                                                  R16
     e. compare term by term, split the `if`, then `simp`:                  R17, R18
  2. The theorem: rewrite with the milestone, then every term with
     `corrects` (the `e` is bound by `∑`, so not plain `rw`):              rw [decode_lin], R13
  3. Fold the scalar sum on the right-hand side:                            R19
-/
-- BEGIN SPEC
theorem corrects_superposition (α β : ℂ) (c : Option (Fin 3) → ℂ) :
    decode (∑ e, c e • err e (enc α β)) = (∑ e, c e) • enc α β :=
-- END SPEC
  by
    rw [decode_lin]
    simp_rw [corrects]
    rw [Finset.sum_smul]

end M148

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `corrects` is a finite check: 4 errors × 8 basis labels, each closed by evaluation. Do not brute-force
    `corrects_superposition` (the `c e` are arbitrary): prove that `decode` is linear (milestone
    `decode_lin` in the SKELETON) and reuse `corrects` for each term.
H2. `corrects`: `funext ⟨a, b, c⟩`, `rcases e with _ | e`, `all_goals (try fin_cases e)`, then split
    `a b c` and `simp` with all seven definitions plus `Fintype.sum_prod_type, Fin.sum_univ_two`.
    `decode_lin`: `funext p`; unfold with `Finset.sum_apply, Pi.smul_apply, smul_eq_mul`; distribute with
    `simp_rw`; swap the sums with `Finset.sum_comm`; compare termwise with `Finset.sum_congr`.
H3. `corrects`, after the splits of `e`:
      `all_goals (fin_cases a <;> fin_cases b <;> fin_cases c <;>
         simp [decode, err, flip, enc, proj, synd, guess, Fintype.sum_prod_type, Fin.sum_univ_two])`
    `decode_lin`, after unfolding: `simp_rw [Finset.mul_sum, mul_ite, mul_zero]`, `rw [Finset.sum_comm]`,
    `refine Finset.sum_congr rfl fun σ _ => ?_`, `split_ifs <;> simp`.
    `corrects_superposition`: `rw [decode_lin]`, then `simp_rw [corrects]`, then `Finset.sum_smul`.
-/
