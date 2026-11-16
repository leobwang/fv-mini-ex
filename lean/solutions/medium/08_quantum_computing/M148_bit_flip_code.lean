/- M148 | Three-qubit bit-flip code | 20 min | quantum error correction, syndromes, projectors, linearity, fin_cases, mathlib
GOAL
  Encode `α|000⟩ + β|111⟩`. Measuring the two parities (syndrome) and flipping the indicated qubit undoes
  any single bit flip; by linearity it also undoes any superposition of such errors ("errors are digitised").

REFERENCE
  -- `Q3 = Fin 2 × Fin 2 × Fin 2` indexes |abc⟩; a state is `v : Q3 → ℂ`. On `Fin 2`, `+` is XOR: `(1 : Fin 2) + 1 = 0`.
  #check Fintype.sum_prod_type  -- ∑ x, f x = ∑ x, ∑ y, f (x, y)
  #check Fin.sum_univ_two       -- ∑ i : Fin 2, f i = f 0 + f 1
  #check Finset.sum_apply       -- (a) (s) (g) : (∑ c ∈ s, g c) a = ∑ c ∈ s, g c a   (sums of functions)
  #check Pi.smul_apply          -- (b • x) i = b • x i
  #check Finset.mul_sum         -- a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
  #check Finset.sum_smul        -- (∑ i ∈ s, r i) • x = ∑ i ∈ s, r i • x
  #check Finset.sum_comm        -- swap two sums
  -- `rcases e with _ | e` splits `e : Option (Fin 3)` into `none` / `some e`; `fin_cases e` then splits `e : Fin 3`.
  example (v w : Fin 2 × Fin 2 → ℂ) (h : ∀ a b, v (a, b) = w (a, b)) : v = w := funext fun ⟨a, b⟩ => h a b
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
H1. `corrects` is a finite check: 4 errors × 8 basis labels. `corrects_superposition` should not be
    brute-forced: show that `decode` is linear and reuse `corrects` for each term.
H2. `corrects`: `funext ⟨a, b, c⟩`, split `e` (`none` or `some e`, then `fin_cases e`), split `a b c`, and `simp`
    with all definitions plus `Fintype.sum_prod_type, Fin.sum_univ_two` (the sum over `σ` has 4 terms).
    Superposition: a helper `decode (∑ e, c e • v e) = ∑ e, c e • decode (v e)`, proved pointwise.
H3. `corrects` skeleton: `rcases e with _ | e; all_goals (try fin_cases e)`, then split the basis label; unfold
    `decode, err, flip, enc, proj, synd, guess`.
    Helper: `theorem decode_lin {ι : Type} [Fintype ι] (c : ι → ℂ) (v : ι → Q3 → ℂ) :
       decode (∑ e, c e • v e) = ∑ e, c e • decode (v e)`
    (pointwise: unfold, distribute the scalar into the sum, swap the two sums). Then rewrite each term with `corrects`.
-/
