/- H083 | Walsh–Hadamard: Bernstein–Vazirani and Deutsch–Jozsa | 1-1.5 h | Hadamard transform, character sums, Fintype.prod_sum, Finset.sum_comm, mathlib
GOAL
  `W` is the closed form of `H^{⊗n}` (defined directly, not as a Kronecker power): on amplitudes `v` over bit
  strings, `(W v) y = 2^{-n/2} ∑ₓ (−1)^{x·y} v x`. Prove `W ∘ W = id`,
  Bernstein–Vazirani (`W` maps the phase state `2^{-n/2}(−1)^{s·x}` to the basis state `|s⟩`) and
  Deutsch–Jozsa (for a balanced `f`, the amplitude of `|0…0⟩` after `W` is 0).

REFERENCE
  -- bit strings `x : Fin n → Fin 2`; `Fin 2` addition is XOR, `(1 : Fin 2) + 1 = 0`; `x + y` is pointwise
  #check Fintype.prod_sum            -- ∏ i, ∑ j, f i j = ∑ x, ∏ i, f i (x i)   (expand a product of sums)
  #check Finset.prod_pow_eq_pow_sum  -- ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i
  #check Finset.prod_mul_distrib     -- ∏ x ∈ s, f x * g x = (∏ x ∈ s, f x) * ∏ x ∈ s, g x
  #check Finset.prod_eq_zero         -- i ∈ s → f i = 0 → ∏ j ∈ s, f j = 0
  #check Finset.sum_comm             -- ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
  #check Finset.sum_ite_eq'          -- ∑ x ∈ s, (if x = a then b x else 0) = if a ∈ s then b a else 0
  #check Finset.sum_filter_add_sum_filter_not  -- ∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬p x, f x = ∑ x ∈ s, f x
  example (n : ℕ) : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹ := by rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
  example (a : Fin 2) (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : P a := by fin_cases a <;> assumption
  -- `Pi.single s 1 y = if y = s then 1 else 0` (`Pi.single_apply`);  `funext y` proves two functions equal
-/
import Mathlib

namespace H083

-- BEGIN SPEC
/-- `x·y` (we only use its parity, through `(−1)^(x·y)`) -/
def dot {n : ℕ} (x y : Fin n → Fin 2) : ℕ := ∑ i, (x i).val * (y i).val

/-- `H^{⊗n}` in closed form: `(W v) y = 2^{-n/2} ∑ₓ (−1)^{x·y} v x` -/
noncomputable def W {n : ℕ} (v : (Fin n → Fin 2) → ℂ) : (Fin n → Fin 2) → ℂ :=
  fun y => (Real.sqrt (2 ^ n) : ℂ)⁻¹ * ∑ x, (-1) ^ dot x y * v x
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- the character sum: `∑_y (−1)^{x·y}` is `2ⁿ` at `x = 0` and `0` otherwise -/
theorem char_sum {n : ℕ} (x : Fin n → Fin 2) :
    ∑ y : Fin n → Fin 2, (-1 : ℂ) ^ dot x y = if x = 0 then 2 ^ n else 0 := by
  simp_rw [dot, ← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val))]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, mul_zero, mul_one, pow_zero]
  split_ifs with hx
  · subst hx; norm_num
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : x i = 1 := by omega
    simp [this]

-- MILESTONE (optional: change or delete)
theorem neg_one_pow_dot_add {n : ℕ} (x y z : Fin n → Fin 2) :
    (-1 : ℂ) ^ dot x y * (-1) ^ dot x z = (-1) ^ dot x (y + z) := by
  simp only [dot, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, Pi.add_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize x i = a; generalize y i = b; generalize z i = c
  -- WHY: `(1 + 1 : Fin 2)` is `0` only definitionally; tell `simp`
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [show (1 + 1 : Fin 2) = 0 from rfl]

-- MILESTONE (optional: change or delete)
theorem dot_comm {n : ℕ} (x y : Fin n → Fin 2) : dot x y = dot y x := by
  simp [dot, mul_comm]

-- MILESTONE (optional: change or delete)
theorem bits_add_eq_zero {n : ℕ} (y z : Fin n → Fin 2) : y + z = 0 ↔ z = y := by
  constructor
  · intro h; funext i
    have := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at this
    revert this; generalize y i = a; generalize z i = b
    fin_cases a <;> fin_cases b <;> simp
  · rintro rfl; funext i; simp only [Pi.add_apply, Pi.zero_apply]; generalize z i = a; fin_cases a <;> rfl

-- BEGIN SPEC
theorem W_W {n : ℕ} (v : (Fin n → Fin 2) → ℂ) : W (W v) = v :=
-- END SPEC
  by
    have hsq : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹ := by
      rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
    funext y
    simp only [W, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    have key : ∀ z, ∑ x : Fin n → Fin 2, (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot x y *
        (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot z x * v z = if z = y then v y else 0 := by
      intro z
      have : ∀ x : Fin n → Fin 2, (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot x y *
          (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot z x * v z
          = ((Real.sqrt (2 ^ n) : ℂ)⁻¹ ^ 2 * v z) * (-1) ^ dot (y + z) x := by
        intro x
        rw [dot_comm z x, dot_comm (y + z) x, ← neg_one_pow_dot_add]; ring
      simp only [this, ← Finset.mul_sum, char_sum, bits_add_eq_zero, hsq]
      split_ifs with h
      · subst h; field_simp
      · simp
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

-- BEGIN SPEC
theorem bernstein_vazirani {n : ℕ} (s : Fin n → Fin 2) :
    W (fun x => (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot s x) = Pi.single s 1 :=
-- END SPEC
  by
    have hsq : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹ := by
      rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
    funext y
    have : ∀ x : Fin n → Fin 2, (-1 : ℂ) ^ dot x y * ((Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot s x)
        = (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot (y + s) x := by
      intro x
      rw [dot_comm s x, dot_comm (y + s) x, ← neg_one_pow_dot_add]; ring
    simp only [W, this, ← Finset.mul_sum, char_sum, bits_add_eq_zero, ← mul_assoc, ← sq, hsq,
      Pi.single_apply, eq_comm (a := s)]
    split_ifs
    · field_simp
    · simp

-- BEGIN SPEC
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Fin 2) → Fin 2)
    (hbal : (Finset.univ.filter fun x => f x = 0).card = (Finset.univ.filter fun x => f x = 1).card) :
    W (fun x => (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ (f x).val) 0 = 0 :=
-- END SPEC
  by
    have hdot : ∀ x : Fin n → Fin 2, dot x 0 = 0 := by simp [dot]
    -- balanced: the `+1` and `−1` terms cancel
    have hsum : ∑ x, (-1 : ℂ) ^ (f x).val = 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = 0)]
      have h0 : ∀ x ∈ Finset.univ.filter (fun x => f x = 0), (-1 : ℂ) ^ (f x).val = 1 := by
        intro x hx; simp at hx; simp [hx]
      have h1 : ∀ x ∈ Finset.univ.filter (fun x => ¬ f x = 0), (-1 : ℂ) ^ (f x).val = -1 := by
        intro x hx
        have : f x = 1 := by simp at hx; omega
        simp [this]
      have hset : (Finset.univ.filter fun x => ¬ f x = 0) = Finset.univ.filter fun x => f x = 1 := by
        ext x; simp; omega
      rw [Finset.sum_congr rfl h0, Finset.sum_congr rfl h1, Finset.sum_const, Finset.sum_const,
        hbal, hset]
      simp
    simp only [W, hdot, pow_zero, one_mul, ← Finset.mul_sum, hsum, mul_zero]

end H083

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything reduces to the character sum (milestone 1) plus "multiplying characters adds the strings" (milestone 2). Deutsch–Jozsa needs neither: at `y = 0` every `(−1)^{x·0}` is 1.
H2. Character sum: write `(−1)^{∑ᵢ xᵢyᵢ}` as `∏ᵢ (−1)^{xᵢyᵢ}`, then `Fintype.prod_sum` turns `∑_y ∏ᵢ` into `∏ᵢ ∑_{b : Fin 2}`; a factor with `xᵢ = 1` is `1 + (−1) = 0`. Milestone 2 is the same product trick, then 8 cases per coordinate. `W_W`: `funext y`, push the scalars in, swap the sums, regroup each term as `c · (−1)^{(y+z)·x}`.
H3. `simp_rw [dot, ← Finset.prod_pow_eq_pow_sum]; rw [← Fintype.prod_sum (fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val))]`. In `W_W`, after `simp only [W, Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]`, show each inner sum is `if z = y then v y else 0` and close with `Finset.sum_ite_eq'`. Deutsch–Jozsa: split `∑ₓ (−1)^{f x}` with `Finset.sum_filter_add_sum_filter_not _ (fun x => f x = 0)` into `card₀ − card₁`.
-/
