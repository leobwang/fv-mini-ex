/- H033 | Wilson's theorem in a finite field | 45-75 min | Finset.prod_involution, Field, Finset.erase, Nat.prime_def, mathlib
GOAL
  In any finite field `K`, the product of all nonzero elements is `-1`: pair each `x` with `x⁻¹`;
  only `1` and `-1` are their own inverses. Then a short warm-up (the `n ! + 1` trick from H029):
  the converse of Wilson's theorem over ℕ, if `2 ≤ n` and `n ∣ (n - 1)! + 1` then `n` is prime.

REFERENCE
  #check Finset.prod_involution  -- given g, 4 goals: f a * f (g a) = 1; f a ≠ 1 → g a ≠ a; g a ∈ s; g (g a) = a.  ⇒ ∏ x ∈ s, f x = 1
  #check Finset.prod_sdiff   -- s₁ ⊆ s₂ → (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x
  #check Finset.prod_pair    -- a ≠ b → ∏ x ∈ {a, b}, f x = f a * f b
  #check Finset.mem_erase    -- a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s     (also `Finset.mem_sdiff`)
  #check mul_inv_cancel₀     -- a ≠ 0 → a * a⁻¹ = 1
  example {K : Type*} [Field K] (x : K) (h : x * x = 1) : (x - 1) * (x + 1) = 0 := by linear_combination h
  #check Nat.prime_def       -- p.Prime ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
  #check Nat.dvd_factorial   -- 0 < m → m ≤ n → m ∣ n.factorial
  #check Nat.dvd_add_right   -- k ∣ m → (k ∣ m + n ↔ k ∣ n)
  -- `Finset.univ`: all elements of a `Fintype`; `s.erase a` is `s` minus `a`; `s \ t` set difference; `x⁻¹` field inverse (`0⁻¹ = 0`).
BANNED: FiniteField.prod_univ_units_id_eq_neg_one, ZMod.wilsons_lemma, ZMod.prod_Ico_one_prime, Nat.prime_iff_fac_equiv_neg_one, Nat.prime_of_fac_equiv_neg_one
NOTE: In characteristic 2, `1 = -1`, so `{1, -1}` has one element; split on `(1 : K) = -1`.
-/
import Mathlib

namespace H033

-- MILESTONE (optional: change or delete)
theorem sq_eq_one {K : Type*} [Field K] (x : K) (h : x * x = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

-- MILESTONE (optional: change or delete)
theorem prod_rest {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    ∏ x ∈ (Finset.univ.erase (0 : K)) \ {1, -1}, x = 1 := by
  refine Finset.prod_involution (fun x _ => x⁻¹) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, and_true, not_or] at ha
    exact mul_inv_cancel₀ ha.1
  · intro a ha _ heq
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, and_true, not_or] at ha
    have haa : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [heq]
        _ = 1 := mul_inv_cancel₀ ha.1
    rcases sq_eq_one a haa with h | h
    · exact ha.2.1 h
    · exact ha.2.2 h
  · intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, and_true, not_or] at ha ⊢
    refine ⟨inv_ne_zero ha.1, fun h => ha.2.1 ?_, fun h => ha.2.2 ?_⟩
    · simpa using congrArg (·⁻¹) h
    · simpa using congrArg (·⁻¹) h
  · intro a _
    exact inv_inv a

-- BEGIN SPEC
theorem wilson_field {K : Type*} [Field K] [Fintype K] [DecidableEq K] :
    ∏ x ∈ (Finset.univ : Finset K).erase 0, x = -1 :=
-- END SPEC
  by
    have hsub : ({1, -1} : Finset K) ⊆ Finset.univ.erase 0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    rw [← Finset.prod_sdiff hsub, prod_rest, one_mul]
    -- WHY: in characteristic 2 the "pair" {1, -1} is a single element.
    by_cases h1 : (1 : K) = -1
    · rw [← h1]; simp
    · rw [Finset.prod_pair h1]; ring

-- BEGIN SPEC
theorem wilson_converse (n : ℕ) (h2 : 2 ≤ n) (h : n ∣ (n - 1).factorial + 1) : n.Prime :=
-- END SPEC
  by
    rw [Nat.prime_def]
    refine ⟨h2, fun m hm => ?_⟩
    by_contra hne
    push Not at hne
    have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by omega)
    have hmn : m < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) hne.2
    have h1 : m ∣ (n - 1).factorial := Nat.dvd_factorial hm0 (by omega)
    have h3 : m ∣ 1 := (Nat.dvd_add_right h1).mp (hm.trans h)
    exact hne.1 (Nat.dvd_one.mp h3)

end H033

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Split the nonzero elements into `{1, -1}` and the rest. On the rest, `x ↦ x⁻¹` has no fixed
    point, so the product of the rest is `1`. The converse reuses H029: a divisor `1 < m < n` of `n` divides `(n - 1)!`.
H2. `prod_rest`: `refine Finset.prod_involution (fun x _ => x⁻¹) ?_ ?_ ?_ ?_`; a fixed point `a = a⁻¹`
    gives `a * a = 1`, which `sq_eq_one` rules out. `wilson_field`: `rw [← Finset.prod_sdiff hsub, prod_rest, one_mul]`
    with `hsub : {1, -1} ⊆ univ.erase 0`. Converse: `rw [Nat.prime_def]`, then `by_contra` on a divisor `m`.
H3. After `prod_sdiff`: `by_cases h1 : (1 : K) = -1`; if so `rw [← h1]; simp`, else `rw [Finset.prod_pair h1]; ring`.
    Converse: `m ∣ (n - 1)!` by `Nat.dvd_factorial`, so `(Nat.dvd_add_right this).mp (hm.trans h) : m ∣ 1`.
    Membership goals: `simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, and_true, not_or] at ha ⊢`.
-/
