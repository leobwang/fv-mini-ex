/- H033 | Wilson's theorem in a finite field | 45-75 min | Finset.prod_involution, Field, Finset.erase, Nat.prime_def, mathlib
GOAL
  In any finite field `K`, the product of all nonzero elements is `-1`: pair each `x` with `x⁻¹`;
  only `1` and `-1` are their own inverses. Then a short warm-up (the `n ! + 1` trick from H029):
  the converse of Wilson's theorem over ℕ, if `2 ≤ n` and `n ∣ (n - 1)! + 1` then `n` is prime.

BANNED: FiniteField.prod_univ_units_id_eq_neg_one, ZMod.wilsons_lemma, ZMod.prod_Ico_one_prime, Nat.prime_iff_fac_equiv_neg_one, Nat.prime_of_fac_equiv_neg_one

GUIDE
  Entries R1–R37: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H033

/- SKELETON · sq_eq_one   (milestone; prove it FIRST; prod_rest uses it to rule out fixed points)
  1. Factor the equation:  have h' : (x - 1) * (x + 1) = 0                         R1
  2. One factor is zero; one goal per factor:                                       R2
  3. x - 1 = 0 gives x = 1, the left disjunct (Or.inl):                             R3
  4. x + 1 = 0 gives x = -1, the right disjunct (Or.inr):                           R4
-/
-- MILESTONE (optional: change or delete)
theorem sq_eq_one {K : Type*} [Field K] (x : K) (h : x * x = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1) * (x + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/- SKELETON · prod_rest   (milestone; prove it SECOND; wilson_field rewrites with it)
  1. Pair x with x⁻¹; four goals:                       R5 with g := fun x _ => x⁻¹
  2. In each goal, `intro` the element `a` and `ha`, then unpack `ha` to
       ha : a ≠ 0 ∧ ¬a = 1 ∧ ¬a = -1                     one simp only [...] at ha: R6, R7, R8, R9, R10
  3. a * a⁻¹ = 1:                                                                    R11 with ha.1
  4. fixed point (also intro `_` and heq : a⁻¹ = a; goal False):
       haa : a * a = 1 via a * a⁻¹                                                   R12 with rw [heq], R11
       sq_eq_one a haa gives a = 1 ∨ a = -1; each case contradicts ha.2.1 / ha.2.2  R2's rcases pattern
  5. a⁻¹ ∈ …: unpack with `at ha ⊢`, then split the three conjuncts:                 R6–R10, R14, R13 (twice)
       each left-over goal `a = 1` from h : a⁻¹ = 1 (and `a = -1` from h : a⁻¹ = -1)  R15 → R17
  6. a⁻¹⁻¹ = a:                                                                      R16
-/
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

/- SKELETON · wilson_field
  0. Prove the milestones sq_eq_one and prod_rest first (prod_rest is used in step 2).
  1. hsub : ({1, -1} : Finset K) ⊆ Finset.univ.erase 0:
       open the subset, unpack hx, substitute, close each membership with simp      R18, R9 at hx, R19
  2. Split off {1, -1} with hsub, replace the rest by 1 with the milestone, drop the 1:
       goal becomes ∏ x ∈ {1, -1}, x = -1                       R20, rw [prod_rest], R21
  3. Characteristic 2 or not:                                                        R22 on (1 : K) = -1
       pos: rw [← h1], then the product over {1, 1}                                  R23, R24 (simp)
       neg: the product over a pair, then ring                                       R25, ring
-/
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

/- SKELETON · wilson_converse
  1. Unfold primality; give 2 ≤ n, introduce the divisor m and hm : m ∣ n:          R26, R27
  2. Contradiction; hne : m ≠ 1 ∧ m ≠ n, goal False:                                 R28, R29
  3. Facts, in order (side goals 0 < n, m ≤ n - 1 by omega, R31):
       hm0 : 0 < m                                                                   R30
       hmn : m < n                                                                   R33 with R32
       h1  : m ∣ (n - 1).factorial                                                   R34
       h3  : m ∣ 1         from h1 and hm.trans h : m ∣ (n - 1).factorial + 1        R36 with R35
  4. m = 1 contradicts hne.1:                                                        R37
-/
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
H1. Split the nonzero elements into `{1, -1}` and the rest. On the rest, `x ↦ x⁻¹` pairs each element
    with a different one (a fixed point has `x * x = 1`, so `x = ±1` by `sq_eq_one`), so the rest
    multiplies to `1`. Mind characteristic 2, where `1 = -1`. The converse reuses H029: a divisor
    `1 < m < n` of `n` divides `(n - 1)!`, hence cannot divide `(n - 1)! + 1`.
H2. `sq_eq_one`: factor as `(x - 1) * (x + 1) = 0` and split with `mul_eq_zero` (R1–R4).
    `prod_rest`: `Finset.prod_involution` with `g := fun x _ => x⁻¹` (R5); in each of the four goals,
    unpack the membership with one `simp only` (R6–R10). `wilson_field`: build `hsub`, rewrite with
    `Finset.prod_sdiff` and `prod_rest`, then `by_cases` on `(1 : K) = -1` (R18–R25).
    Converse: `rw [Nat.prime_def]`, then `by_contra` on a divisor `m` and derive `m ∣ 1` (R26–R37).
H3. `have h' : (x - 1) * (x + 1) = 0 := by linear_combination h`.
    `refine Finset.prod_involution (fun x _ => x⁻¹) ?_ ?_ ?_ ?_`, and in each goal
    `simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, and_true, not_or] at ha`.
    `rw [← Finset.prod_sdiff hsub, prod_rest, one_mul]`; then `by_cases h1 : (1 : K) = -1`;
    if so `rw [← h1]; simp`, else `rw [Finset.prod_pair h1]; ring`.
    Converse: `(Nat.dvd_add_right (Nat.dvd_factorial hm0 _)).mp (hm.trans h) : m ∣ 1`.
-/
