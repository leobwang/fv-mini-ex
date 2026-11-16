/- M114 | Polynomial interpolation: existence, and uniqueness by root counting | 15-20 min | Lagrange.interpolate, ExistsUnique, degree, roots, Finset.image, mathlib
GOAL
  Through n distinct nodes `v i` (i ∈ s, n = s.card) there is exactly one real polynomial of degree < n
  with prescribed values `r i`. Existence: Lagrange's interpolant. Uniqueness: count roots (a nonzero
  polynomial of natDegree < n cannot vanish at n distinct points).

REFERENCE
  #check Lagrange.degree_interpolate_lt     -- (r) (hv : Set.InjOn v s) : (interpolate s v r).degree < s.card
  #check Lagrange.eval_interpolate_at_node  -- (r) (hv) (hi : i ∈ s) : eval (v i) (interpolate s v r) = r i
  #check Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    -- p (t : Finset ℝ) (∀ x ∈ t, p.eval x = 0) (p.natDegree < t.card) : p = 0
  #check Polynomial.degree_sub_le           -- (p - q).degree ≤ max p.degree q.degree
  #check Polynomial.natDegree_lt_iff_degree_lt  -- p ≠ 0 → (p.natDegree < n ↔ p.degree < n)
  #check Finset.card_image_of_injOn         -- Set.InjOn f s → (s.image f).card = s.card
  example (P : ℕ → Prop) (h : P 0) (hu : ∀ m, P m → m = 0) : ∃! n, P n := ⟨0, h, hu⟩
  `∃! p, P p` means `∃ p, P p ∧ ∀ q, P q → q = p`. `Set.InjOn v s`: v is injective on s (distinct nodes).
  `p.degree : WithBot ℕ` (⊥ for p = 0), `p.natDegree : ℕ` (0 for p = 0). `ℝ[X]` needs `open Polynomial`.
BANNED: eq_interpolate, eq_interpolate_of_eval_eq, eq_interpolate_iff, interpolate_eq_iff_values_eq_on, eq_zero_of_degree_lt_of_eval_finset_eq_zero, eq_of_degree_sub_lt_of_eval_finset_eq, eq_of_degrees_lt_of_eval_finset_eq, eq_of_degree_le_of_eval_finset_eq, eq_zero_of_degree_lt_of_eval_index_eq_zero, eq_of_degree_sub_lt_of_eval_index_eq, eq_of_degrees_lt_of_eval_index_eq, eq_of_degree_le_of_eval_index_eq, eq_of_natDegree_lt_card_of_eval_eq, eq_of_natDegree_lt_card_of_eval_eq', funEquivDegreeLT
NOTE: `Lagrange.interpolate s v` is a linear map; `Lagrange.interpolate s v r` applies it to the values `r`.
-/
import Mathlib

open Polynomial

namespace M114

-- BEGIN SPEC
theorem interpolation_exists_unique {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hv : Set.InjOn v s) (r : ι → ℝ) :
    ∃! p : ℝ[X], p.degree < s.card ∧ ∀ i ∈ s, p.eval (v i) = r i :=
-- END SPEC
  by
    refine ⟨Lagrange.interpolate s v r, ⟨Lagrange.degree_interpolate_lt r hv,
      fun i hi => Lagrange.eval_interpolate_at_node r hv hi⟩, ?_⟩
    rintro q ⟨hdeg, hval⟩
    rw [← sub_eq_zero]
    set d := q - Lagrange.interpolate s v r
    by_contra hd
    have hdeg' : d.degree < s.card :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hdeg (Lagrange.degree_interpolate_lt r hv))
    apply hd
    -- WHY: count roots on the image `s.image v`, which has `s.card` points because `v` is injective on `s`.
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' d (s.image v)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [d, eval_sub, hval i hi, Lagrange.eval_interpolate_at_node r hv hi, sub_self]
    · rw [Finset.card_image_of_injOn hv, natDegree_lt_iff_degree_lt hd]
      exact hdeg'

end M114

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The witness is `Lagrange.interpolate s v r`. For uniqueness, `rintro q ⟨hdeg, hval⟩` and study
    `d := q - Lagrange.interpolate s v r`: after `rw [← sub_eq_zero]` the goal is `d = 0`; argue `by_contra hd`.
H2. Suppose `d ≠ 0`. Its degree is < s.card (`degree_sub_le` + `max_lt`), and it vanishes at every point
    of `s.image v`, a Finset with s.card elements because `v` is injective on `s`. Root counting says d = 0.
H3. `apply hd` (goal back to `d = 0`), then `apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' d (s.image v)`;
    roots: `intro x hx`, `obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx`, then `simp only [d, eval_sub,
    hval i hi, Lagrange.eval_interpolate_at_node r hv hi, sub_self]`; size: `rw [Finset.card_image_of_injOn hv,
    natDegree_lt_iff_degree_lt hd]`.
-/
