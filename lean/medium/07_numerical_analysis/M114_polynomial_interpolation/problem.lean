/- M114 | Polynomial interpolation: existence, and uniqueness by root counting | 15-20 min | Lagrange.interpolate, ExistsUnique, degree, roots, Finset.image, mathlib
GOAL
  Through n distinct nodes `v i` (i ∈ s, n = s.card) there is exactly one real polynomial of degree < n
  with prescribed values `r i`. Existence: Lagrange's interpolant. Uniqueness: count roots (a nonzero
  polynomial of natDegree < n cannot vanish at n distinct points).
BANNED: eq_interpolate, eq_interpolate_of_eval_eq, eq_interpolate_iff, interpolate_eq_iff_values_eq_on, eq_zero_of_degree_lt_of_eval_finset_eq_zero, eq_of_degree_sub_lt_of_eval_finset_eq, eq_of_degrees_lt_of_eval_finset_eq, eq_of_degree_le_of_eval_finset_eq, eq_zero_of_degree_lt_of_eval_index_eq_zero, eq_of_degree_sub_lt_of_eval_index_eq, eq_of_degrees_lt_of_eval_index_eq, eq_of_degree_le_of_eval_index_eq, eq_of_natDegree_lt_card_of_eval_eq, eq_of_natDegree_lt_card_of_eval_eq', funEquivDegreeLT
GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Polynomial

namespace M114

/- SKELETON · interpolation_exists_unique
  1. Witness `Lagrange.interpolate s v r`, its two properties, and the uniqueness goal:   R1, R2
       degree < ↑s.card                                                                   R3
       the values at the nodes, as `fun i hi => …`                                        R4
  2. Uniqueness: take `q` with `hdeg`, `hval`                                             R5
     `q = interpolant` → `q - interpolant = 0`, name the difference `d`                    R6, R7
     assume `hd : ¬d = 0` (R20 below needs `d ≠ 0`)                                        R8
  3. Prove first, while there is one goal:
       hdeg' : d.degree < ↑s.card                                                         R11 with R9, R10, R3
  4. Back to `d = 0`; count roots on the points `Finset.image v s` (a Finset ℝ)           R12, R13
  5. Roots goal: `intro x hx`, then turn `x` into `v i` with `hi : i ∈ s`                  R14 → R15
       evaluate with one `simp only [d, …]`: unfold d, split eval, use `hval i hi` and R4,
       cancel                                                                             R16, R17, R4, R18
  6. Size goal: image card → `s.card`, natDegree → degree (needs `hd`), then `hdeg'`       R19, R20
-/
-- BEGIN SPEC
theorem interpolation_exists_unique {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ)
    (hv : Set.InjOn v s) (r : ι → ℝ) :
    ∃! p : ℝ[X], p.degree < s.card ∧ ∀ i ∈ s, p.eval (v i) = r i :=
-- END SPEC
  sorry

end M114

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Existence is Mathlib's: the witness is `Lagrange.interpolate s v r`, and R3, R4 give its two
    properties. Uniqueness is root counting: if `q` also works, `d := q - Lagrange.interpolate s v r` has
    degree < s.card and vanishes at the s.card distinct points `v i`. Argue by contradiction (`d ≠ 0`),
    because turning `degree <` into `natDegree <` (R20) needs it.
H2. `refine ⟨Lagrange.interpolate s v r, ⟨?_, ?_⟩, ?_⟩`; then `rintro q ⟨hdeg, hval⟩`, `rw [← sub_eq_zero]`,
    `set d := q - Lagrange.interpolate s v r`, `by_contra hd`. The degree bound: `lt_of_le_of_lt
    (degree_sub_le _ _) (max_lt hdeg …)`. Then `apply hd` and count roots on `s.image v`, whose size is
    s.card because `v` is injective on `s` (`Finset.card_image_of_injOn hv`).
H3. `apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' d (s.image v)`;
    roots: `intro x hx`, `obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx`, then `simp only [d, eval_sub,
    hval i hi, Lagrange.eval_interpolate_at_node r hv hi, sub_self]`;
    size: `rw [Finset.card_image_of_injOn hv, natDegree_lt_iff_degree_lt hd]`, then `exact hdeg'`.
-/
