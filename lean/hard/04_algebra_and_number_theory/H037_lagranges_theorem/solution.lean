/- H037 | Lagrange's theorem | 1-1.5 h | cosets, Finset.card, fibers, Nat.card, mathlib
GOAL
  Prove Lagrange's theorem `|H| ∣ |G|` by hand: the left cosets `gH` (as `Finset`s) partition `G` and each
  has `|H|` elements. Then derive that the order of every element divides `|G|`.
  (`Nat.card H` = number of elements of `H` viewed as a type; `orderOf g` = least `n > 0` with `g ^ n = 1`.)

BANNED: Subgroup.card_subgroup_dvd_card, Subgroup.card_mul_index, Subgroup.index_mul_card, Subgroup.groupEquivQuotientProdSubgroup, Subgroup.card_eq_card_quotient_mul_card_subgroup, Subgroup.index_dvd_card, Subgroup.card_dvd_of_le, Subgroup.card_dvd_of_injective, Subgroup.card_dvd_of_surjective, Subgroup.card_quotient_dvd_card, Subgroup.relIndex_mul_relIndex, Subgroup.relIndex_mul_index, Subgroup.relIndex_bot_left, Subgroup.relIndex_top_right, Subgroup.relIndex_dvd_card, Subgroup.relIndex, Subgroup.index, QuotientGroup, ⧸, MulAction, MulAction.card_orbit_mul_card_stabilizer_eq_card_group
BANNED: orderOf_dvd_card, orderOf_dvd_natCard, pow_card_eq_one, pow_card_eq_one', Group.exponent_dvd_nat_card, Group.exponent_dvd_card, Monoid.order_dvd_exponent, Monoid.exponent, ZMod.orderOf_dvd_card_sub_one
BANNED: Subgroup.card_comap_dvd_of_injective, Subgroup.card_map_dvd, Subgroup.card_range_dvd, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, Subgroup.IsComplement, Subgroup.IsComplement', Subgroup.exists_isComplement_left, Subgroup.exists_isComplement_right, Subgroup.exists_left_transversal_of_le, Subgroup.exists_right_transversal_of_le, Subgroup.IsComplement.card_mul, Subgroup.IsComplement.card_mul_card, Subgroup.IsComplement.card_left, Subgroup.IsComplement.card_right, MulAction.IsBlock, MulAction.isBlock_subgroup, MulAction.isBlock_subgroup', MulAction.IsBlock.ncard_dvd_card, Finset.card_dvd_card_mul_left, Finset.card_dvd_card_mul_right, Finset.card_dvd_card_smul_right, Finset.card_dvd_card_image₂_left, Finset.card_dvd_card_image₂_right
BANNED: Additive, Multiplicative, Additive.ofMul, Additive.toMul, Multiplicative.ofAdd, Multiplicative.toAdd, Subgroup.toAddSubgroup, Subgroup.toAddSubgroup', AddSubgroup.toSubgroup, AddSubgroup.toSubgroup', MonoidHom.toAdditive, AddMonoidHom.toMultiplicative, AddSubgroup, AddAction, QuotientAddGroup, AddSubgroup.card_addSubgroup_dvd_card, AddSubgroup.addGroupEquivQuotientProdAddSubgroup, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup, AddSubgroup.card_add_eq_card_addSubgroup_add_card_quotient, AddSubgroup.card_dvd_of_le, addOrderOf, addOrderOf_dvd_natCard, addOrderOf_dvd_card, addOrderOf_ofMul_eq_orderOf, orderOf_ofAdd_eq_addOrderOf, card_nsmul_eq_zero, card_nsmul_eq_zero', Nat.card_zmultiples, AddSubgroup.zmultiples, Finset.card_dvd_card_add_left, Finset.card_dvd_card_add_right, Finset.card_dvd_card_vadd_right
BANNED: exact?, apply?, try?, hint
GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H037

open Finset

-- MILESTONE (optional: change or delete)
/-- The left coset `g * H`, as the finset of all `x` with `g⁻¹ * x ∈ H`. -/
def coset {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [DecidablePred (· ∈ H)] (g : G) :
    Finset G :=
  univ.filter (fun x => g⁻¹ * x ∈ H)

/- SKELETON · coset_card   (milestone; prove it FIRST; lagrange_finset uses it for the fiber sizes)
  1. Describe the coset as an image, as a fact proved first:                          have
       this : coset H g = (univ.filter (· ∈ H)).image (g * ·)
     a. finset equation → membership `↔`:                                             R1
     b. unfold `coset` and the memberships: `simp only [coset, …]`                   R2, R3, R4
     c. split the `↔`:                                                                R5
     d. →: the witness is `g⁻¹ * x`; what is left is a group identity:                R6, R7
     e. ←: take the image membership apart, then simplify the hypothesis:             R8, R9
  2. rw [this], then count the image of an injective map:                             R10 with R11
-/
-- MILESTONE (optional: change or delete)
theorem coset_card {G : Type*} [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] (g : G) : #(coset H g) = #(univ.filter (· ∈ H)) := by
  have : coset H g = (univ.filter (· ∈ H)).image (g * ·) := by
    ext x
    simp only [coset, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      exact ⟨g⁻¹ * x, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [this, card_image_of_injective _ (mul_right_injective g)]

/- SKELETON · coset_eq_iff   (milestone; lagrange_finset uses it inside `simp` for the fibers)
  1. Unfold both cosets and the membership: `simp only [coset, …]`                    R2, R3
  2. Split the `↔`:                                                                   R5
  3. →: `x` lies in its own coset. State it as a `have` about the UNFOLDED finset, the
        left side of the equation `h` (`x ∈ univ.filter (fun y => x⁻¹ * y ∈ H)`), not
        `x ∈ coset H x`: `rw [h] at` only finds the unfolded text:                    have
        a. prove it: unfold the membership, then `x⁻¹ * x ∈ H`:                       R2, R3, R12
        b. move that fact along the equation, then simplify:                          R13, R9
  4. ←: finset equation → membership of a FRESH `y`, unfold again:                    R1, R2, R3
        split the `↔`:                                                                R5
        each half: `simpa [mul_assoc] using` a product of two members of `H`, with
        the coset hypothesis on the LEFT so the middle factors cancel:                R9, R16, R17
          the → half: `(g⁻¹ * x) * (x⁻¹ * y)`, the two hypotheses multiplied:         R14
          the ← half: `(g⁻¹ * x)⁻¹ * (g⁻¹ * y)`, the coset hypothesis inverted first: R15 → R14
-/
-- MILESTONE (optional: change or delete)
theorem coset_eq_iff {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [DecidablePred (· ∈ H)]
    (g x : G) : coset H x = coset H g ↔ x ∈ coset H g := by
  simp only [coset, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have : x ∈ univ.filter (fun y => x⁻¹ * y ∈ H) := by simp [H.one_mem]
    rw [h] at this
    simpa using this
  · intro hx
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hy
      simpa [mul_assoc] using H.mul_mem hx hy
    · intro hy
      simpa [mul_assoc] using H.mul_mem (H.inv_mem hx) hy

/- SKELETON · lagrange_finset   (milestone; lagrange uses it)
  0. Prove the milestones coset_card and coset_eq_iff first (both used in step 2).
  1. |G| as a sum over the fibers of `coset H`, with `f := coset H`, `s := univ`:       R18 → R19
  2. Every fiber has |H| elements, as a fact proved first:                            have
       hfib : ∀ c ∈ univ.image (coset H),
                #(univ.filter (fun x => coset H x = c)) = #(univ.filter (· ∈ H))
     write `c` as `coset H g`:                                                        R20
     rw [← coset_card H g], then compare the finsets:                                 R21, R1
     the fiber of `coset H g` is `coset H g`: `simp [coset_eq_iff]`
  3. The sum of a constant:                                                           R22
  4. Close `|H| ∣ (number of cosets) * |H|`:                                          R23
-/
-- MILESTONE (optional: change or delete)
theorem lagrange_finset {G : Type*} [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] : #(univ.filter (· ∈ H)) ∣ Fintype.card G := by
  rw [← card_univ, card_eq_sum_card_image (coset H) univ]
  -- WHY: each fiber `{x | coset H x = c}` is the coset `c` itself, so all fibers have size `|H|`.
  have hfib : ∀ c ∈ univ.image (coset H),
      #(univ.filter (fun x => coset H x = c)) = #(univ.filter (· ∈ H)) := by
    intro c hc
    obtain ⟨g, -, rfl⟩ := mem_image.mp hc
    rw [← coset_card H g]
    congr 1
    ext x
    simp [coset_eq_iff]
  rw [sum_const_nat hfib]
  exact dvd_mul_left _ _

/- SKELETON · lagrange
  0. Uses the milestone lagrange_finset (step 3).
  1. Decidability first, then a `Fintype G` from `Finite G`:                          R24, R25
  2. `Nat.card` → `Fintype.card` (once for `↥H`, once for `G`), subtype → filter:     R26, R26, R27
  3. The goal is now lagrange_finset's statement:                                     exact
-/
-- BEGIN SPEC
theorem lagrange {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Nat.card H ∣ Nat.card G :=
-- END SPEC
  by
    classical
    haveI := Fintype.ofFinite G
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact lagrange_finset H

/- SKELETON · orderOf_dvd
  1. The order of `g` is the size of the cyclic subgroup `Subgroup.zpowers g`:         R28
  2. Apply lagrange to that subgroup:                                                 exact
-/
-- BEGIN SPEC
theorem orderOf_dvd {G : Type*} [Group G] [Finite G] (g : G) : orderOf g ∣ Nat.card G :=
-- END SPEC
  by
    rw [← Nat.card_zpowers]
    exact lagrange _

end H037

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones in order. `coset_card`: a coset is the image of `H` under `x ↦ g * x`, an injective
    map. `coset_eq_iff`: two cosets are equal exactly when they share a point. `lagrange_finset`: group the
    elements of `G` by their coset; the fiber over a coset is that coset. `lagrange` only translates `Nat.card`
    into finset counts, and `orderOf_dvd` applies it to `Subgroup.zpowers g`.
H2. `coset_card`: `have : coset H g = (univ.filter (· ∈ H)).image (g * ·)` by `ext x` (R1–R9: witness
    `g⁻¹ * x`, close with `group`), then `rw [this, card_image_of_injective _ (mul_right_injective g)]`.
    `coset_eq_iff`: →: `x` is in its own coset, stated unfolded as `x ∈ univ.filter (fun y => x⁻¹ * y ∈ H)`
    (by `simp [H.one_mem]`), then `rw [h] at this`; ←: `ext y` and `simpa [mul_assoc] using H.mul_mem …`. `lagrange_finset`: `rw [← card_univ, card_eq_sum_card_image (coset H) univ]`,
    every fiber has size `|H|`, then `sum_const_nat`.
H3. `hfib : ∀ c ∈ univ.image (coset H), #(univ.filter (fun x => coset H x = c)) = #(univ.filter (· ∈ H))`,
    by `obtain ⟨g, -, rfl⟩ := mem_image.mp hc`, `rw [← coset_card H g]`, `congr 1`, `ext x`, `simp [coset_eq_iff]`;
    then `rw [sum_const_nat hfib]` and `dvd_mul_left`. `lagrange`: `classical`, `haveI := Fintype.ofFinite G`,
    `rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
    `orderOf_dvd`: `rw [← Nat.card_zpowers]`, then `lagrange`.
-/
