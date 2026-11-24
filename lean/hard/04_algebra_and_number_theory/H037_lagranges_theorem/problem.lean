/- H037 | Lagrange's theorem | 1-1.5 h | cosets, Finset.card, fibers, Nat.card, mathlib
GOAL
  Prove Lagrange's theorem `|H| ∣ |G|` by hand: the left cosets `gH` (as `Finset`s) partition `G` and each
  has `|H|` elements. Then derive that the order of every element divides `|G|`.
  (`Nat.card H` = number of elements of `H` viewed as a type; `orderOf g` = least `n > 0` with `g ^ n = 1`.)

REFERENCE
  #check Finset.card_eq_sum_card_image  -- #s = ∑ b ∈ s.image f, #{a ∈ s | f a = b}   (`#s` is `s.card`)
  #check Finset.sum_const_nat           -- (∀ x ∈ s, f x = m) → ∑ x ∈ s, f x = #s * m
  #check Finset.card_image_of_injective -- (s) (Injective f) : #(s.image f) = #s
  #check mul_right_injective            -- (a : G) : Injective (fun x => a * x)
  #check Fintype.ofFinite               -- (α) [Finite α] : Fintype α;  use as `haveI := Fintype.ofFinite G`
  #check Nat.card_eq_fintype_card       -- Nat.card α = Fintype.card α
  #check Fintype.card_subtype           -- Fintype.card {x // p x} = #{x | p x}   (`#{x | p x}` filters `univ`)
  #check Nat.card_zpowers               -- Nat.card (Subgroup.zpowers a) = orderOf a
  -- `H.one_mem`, `H.mul_mem hx hy`, `H.inv_mem hx`; the `group` tactic proves group identities; `classical` gives decidability
BANNED: Subgroup.card_subgroup_dvd_card, Subgroup.card_mul_index, Subgroup.index_mul_card, Subgroup.groupEquivQuotientProdSubgroup, Subgroup.card_eq_card_quotient_mul_card_subgroup, Subgroup.index_dvd_card, Subgroup.card_dvd_of_le, Subgroup.card_dvd_of_injective, Subgroup.card_dvd_of_surjective, Subgroup.card_quotient_dvd_card, Subgroup.relIndex_mul_relIndex, Subgroup.relIndex_mul_index, Subgroup.relIndex_bot_left, Subgroup.relIndex_top_right, Subgroup.relIndex_dvd_card, Subgroup.relIndex, Subgroup.index, QuotientGroup, ⧸, MulAction, MulAction.card_orbit_mul_card_stabilizer_eq_card_group
BANNED: orderOf_dvd_card, orderOf_dvd_natCard, pow_card_eq_one, pow_card_eq_one', Group.exponent_dvd_nat_card, Group.exponent_dvd_card, Monoid.order_dvd_exponent, Monoid.exponent, ZMod.orderOf_dvd_card_sub_one
BANNED: Subgroup.card_comap_dvd_of_injective, Subgroup.card_map_dvd, Subgroup.card_range_dvd, Subgroup.card_mul_eq_card_subgroup_mul_card_quotient, Subgroup.IsComplement, Subgroup.IsComplement', Subgroup.exists_isComplement_left, Subgroup.exists_isComplement_right, Subgroup.exists_left_transversal_of_le, Subgroup.exists_right_transversal_of_le, Subgroup.IsComplement.card_mul, Subgroup.IsComplement.card_mul_card, Subgroup.IsComplement.card_left, Subgroup.IsComplement.card_right, MulAction.IsBlock, MulAction.isBlock_subgroup, MulAction.isBlock_subgroup', MulAction.IsBlock.ncard_dvd_card, Finset.card_dvd_card_mul_left, Finset.card_dvd_card_mul_right, Finset.card_dvd_card_smul_right, Finset.card_dvd_card_image₂_left, Finset.card_dvd_card_image₂_right
BANNED: Additive, Multiplicative, Additive.ofMul, Additive.toMul, Multiplicative.ofAdd, Multiplicative.toAdd, Subgroup.toAddSubgroup, Subgroup.toAddSubgroup', AddSubgroup.toSubgroup, AddSubgroup.toSubgroup', MonoidHom.toAdditive, AddMonoidHom.toMultiplicative, AddSubgroup, AddAction, QuotientAddGroup, AddSubgroup.card_addSubgroup_dvd_card, AddSubgroup.addGroupEquivQuotientProdAddSubgroup, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup, AddSubgroup.card_add_eq_card_addSubgroup_add_card_quotient, AddSubgroup.card_dvd_of_le, addOrderOf, addOrderOf_dvd_natCard, addOrderOf_dvd_card, addOrderOf_ofMul_eq_orderOf, orderOf_ofAdd_eq_addOrderOf, card_nsmul_eq_zero, card_nsmul_eq_zero', Nat.card_zmultiples, AddSubgroup.zmultiples, Finset.card_dvd_card_add_left, Finset.card_dvd_card_add_right, Finset.card_dvd_card_vadd_right
BANNED: exact?, apply?, try?, hint
NOTE: quotients `G ⧸ H`, indices, group actions, complements and the additive (`Additive G`) twins are banned: count cosets as `Finset`s yourself. You need none of the banned names.
-/
import Mathlib

namespace H037

open Finset

-- MILESTONE (optional: change or delete)
/-- The left coset `g * H`, as the finset of all `x` with `g⁻¹ * x ∈ H`. -/
def coset {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [DecidablePred (· ∈ H)] (g : G) :
    Finset G :=
  univ.filter (fun x => g⁻¹ * x ∈ H)

-- MILESTONE (optional: change or delete)
theorem coset_card {G : Type*} [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] (g : G) : #(coset H g) = #(univ.filter (· ∈ H)) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem coset_eq_iff {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [DecidablePred (· ∈ H)]
    (g x : G) : coset H x = coset H g ↔ x ∈ coset H g := by
  sorry

-- MILESTONE (optional: change or delete)
theorem lagrange_finset {G : Type*} [Group G] [Fintype G] [DecidableEq G] (H : Subgroup G)
    [DecidablePred (· ∈ H)] : #(univ.filter (· ∈ H)) ∣ Fintype.card G := by
  sorry

-- BEGIN SPEC
theorem lagrange {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Nat.card H ∣ Nat.card G :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem orderOf_dvd {G : Type*} [Group G] [Finite G] (g : G) : orderOf g ∣ Nat.card G :=
-- END SPEC
  sorry

end H037

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `coset H g` is the image of `{x | x ∈ H}` under `x ↦ g * x`, and two cosets are equal exactly when they share a point. Group the elements of `G` by their coset.
H2. `rw [← card_univ, card_eq_sum_card_image (coset H) univ]`: every fiber `{x | coset H x = c}` is `c` itself (by `coset_eq_iff`), whose card is `|H|`, so `sum_const_nat` makes the sum `#(image) * |H|`. For the `Finite`/`Nat.card` version: `classical`, `haveI := Fintype.ofFinite G`, then `rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
H3. `coset_card`: show `coset H g = (univ.filter (· ∈ H)).image (g * ·)` by `ext x` (witness `g⁻¹ * x`, close with `group`), then `card_image_of_injective _ (mul_right_injective g)`. `orderOf_dvd`: `rw [← Nat.card_zpowers]; exact lagrange _`.
-/
