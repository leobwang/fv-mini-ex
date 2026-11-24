/- H035 | Euler's theorem | 45-75 min | Nat.totient, Finset.prod_image, bijection on residues, Nat.ModEq, mathlib
GOAL
  If `a` is coprime to `n`, then `a ^ φ(n) ≡ 1 (mod n)`, where `φ(n)` (`Nat.totient n`) counts the `k < n`
  coprime to `n`. Let `R` be that set of residues: `k ↦ a * k % n` maps `R` into `R` injectively, hence onto
  `R`, so `∏ R ≡ ∏_{k ∈ R} a * k = a ^ φ(n) * ∏ R (mod n)`, and `∏ R` is coprime to `n`, so it cancels.
BANNED: Nat.ModEq.pow_totient, ZMod.pow_totient, Nat.pow_totient_mod_eq_one, Nat.pow_totient_mod, Nat.pow_add_totient_mod_eq, Nat.pow_add_mul_totient_mod_eq, ZMod, ZMod.card_units_eq_totient, ZMod.unitsEquivCoprime, Units, pow_card_eq_one, pow_card_eq_one', orderOf_dvd_card, orderOf_dvd_natCard, ArithmeticFunction, ArithmeticFunction.carmichael, ArithmeticFunction.pow_carmichael, ArithmeticFunction.carmichael_dvd_totient, exact?, apply?, rw?, try?, hint
GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H035

open Finset

/- SKELETON · mul_mod_mem   (MILESTONE 1: used in MILESTONE 3's inclusion goal)
  1. Unpack the membership in `hk` and in the goal at once:                     R1, R2
       hk : k < n ∧ n.Coprime k        goal: a * k % n < n ∧ n.Coprime (a * k % n)
  2. Prove the first half from `hn`, keep the second as the goal:               R3
  3. `Coprime` → `gcd … = 1`, then remove the `% n` inside the gcd:              R4, R5, R6
       goal: n.gcd (a * k) = 1
  4. `n` is coprime to `a` (flip `ha`) and to `k` (second half of `hk`):         R7, R8
-/
-- MILESTONE (optional: change or delete)
theorem mul_mod_mem (n a k : ℕ) (hn : 0 < n) (ha : Nat.Coprime a n)
    (hk : k ∈ (range n).filter (Nat.Coprime n)) : a * k % n ∈ (range n).filter (Nat.Coprime n) := by
  rw [mem_filter, mem_range] at hk ⊢
  refine ⟨Nat.mod_lt _ hn, ?_⟩
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
  exact Nat.Coprime.mul_right ha.symm hk.2

/- SKELETON · mul_mod_inj   (MILESTONE 2: used in MILESTONE 3 and in `euler`'s reindexing)
  1. Introduce two elements of R and the equation of their images:              R9
       hkj : (fun k => a * k % n) k = (fun k => a * k % n) j
  2. Turn `hk`, `hj` into `k < n ∧ …`, `j < n ∧ …` (one `simp only […] at hk hj`):  R10, R11, R2
  3. Read `hkj` as `a * k ≡ a * j [MOD n]` and cancel `a`; the lemma wants
     `n.gcd a = 1`, so pass `ha` flipped:                                        R12, R7, R13
       h : k ≡ j [MOD n]
  4. Unfold `h`, drop `% n` on both sides (k, j < n), close:                     R14, R15, R16
-/
-- MILESTONE (optional: change or delete)
theorem mul_mod_inj (n a : ℕ) (ha : Nat.Coprime a n) :
    Set.InjOn (fun k => a * k % n) ↑((range n).filter (Nat.Coprime n)) := by
  intro k hk j hj hkj
  simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hk hj
  -- WHY: `a * k % n = a * j % n` is definitionally `a * k ≡ a * j [MOD n]`.
  have h := Nat.ModEq.cancel_left_of_coprime ha.symm (hkj : a * k ≡ a * j [MOD n])
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hj.1] at h

/- SKELETON · image_mul_mod   (MILESTONE 3: uses MILESTONES 1 and 2; used in `euler`)
  1. Two finsets are equal by inclusion and size:                               R17
  2. Inclusion: an element of the image is `a * k % n` with `k ∈ R`:            R18, R19 → R20
       then MILESTONE 1
  3. Size: the image has #R elements by MILESTONE 2; `rw` then closes `#R ≤ #R`:  R21
-/
-- MILESTONE (optional: change or delete)
theorem image_mul_mod (n a : ℕ) (hn : 0 < n) (ha : Nat.Coprime a n) :
    ((range n).filter (Nat.Coprime n)).image (fun k => a * k % n) = (range n).filter (Nat.Coprime n) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact mul_mod_mem n a k hn ha hk
  · rw [card_image_of_injOn (mul_mod_inj n a ha)]

/- SKELETON · euler   (uses MILESTONES 2 and 3: prove them first)
  1. Split off `n = 0`; there `simp` closes the goal:                            R22, then simp (R23, R24)
  2. himg : image (fun k => a * k % n) R = R      MILESTONE 3, stated BEFORE step 3
  3. Name R := (range n).filter (Nat.Coprime n) everywhere:                      R25
  4. hprod : ∏ k ∈ R, k = ∏ k ∈ R, a * k % n
       rewrite only the left R with `← himg`, then reindex with MILESTONE 2:     R26, R27
  5. hP : Nat.Coprime n (∏ k ∈ R, k)       every factor is coprime to n:        R28, R1
  6. key : (∏ k ∈ R, k) * a ^ Nat.totient n ≡ (∏ k ∈ R, k) * 1 [MOD n]
       first  hpow : ∏ k ∈ R, a * k = a ^ Nat.totient n * ∏ k ∈ R, k          R29, R30, R31
       then a `calc` on `% n` (R34) with three steps:
         … % n = (∏ k ∈ R, a * k) % n            hpow, R32
             _ = (∏ k ∈ R, a * k % n) % n        R33
             _ = (∏ k ∈ R, k) * 1 % n            hprod (right to left), R32
  7. Cancel the product from `key` using `hP`:                                   R13
-/
-- BEGIN SPEC
theorem euler (n a : ℕ) (ha : Nat.Coprime a n) : a ^ Nat.totient n ≡ 1 [MOD n] :=
-- END SPEC
  by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have himg := image_mul_mod n a hn ha
    set R := (range n).filter (Nat.Coprime n) with hR
    have hprod : ∏ k ∈ R, k = ∏ k ∈ R, a * k % n := by
      conv_lhs => rw [← himg]
      rw [prod_image (mul_mod_inj n a ha)]
    have hP : Nat.Coprime n (∏ k ∈ R, k) :=
      Nat.coprime_prod_right_iff.mpr fun k hk => (mem_filter.mp hk).2
    have key : (∏ k ∈ R, k) * a ^ Nat.totient n ≡ (∏ k ∈ R, k) * 1 [MOD n] := by
      have hpow : ∏ k ∈ R, a * k = a ^ Nat.totient n * ∏ k ∈ R, k := by
        rw [prod_mul_distrib, prod_const, Nat.totient_eq_card_coprime]
      calc (∏ k ∈ R, k) * a ^ Nat.totient n % n = (∏ k ∈ R, a * k) % n := by rw [hpow, mul_comm]
        _ = (∏ k ∈ R, a * k % n) % n := prod_nat_mod _ _ _
        _ = (∏ k ∈ R, k) * 1 % n := by rw [← hprod, mul_one]
    exact Nat.ModEq.cancel_left_of_coprime hP key

end H035

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones in order: `k ↦ a * k % n` maps `R` into `R` (1), is injective on `R` (2), hence maps
    `R` onto `R` (3). `euler` then compares two products over `R`. Dispose of `n = 0` first (`φ 0 = 0`,
    so `simp`); everything else needs `0 < n`.
H2. MILESTONE 1: unpack with `Finset.mem_filter, Finset.mem_range`; `gcd n (a * k % n) = gcd n (a * k)` by
    `Nat.gcd_comm` and `← Nat.gcd_rec`; then `Nat.Coprime.mul_right`. MILESTONE 2: the image equation is
    literally `a * k ≡ a * j [MOD n]`; cancel `a` with `Nat.ModEq.cancel_left_of_coprime ha.symm`, then
    `Nat.mod_eq_of_lt` on both sides. MILESTONE 3: `Finset.eq_of_subset_of_card_le`, `Finset.mem_image`,
    `Finset.card_image_of_injOn`. `euler`: with `P = ∏ k ∈ R, k`, show `P = ∏ k ∈ R, a * k % n` (reindex),
    then `P * a ^ φ n ≡ P * 1 [MOD n]` by a `calc` on `% n`, then cancel `P` (coprime to `n` by
    `Nat.coprime_prod_right_iff`).
H3. `have himg := image_mul_mod n a hn ha` BEFORE `set R := (range n).filter (Nat.Coprime n) with hR`;
    `hprod` is `conv_lhs => rw [← himg]` then `rw [Finset.prod_image (mul_mod_inj n a ha)]`; `hpow` is
    `rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.totient_eq_card_coprime]`; the middle `calc` step is
    `Finset.prod_nat_mod _ _ _`; finish with `exact Nat.ModEq.cancel_left_of_coprime hP key`.
-/
