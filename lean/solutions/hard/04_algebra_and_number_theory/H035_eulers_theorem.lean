/- H035 | Euler's theorem | 45-75 min | Nat.totient, Finset.prod_image, bijection on residues, Nat.ModEq, mathlib
GOAL
  If `a` is coprime to `n`, then `a ^ φ(n) ≡ 1 (mod n)`, where `φ(n)` (`Nat.totient n`) counts the `k < n`
  coprime to `n`. Let `R` be that set of residues: `k ↦ a * k % n` maps `R` into `R` injectively, hence onto
  `R`, so `∏ R ≡ ∏_{k ∈ R} a * k = a ^ φ(n) * ∏ R (mod n)`, and `∏ R` is coprime to `n`, so it cancels.

REFERENCE
  example (n : ℕ) : n.totient = ((Finset.range n).filter n.Coprime).card := rfl  -- φ by definition
  #check Nat.totient_eq_card_coprime   -- n.totient = #{a ∈ range n | n.Coprime a}   (same fact, as a rewrite)
  #check Finset.card_image_of_injOn     -- Set.InjOn f ↑s → #(s.image f) = #s       (#s = s.card)
  #check Finset.eq_of_subset_of_card_le -- s ⊆ t → #t ≤ #s → s = t
  #check Finset.prod_image              -- Set.InjOn g ↑s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x)
  #check Finset.prod_nat_mod            -- (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n
  #check Nat.ModEq.cancel_left_of_coprime -- m.gcd c = 1 → c * a ≡ c * b [MOD m] → a ≡ b [MOD m]
  #check Nat.gcd_rec                    -- gcd m n = gcd (n % m) m
  #check Nat.coprime_prod_right_iff     -- x.Coprime (∏ i ∈ t, s i) ↔ ∀ i ∈ t, x.Coprime (s i)
  -- `Set.InjOn f ↑s`: `f` is injective on (the set of) finset `s`; `intro k hk j hj hkj` to prove one.
  -- `a ≡ b [MOD n]` is `Nat.ModEq n a b`, by definition `a % n = b % n` (`unfold Nat.ModEq`).
  -- `conv_lhs => rw [← h]` rewrites only the left-hand side of the goal.
BANNED: Nat.ModEq.pow_totient, ZMod.pow_totient, Nat.pow_totient_mod_eq_one, Nat.pow_totient_mod, Nat.pow_add_totient_mod_eq, Nat.pow_add_mul_totient_mod_eq, ZMod, ZMod.card_units_eq_totient, ZMod.unitsEquivCoprime, Units, pow_card_eq_one, pow_card_eq_one', orderOf_dvd_card, orderOf_dvd_natCard, ArithmeticFunction, ArithmeticFunction.carmichael, ArithmeticFunction.pow_carmichael, ArithmeticFunction.carmichael_dvd_totient, exact?, apply?, rw?, try?, hint
NOTE: `ZMod`, `Units` and `ArithmeticFunction` (Carmichael's `λ(n) ∣ φ(n)`) are banned: the point is the residue-permutation argument in plain ℕ.
-/
import Mathlib

namespace H035

open Finset

-- MILESTONE (optional: change or delete)
theorem mul_mod_mem (n a k : ℕ) (hn : 0 < n) (ha : Nat.Coprime a n)
    (hk : k ∈ (range n).filter (Nat.Coprime n)) : a * k % n ∈ (range n).filter (Nat.Coprime n) := by
  rw [mem_filter, mem_range] at hk ⊢
  refine ⟨Nat.mod_lt _ hn, ?_⟩
  rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
  exact Nat.Coprime.mul_right ha.symm hk.2

-- MILESTONE (optional: change or delete)
theorem mul_mod_inj (n a : ℕ) (ha : Nat.Coprime a n) :
    Set.InjOn (fun k => a * k % n) ↑((range n).filter (Nat.Coprime n)) := by
  intro k hk j hj hkj
  simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hk hj
  -- WHY: `a * k % n = a * j % n` is definitionally `a * k ≡ a * j [MOD n]`.
  have h := Nat.ModEq.cancel_left_of_coprime ha.symm (hkj : a * k ≡ a * j [MOD n])
  unfold Nat.ModEq at h
  rwa [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hj.1] at h

-- MILESTONE (optional: change or delete)
theorem image_mul_mod (n a : ℕ) (hn : 0 < n) (ha : Nat.Coprime a n) :
    ((range n).filter (Nat.Coprime n)).image (fun k => a * k % n) = (range n).filter (Nat.Coprime n) := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hx
    exact mul_mod_mem n a k hn ha hk
  · rw [card_image_of_injOn (mul_mod_inj n a ha)]

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
H1. Dispose of `n = 0` first (`φ 0 = 0`, so `simp`). Then name `R := (range n).filter (Nat.Coprime n)`: the milestones say `k ↦ a * k % n` is a bijection `R → R`.
H2. `mul_mod_mem`: `Nat.mod_lt`, and `gcd n (a * k % n) = gcd (a * k) n` by `Nat.gcd_comm` + `Nat.gcd_rec`. `mul_mod_inj`: the hypothesis `a * k % n = a * j % n` is literally `a * k ≡ a * j [MOD n]`; cancel `a`, then `Nat.mod_eq_of_lt` on both sides. `image_mul_mod`: `eq_of_subset_of_card_le` + `card_image_of_injOn`.
H3. With `himg := image_mul_mod n a hn ha` (state it before any `set R := …`), get `∏ k ∈ R, k = ∏ k ∈ R, a * k % n` by `conv_lhs => rw [← himg]` then `rw [prod_image (mul_mod_inj n a ha)]`. Then show `P * a ^ φ n ≡ P * 1 [MOD n]` (with `P = ∏ k ∈ R, k`) by a `calc` on `% n` using `prod_mul_distrib, prod_const, prod_nat_mod` (`prod_const` leaves `a ^ #R`, not `a ^ φ n`: bridge with `rw [Nat.totient_eq_card_coprime]` or the `rfl` in REFERENCE), and finish with `Nat.ModEq.cancel_left_of_coprime` and `Nat.coprime_prod_right_iff`.
-/
