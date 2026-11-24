/- H036 | σ is multiplicative | 45-60 min | Nat.divisors, Finset.sum_image, InjOn, coprimality, mathlib
GOAL
  Let `σ(k) = ∑_{d ∣ k} d` be the sum of the divisors of `k`. For coprime `m, n`, prove `σ(mn) = σ(m)σ(n)`:
  the divisors of `mn` are exactly the products `d * e` with `d ∣ m`, `e ∣ n`, each arising once
  (`Nat.divisors k` is the finset of divisors of `k`; it is `∅` for `k = 0`).

REFERENCE
  #check Nat.mem_divisors     -- n ∈ m.divisors ↔ n ∣ m ∧ m ≠ 0
  #check Finset.mem_product   -- p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t      (`×ˢ`: product of finsets)
  #check Finset.sum_image     -- Set.InjOn g ↑s → ∑ x ∈ s.image g, f x = ∑ x ∈ s, f (g x)
  #check Finset.sum_mul_sum   -- (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j
  #check Finset.sum_product   -- ∑ x ∈ s ×ˢ t, f x = ∑ x ∈ s, ∑ y ∈ t, f (x, y)
  #check Nat.Coprime.gcd_mul  -- (k : ℕ) (h : m.Coprime n) : k.gcd (m * n) = k.gcd m * k.gcd n
  #check Nat.gcd_eq_left      -- m ∣ n → m.gcd n = m
  #check Nat.Coprime.dvd_of_dvd_mul_right -- k.Coprime n → k ∣ m * n → k ∣ m
  #check Nat.Coprime.coprime_dvd_left     -- m ∣ k → k.Coprime n → m.Coprime n   (also `_right`)
  -- `Set.InjOn f ↑s`: `f` is injective on finset `s`; open with `rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq`.
BANNED: Nat.Coprime.sum_divisors_mul, Nat.Coprime.divisors_mul, Nat.divisors_mul, Nat.Coprime.card_divisors_mul, Nat.Coprime.mul_injOn_divisors, Nat.divisorsHom, Finset.nat_divisors_prod, Nat.sum_divisors, ArithmeticFunction, ArithmeticFunction.isMultiplicative_sigma, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime, ArithmeticFunction.sigma_apply, exact?, apply?, rw?, try?, hint
-/
import Mathlib

namespace H036

open Finset

-- MILESTONE (optional: change or delete)
theorem divisors_eq (m n : ℕ) (h : m.Coprime n) :
    (m * n).divisors = (m.divisors ×ˢ n.divisors).image (fun p => p.1 * p.2) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem mul_inj (m n : ℕ) (h : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(m.divisors ×ˢ n.divisors) := by
  sorry

-- BEGIN SPEC
theorem sigma_mul (m n : ℕ) (h : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * (∑ d ∈ n.divisors, d) :=
-- END SPEC
  sorry

end H036

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. With both milestones the main theorem is one `rw` chain: reindex the left sum over `m.divisors ×ˢ n.divisors`, then split the right-hand product of sums into a double sum.
H2. Coprimality does its work in two places only: the gcd witnesses in `divisors_eq` and injectivity in `mul_inj` (without it, `2 * 2 = 4 * 1` with `m = n = 4`). `divisors_eq`: `ext d`, `simp only [mem_image, mem_product, Nat.mem_divisors, Prod.exists]`. For `d ∣ m * n`, the witnesses are `(d.gcd m, d.gcd n)`: their product is `d.gcd (m * n) = d`. `mul_inj`: from `a * b = a' * b'`, `a` is coprime to `b'` (it divides `m`, `b'` divides `n`), so `a ∣ a'`; symmetrically `a' ∣ a`.
H3. `divisors_eq` key line: `rw [← Nat.Coprime.gcd_mul d h, Nat.gcd_eq_left hd]`. `mul_inj`: `(h.coprime_dvd_left hab.1.1).coprime_dvd_right hab'.2.1 |>.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a b)`, then `Nat.dvd_antisymm` and `Nat.eq_of_mul_eq_mul_left`. Main: `rw [divisors_eq m n h, sum_image (mul_inj m n h), sum_mul_sum, sum_product]`.
-/
