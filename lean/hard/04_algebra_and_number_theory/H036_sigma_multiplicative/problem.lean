/- H036 | σ is multiplicative | 45-60 min | Nat.divisors, Finset.sum_image, InjOn, coprimality, mathlib
GOAL
  Let `σ(k) = ∑_{d ∣ k} d` be the sum of the divisors of `k`. For coprime `m, n`, prove `σ(mn) = σ(m)σ(n)`:
  the divisors of `mn` are exactly the products `d * e` with `d ∣ m`, `e ∣ n`, each arising once
  (`Nat.divisors k` is the finset of divisors of `k`; it is `∅` for `k = 0`).

BANNED: Nat.Coprime.sum_divisors_mul, Nat.Coprime.divisors_mul, Nat.divisors_mul, Nat.Coprime.card_divisors_mul, Nat.Coprime.mul_injOn_divisors, Nat.divisorsHom, Finset.nat_divisors_prod, Nat.sum_divisors, ArithmeticFunction, ArithmeticFunction.isMultiplicative_sigma, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime, ArithmeticFunction.sigma_apply, exact?, apply?, rw?, try?, hint

GUIDE
  Entries R1–R34: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H036

open Finset

/- SKELETON · divisors_eq   (milestone; prove it FIRST; sigma_mul uses it in step 1)
  1. Finset equality → membership of an arbitrary `d`:                                  R1
  2. Unfold every membership in one `simp only [mem_image, mem_product,
     Nat.mem_divisors, Prod.exists]`:                                                   R2, R3, R4, R5
       ⊢ d ∣ m * n ∧ m * n ≠ 0 ↔ ∃ a b, ((a ∣ m ∧ m ≠ 0) ∧ b ∣ n ∧ n ≠ 0) ∧ a * b = d
  3. Split the `↔`:                                                                     R6
  4. mp: introduce `hd : d ∣ m * n` and `hmn : m * n ≠ 0`:                              R7
     give the witnesses `d.gcd m`, `d.gcd n` and their four membership facts:           R9 with R10, R11
     what is left, `d.gcd m * d.gcd n = d`, is the coprime gcd split:                   R12 → R13
  5. mpr: introduce `a b` and the facts, substituting `d := a * b`:                     R8
     then `⟨_, _⟩` for `a * b ∣ m * n ∧ m * n ≠ 0`:                                      R14, R15
-/
-- MILESTONE (optional: change or delete)
theorem divisors_eq (m n : ℕ) (h : m.Coprime n) :
    (m * n).divisors = (m.divisors ×ˢ n.divisors).image (fun p => p.1 * p.2) := by
  sorry

/- SKELETON · mul_inj   (milestone; prove it SECOND; sigma_mul uses it in step 2)
  1. Open `Set.InjOn`, splitting both pairs: `⟨a, b⟩ hab ⟨a', b'⟩ hab' heq`:              R16
  2. Clean the memberships `at hab hab'`, so `hab.1.1 : a ∣ m`, `hab.2.1 : b ∣ n`, …:    R17, R18, R19, R4
  3. Evaluate the function in `heq`, giving `heq : a * b = a' * b'`:                     R20
  4. have h1 : a ∣ a'   (`a` is coprime to `b'`, and `a ∣ a' * b'`):                    R21 → R22 → R23
       the divisibility `a ∣ a' * b'` is `a ∣ a * b` moved along `heq`:                 R24, R25 (W3)
     have h2 : a' ∣ a   the same with the primed and unprimed names swapped (`heq.symm`)
  5. `a = a'`, then substitute it away:                                                 R26, R27
  6. have ha0 : 0 < a   (a divisor of `m ≠ 0`):                                          R29 with R28
  7. Close `(a, b) = (a, b')`; the second component cancels `a`:                         R31 with R30
-/
-- MILESTONE (optional: change or delete)
theorem mul_inj (m n : ℕ) (h : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(m.divisors ×ˢ n.divisors) := by
  sorry

/- SKELETON · sigma_mul
  0. Prove the milestones divisors_eq and mul_inj first (used in steps 1 and 2).
  1. Replace `(m * n).divisors` by the image of `m.divisors ×ˢ n.divisors`:            rw [divisors_eq m n h]
  2. Reindex the left sum over the pairs, with injectivity from mul_inj m n h:          R32
  3. The right side, a product of two sums, becomes a double sum:                       R33
  4. The left side, a sum over pairs, becomes a double sum; both sides now agree
     and `rw` closes the goal with `rfl`:                                               R34
-/
-- BEGIN SPEC
theorem sigma_mul (m n : ℕ) (h : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * (∑ d ∈ n.divisors, d) :=
-- END SPEC
  sorry

end H036

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the two milestones first; with them `sigma_mul` is one `rw` chain (R32–R34). Coprimality is
    used in exactly two places: the gcd split in `divisors_eq` (R12) and Euclid's lemma in `mul_inj`
    (R23). Without it injectivity fails: `m = n = 4`, `2 * 2 = 4 * 1`.
H2. `divisors_eq`: `ext d`, `simp only [mem_image, mem_product, Nat.mem_divisors, Prod.exists]`,
    `constructor`. mp: the witnesses are `(d.gcd m, d.gcd n)`, whose product is `d.gcd (m * n) = d`.
    mpr: `rintro ⟨a, b, ⟨⟨ha, hm⟩, ⟨hb, hn⟩⟩, rfl⟩`, then `mul_dvd_mul` and `mul_ne_zero`.
    `mul_inj`: `rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq`, clean `hab hab'` with
    `simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors] at hab hab'` and
    `change a * b = a' * b' at heq`. Show `a ∣ a'` and `a' ∣ a`, so `a = a'` (R26, R27); then cancel `a > 0`.
H3. `divisors_eq` mp: `refine ⟨d.gcd m, d.gcd n, ⟨⟨Nat.gcd_dvd_right _ _, fun hm => hmn (by simp [hm])⟩, ⟨…⟩⟩, ?_⟩`
    and `rw [← Nat.Coprime.gcd_mul d h, Nat.gcd_eq_left hd]`.
    `mul_inj`: `have h1 : a ∣ a' := (h.coprime_dvd_left hab.1.1).coprime_dvd_right hab'.2.1
    |>.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a b)`, then `obtain rfl := Nat.dvd_antisymm h1 h2` and
    `Prod.ext rfl (Nat.eq_of_mul_eq_mul_left ha0 heq)`.
    Main: `rw [divisors_eq m n h, sum_image (mul_inj m n h), sum_mul_sum, sum_product]`.
-/
