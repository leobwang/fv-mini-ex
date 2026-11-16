/- M141 | CHSH inequality for local hidden variables | 15 min | CHSH, Bell inequality, abs, Finset sums, case bash, mathlib
GOAL
  A local-hidden-variable model: a hidden value `l : Λ` with probability `p l`; Alice's setting `x` and
  Bob's setting `y` give outcomes `A x l, B y l ∈ {±1}`. Prove `|E₀₀ + E₀₁ + E₁₀ − E₁₁| ≤ 2`, where
  `Eₓᵧ = ∑ l, p l * A x l * B y l` (all four correlations are written inside one sum).

REFERENCE
  #check @Finset.abs_sum_le_sum_abs  -- |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i|
  #check @abs_mul                    -- |a * b| = |a| * |b|
  #check @abs_of_nonneg              -- 0 ≤ a → |a| = a
  #check @Finset.sum_le_sum          -- (∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
  #check @mul_le_mul_of_nonneg_left  -- b ≤ c → 0 ≤ a → a * b ≤ a * c
  #check @Finset.sum_mul             -- (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
  #check @abs_le                     -- |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
  example (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : |a * b| ≤ 1 := by
    rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;> norm_num   -- `<;>` runs on every case
  -- `calc _ ≤ ∑ l, |p l * _| := ... ; _ = ... := ... ; _ ≤ ... := ...` chains the estimate.
-/
import Mathlib

namespace M141

-- BEGIN SPEC
theorem chsh_lhv {Λ : Type} [Fintype Λ] (p : Λ → ℝ) (hp : ∀ l, 0 ≤ p l) (hsum : ∑ l, p l = 1)
    (A B : Fin 2 → Λ → ℝ) (hA : ∀ x l, A x l = 1 ∨ A x l = -1) (hB : ∀ y l, B y l = 1 ∨ B y l = -1) :
    |∑ l, p l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l)| ≤ 2 :=
-- END SPEC
  by
    have pt : ∀ l, |A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l| ≤ 2 := by
      intro l
      rcases hA 0 l with h1 | h1 <;> rcases hA 1 l with h2 | h2 <;> rcases hB 0 l with h3 | h3 <;>
        rcases hB 1 l with h4 | h4 <;> rw [h1, h2, h3, h4] <;> norm_num [abs_le]
    calc _ ≤ ∑ l, |p l * (A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, p l * |A 0 l * B 0 l + A 0 l * B 1 l + A 1 l * B 0 l - A 1 l * B 1 l| :=
          Finset.sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg (hp l)]
      _ ≤ ∑ l, p l * 2 := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (pt l) (hp l)
      _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]

end M141

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First prove the bound for one hidden value: `|A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁| ≤ 2` for every `l`
    (it equals `A₀(B₀ + B₁) + A₁(B₀ − B₁)`, and one of the brackets is 0). Then average over `l`.
H2. Pointwise: 16 cases from `rcases` on `hA 0 l`, `hA 1 l`, `hB 0 l`, `hB 1 l`, each closed by `rw` and `norm_num [abs_le]`.
    Averaging: triangle inequality for sums, pull `|p l| = p l` out, bound each term by `p l * 2`, then `∑ p l = 1`.
H3. `calc _ ≤ ∑ l, |p l * _| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, p l * |…| := Finset.sum_congr rfl fun l _ => by rw [abs_mul, abs_of_nonneg (hp l)]
      _ ≤ ∑ l, p l * 2 := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (pt l) (hp l)
      _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]`
-/
