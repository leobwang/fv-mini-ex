/- H085 | Qudit one-time pad (Weyl twirl) | 1-1.5 h | ZMod d, clock and shift, roots of unity, double sums, conjugate transpose, mathlib
GOAL
  On `ℂ^d` with basis indexed by `ZMod d` (integers mod `d`), let `ω = e^{2πi/d}` and `W_{a,b} = X^a Z^b`
  (shift `X|j⟩ = |j+1⟩`, clock `Z|j⟩ = ω^j |j⟩`). Prove the one-time pad: averaging `W ρ W†` over all
  `d²` pairs `(a, b)` gives `(tr ρ / d) · I`, for every `d × d` matrix `ρ`.

REFERENCE
  -- `Mᴴ` = conjugate transpose (`W†`);  `c • M` = scalar times matrix;  `b.val : ℕ` = representative of `b` in `[0, d)`
  -- `Matrix.of f` = the matrix with entries `f i j`;  `[NeZero d]` = assumption that `d ≠ 0` (so `ZMod d` is finite, not ℤ);  `∑ a, g a` = sum over every `a : ZMod d`
  #check Matrix.mul_apply           -- (M * N) i k = ∑ j, M i j * N j k     (also `Matrix.conjTranspose_apply`)
  #check Finset.sum_ite_eq'         -- ∑ x ∈ s, (if x = a then b x else 0) = if a ∈ s then b a else 0
  #check geom_sum_eq                -- x ≠ 1 → ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1)
  example (d : ℕ) [NeZero d] : IsPrimitiveRoot (ω d) d := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  #check IsPrimitiveRoot.pow_inj    -- ζ primitive k-th root, i < k, j < k, ζ ^ i = ζ ^ j → i = j
  #check ZMod.val_injective         -- (n) [NeZero n] : Function.Injective ZMod.val      (and `ZMod.val_lt`)
  #check Equiv.sum_comp             -- (e : ι ≃ κ) g : ∑ i, g (e i) = ∑ i, g i     (`Equiv.subLeft i : j ↦ i - j`)
  #check Complex.exp_conj           -- cexp (conj x) = conj (cexp x)   (`starRingEnd ℂ` is complex conjugation)
  #check Matrix.sum_apply           -- (∑ c ∈ s, g c) i j = ∑ c ∈ s, g c i j     (and `Matrix.smul_apply`, `Matrix.one_apply`)
NOTE: `ZMod d` is not `Fin d` for a variable `d`; first make `d` a successor with `obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)`, after which `ZMod (n+1)` unfolds to `Fin (n+1)`.
-/
import Mathlib

open Matrix Complex

namespace H085

-- BEGIN SPEC
/-- `ω = e^{2πi/d}`, a primitive `d`-th root of unity -/
noncomputable def ω (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

/-- the Weyl operator `X^a Z^b`: `(X^a Z^b)ᵢⱼ = [i = j + a] · ω^{b·j}` -/
noncomputable def weyl {d : ℕ} [NeZero d] (a b : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.of fun i j => if i = j + a then ω d ^ (b.val * j.val) else 0
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- conjugation by `W_{a,b}` moves the entry `(i-a, k-a)` to `(i, k)` and attaches a phase -/
theorem weyl_conj_apply {d : ℕ} [NeZero d] (a b : ZMod d) (ρ : Matrix (ZMod d) (ZMod d) ℂ)
    (i k : ZMod d) :
    (weyl a b * ρ * (weyl a b)ᴴ) i k
      = ω d ^ (b.val * (i - a).val) * starRingEnd ℂ (ω d ^ (b.val * (k - a).val))
        * ρ (i - a) (k - a) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem zmod_sum_range {d : ℕ} [NeZero d] (f : ℕ → ℂ) :
    ∑ b : ZMod d, f b.val = ∑ k ∈ Finset.range d, f k := by
  sorry

-- MILESTONE (optional: change or delete)
/-- averaging over the clock index kills off-diagonal phases -/
theorem clock_sum {d : ℕ} [NeZero d] (x y : ZMod d) :
    ∑ b : ZMod d, ω d ^ (b.val * x.val) * starRingEnd ℂ (ω d ^ (b.val * y.val))
      = if x = y then (d : ℂ) else 0 := by
  sorry

-- MILESTONE (optional: change or delete)
/-- averaging over the shift index sums the diagonal -/
theorem shift_sum {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) (i : ZMod d) :
    ∑ a, ρ (i - a) (i - a) = ρ.trace := by
  sorry

-- BEGIN SPEC
theorem weyl_twirl {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) :
    (1 / (d : ℂ) ^ 2) • ∑ a, ∑ b, weyl a b * ρ * (weyl a b)ᴴ
      = (ρ.trace / d) • (1 : Matrix (ZMod d) (ZMod d) ℂ) :=
-- END SPEC
  sorry

end H085

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work entrywise (`ext i k`). Conjugating by `W_{a,b}` only relabels entries and multiplies by phases (milestone 1); the `b`-average then kills every entry with `i ≠ k` (milestone 3), and the `a`-average turns the diagonal into the trace (milestone 4).
H2. Milestone 1: each row of `weyl a b` has one nonzero entry, at `j = i - a`; rewrite `i = j + a` as `j = i - a`, then `Finset.sum_ite_eq'` collapses both sums. Milestone 3: `conj ω = ω⁻¹`, so the summand is `r ^ b.val` with `r = ω^{x.val} (ω^{y.val})⁻¹`; move to `Finset.range d` (milestone 2), then `x = y` gives `r = 1`, and otherwise `r ≠ 1`, `r ^ d = 1`, `geom_sum_eq`.
H3. Main: `ext i k; simp only [Matrix.smul_apply, Matrix.sum_apply, weyl_conj_apply, ← Finset.sum_mul, clock_sum, Matrix.one_apply, smul_eq_mul]`, then `by_cases hik : i = k`. Milestone 4 is `Equiv.sum_comp (Equiv.subLeft i) (fun j => ρ j j)`. For `r ≠ 1`: `rw [mul_inv_eq_one₀ (pow_ne_zero _ hne)] at h1` and `ZMod.val_injective _ (hp.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h1)`. Milestone 2, after the NOTE's `obtain`: `exact Fin.sum_univ_eq_sum_range f (n + 1)` (by `exact`, not `rw`).
-/
