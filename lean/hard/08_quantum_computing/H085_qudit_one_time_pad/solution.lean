/- H085 | Qudit one-time pad (Weyl twirl) | 1-1.5 h | ZMod d, clock and shift, roots of unity, double sums, conjugate transpose, mathlib
GOAL
  On `ℂ^d` with basis indexed by `ZMod d` (integers mod `d`), let `ω = e^{2πi/d}` and `W_{a,b} = X^a Z^b`
  (shift `X|j⟩ = |j+1⟩`, clock `Z|j⟩ = ω^j |j⟩`). Prove the one-time pad: averaging `W ρ W†` over all
  `d²` pairs `(a, b)` gives `(tr ρ / d) · I`, for every `d × d` matrix `ρ`.

GUIDE
  Entries R1–R53: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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
/- SKELETON · weyl_conj_apply
  1. Turn the row condition of `weyl` around, once for all indices:                R1, intro, R2, R3
       h : ∀ x j : ZMod d, (x = j + a) ↔ (j = x - a)
  2. ONE `simp only`: both products to sums, `ᴴ` to `star`, unfold `weyl`, apply h:  R4, R5, R6, R7
       ⊢ ∑ x, (∑ x_1, (if x_1 = i - a then … else 0) * ρ x_1 x) * star (if x = k - a then … else 0) = …
  3. ONE `simp only`: move factors and `star` into the `if`s, collapse both sums:    R8, R11, R12, R10, R9
  4. `star` → `starRingEnd ℂ` (simp also applies R24), then reorder factors:         R13, ring
-/
/-- conjugation by `W_{a,b}` moves the entry `(i-a, k-a)` to `(i, k)` and attaches a phase -/
theorem weyl_conj_apply {d : ℕ} [NeZero d] (a b : ZMod d) (ρ : Matrix (ZMod d) (ZMod d) ℂ)
    (i k : ZMod d) :
    (weyl a b * ρ * (weyl a b)ᴴ) i k
      = ω d ^ (b.val * (i - a).val) * starRingEnd ℂ (ω d ^ (b.val * (k - a).val))
        * ρ (i - a) (k - a) := by
  have h : ∀ x j : ZMod d, (x = j + a) ↔ (j = x - a) := fun x j => by
    constructor <;> intro h <;> subst h <;> ring
  simp only [mul_apply, conjTranspose_apply, weyl, of_apply, h]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero]
  simp [RCLike.star_def]
  ring

-- MILESTONE (optional: change or delete)
/- SKELETON · zmod_sum_range
  1. Make `d` a successor, so `ZMod d` becomes `Fin (n + 1)`:                         R14
  2. Close with the `Fin` lemma by `exact` (not `rw`: the match needs unfolding):     R15 (W1)
-/
theorem zmod_sum_range {d : ℕ} [NeZero d] (f : ℕ → ℂ) :
    ∑ b : ZMod d, f b.val = ∑ k ∈ Finset.range d, f k := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact Fin.sum_univ_eq_sum_range f (n + 1)

-- MILESTONE (optional: change or delete)
/- SKELETON · clock_sum   (uses milestone zmod_sum_range in step 6)
  1. hp : IsPrimitiveRoot (ω d) d                                                     R16 with NeZero.ne d
  2. hne : ω d ≠ 0                                                                    R17
  3. hconj : starRingEnd ℂ (ω d) = (ω d)⁻¹:                                           R18 → R19 → R20 → R21 → R22 → ring (W3)
  4. Name the ratio: r := ω d ^ x.val * (ω d ^ y.val)⁻¹, with hr                     R23
  5. hterm : ∀ b, (the summand) = r ^ b.val: intro b, then ONE rw chain
       R24, rw [hconj], rw [hr], R25, R26 (twice), R27 ← (twice), R28 (twice)
  6. Rewrite every summand, then move to `Finset.range d`:                            R29, rw [zmod_sum_range …]
  7. Split on `x = y`:                                                                R30
       x = y:  R2, then `simp` with hr, hne                                           R31, R32
       x ≠ y:  hr1 : r ≠ 1                 R33; rw [hr] then R34 (with R35) at h1;
                                           then `exact h (…)`: R38 (R36 (R37) (R37) h1)
               hrN : r ^ d = 1             rw: hr, R25, R26, R27 ← ×2, R28 ×2, R27 ×2, R39; simp
               rw [geom_sum_eq hr1, hrN], then simp                                   R40 (W2)
-/
/-- averaging over the clock index kills off-diagonal phases -/
theorem clock_sum {d : ℕ} [NeZero d] (x y : ZMod d) :
    ∑ b : ZMod d, ω d ^ (b.val * x.val) * starRingEnd ℂ (ω d ^ (b.val * y.val))
      = if x = y then (d : ℂ) else 0 := by
  have hp : IsPrimitiveRoot (ω d) d := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  have hne : ω d ≠ 0 := hp.ne_zero (NeZero.ne d)
  have hconj : starRingEnd ℂ (ω d) = (ω d)⁻¹ := by
    unfold ω; rw [← Complex.exp_conj, ← Complex.exp_neg]; congr 1; simp [map_ofNat]; ring
  set r := ω d ^ x.val * (ω d ^ y.val)⁻¹ with hr
  have hterm : ∀ b : ZMod d,
      ω d ^ (b.val * x.val) * starRingEnd ℂ (ω d ^ (b.val * y.val)) = r ^ b.val := by
    intro b
    rw [map_pow, hconj, hr, mul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm x.val,
      mul_comm y.val]
  simp_rw [hterm]
  rw [zmod_sum_range (fun k => r ^ k)]
  split_ifs with h
  · subst h; simp [hr, hne]
  · have hr1 : r ≠ 1 := by
      intro h1
      rw [hr, mul_inv_eq_one₀ (pow_ne_zero _ hne)] at h1
      exact h (ZMod.val_injective _ (hp.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h1))
    have hrN : r ^ d = 1 := by
      rw [hr, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm x.val, mul_comm y.val, pow_mul,
        pow_mul, hp.pow_eq_one]
      simp
    rw [geom_sum_eq hr1, hrN]; simp

-- MILESTONE (optional: change or delete)
/- SKELETON · shift_sum
  1. Reindex by the bijection a ↦ i - a, in one `exact`:                              R41 with R42, R43 (W5)
       g := fun j => ρ j j,  e := Equiv.subLeft i
-/
/-- averaging over the shift index sums the diagonal -/
theorem shift_sum {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) (i : ZMod d) :
    ∑ a, ρ (i - a) (i - a) = ρ.trace := by
  exact Equiv.sum_comp (Equiv.subLeft i) (fun j => ρ j j)

/- SKELETON · weyl_twirl
  Prove the milestones first: weyl_conj_apply, clock_sum (which uses zmod_sum_range) and shift_sum
  are all used in steps 3–4 below.
  1. hd : (d : ℂ) ≠ 0                                                                 R44
  2. Entrywise: ext i k
  3. ONE `simp only`: R45, R46, weyl_conj_apply, R47 (←), clock_sum, R48
       ⊢ 1 / ↑d ^ 2 * ∑ x, (if i - x = k - x then ↑d else 0) * ρ (i - x) (k - x)
           = ρ.trace / ↑d * if i = k then 1 else 0
  4. Case split:                                                                      R49
       i = k:  R2; `simp only` with if_true, R50 (←), shift_sum; then                 R51
       i ≠ k:  this : ∀ a, ¬ (i - a = k - a): intro a h (R33), feed hik with R52
               then `simp` with this and hik                                          R53
-/
-- BEGIN SPEC
theorem weyl_twirl {d : ℕ} [NeZero d] (ρ : Matrix (ZMod d) (ZMod d) ℂ) :
    (1 / (d : ℂ) ^ 2) • ∑ a, ∑ b, weyl a b * ρ * (weyl a b)ᴴ
      = (ρ.trace / d) • (1 : Matrix (ZMod d) (ZMod d) ℂ) :=
-- END SPEC
  by
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    ext i k
    simp only [Matrix.smul_apply, Matrix.sum_apply, weyl_conj_apply, ← Finset.sum_mul, clock_sum,
      one_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst hik
      simp only [if_true, ← Finset.mul_sum, shift_sum]
      field_simp
    · have : ∀ a : ZMod d, ¬ (i - a = k - a) := fun a h => hik (by simpa using h)
      simp [this, hik]

end H085

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Work entrywise (`ext i k`). Conjugating by `W_{a,b}` only relabels entries and multiplies by phases
    (`weyl_conj_apply`); the `b`-average then kills every entry with `i ≠ k` (`clock_sum`), and the
    `a`-average turns the diagonal into the trace (`shift_sum`). Prove these milestones first.
H2. `weyl_conj_apply`: each row of `weyl a b` has one nonzero entry, at `j = i - a`; rewrite `i = j + a`
    as `j = i - a` (R7), then `Finset.sum_ite_eq'` (R11) collapses both sums. `zmod_sum_range`: R14, then
    `exact` R15. `clock_sum`: `conj ω = ω⁻¹` (R18–R22), so every summand is `r ^ b.val` with
    `r = ω ^ x.val * (ω ^ y.val)⁻¹` (R23–R29); move to `Finset.range d`; `x = y` gives `r = 1`,
    otherwise `r ≠ 1`, `r ^ d = 1` and `geom_sum_eq` (R40). `shift_sum`: R41 with `Equiv.subLeft i`.
H3. Main: `ext i k; simp only [Matrix.smul_apply, Matrix.sum_apply, weyl_conj_apply, ← Finset.sum_mul,
    clock_sum, Matrix.one_apply, smul_eq_mul]`, then `by_cases hik : i = k`.
    `shift_sum`: `exact Equiv.sum_comp (Equiv.subLeft i) (fun j => ρ j j)`.
    `clock_sum`, `r ≠ 1`: `rw [hr, mul_inv_eq_one₀ (pow_ne_zero _ hne)] at h1` and
    `exact h (ZMod.val_injective _ (hp.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h1))`.
    `weyl_conj_apply`, step 3: `simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero]`.
-/
