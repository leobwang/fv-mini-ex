/- H072 | Global error of Euler's method | 1-1.25 h | ODE, mean value theorem, Lipschitz, discrete Gronwall, error recursion, HasDerivAt, mathlib
GOAL
  `y` solves `y' = F(t, y)`; Euler with step `h` from `(t₀, y t₀)` is `Yₖ₊₁ = Yₖ + h F(t₀ + kh, Yₖ)`. If `F` is
  `L`-Lipschitz in its second argument and `y'` is `M`-Lipschitz (a stand-in for `|y''| ≤ M`), the global error is
  `|y(t₀ + nh) − Yₙ| ≤ e^{n h L} · n M h²`. At fixed `T = nh` that is `e^{TL} T M h = O(h)`: first-order convergence.
  Plan: local error `≤ M h²` per step (mean value theorem) + error recursion + discrete Gronwall (M119).

REFERENCE
  #check exists_hasDerivAt_eq_slope  -- (f f') a < b → ContinuousOn f (Icc a b) → (∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
                                     --   → ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a)
  example (y y' : ℝ → ℝ) (hy : ∀ t, HasDerivAt y (y' t) t) : Continuous y :=
    continuous_iff_continuousAt.mpr fun t => (hy t).continuousAt   -- then `.continuousOn`
  #check mul_div_cancel₀   -- b ≠ 0 → b * (a / b) = a
  #check abs_add_le        -- |a + b| ≤ |a| + |b|        (`abs_mul`, `abs_of_pos`)
  example (t₀ h : ℝ) (k : ℕ) : t₀ + ((k + 1 : ℕ) : ℝ) * h = t₀ + k * h + h := by push_cast; ring
  `set t := t₀ + k * h` names a subterm everywhere; `gcongr` proves `a + b ≤ a' + b'` from `a ≤ a'`, `b ≤ b'`.
  `0 ≤ M` is not a hypothesis: get it from `hlip` at two distinct points.
NOTE: The Lipschitz hypotheses are global (a simplification). Not vacuous: `F t u = -u + sin t`, `y t = (sin t - cos t) / 2`.
-/
import Mathlib

namespace H072

-- BEGIN SPEC
/-- Euler's method for `y' = F t y` with step `h`, started at time `t₀` from value `y₀` -/
noncomputable def eulerSeq (F : ℝ → ℝ → ℝ) (t₀ y₀ h : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => eulerSeq F t₀ y₀ h n + h * F (t₀ + n * h) (eulerSeq F t₀ y₀ h n)
-- END SPEC

-- MILESTONE (optional: change or delete)
-- local truncation error: one exact step versus one Euler step from the exact value
theorem local_error (y y' : ℝ → ℝ) (M t h : ℝ) (hh : 0 < h) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hlip : ∀ s t, |y' s - y' t| ≤ M * |s - t|) :
    |y (t + h) - y t - h * y' t| ≤ M * h ^ 2 := by
  have hcont : Continuous y := continuous_iff_continuousAt.mpr fun s => (hy s).continuousAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope y y' (show t < t + h by linarith)
    hcont.continuousOn (fun s _ => hy s)
  have e : y (t + h) - y t - h * y' t = h * (y' c - y' t) := by
    rw [hslope, show t + h - t = h by ring, mul_sub, mul_div_cancel₀ _ hh.ne']
  -- WHY: `0 ≤ M` is not assumed; a Lipschitz bound at two distinct points forces it
  have hM : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ M * |t + 1 - t| := (abs_nonneg _).trans (hlip (t + 1) t)
    simpa using h1
  have hct : |c - t| ≤ h := by
    rw [abs_of_pos (by linarith [hc.1])]
    linarith [hc.2]
  rw [e, abs_mul, abs_of_pos hh]
  calc h * |y' c - y' t| ≤ h * (M * |c - t|) := by gcongr; exact hlip c t
    _ ≤ h * (M * h) := by gcongr
    _ = M * h ^ 2 := by ring

-- MILESTONE (optional: change or delete)
-- error recursion: the new error is the old one amplified by `1 + hL`, plus the local error
theorem error_step (F : ℝ → ℝ → ℝ) (y y' : ℝ → ℝ) (t₀ h L M : ℝ) (hh : 0 < h)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hode : ∀ t, y' t = F t (y t))
    (hlip : ∀ s t, |y' s - y' t| ≤ M * |s - t|)
    (hF : ∀ t u v, |F t u - F t v| ≤ L * |u - v|) (k : ℕ) :
    |y (t₀ + ((k + 1 : ℕ) : ℝ) * h) - eulerSeq F t₀ (y t₀) h (k + 1)|
      ≤ (1 + h * L) * |y (t₀ + k * h) - eulerSeq F t₀ (y t₀) h k| + M * h ^ 2 := by
  simp only [eulerSeq]
  set t := t₀ + k * h
  set Y := eulerSeq F t₀ (y t₀) h k
  have ht : t₀ + ((k + 1 : ℕ) : ℝ) * h = t + h := by push_cast; ring
  rw [ht]
  have key : y (t + h) - (Y + h * F t Y)
      = (y (t + h) - y t - h * y' t) + ((y t - Y) + h * (F t (y t) - F t Y)) := by
    rw [hode t]; ring
  rw [key]
  calc _ ≤ |y (t + h) - y t - h * y' t| + |(y t - Y) + h * (F t (y t) - F t Y)| := abs_add_le _ _
    _ ≤ M * h ^ 2 + (|y t - Y| + h * (L * |y t - Y|)) := by
        gcongr
        · exact local_error y y' M t h hh hy hlip
        · calc _ ≤ |y t - Y| + |h * (F t (y t) - F t Y)| := abs_add_le _ _
            _ ≤ _ := by rw [abs_mul, abs_of_pos hh]; gcongr; exact hF _ _ _
    _ = (1 + h * L) * |y t - Y| + M * h ^ 2 := by ring

-- MILESTONE (optional: change or delete)  (proved in M119: paste your proof)
theorem discrete_gronwall (e : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, e (n + 1) ≤ (1 + a) * e n + b) (n : ℕ) :
    e n ≤ Real.exp (n * a) * (e 0 + n * b) := by
  -- WHY: induct on the sharper bound with `(1 + a) ^ n`, then compare with the exponential
  have key : ∀ n : ℕ, e n ≤ (1 + a) ^ n * (e 0 + n * b) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (1 : ℝ) ≤ (1 + a) ^ n := one_le_pow₀ (by linarith)
      calc e (n + 1) ≤ (1 + a) * e n + b := hstep n
        _ ≤ (1 + a) * ((1 + a) ^ n * (e 0 + n * b)) + b := by gcongr
        _ ≤ (1 + a) ^ (n + 1) * (e 0 + (n + 1 : ℕ) * b) := by
          push_cast
          rw [pow_succ]
          nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + a)]
  calc e n ≤ (1 + a) ^ n * (e 0 + n * b) := key n
    _ ≤ Real.exp (n * a) * (e 0 + n * b) := by
      gcongr
      calc (1 + a) ^ n ≤ Real.exp a ^ n := by gcongr; linarith [Real.add_one_le_exp a]
        _ = Real.exp (n * a) := by rw [← Real.exp_nat_mul]

-- BEGIN SPEC
theorem euler_global_error (F : ℝ → ℝ → ℝ) (y y' : ℝ → ℝ) (t₀ h L M : ℝ) (hh : 0 < h) (hL : 0 ≤ L)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hode : ∀ t, y' t = F t (y t))
    (hlip : ∀ s t, |y' s - y' t| ≤ M * |s - t|)
    (hF : ∀ t u v, |F t u - F t v| ≤ L * |u - v|) (n : ℕ) :
    |y (t₀ + n * h) - eulerSeq F t₀ (y t₀) h n| ≤ Real.exp (n * (h * L)) * (n * (M * h ^ 2)) :=
-- END SPEC
  by
    have hM : 0 ≤ M := by
      have h1 : (0 : ℝ) ≤ M * |1 - 0| := (abs_nonneg _).trans (hlip 1 0)
      simpa using h1
    have := discrete_gronwall (fun k : ℕ => |y (t₀ + k * h) - eulerSeq F t₀ (y t₀) h k|)
      (h * L) (M * h ^ 2) (by positivity) (by positivity) (abs_nonneg _)
      (error_step F y y' t₀ h L M hh hy hode hlip hF) n
    simpa [eulerSeq] using this

end H072

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `eₖ = |y(t₀ + kh) − Yₖ|`. Show `eₖ₊₁ ≤ (1 + hL) eₖ + M h²` and `e₀ = 0`; discrete Gronwall finishes.
    The `M h²` is the local error: by the mean value theorem `y(t+h) − y(t) = h y'(c)` for some `c ∈ (t, t+h)`.
H2. `local_error`: with `hcont : Continuous y` from the REFERENCE example, `obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope y y' (show t < t + h by linarith) hcont.continuousOn (fun s _ => hy s)`,
    rewrite the left side as `h * (y' c - y' t)`, then `|c − t| ≤ h` and `hlip c t`. `error_step`: unfold `eulerSeq` once
    (`simp only [eulerSeq]`), turn `t₀ + ↑(k+1) * h` into `t + h`, and split the error into local + propagated parts.
H3. With `t := t₀ + k * h`, `Y := eulerSeq F t₀ (y t₀) h k`:
    `y (t + h) - (Y + h * F t Y) = (y (t + h) - y t - h * y' t) + ((y t - Y) + h * (F t (y t) - F t Y))` (by `rw [hode t]; ring`),
    then `abs_add_le` twice, `local_error`, and `hF`. Main: `discrete_gronwall (fun k => |y (t₀ + k * h) - eulerSeq F t₀ (y t₀) h k|)
    (h * L) (M * h ^ 2) _ _ _ (error_step ...) n`, and `simpa [eulerSeq]` to clean up `e 0 = 0`.
-/
