/- H072 | Global error of Euler's method | 1-1.25 h | ODE, mean value theorem, Lipschitz, discrete Gronwall, error recursion, HasDerivAt, mathlib
GOAL
  `y` solves `y' = F(t, y)`; Euler with step `h` from `(t₀, y t₀)` is `Yₖ₊₁ = Yₖ + h F(t₀ + kh, Yₖ)`. If `F` is
  `L`-Lipschitz in its second argument and `y'` is `M`-Lipschitz (a stand-in for `|y''| ≤ M`), the global error is
  `|y(t₀ + nh) − Yₙ| ≤ e^{n h L} · n M h²`. At fixed `T = nh` that is `e^{TL} T M h = O(h)`: first-order convergence.

GUIDE
  Entries R1–R33: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H072

-- BEGIN SPEC
/-- Euler's method for `y' = F t y` with step `h`, started at time `t₀` from value `y₀` -/
noncomputable def eulerSeq (F : ℝ → ℝ → ℝ) (t₀ y₀ h : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => eulerSeq F t₀ y₀ h n + h * F (t₀ + n * h) (eulerSeq F t₀ y₀ h n)
-- END SPEC

/- SKELETON · local_error   (MILESTONE 1: prove first. error_step uses it for the local part of
   the error, `|y (t + h) - y t - h * y' t| ≤ M * h ^ 2`)
  1. Continuity of `y` from the derivatives:                                    R1, R2
       hcont : Continuous y
  2. Mean value theorem on `[t, t + h]`; name `c hc hslope`. Its three premises:
     `t < t + h` inline, continuity on the interval, the derivative premise:   R6 with R4, R3, R5
  3. Prove the identity first:
       e : y (t + h) - y t - h * y' t = h * (y' c - y' t)
     `rw [hslope]`, then `t + h - t` → `h`, expand, cancel `h * (… / h)`:       R7, R8, R9 → R10
  4. hM : 0 ≤ M   (not assumed: `hlip` at two points at distance 1):          R11, R12
  5. hct : |c - t| ≤ h: `rw [abs_of_pos …]` with `0 < c - t` from `hc.1`, then
     `c - t ≤ h` from `hc.2`:                                                 R14 with R4, R13; R4
  6. `rw [e]`, then strip `|h * …|` down to `h * |y' c - y' t|`:                R15, R14
  7. `calc` in three steps: `hlip c t` under the factor `h`; then `hct` under
     `h * (M * ·)` (needs `hM`); then `ring`:                                    R16, R17
-/
-- MILESTONE (optional: change or delete)
-- local truncation error: one exact step versus one Euler step from the exact value
theorem local_error (y y' : ℝ → ℝ) (M t h : ℝ) (hh : 0 < h) (hy : ∀ t, HasDerivAt y (y' t) t)
    (hlip : ∀ s t, |y' s - y' t| ≤ M * |s - t|) :
    |y (t + h) - y t - h * y' t| ≤ M * h ^ 2 := by
  sorry

/- SKELETON · error_step   (MILESTONE 2: after local_error, which it uses. The main theorem passes
   it to discrete_gronwall as `hstep`)
  1. Unfold one Euler step on the left (only the `k + 1` term unfolds):         R18
  2. Name `t := t₀ + ↑k * h` and `Y := eulerSeq F t₀ (y t₀) h k`:                R19
  3. ht : t₀ + ↑(k + 1) * h = t + h   (move the cast, then `ring`); `rw [ht]`:   R20
  4. Prove the split first (`rw [hode t]`, then `ring`), then `rw` with it:
       key : y (t + h) - (Y + h * F t Y)
           = (y (t + h) - y t - h * y' t) + ((y t - Y) + h * (F t (y t) - F t Y))
  5. `calc`: triangle inequality; then both parts at once with `gcongr`;
     then `ring` into `(1 + h * L) * |y t - Y| + M * h ^ 2`:                     R16, R21, R22
       local part:       `local_error y y' M t h hh hy hlip`
       propagated part:  triangle inequality again, strip `|h * …|`, `gcongr`, `hF`:  R21, R15, R14, R17
-/
-- MILESTONE (optional: change or delete)
-- error recursion: the new error is the old one amplified by `1 + hL`, plus the local error
theorem error_step (F : ℝ → ℝ → ℝ) (y y' : ℝ → ℝ) (t₀ h L M : ℝ) (hh : 0 < h)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hode : ∀ t, y' t = F t (y t))
    (hlip : ∀ s t, |y' s - y' t| ≤ M * |s - t|)
    (hF : ∀ t u v, |F t u - F t v| ≤ L * |u - v|) (k : ℕ) :
    |y (t₀ + ((k + 1 : ℕ) : ℝ) * h) - eulerSeq F t₀ (y t₀) h (k + 1)|
      ≤ (1 + h * L) * |y (t₀ + k * h) - eulerSeq F t₀ (y t₀) h k| + M * h ^ 2 := by
  sorry

/- SKELETON · discrete_gronwall   (MILESTONE 3: M119's theorem, independent of 1 and 2; the main
   theorem applies it to the error sequence)
  1. Prove the sharper bound first, by induction on `n` (Lean basics):
       key : ∀ n : ℕ, e n ≤ (1 + a) ^ n * (e 0 + n * b)
     (`intro n` shadows the outer `n`, which then prints as `n✝`.)
     zero: `simp`.  succ: first h1 : 1 ≤ (1 + a) ^ n  (premise by R4):         R23
       `calc` via `hstep n`, then `ih` under `(1 + a) * · + b`, then the cast
       `↑(n + 1)`, `pow_succ`, and `nlinarith` given the product fact
       `(1 + a) * 1 ≤ (1 + a) * (1 + a) ^ n` built from `h1`:                    R16, R17, R20, R24, R26 with R25
  2. `calc e n ≤ (1 + a) ^ n * (e 0 + n * b)` by `key n`, then strip the common
     right factor:                                                               R16, R27
     the goal `(1 + a) ^ n ≤ Real.exp (↑n * a)`: a `calc` through
     `Real.exp a ^ n`, with `gcongr` and `1 + a ≤ Real.exp a`:                    R29, R28, R30
-/
-- MILESTONE (optional: change or delete)  (proved in M119: paste your proof)
theorem discrete_gronwall (e : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, e (n + 1) ≤ (1 + a) * e n + b) (n : ℕ) :
    e n ≤ Real.exp (n * a) * (e 0 + n * b) := by
  sorry

/- SKELETON · euler_global_error   (prove the three milestones first; this uses error_step and
   discrete_gronwall)
  1. hM : 0 ≤ M, as in local_error (needed by `positivity` below):              R11, R12
  2. `have :=` discrete_gronwall at the error sequence
       e := fun k : ℕ => |y (t₀ + k * h) - eulerSeq F t₀ (y t₀) h k|
     with `a := h * L`, `b := M * h ^ 2`. Premises: `0 ≤ a`, `0 ≤ b` by `positivity`;
     `0 ≤ e 0` by `abs_nonneg _`; `hstep` is `error_step …` (all its arguments):  R31, R32, R11
  3. `this` still contains `e 0 = |y (t₀ + ↑0 * h) - eulerSeq F t₀ (y t₀) h 0|`;
     simplify it to `0` with `eulerSeq` and close:                               R33
-/
-- BEGIN SPEC
theorem euler_global_error (F : ℝ → ℝ → ℝ) (y y' : ℝ → ℝ) (t₀ h L M : ℝ) (hh : 0 < h) (hL : 0 ≤ L)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hode : ∀ t, y' t = F t (y t))
    (hlip : ∀ s t, |y' s - y' t| ≤ M * |s - t|)
    (hF : ∀ t u v, |F t u - F t v| ≤ L * |u - v|) (n : ℕ) :
    |y (t₀ + n * h) - eulerSeq F t₀ (y t₀) h n| ≤ Real.exp (n * (h * L)) * (n * (M * h ^ 2)) :=
-- END SPEC
  sorry

end H072

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Write `eₖ = |y(t₀ + kh) − Yₖ|`. Show `eₖ₊₁ ≤ (1 + hL) eₖ + M h²` (error_step) and `e₀ = 0`; discrete
    Gronwall finishes. The `M h²` is the local error (local_error): by the mean value theorem
    `y(t+h) − y(t) = h y'(c)` for some `c ∈ (t, t+h)`, and `|y'(c) − y'(t)| ≤ M |c − t| ≤ M h`.
H2. local_error: `Continuous y` (R1, R2), the mean value theorem (R6), the identity
    `y (t + h) - y t - h * y' t = h * (y' c - y' t)` (R7–R10), `0 ≤ M` and `|c - t| ≤ h`, then a `calc` with
    `gcongr`. error_step: `simp only [eulerSeq]`, `set` `t` and `Y`, `t₀ + ↑(k + 1) * h = t + h` by
    `push_cast; ring`, the split identity, the triangle inequality twice, local_error and `hF`.
    Main: discrete_gronwall at the error sequence with `a = h * L`, `b = M * h ^ 2`.
H3. `obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope y y' (show t < t + h by linarith)
    hcont.continuousOn (fun s _ => hy s)`. The split (by `rw [hode t]; ring`):
    `y (t + h) - (Y + h * F t Y) = (y (t + h) - y t - h * y' t) + ((y t - Y) + h * (F t (y t) - F t Y))`.
    Main: `discrete_gronwall (fun k : ℕ => |y (t₀ + k * h) - eulerSeq F t₀ (y t₀) h k|) (h * L) (M * h ^ 2)
    (by positivity) (by positivity) (abs_nonneg _) (error_step F y y' t₀ h L M hh hy hode hlip hF) n`,
    then `simpa [eulerSeq] using this`.
-/
