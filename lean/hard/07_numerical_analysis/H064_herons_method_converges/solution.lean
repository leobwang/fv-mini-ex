/- H064 | Heron's method converges | 1-1.25 h | monotone convergence, ciInf, limit identification, Filter.Tendsto, Real.sqrt, mathlib
GOAL
  Heron's iteration `xₙ₊₁ = (xₙ + a / xₙ) / 2` (`a > 0`, `x₀ > 0`) converges to `√a`: from step 1 on it
  decreases and stays `≥ √a`, so it has a limit `L > 0`, and the recursion in the limit forces `L = √a`.
  Milestones 1-3 are M109's specs (`babylon_error`, `sqrt_le_babylon`, `babylon_le`): paste your proofs.

GUIDE
  Entries R1–R29: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Filter Topology

namespace H064

-- BEGIN SPEC
-- the Babylonian (Newton) step for √a
noncomputable def babylon (a x : ℝ) : ℝ := (x + a / x) / 2

/-- Heron's iteration from `x₀`: `heron a x₀ n = xₙ` -/
noncomputable def heron (a x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => babylon a (heron a x₀ n)
-- END SPEC

-- MILESTONE (optional: change or delete)  (proved in M109: paste your proof)
-- error identity: the step's overshoot above `√a` is a square over `2x`
/- SKELETON · babylon_error
  1. Unfold the step:                                               R1
  2. The square-root fact  hs : √a ^ 2 = a                          R2
  3. Clear the denominator 2 * x (hx is in the context):            R3
       goal: a polynomial identity in x, a, √a
  4. Close it with hs as a hint:                                    R4 (R6 also works)
-/
theorem babylon_error (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) :
    babylon a x - √a = (x - √a) ^ 2 / (2 * x) := by
  unfold babylon
  have hs := Real.sq_sqrt ha
  field_simp
  nlinarith [hs]

-- MILESTONE (optional: change or delete)  (proved in M109: paste your proof)
/- SKELETON · sqrt_le_babylon
  1. he : babylon a x - √a = (x - √a) ^ 2 / (2 * x)                MILESTONE babylon_error
  2. have : 0 ≤ (x - √a) ^ 2 / (2 * x)                              R5
  3. Combine the two:                                               R6
-/
theorem sqrt_le_babylon (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) : √a ≤ babylon a x := by
  have he := babylon_error a x ha hx
  have : 0 ≤ (x - √a) ^ 2 / (2 * x) := by positivity
  linarith

-- MILESTONE (optional: change or delete)  (proved in M109: paste your proof)
/- SKELETON · babylon_le
  1. Unfold the step:                                               R1
  2. hax : a / x ≤ x
       multiply out the division:                                   R7
       a ≤ x * x from √a ≤ x, with hint terms 0 ≤ √a and √a ^ 2 = a:  R4 with R8, R2
  3. (x + a / x) / 2 ≤ x from hax:                                  R6
-/
theorem babylon_le (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) (hsx : √a ≤ x) : babylon a x ≤ x := by
  unfold babylon
  have hax : a / x ≤ x := by
    rw [div_le_iff₀ hx]
    nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt ha]
  linarith

-- MILESTONE (optional: change or delete)
/- SKELETON · heron_ge
  1. Induction on n:                                                R9
  2. zero: heron a x₀ (0 + 1) is babylon a x₀ by definition (R10);
       MILESTONE sqrt_le_babylon with 0 ≤ a from 0 < a:             R11
  3. succ: heron a x₀ (n + 1 + 1) is babylon a (heron a x₀ (n + 1)) (R10);
       MILESTONE sqrt_le_babylon again; the iterate is positive because
       0 < √a ≤ heron a x₀ (n + 1) (ih):                            R11, R12 with R13
-/
theorem heron_ge (a x₀ : ℝ) (ha : 0 < a) (hx : 0 < x₀) (n : ℕ) : √a ≤ heron a x₀ (n + 1) := by
  induction n with
  | zero => exact sqrt_le_babylon a x₀ ha.le hx
  | succ n ih => exact sqrt_le_babylon a _ ha.le (lt_of_lt_of_le (Real.sqrt_pos.mpr ha) ih)

-- MILESTONE (optional: change or delete)
-- the only positive fixed point of the step is `√a`
/- SKELETON · fixed_point_eq_sqrt
  1. Unfold the step in h:                                          R14
  2. hsq : L ^ 2 = a
       clear the denominators in h:                                 R15
       h : L ^ 2 + a = L ^ 2 * 2, then                              R4 (R6 also works)
  3. Turn √a into √(L ^ 2), then take the root (0 ≤ L from 0 < L):  rw [← hsq], R16 with R11
-/
theorem fixed_point_eq_sqrt (a L : ℝ) (hL : 0 < L) (h : babylon a L = L) : L = √a := by
  unfold babylon at h
  have hsq : L ^ 2 = a := by
    field_simp at h
    nlinarith
  rw [← hsq, Real.sqrt_sq hL.le]

/- SKELETON · heron_tendsto
  Prove the five MILESTONE lemmas above first; this proof combines them.
  1. hs : 0 < √a                                                    R13
  2. Name the shifted sequence:
       set g := fun n => heron a x₀ (n + 1) with hg                 R17
  3. hge : ∀ n, √a ≤ g n                                            MILESTONE heron_ge
  4. anti : Antitone g                                              R18
       each step g (n + 1) ≤ g n is babylon a (g n) ≤ g n (R10):
       MILESTONE babylon_le, with 0 < g n from hs and hge n         R11, R12
  5. bdd : BddBelow (Set.range g), bound √a                         R19, R20, hge
  6. tg : Tendsto g atTop (𝓝 (⨅ n, g n))                            R21
     set L := ⨅ n, g n                                              R17
  7. hL0 : 0 < L                                                    R12 with R22 (and hge)
  8. Two limits of the sequence n ↦ g (n + 1) = babylon a (g n):
       hc  : ContinuousAt (babylon a) L                             R1, R24 with R23
       tb  : Tendsto (fun n => babylon a (g n)) atTop (𝓝 (babylon a L))   R25, R26
       tg1 : Tendsto (fun n => g (n + 1)) atTop (𝓝 L)                R26, R27
       hfix : babylon a L = L                                       R28
  9. Shift the goal back to g, replace √a by L, and finish with tg:
       R29, rw [← MILESTONE fixed_point_eq_sqrt a L hL0 hfix], exact tg
-/
-- BEGIN SPEC
theorem heron_tendsto (a x₀ : ℝ) (ha : 0 < a) (hx : 0 < x₀) :
    Tendsto (heron a x₀) atTop (𝓝 √a) :=
-- END SPEC
  by
    have hs : 0 < √a := Real.sqrt_pos.mpr ha
    set g := fun n => heron a x₀ (n + 1) with hg
    have hge : ∀ n, √a ≤ g n := heron_ge a x₀ ha hx
    have anti : Antitone g :=
      antitone_nat_of_succ_le fun n => babylon_le a (g n) ha.le (lt_of_lt_of_le hs (hge n)) (hge n)
    have bdd : BddBelow (Set.range g) := ⟨√a, by rintro _ ⟨n, rfl⟩; exact hge n⟩
    have tg : Tendsto g atTop (𝓝 (⨅ n, g n)) := tendsto_atTop_ciInf anti bdd
    set L := ⨅ n, g n
    have hL0 : 0 < L := lt_of_lt_of_le hs (le_ciInf hge)
    -- `g (n + 1) = babylon a (g n)`: the same sequence has limits `babylon a L` and `L`
    have hc : ContinuousAt (babylon a) L := by
      unfold babylon
      fun_prop (disch := exact hL0.ne')
    have tb : Tendsto (fun n => babylon a (g n)) atTop (𝓝 (babylon a L)) := hc.tendsto.comp tg
    have tg1 : Tendsto (fun n => g (n + 1)) atTop (𝓝 L) := tg.comp (tendsto_add_atTop_nat 1)
    have hfix : babylon a L = L := tendsto_nhds_unique tb tg1
    rw [← tendsto_add_atTop_iff_nat 1, ← fixed_point_eq_sqrt a L hL0 hfix]
    exact tg

end H064

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. From step 1 on the iterates are `≥ √a` and decrease (milestones `heron_ge`, `babylon_le`), but
    `x₀` may be below `√a`. So work with the shifted sequence `g n := heron a x₀ (n + 1)` (R17): it has
    a limit `L := ⨅ n, g n` (monotone convergence), and at the end shift back (R29). Prove the
    milestones in file order; the first three are M109's.
H2. Monotone convergence: `Antitone g` from one-step decrease (R18), a lower bound `√a` (R19, R20),
    then R21; and `√a ≤ L` (R22), so `L > 0`. Identify the limit: `g (n + 1)` *is* `babylon a (g n)`
    (R10). That one sequence tends to `babylon a L` (continuity at `L ≠ 0`, R24–R26) and to `L` (a tail
    of `g`, R26–R27), so `babylon a L = L` (R28), and `fixed_point_eq_sqrt` gives `L = √a`
    (clear denominators to get `L ^ 2 = a`, R15).
H3. `have tg := tendsto_atTop_ciInf anti bdd`; `have hL0 : 0 < L := lt_of_lt_of_le hs (le_ciInf hge)`;
    `have hc : ContinuousAt (babylon a) L := by unfold babylon; fun_prop (disch := exact hL0.ne')`;
    `have hfix := tendsto_nhds_unique (hc.tendsto.comp tg) (tg.comp (tendsto_add_atTop_nat 1))`.
    Last step: `rw [← tendsto_add_atTop_iff_nat 1, ← fixed_point_eq_sqrt a L hL0 hfix]; exact tg`.
-/
