/- H098 | Mean-field Curie–Weiss transition | 1-1.5 h | tanh inequalities, derivative monotonicity, intermediate value theorem, mathlib
GOAL
  Mean-field (Curie–Weiss) theory: the magnetisation per spin `m` solves `m = tanh (a * m)`, where
  `a = βJz` (β = 1/(kB T), J = coupling, z = number of neighbours). Prove a solution `m > 0`
  (spontaneous magnetisation) exists iff `a > 1`, i.e. iff `T < T_c = Jz/kB`.

GUIDE
  Entries R1–R46: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H098

/- SKELETON · tanh_exp_form   (milestone 1; used by milestones 2 and 3)
  1. Unfold tanh into exponentials:                                         R1
  2. Write 2 * y as y + y, then split exp (y + y) and exp (-y):             R2, R3, R4
  3. Put 0 < exp y in the context, then clear the denominators:             R5, R6
-/
-- MILESTONE (optional: change or delete)
theorem tanh_exp_form (y : ℝ) :
    Real.tanh y = (Real.exp (2 * y) - 1) / (Real.exp (2 * y) + 1) := by
  rw [Real.tanh_eq, show 2 * y = y + y by ring, Real.exp_add, Real.exp_neg]
  have := Real.exp_pos y
  field_simp

/- SKELETON · tanh_lt_self   (milestone 2; uses milestone 1; used in the (←) direction)
  Idea: f y = (1 + y) * exp (-2 * y) - (1 - y) has f 0 = 0 and is strictly increasing on [0, ∞).
  1. Name f:                                                                R7
  2. hmono : StrictMonoOn f (Set.Ici 0)
       reduce to a positive derivative, continuity by fun_prop:             R8, R9
       intro x hx; make hx into 0 < x:                                      R10
       hd : HasDerivAt f (1 - (1 + 2 * x) * Real.exp (-2 * x)) x
         three pieces, each from hasDerivAt_id x and cleaned by R16:
           h1 : HasDerivAt (fun y => 1 + y) 1 x                             R11 → R12
           h2 : HasDerivAt (fun y => Real.exp (-2 * y)) (Real.exp (-2 * x) * (-2)) x
                                                                            R11 → R13 → R14
           h3 : HasDerivAt (fun y => 1 - y) (-1) x                          R11 → R15
         combine them and restate the derivative (by ring):                 R17, R18, R19
       rewrite deriv f x with hd:                                           R20
       facts: 2 * x + 1 < exp (2 * x)  (side goal by R21):                  R22
              exp (2 * x) * exp (-2 * x) = 1:                               rw [← Real.exp_add] (R3), R23
       finish, hint exp_pos (-2 * x):                                       R24
  3. key : f 0 < f y from hmono at 0 and y:                                 R25, R26
     unfold f and evaluate at 0 in key:                                     R27, R28
  4. tanh y < y: milestone 1, clear the denominator (side goal R21):       rw [tanh_exp_form], R29
     exp (2 * y) * exp (-2 * y) = 1 as in step 2, finish with hints:        R3, R23, R24 with R5
-/
-- MILESTONE (optional: change or delete)
theorem tanh_lt_self (y : ℝ) (hy : 0 < y) : Real.tanh y < y := by
  -- f y = (1 + y) e^{-2y} - (1 - y) vanishes at 0 and is strictly increasing on [0, ∞)
  let f : ℝ → ℝ := fun y => (1 + y) * Real.exp (-2 * y) - (1 - y)
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici] at hx
    have hd : HasDerivAt f (1 - (1 + 2 * x) * Real.exp (-2 * x)) x := by
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (-2 * y)) (Real.exp (-2 * x) * (-2)) x := by
        simpa using ((hasDerivAt_id x).const_mul (-2)).exp
      have h3 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      exact ((h1.mul h2).sub h3).congr_deriv (by ring)
    rw [hd.deriv]
    have hx0 : (0 : ℝ) < x := hx
    have hlt : 2 * x + 1 < Real.exp (2 * x) := Real.add_one_lt_exp (by positivity)
    have hinv : Real.exp (2 * x) * Real.exp (-2 * x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-2 * x)]
  have key := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy.le) hy
  simp only [f, mul_zero, Real.exp_zero, add_zero, sub_zero, mul_one, sub_self] at key
  rw [tanh_exp_form, div_lt_iff₀ (by positivity)]
  have hinv : Real.exp (2 * y) * Real.exp (-2 * y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (2 * y), Real.exp_pos (-2 * y)]

/- SKELETON · le_tanh   (milestone 3; uses milestone 1; used in the (→) direction)
  1. Milestone 1, then cross-multiply (side goals by R21):                  rw [tanh_exp_form], R30
  2. Finish with exp (2 * y) ≥ 2 * y + 1 as a hint:                         R24 with R31
-/
-- MILESTONE (optional: change or delete)
theorem le_tanh (y : ℝ) (hy : 0 ≤ y) : y / (1 + y) ≤ Real.tanh y := by
  rw [tanh_exp_form, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.add_one_le_exp (2 * y)]

/- SKELETON · continuous_tanh   (milestone 4; used in the (→) direction)
  1. Replace tanh by fun x => sinh x / cosh x (Real.tanh_eq_sinh_div_cosh): R32
  2. Quotient of continuous functions, denominator ≠ 0:                     R33: R9, R9, R34
-/
-- MILESTONE (optional: change or delete)
theorem continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from funext Real.tanh_eq_sinh_div_cosh]
  exact Continuous.div (by fun_prop) (by fun_prop) fun x => (Real.cosh_pos x).ne'

/- SKELETON · mean_field_transition
  Prove the four milestones first: tanh_exp_form (used by tanh_lt_self, le_tanh),
  tanh_lt_self (used in step 8), le_tanh (step 3), continuous_tanh (step 4).
  Split the ↔ with constructor (E005).
  (→) intro h1 : 1 < a.
  1. m₀ := (a - 1) / (2 * a):                                               R35
  2. hm₀pos : 0 < m₀                                                        R36, R37
     hm₀1 : m₀ ≤ 1                                                          rw [hm₀], R38, R37
     ham₀ : a * m₀ = (a - 1) / 2                                            rw [hm₀], R6
  3. g := fun m => Real.tanh (a * m) - m:                                   R7
     hg0 : 0 ≤ g m₀   le_tanh at a * m₀ (side goal R21), then
                      m₀ ≤ a * m₀ / (1 + a * m₀):                           R39 (side goal R21), rw [ham₀], R24
                      unfold g, finish:                                     R27, R37
     hg1 : g 1 ≤ 0    unfold g (with mul_one), tanh a < 1:                  R27, R40, R37
  4. hcont : ContinuousOn g (Set.Icc m₀ 1), with continuous_tanh in context: R41, R9
  5. IVT on [m₀, 1] and unpack m, hm, hgm:                                  R42 → R43
  6. Give m: 0 < m from 0 < m₀ ≤ m; tanh (a * m) = m from hgm:              R44, R27, R37
  (←) rintro ⟨m, hm, heq⟩ (E005).
  7. Suppose a ≤ 1:                                                         R45, R46
  8. tanh (a * m) < a * m (milestone 2, side goal R21), then finish:        R24
-/
-- BEGIN SPEC
theorem mean_field_transition (a : ℝ) (ha : 0 < a) :
    1 < a ↔ ∃ m : ℝ, 0 < m ∧ Real.tanh (a * m) = m :=
-- END SPEC
  by
    constructor
    · intro h1
      -- g m = tanh (a m) - m changes sign on [m₀, 1]
      set m₀ := (a - 1) / (2 * a) with hm₀
      have hm₀pos : 0 < m₀ := div_pos (by linarith) (by linarith)
      have hm₀1 : m₀ ≤ 1 := by rw [hm₀, div_le_one (by linarith)]; linarith
      have ham₀ : a * m₀ = (a - 1) / 2 := by rw [hm₀]; field_simp
      let g : ℝ → ℝ := fun m => Real.tanh (a * m) - m
      have hg0 : 0 ≤ g m₀ := by
        have h := le_tanh (a * m₀) (by positivity)
        have hk : m₀ ≤ a * m₀ / (1 + a * m₀) := by
          rw [le_div_iff₀ (by positivity), ham₀]
          nlinarith
        simp only [g]
        linarith
      have hg1 : g 1 ≤ 0 := by
        simp only [g, mul_one]
        linarith [Real.tanh_lt_one a]
      have hcont : ContinuousOn g (Set.Icc m₀ 1) := by
        have := continuous_tanh
        exact (by fun_prop : Continuous g).continuousOn
      obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' hm₀1 hcont ⟨hg1, hg0⟩
      refine ⟨m, lt_of_lt_of_le hm₀pos hm.1, ?_⟩
      simp only [g] at hgm
      linarith
    · rintro ⟨m, hm, heq⟩
      by_contra h
      push Not at h
      -- m = tanh (a m) < a m ≤ m
      have := tanh_lt_self (a * m) (by positivity)
      nlinarith

end H098

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (←) If `a ≤ 1` and `m > 0` solved it, `m = tanh (a m) < a m ≤ m`. (→) `g m = tanh (a m) - m` is
    `≥ 0` at a small `m₀ > 0` and `< 0` at `m = 1` (`tanh < 1`, R40): use the intermediate value theorem
    for a decreasing sign change (R42). Everything rests on `y / (1 + y) ≤ tanh y < y` for `y > 0`.
H2. Milestone 1 rewrites `tanh y = (e^{2y} - 1)/(e^{2y} + 1)`. Then `tanh y < y` ⇔ `1 - y < (1 + y) e^{-2y}`:
    `f y = (1 + y) e^{-2y} - (1 - y)` has `f 0 = 0` and `f' y = 1 - (1 + 2y) e^{-2y} > 0` for `y > 0`
    (since `e^{2y} > 1 + 2y`, R22), so `f` is strictly increasing on `[0, ∞)` (R8). The lower bound is
    cross-multiplication (R30) plus `e^{2y} ≥ 1 + 2y` (R31). Continuity of tanh goes through sinh / cosh (R32).
H3. (→): `set m₀ := (a - 1) / (2 * a) with hm₀`, so `a * m₀ = (a - 1) / 2`; then
    `obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' hm₀1 hcont ⟨hg1, hg0⟩`.
    `tanh_lt_self`: `apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)`, then `rw [hd.deriv]` where
    `hd : HasDerivAt f (1 - (1 + 2 * x) * Real.exp (-2 * x)) x`; finish with
    `nlinarith [Real.exp_pos (-2 * x)]` using `Real.exp (2 * x) * Real.exp (-2 * x) = 1` in the context.
-/
