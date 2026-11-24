/- M119 | Discrete Gronwall inequality | 15 min | induction, strengthening, exp bound, error recursion, mathlib
GOAL
  If an error sequence obeys `eₙ₊₁ ≤ (1 + a) eₙ + b` with `a, b, e₀ ≥ 0`, then `eₙ ≤ e^(na) (e₀ + n b)`.
  This discrete Gronwall inequality is how one bounds the global error of a one-step ODE method
  (`b` = local error per step, `1 + a` = how much one step can amplify an existing error).

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M119

/- SKELETON · discrete_gronwall
  1. MILESTONE first (used in step 2): the sharper bound with `(1 + a) ^ n` in place of `exp`,
       have key : ∀ n : ℕ, e n ≤ (1 + a) ^ n * (e 0 + n * b)
     proof: intro n, then induction on n                                      R1
       zero: clean up `^ 0` and `↑0`                                          R2
       succ: a fact for later  h1 : (1:ℝ) ≤ (1 + a) ^ n                       R3 with R4
             then a three-step chain                                          R5
               e (n + 1) ≤ (1 + a) * e n + b                                 hstep n
               _ ≤ (1 + a) * ((1 + a) ^ n * (e 0 + n * b)) + b               R6 (closes with ih)
               _ ≤ (1 + a) ^ (n + 1) * (e 0 + (n + 1 : ℕ) * b)               R7 → R8 → R10 with R9 on h1
             (write `(n + 1 : ℕ)` so the last line matches the goal's `↑(n + 1)`)
  2. Main chain                                                               R5
       e n ≤ (1 + a) ^ n * (e 0 + n * b)                                      key n
       _ ≤ Real.exp (n * a) * (e 0 + n * b)                                   R11, leaving (1 + a) ^ n ≤ Real.exp (↑n * a)
          (its side goal 0 ≤ e 0 + ↑n * b is closed by `positivity` from he0, hb)
     that last goal by a two-step chain                                       R5
       (1 + a) ^ n ≤ Real.exp a ^ n                                           R12, then R4 with R13
       _ = Real.exp (n * a)                                                   R14
-/
-- BEGIN SPEC
theorem discrete_gronwall (e : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (he0 : 0 ≤ e 0)
    (hstep : ∀ n, e (n + 1) ≤ (1 + a) * e n + b) (n : ℕ) :
    e n ≤ Real.exp (n * a) * (e 0 + n * b) :=
-- END SPEC
  sorry

end M119

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Inducting on the statement as given is awkward because of the exponential. Prove a sharper bound with
    `(1 + a) ^ n` in place of `e^(na)` first (a `have key : ∀ n : ℕ, …`), then compare the two factors.
H2. Claim `e n ≤ (1 + a) ^ n * (e 0 + n * b)`, by `intro n; induction n with …`. Step: `calc` from `hstep n`,
    then `gcongr` (it uses `ih`); what remains is `(1+a)·(1+a)ⁿ(e₀ + nb) + b ≤ (1+a)ⁿ⁺¹(e₀ + (n+1)b)`, true
    because `1 ≤ (1+a)ⁿ`. Finally `calc` with `key n`, `gcongr`, and `(1 + a)ⁿ ≤ (e^a)ⁿ = e^(na)`.
H3. Last step of the induction: `push_cast; rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 + a)]`
    with `h1 : (1:ℝ) ≤ (1 + a) ^ n := one_le_pow₀ (by linarith)`. End: `gcongr`, then
    `(1 + a) ^ n ≤ Real.exp a ^ n` by `gcongr; linarith [Real.add_one_le_exp a]`, and `rw [← Real.exp_nat_mul]`.
-/
