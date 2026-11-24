/- M097 | Stationary distribution of a 2-state chain | 15 min | Markov chain, Matrix.vecMul, fin_cases, field_simp, mathlib
GOAL
  A chain on states {0, 1} leaves state 0 with probability `a` and state 1 with probability `b`
  (`a + b > 0`). Show its stationary distributions (probability vectors `π` with `π P = π`) are
  exactly `π = (b / (a + b), a / (a + b))`. The statement only assumes `a, b ≥ 0`, `a + b > 0`.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M097

-- BEGIN SPEC
/-- transition matrix: row `i` is the distribution of the next state from state `i`
    (leave state 0 w.p. `a`, leave state 1 w.p. `b`). -/
def P (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - a, a; b, 1 - b]

/-- `π` is a probability vector fixed by the chain: `π P = π`. -/
def IsStationary (a b : ℝ) (π : Fin 2 → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ π 0 + π 1 = 1 ∧ Matrix.vecMul π (P a b) = π
-- END SPEC

/- SKELETON · stationary_iff
  1. Before splitting, the denominator fact, so both halves have it:            R1
       hne : a + b ≠ 0          (field_simp needs it, R12)
  2. Split the ↔ into (→) `mp` and (←) `mpr`:                                    R2
  3. (→) Take the hypothesis apart; nonnegativity is not needed:                 R3
       Coordinate 0 of the fixed-point equation, as a new hypothesis h0:         R4
       Evaluate h0 into an equation between reals (unfold `P` as well):          R5 with R6 → R7 → R8
       Vector equation → two coordinate goals:                                   R9 → R10
       In each coordinate: read the literal, clear `a + b`, close:               R11 → R12 → R13
  4. (←) Substitute the literal vector for `π`:                                  R14
       Split `IsStationary` into its three parts:                                R15
         nonnegativity   `intro i`, then                                         R10 → R11 → R16
         sum = 1                                                                 R11 → R12 → ring
         π P = π         coordinates, then step 3's `simp [...]` list on the goal
                         (no `at`; it also reads the literal, R11):              R9 → R10 → R6–R8, R11 → R12 → ring
-/
-- BEGIN SPEC
theorem stationary_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) (π : Fin 2 → ℝ) :
    IsStationary a b π ↔ π = ![b / (a + b), a / (a + b)] :=
-- END SPEC
  by
    have hne : a + b ≠ 0 := hab.ne'
    constructor
    · rintro ⟨-, hsum, hfix⟩
      -- coordinate 0 of `π P = π`: `π 0 * (1 - a) + π 1 * b = π 0`
      have h0 := congrFun hfix 0
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] at h0
      ext i; fin_cases i
      · simp; field_simp; nlinarith
      · simp; field_simp; nlinarith
    · rintro rfl
      refine ⟨?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> positivity
      · simp; field_simp; ring
      · ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] <;> field_simp <;> ring

end M097

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Coordinate 0 of `π P = π` reads `π 0 * (1 - a) + π 1 * b = π 0`, i.e. `a * π 0 = b * π 1`.
    With `π 0 + π 1 = 1` that pins `π` down. The converse is three direct checks on the literal vector.
H2. `have hne : a + b ≠ 0 := hab.ne'`, then `constructor`. (→) `rintro ⟨-, hsum, hfix⟩`,
    `have h0 := congrFun hfix 0`, evaluate `h0` with `simp [...] at h0`, then `ext i; fin_cases i`.
    (←) `rintro rfl; refine ⟨?_, ?_, ?_⟩`.
H3. `simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] at h0`; each (→) coordinate closes with
    `simp; field_simp; nlinarith`. (←) nonnegativity: `intro i; fin_cases i <;> simp <;> positivity`;
    the sum: `simp; field_simp; ring`; the fixed point:
    `ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] <;> field_simp <;> ring`.
-/
