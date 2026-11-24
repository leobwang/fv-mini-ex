/- E020 | calc | 3 min | calc, Nat.add_mul
GOAL
  Write proofs as `calc` chains of equalities and inequalities.
BANNED: grind

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · calc_lt
  1. One `calc` chain from `a` to `d`, one step per hypothesis, in the order
     `<`, `≤`, `<`; the chain's relation is then `<`:                           R1, R2
  2. Each step is proved by its hypothesis (a term, no `by` needed).
-/
-- BEGIN SPEC
theorem calc_lt (a b c d : Nat) (h1 : a < b) (h2 : b ≤ c) (h3 : c < d) : a < d :=
-- END SPEC
  calc a < b := h1
    _ ≤ c := h2
    _ < d := h3

/- SKELETON · calc_sq
  1. A `calc` chain of three `=` steps from `a * a` to `4 * (b * b)`:            R1
     (to see the goal a step starts from, write `by calc …` and prove the step
     by `?_` first; `?_` needs tactic mode:                                     R3)
  2. Step 1, substitute:  `a * a = (b + b) * (b + b)`                            R4 (h1, then h2)
  3. Step 2, expand:      `_ = b * b + b * b + (b * b + b * b)`                  R5 → R6
  4. Step 3, collect the four `b * b` atoms:  `_ = 4 * (b * b)`                  R7
-/
-- BEGIN SPEC
theorem calc_sq (a b c : Nat) (h1 : a = b + c) (h2 : c = b) : a * a = 4 * (b * b) :=
-- END SPEC
  calc a * a = (b + b) * (b + b) := by rw [h1, h2]
    _ = b * b + b * b + (b * b + b * b) := by rw [Nat.add_mul, Nat.mul_add]
    _ = 4 * (b * b) := by omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `calc_lt` is three steps, one per hypothesis. `calc_sq`: `omega` cannot expand `(b + b) * (b + b)`
    (a product is one unknown to it), so a middle step must expand it first.
H2. `calc_lt`: `calc a < b := …`, then `_ ≤ c`, then `_ < d` (R1, R2).
    `calc_sq`: substitute with `rw [h1, h2]` (R4), expand with `Nat.add_mul` then `Nat.mul_add` (R5, R6),
    collect with `omega` (R7).
H3. Steps: `a * a = (b + b) * (b + b)` by `rw [h1, h2]`, `_ = b * b + b * b + (b * b + b * b)` by
    `rw [Nat.add_mul, Nat.mul_add]`, `_ = 4 * (b * b)` by `omega`.
-/
