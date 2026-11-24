/- M003 | Postage stamps | 10 min | strong induction, Nat.strongRecOn
GOAL
  Every amount `n ≥ 8` can be paid with 3- and 5-cent stamps. Use strong induction: the
  case `n` may use the result for `n - 3`.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · stamps
  1. Strong induction on `n`. `h : 8 ≤ n` mentions `n`, so `ih` gets the
     extra premise: ih : ∀ (m : Nat), m < n → 8 ≤ m → ∃ a b, …              R1, R2
  2. Base cases: the `n` with `n - 3 < 8` are 8, 9, 10. For each one:
       split it off                                                         R3
       give the two stamp counts, prove the equation from `n = 8` etc.      R4 → R5
  3. Now `n ≥ 11` (from `h` and the three negations). Use `ih` at `n - 3`,
     its two side conditions `n - 3 < n`, `8 ≤ n - 3` by `(by omega)`,
     and unpack the resulting `∃`:                                          R6 + R7, R5
  4. One more 3-cent stamp than the counts for `n - 3`:                     R4 → R5
-/
-- BEGIN SPEC
theorem stamps (n : Nat) (h : 8 ≤ n) : ∃ a b : Nat, n = 3 * a + 5 * b :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Going from `n - 3` to `n` adds one 3-cent stamp, so you need the claim at `n - 3`, not at `n - 1`:
    strong induction (R1). Which `n ≥ 8` have no `n - 3 ≥ 8`? Those are your base cases.
H2. `induction n using Nat.strongRecOn with | _ n ih => …`; note `ih` also asks for `8 ≤ m` (R2).
    Split off `n = 8`, `n = 9`, `n = 10` with `by_cases` and give witnesses (R3, R4, R5); otherwise
    `n ≥ 11`, so apply `ih (n - 3)` (R6, R7).
H3. `obtain ⟨a, b, hab⟩ := ih (n - 3) (by omega) (by omega)` then `exact ⟨a + 1, b, by omega⟩`.
-/
