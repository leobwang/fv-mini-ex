/- M05 | Postage stamps | 10 min | strong induction, Nat.strongRecOn
GOAL
  Every amount `n ≥ 8` can be paid with 3- and 5-cent stamps. Use strong induction: the
  case `n` may use the result for `n - 3`.

REFERENCE
  example (n : Nat) : n = n := by
    induction n using Nat.strongRecOn with
    | _ n ih => rfl        -- ih : ∀ m < n, P m   (P = the goal, as a function of n)
  example (n : Nat) (h : 3 ≤ n) : n - 3 < n := by omega
  example (P : Prop) (h : 1 = 1 → P) : P := by
    by_cases h1 : (1 : Nat) = 1      -- peel off base cases one by one
    · exact h h1
    · exact absurd rfl h1
-/

-- BEGIN SPEC
theorem stamps (n : Nat) (h : 8 ≤ n) : ∃ a b : Nat, n = 3 * a + 5 * b :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Going from `n - 3` to `n` adds one 3-cent stamp. Which `n` have no `n - 3 ≥ 8`?
H2. Base cases 8, 9, 10; otherwise `n ≥ 11`, so apply `ih (n - 3)`.
H3. `obtain ⟨a, b, hab⟩ := ih (n - 3) (by omega) (by omega)` then `exact ⟨a + 1, b, by omega⟩`.
-/
