/- E051 | Congruence | 2-3 min | congrArg, congrFun, congr
GOAL
  Push equalities through functions (`congrArg`), evaluate a function equality at a point
  (`congrFun`), and split `f a c = f b d` into argument equalities (`congr`).

REFERENCE
  #check @congrArg   -- (f : α → β) → a₁ = a₂ → f a₁ = f a₂
  #check @congrFun   -- f = g → ∀ a, f a = g a
  example (a b : Nat) (h : a = b) : a * 3 = b * 3 := congrArg (· * 3) h  -- `(· * 3)` = fun x => x * 3
  example (f g : Nat → Nat) (h : f = g) : f 0 = g 0 := congrFun h 0
  example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by congr
    -- `congr` reduces `f x = f y` to `x = y` and closes such goals by `rfl` or a hypothesis
  #check @Nat.succ_ne_self   -- n.succ ≠ n      (`x ≠ y` means `x = y → False`)
BANNED: rw, subst, simp, simpa, simp_all, grind, cases, rcases, obtain, match, ▸, Eq.subst, Eq.mpr, Eq.mp, Eq.rec, Eq.ndrec, Eq.recOn, solve_by_elim, exact?, apply?, try?
NOTE: `▸` (E046) is banned so you meet the congruence lemmas. `congr` closes `congr_arg_ex` too; save it for `congr_two`.
-/

namespace E051

-- BEGIN SPEC
theorem congr_arg_ex (f g : Nat → Nat) (a b : Nat) (h : a = b) : f (g a) = f (g b) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem congr_fun_ex (f g : Nat → Nat) (h : f = g) (x : Nat) : f x + 1 = g x + 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem succ_ne_id : (fun n : Nat => n + 1) ≠ (fun n => n) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem congr_two (f : Nat → Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : c = d) :
    f a c = f b d :=
-- END SPEC
  sorry

end E051

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `congrArg F h` needs the "context" `F` around the part that changes: here `F` is a lambda.
H2. `congr_fun_ex`: first `congrFun h x : f x = g x`, then add one with `congrArg`.
    `succ_ne_id`: assume the functions are equal and evaluate both sides at `0`.
H3. `congr_arg_ex`: `congrArg (fun x => f (g x)) h`;
    `succ_ne_id`: `fun h => Nat.succ_ne_self 0 (congrFun h 0)`; `congr_two`: `by congr`.
-/
