/- E023 | Implicit arguments | 3 min | implicit arguments, @, named arguments
GOAL
  Use a lemma whose arguments are implicit: let Lean infer them, name them, or pass all with `@`.

REFERENCE
  theorem le_succ' {n : Nat} : n ≤ n + 1 := Nat.le_succ n   -- `{n}`: inferred from the goal
  example : 3 ≤ 4 := le_succ'                     -- n := 3 inferred
  example : 3 ≤ 4 := le_succ' (n := 3)            -- named argument
  example : 3 ≤ 4 := @le_succ' 3                  -- `@` makes every argument explicit
  example (h : ∀ {k : Nat}, k ≤ 10) : 2 ≤ 10 := @h 2   -- implicit binders in hypotheses too
  `#check @Nat.le_trans` shows all arguments, including implicit ones.
BANNED: omega, grind, simp
-/

-- BEGIN SPEC
theorem my_le_trans {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := Nat.le_trans h1 h2
-- END SPEC

-- BEGIN SPEC
theorem use_inferred (x : Nat) (h1 : x ≤ 5) (h2 : 5 ≤ 7) : x ≤ 7 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem use_named (h1 : 2 ≤ 4) (h2 : 4 ≤ 9) : 2 ≤ 9 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem use_explicit : ∀ (a b c : Nat), a ≤ b → b ≤ c → a ≤ c :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem hyp_implicit (f : Nat → Nat) (h : ∀ {n : Nat}, f n = n) : f (f 3) = 3 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `my_le_trans h1 h2` only needs the two proofs; `a b c` come from their types.
H2. `use_explicit` asks for a function of `a b c`: that is exactly `@my_le_trans`.
H3. `hyp_implicit`: `@h 3 : f 3 = 3`; rewrite with it twice (`rw [@h 3, @h 3]`), or use `congrArg f (@h 3)`.
-/
