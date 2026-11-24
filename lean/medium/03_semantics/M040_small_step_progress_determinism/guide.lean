/- Guide for M040 (Small-step arithmetic: progress and determinism).
Part R: one reference entry per tactic or proof-term move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P`, `G` stand for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `k…` in an entry is only there to finish the example; it shows what the goal became.
The entries work on a toy language defined below (`Ex`, `Red`), NOT the exercise's `Expr`, `Step`.
Part W: worked combinations on the same toy objects.
Assumed: Lean basics (E001–E033). No Mathlib: everything is core Lean.
-/

namespace M040Guide

/-! # Toy objects (not the exercise's) -/

/-- Toy syntax: numerals `k n`, truncated subtraction `sub a b`, doubling `dbl a`. -/
inductive Ex where
  | k (n : Nat)
  | sub (a b : Ex)
  | dbl (a : Ex)

/-- `Red e e'`: `e` reduces to `e'` in one step. A proof of `Red e e'` is a tree of these rules
(a *derivation*). `subK`, `dblK` compute on numerals; `subL`, `subR`, `dblC` reduce inside a
subexpression (*congruence* rules); `subR` only fires once the left side is a numeral. -/
inductive Red : Ex → Ex → Prop
  | subK {m n : Nat} : Red (.sub (.k m) (.k n)) (.k (m - n))
  | subL {a a' b : Ex} : Red a a' → Red (.sub a b) (.sub a' b)
  | subR {m : Nat} {b b' : Ex} : Red b b' → Red (.sub (.k m) b) (.sub (.k m) b')
  | dblK {n : Nat} : Red (.dbl (.k n)) (.k (2 * n))
  | dblC {a a' : Ex} : Red a a' → Red (.dbl a) (.dbl a')

/-! # Part R · Reference entries -/

/-! ## A numeral does not step: inversion with no matching rule -/

/-! ### R1. `intro h` · goal `¬ A` → context gains `h : A`, goal `False`
`¬ A` is notation for `A → False`, so `intro` works on it like on any implication. -/
example (A : Prop) (k : A → False) : ¬ A := by
  intro h
  exact k h

/-! ### R2. `cases h` where no rule can produce `h` · goal list: closes the goal
Every rule of `Red` concludes `Red (.sub …) _` or `Red (.dbl …) _`; none has `.k n` on the left,
so no case is left to prove. -/
example (n : Nat) (e : Ex) (G : Prop) (h : Red (.k n) e) : G := by
  cases h

/-! ## Progress: structural induction on the syntax -/

/-! ### R3. `induction e` with `e : Ex` · goal list: one goal per constructor of `Ex`; every
argument of type `Ex` gets an induction hypothesis (IH) `a_ih✝`.
`induction e with | k n => … | sub a b iha ihb => … | dbl a iha => …` names the constructor's
arguments first, then the IHs. -/
example (e : Ex) (P : Ex → Prop) (kk : ∀ x, P x) : P e := by
  induction e
  all_goals exact kk _

/-! ### R4. `exact .inl ⟨n, rfl⟩` · closes `(∃ m, x = y) ∨ B` with the left side
`.inl` is `Or.inl` (Lean reads the namespace off the expected type `_ ∨ _`); `⟨n, rfl⟩` gives the
witness `n` and proves `Ex.k n = Ex.k n` by `rfl`. -/
example (n : Nat) (B : Prop) : (∃ m, Ex.k n = Ex.k m) ∨ B := by
  exact .inl ⟨n, rfl⟩

/-! ### R5. `right` (and `left`) · goal: `A ∨ B` → `B` (`left`: → `A`) -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R6. `rcases ih with ⟨m, rfl⟩ | ⟨a', ha⟩` · goal list: one goal per side of `∨`.
Left: the `∃` is opened and `rfl` substitutes `a := Ex.k m` everywhere (`a` must be a local
variable). Right: a witness `a'` and its step `ha`. -/
example {a : Ex} (P : Ex → Prop) (k1 : ∀ m, P (.k m)) (k2 : ∀ a', Red a a' → P a)
    (ih : (∃ m, a = .k m) ∨ ∃ a', Red a a') : P a := by
  rcases ih with ⟨m, rfl⟩ | ⟨a', ha⟩
  exact k1 m
  exact k2 a' ha

/-! ### R7. `exact ⟨_, .subK⟩` · closes `∃ e', Red e e'` with a computation rule; the witness `_`
is read off the rule's conclusion. The rule must match `e` literally: `.subK` needs both sides to be
`Ex.k _` already (that is what the `rfl` of R6 buys). -/
example (m n : Nat) : ∃ e', Red (.sub (.k m) (.k n)) e' := by
  exact ⟨_, .subK⟩

/-! ### R8. `exact ⟨_, .subL ha⟩` · closes `∃ e', Red e e'` with a congruence rule applied to a
step `ha` of a subexpression -/
example {a a' : Ex} (b : Ex) (ha : Red a a') : ∃ e', Red (.sub a b) e' := by
  exact ⟨_, .subL ha⟩

/-! ## Determinism: induction on one derivation, inversion of the other -/

/-! ### R9. `induction h1 generalizing e2` · goal list: one goal per rule of `Red`. `h2` mentions
`e2`, so Lean reverts it too; with `generalizing e2` each IH reads `∀ {e2}, Red a e2 → …`, usable
at the other derivation's target whatever it is.
`induction h1 generalizing e2 with | subK | dblK => tac | subL _ ih | subR _ ih => tac …` names
the premises and IHs, and one `=> tac` may serve several rules (their names must agree). -/
example {e e1 e2 : Ex} (P : Ex → Ex → Prop) (kk : ∀ x y, P x y) (h1 : Red e e1)
    (h2 : Red e e2) : P e1 e2 := by
  induction h1 generalizing e2
  all_goals exact kk _ _

/-! ### R10. `cases h2` with `h2 : Red (.sub a b) e2` (inversion) · goal list: one goal per rule
whose left side can be `.sub a b`, and in each `a`, `b`, `e2` are replaced by that rule's shapes.
`dblK`, `dblC` cannot match and do not appear. -/
example {a b e2 : Ex} (P : Ex → Prop) (kk : ∀ x, P x) (h2 : Red (.sub a b) e2) : P e2 := by
  cases h2
  all_goals exact kk _

/-- A toy lemma for R11 (proved with R1, R2): a numeral does not reduce. -/
theorem k_stuck {n : Nat} {e : Ex} : ¬ Red (.k n) e := by
  intro h
  cases h

/-! ### R11. `simp_all [k_stuck]` · closes a goal whose context holds a step out of a numeral:
`simp_all` simplifies every hypothesis and the goal together, and the lemma
`k_stuck : ¬ Red (.k n) e` rewrites `h : Red (.k n) e` to `False`. A theorem must be named in the
brackets; hypotheses are used without being named. -/
example {n : Nat} {e : Ex} (G : Prop) (h : Red (.k n) e) : G := by
  simp_all [k_stuck]

/-! ### R12. constructor injectivity, `Ex.sub.injEq` (used by `simp` / `simp_all`) · goal:
`a.sub b = a'.sub b` → `a = a'`. Lemma: `(Ex.sub a b = Ex.sub a' b') = (a = a' ∧ b = b')`; Lean
generates one such `injEq` lemma per constructor, and `simp` uses them unasked. -/
example {a a' b : Ex} (h : a = a') : Ex.sub a b = Ex.sub a' b := by
  simp
  exact h

/-! ### R13. `exact ih ‹_›` · closes the goal with the IH. `‹T›` is `by assumption`: a hypothesis
of type `T`; `‹_›` lets Lean compute `T` (here `Red a a''`) from `ih` and the goal. -/
example {a a' a'' : Ex} (ih : ∀ {e2 : Ex}, Red a e2 → a' = e2) (h : Red a a'') : a' = a'' := by
  exact ih ‹_›

/-! # Part W · Worked combinations (toy objects, not the exercise's) -/

/-! ### W1. Rules are constructors, so they build derivations: a step inside the left operand -/
example : Red (.sub (.sub (.k 5) (.k 2)) (.k 1)) (.sub (.k 3) (.k 1)) :=
  .subL .subK

/-! ### W2. Inversion twice: R1, R10 on `dbl`, then R2 on the inner step out of a numeral -/
example (e : Ex) : Red (.dbl (.k 3)) e → e = .k 6 := by
  intro h
  cases h with
    | dblK => rfl
    | dblC h' => cases h'

/-! ### W3. Progress for `dbl` alone: R6, then R7 or R8 -/
example {a : Ex} (ih : (∃ m, a = .k m) ∨ ∃ a', Red a a') : ∃ e', Red (.dbl a) e' := by
  rcases ih with ⟨m, rfl⟩ | ⟨a', ha⟩
  · exact ⟨_, .dblK⟩
  · exact ⟨_, .dblC ha⟩

/-! ### W4. One congruence case of determinism for `dbl`: R10, R11 + R12, R13 -/
example {a a' e2 : Ex} (ha : Red a a') (ih : ∀ {e2 : Ex}, Red a e2 → a' = e2)
    (h2 : Red (.dbl a) e2) : Ex.dbl a' = e2 := by
  cases h2 <;> simp_all [k_stuck]
  exact ih ‹_›

end M040Guide
