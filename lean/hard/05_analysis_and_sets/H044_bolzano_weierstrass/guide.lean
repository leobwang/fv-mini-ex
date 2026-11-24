/- Guide for H044 (Bolzano–Weierstrass).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (no bounded sequence, no peaks).
Assumed: Lean basics (E001–E033). New: Mathlib's order library on `ℝ` and `ℕ` (`sSup`, `BddAbove`,
`Monotone`, `StrictMono`, `Set.range`, `Set.Finite`), `Nat.nth`, iterates `g^[k]`, `choose`,
`linarith`, `omega`.
The import lines are the exercise's frozen imports; its BANNED line forbids adding more.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace H044Guide

/-! # Part R · Reference entries -/

/-! ## ε–N statements and least upper bounds -/

/-- A toy definition whose body is an `∀ ε > 0`. -/
def ForallPos (P : ℝ → Prop) : Prop := ∀ ε > 0, P ε

/-! ### R1. `intro ε hε` · goal `∀ ε > 0, P ε` (even behind a `def`) → context gains `ε`, `hε` -/
example (P : ℝ → Prop) (h : ∀ ε : ℝ, 0 < ε → P ε) : ForallPos P := by
  intro ε hε
  exact h ε hε

/-! ### R2. `Set.range_nonempty` · `(Set.range f).Nonempty` for `f : ℕ → α` · context gains a fact -/
example {α : Type} (f : ℕ → α) (P : Prop) (h : (Set.range f).Nonempty → P) : P := by
  have hne := Set.range_nonempty f
  exact h hne

/-! ### R3. `sub_lt_self` · `0 < b → a - b < a` · context gains `a - b < a` -/
example (a b : ℝ) (hb : 0 < b) (P : Prop) (h : a - b < a → P) : P := by
  have hlt := sub_lt_self a hb
  exact h hlt

/-! ### R4. `exists_lt_of_lt_csSup` · `s.Nonempty → b < sSup s → ∃ x ∈ s, b < x` · context -/
example (s : Set ℝ) (b : ℝ) (hs : s.Nonempty) (hb : b < sSup s) (P : Prop)
    (h : (∃ x ∈ s, b < x) → P) : P := by
  have hx := exists_lt_of_lt_csSup hs hb
  exact h hx

/-! ### R5. `obtain ⟨_, ⟨N, rfl⟩, hN⟩` · context: `∃ x ∈ Set.range f, b < x` → `N`, `hN : b < f N`
`x ∈ Set.range f` means `∃ y, f y = x`; the pattern `rfl` replaces `x` by `f N` everywhere. -/
example {α : Type} [LT α] (f : ℕ → α) (b : α) (P : Prop) (h : ∀ N, b < f N → P)
    (hx : ∃ x ∈ Set.range f, b < x) : P := by
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := hx
  exact h N hN

/-! ### R6. `refine ⟨N, fun n hn => ?_⟩` · goal `∃ N, ∀ n ≥ N, P n` → context gains `n`, `hn : n ≥ N` -/
example (P : ℕ → Prop) (N : ℕ) (h : ∀ n, N ≤ n → P n) : ∃ N : ℕ, ∀ n ≥ N, P n := by
  refine ⟨N, fun n hn => ?_⟩
  exact h n hn

/-! ### R7. `le_csSup` with `⟨n, rfl⟩` · `BddAbove s → x ∈ s → x ≤ sSup s` · context
`⟨n, rfl⟩` proves `f n ∈ Set.range f` (the witness is `n`, and `f n = f n` by `rfl`). -/
example (f : ℕ → ℝ) (hb : BddAbove (Set.range f)) (n : ℕ) (P : Prop)
    (h : f n ≤ sSup (Set.range f) → P) : P := by
  have h1 := le_csSup hb ⟨n, rfl⟩
  exact h h1

/-! ### R8. Using `hm : Monotone f` · `hm hij : f i ≤ f j` from `hij : i ≤ j` · context
`Monotone f` unfolds to `∀ ⦃i j⦄, i ≤ j → f i ≤ f j`; `n ≥ N` is notation for `N ≤ n`. -/
example (f : ℕ → ℝ) (hm : Monotone f) (N n : ℕ) (hn : n ≥ N) (P : Prop) (h : f N ≤ f n → P) : P := by
  have h2 := hm hn
  exact h h2

/-! ### R9. `abs_sub_lt_iff` · `|a - b| < c ↔ a - b < c ∧ b - a < c` · goal -/
example (a b c : ℝ) (h : a - b < c ∧ b - a < c) : |a - b| < c := by
  rw [abs_sub_lt_iff]
  exact h

/-! ### R10. `linarith` · closes a linear (in)equality that follows from hypotheses by adding them up
`linarith [t]` also uses the extra fact `t`. -/
example (x y z ε : ℝ) (h1 : x ≤ y) (h2 : y - ε < z) : x - z < ε := by
  linarith

/-! ## Negation flips the order -/

/-! ### R11. `obtain ⟨B, hB⟩ := hb` · context: `hb : BddBelow s` → `B`, `hB : B ∈ lowerBounds s`
`hB hx : B ≤ x` for `hx : x ∈ s`. -/
example (s : Set ℝ) (hb : BddBelow s) (x : ℝ) (hx : x ∈ s) (P : Prop) (h : ∀ B, B ≤ x → P) : P := by
  obtain ⟨B, hB⟩ := hb
  exact h B (hB hx)

/-! ### R12. `neg_le_neg` · `a ≤ b → -b ≤ -a` · goal -/
example (a b : ℝ) (h : a ≤ b) : -b ≤ -a := by
  apply neg_le_neg
  exact h

/-! ### R13. `refine ⟨c, ?_⟩` on `BddAbove s` · goal → `c ∈ upperBounds s`
`BddAbove s` unfolds to `∃ c, c ∈ upperBounds s`: give the bound, prove it bounds. -/
example (s : Set ℝ) (c : ℝ) (h : c ∈ upperBounds s) : BddAbove s := by
  refine ⟨c, ?_⟩
  exact h

/-! ### R14. `rintro _ ⟨n, rfl⟩` · goal `c ∈ upperBounds (Set.range f)` → context `n`, goal `f n ≤ c`
`c ∈ upperBounds s` unfolds to `∀ ⦃x⦄, x ∈ s → x ≤ c`. -/
example (f : ℕ → ℝ) (c : ℝ) (h : ∀ n, f n ≤ c) : c ∈ upperBounds (Set.range f) := by
  rintro _ ⟨n, rfl⟩
  exact h n

/-! ### R15. `rw [show e₁ = e₂ by ring]` · goal: rewrite with an identity proved on the spot -/
example (x y : ℝ) (P : ℝ → Prop) (h : P (-(y - x))) : P (x - y) := by
  rw [show x - y = -(y - x) by ring]
  exact h

/-! ### R16. `abs_neg` · `|-a| = |a|` · goal -/
example (a : ℝ) (P : ℝ → Prop) (h : P |a|) : P |(-a)| := by
  rw [abs_neg]
  exact h

/-! ## Finite or infinite: the peak case split -/

/-! ### R17. `rcases Set.finite_or_infinite s with hfin | hinf` · goal list: one goal per case -/
example {α : Type} (s : Set α) (P : Prop) (h1 : s.Finite → P) (h2 : s.Infinite → P) : P := by
  rcases Set.finite_or_infinite s with hfin | hinf
  · exact h1 hfin
  · exact h2 hinf

/-! ### R18. `Set.Finite.bddAbove` · `s.Finite → BddAbove s` (for `s : Set ℕ`) · context
Then `obtain ⟨N, hN⟩` gives `hN : N ∈ upperBounds s`, and `hN hx : x ≤ N` for `hx : x ∈ s`. -/
example (s : Set ℕ) (hfin : s.Finite) (P : Prop) (h : ∀ N, N ∈ upperBounds s → P) : P := by
  obtain ⟨N, hN⟩ := hfin.bddAbove
  exact h N hN

/-! ### R19. `by_cases hn : p` · goal list: one goal with `hn : p`, one with `hn : ¬p` -/
example (N n : ℕ) (P : Prop) (h1 : N < n → P) (h2 : ¬N < n → P) : P := by
  by_cases hn : N < n
  · exact h1 hn
  · exact h2 hn

/-! ### R20. `absurd` · `a → ¬a → b` · closes any goal from a fact and its negation
A proof of `x ∉ s` is a function `fun hx => …` from `hx : x ∈ s` to `False`. -/
example (s : Set ℕ) (x : ℕ) (hb : ∀ y ∈ s, y ≤ 5) (hx5 : 5 < x) : x ∉ s := by
  intro hx
  exact absurd (hb x hx) (by omega)

/-! ### R21. `omega` · closes linear arithmetic over `ℕ`/`ℤ`, including `¬`, `<`, `≤` -/
example (N n : ℕ) (h : N < n) : ¬n ≤ N := by
  omega

/-! ### R22. `simp only [Set.mem_setOf_eq, not_forall, not_le] at h` · context: push `¬` inside
`Set.mem_setOf_eq : (x ∈ {y | p y}) = p x`, `not_forall : (¬∀ x, p x) ↔ ∃ x, ¬p x`,
`not_le : ¬a ≤ b ↔ b < a`. `∃ x, ∃ (_ : q), r` is how Lean prints "∃ x, q ∧ r" here. -/
example (f g : ℕ → ℝ) (n : ℕ) (P : Prop) (h' : ∀ m, n < m → g n < f m → P)
    (h : n ∉ {k | ∀ m > k, f m ≤ g k}) : P := by
  simp only [Set.mem_setOf_eq, not_forall, not_le] at h
  obtain ⟨m, hm, hlt⟩ := h
  exact h' m hm hlt

/-! ## Building a subsequence: `choose`, iterates, `Nat.nth` -/

/-! ### R23. `choose g hg1 hg2 using h` · context: `h : ∀ n, ∃ m, A n m ∧ B n m` → function `g` and
`hg1 : ∀ n, A n (g n)`, `hg2 : ∀ n, B n (g n)` -/
example (A B : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, A n m ∧ B n m) (P : Prop)
    (k : (g : ℕ → ℕ) → (∀ n, A n (g n)) → (∀ n, B n (g n)) → P) : P := by
  choose g hg1 hg2 using h
  exact k g hg1 hg2

/-! ### R24. `Function.iterate_succ_apply'` · `g^[n.succ] x = g (g^[n] x)` · goal
`g^[n] x` is `g` applied `n` times to `x`; `g^[0] x` simplifies to `x` (`simp`). -/
example (g : ℕ → ℕ) (n x : ℕ) (P : ℕ → Prop) (h : P (g (g^[n] x))) : P (g^[n + 1] x) := by
  rw [Function.iterate_succ_apply']
  exact h

/-! ### R25. `lt_trans` · `a < b → b < c → a < c` · goal -/
example (a b c : ℕ) (h1 : a < b) (h2 : b < c) : a < c := by
  apply lt_trans h1
  exact h2

/-! ### R26. `LT.lt.le` (written `h.le`) · `a < b → a ≤ b` · goal -/
example (a b : ℝ) (h : a < b) : a ≤ b := by
  exact h.le

/-! ### R27. `strictMono_nat_of_lt_succ` · `(∀ n, f n < f (n + 1)) → StrictMono f` · goal
`StrictMono f` means `∀ ⦃a b⦄, a < b → f a < f b`: one step at a time suffices on `ℕ`. -/
example (f : ℕ → ℕ) (h : ∀ n, f n < f (n + 1)) : StrictMono f := by
  apply strictMono_nat_of_lt_succ
  exact h

/-! ### R28. `monotone_nat_of_le_succ` · `(∀ n, f n ≤ f (n + 1)) → Monotone f` · goal -/
example (f : ℕ → ℝ) (h : ∀ n, f n ≤ f (n + 1)) : Monotone f := by
  apply monotone_nat_of_le_succ
  exact h

/-! ### R29. `antitone_nat_of_succ_le` · `(∀ n, f (n + 1) ≤ f n) → Antitone f` · goal
`Antitone f` means `∀ ⦃a b⦄, a ≤ b → f b ≤ f a`. -/
example (f : ℕ → ℝ) (h : ∀ n, f (n + 1) ≤ f n) : Antitone f := by
  apply antitone_nat_of_succ_le
  exact h

/-! ### R30. `Function.comp` · goal: `(f ∘ φ) k` → `f (φ k)` (`simp only [Function.comp]`) -/
example (f : ℕ → ℝ) (φ : ℕ → ℕ) (k : ℕ) (P : ℝ → Prop) (h : P (f (φ k))) : P ((f ∘ φ) k) := by
  simp only [Function.comp]
  exact h

/-! ### R31. `Nat.nth_strictMono` · `(setOf p).Infinite → StrictMono (Nat.nth p)` · goal
`Nat.nth p k` is the `k`-th natural number (counting from 0) satisfying `p`; `{n | p n}` is `setOf p`. -/
example (p : ℕ → Prop) (hinf : {n | p n}.Infinite) : StrictMono (Nat.nth p) := by
  exact Nat.nth_strictMono hinf

/-! ### R32. `Nat.nth_mem_of_infinite` · `(setOf p).Infinite → ∀ k, p (Nat.nth p k)` · goal -/
example (p : ℕ → Prop) (hinf : {n | p n}.Infinite) (k : ℕ) : p (Nat.nth p k) := by
  exact Nat.nth_mem_of_infinite hinf k

/-! ### R33. Using `hφ : StrictMono φ` with `Nat.lt_succ_self` · `hφ (Nat.lt_succ_self k) : φ k < φ (k + 1)` -/
example (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ℕ) (P : Prop) (h : φ k < φ k.succ → P) : P := by
  have hk := hφ (Nat.lt_succ_self k)
  exact h hk

/-! ## Assembling: or-elimination and absolute values -/

/-! ### R34. `obtain ⟨φ, hφ, h1 | h2⟩` · context: `∃ φ, A φ ∧ (B φ ∨ C φ)` → goal list: one goal per side -/
example (A B C : (ℕ → ℕ) → Prop) (P : Prop) (hb : ∀ φ, A φ → B φ → P) (hc : ∀ φ, A φ → C φ → P)
    (h : ∃ φ, A φ ∧ (B φ ∨ C φ)) : P := by
  obtain ⟨φ, hφ, h1 | h2⟩ := h
  · exact hb φ hφ h1
  · exact hc φ hφ h2

/-! ### R35. `abs_le` · `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b` · `(abs_le.mp h).1`, `(abs_le.mp h).2` · context -/
example (a b : ℝ) (h : |a| ≤ b) (P : Prop) (k : -b ≤ a → a ≤ b → P) : P := by
  have h' := abs_le.mp h
  exact k h'.1 h'.2

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. `choose` + iterate: a strictly increasing sequence from "there is always a bigger one"
(R23, R24, R27). -/
example (h : ∀ n : ℕ, ∃ m, n < m) : ∃ φ : ℕ → ℕ, StrictMono φ := by
  choose g hg1 using h
  refine ⟨fun k => g^[k] 0, strictMono_nat_of_lt_succ fun k => ?_⟩
  rw [Function.iterate_succ_apply']
  exact hg1 _

/-! ### W2. A bound proved by induction on the number of iterations (R24, R25) -/
example (g : ℕ → ℕ) (hg : ∀ n, n < g n) : ∀ k, 3 < g^[k] 4 := by
  intro k
  induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact lt_trans ih (hg _)

/-! ### W3. `Nat.nth` gives an increasing enumeration of an infinite set (R31, R32, R33) -/
example (p : ℕ → Prop) (hinf : {n | p n}.Infinite) :
    StrictMono (Nat.nth p) ∧ ∀ k, Nat.nth p k < Nat.nth p (k + 1) ∧ p (Nat.nth p k) := by
  refine ⟨Nat.nth_strictMono hinf, fun k => ⟨?_, Nat.nth_mem_of_infinite hinf k⟩⟩
  exact Nat.nth_strictMono hinf (Nat.lt_succ_self k)

/-! ### W4. Moving a minus sign through `|·|` (R15, R16) -/
example (x y : ℝ) : |x - -y| = |-x - y| := by
  rw [show -x - y = -(x - -y) by ring, abs_neg]

/-! ### W5. An upper bound for the range of a sequence bounded in absolute value (R13, R14, R35) -/
example (f : ℕ → ℝ) (hb : ∀ n, |f n| ≤ 7) : BddAbove (Set.range fun n => f n + 1) := by
  refine ⟨8, ?_⟩
  rintro _ ⟨n, rfl⟩
  linarith [(abs_le.mp (hb n)).2]

end H044Guide
