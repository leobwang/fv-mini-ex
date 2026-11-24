/- Guide for H011 (Dutch national flag).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's: `sweep`, a two-way partition
that moves every `Sign.neg` to the front of an array of signs.
Assumed: Lean basics (E001–E033).
-/

namespace H011Guide

/-- A three-constructor type, like a colour type. -/
inductive Sign where
  | neg
  | zero
  | pos

/-- A one-pass partition: `[0, lo)` holds `neg`, `[lo, i)` holds the rest, `[i, size)` is unread.
Same shape as a loop written as recursion: a guard `if h : …`, a `match` on the cell, an exit `else`. -/
def sweep (a : Array Sign) (lo i : Nat) : Array Sign :=
  if h : lo ≤ i ∧ i < a.size then
    match a[i] with
    | .neg => sweep (a.swap lo i) (lo + 1) (i + 1)
    | .zero => sweep a lo (i + 1)
    | .pos => sweep a lo (i + 1)
  else a
termination_by a.size - i

/-- The entry point: start the loop at `lo = i = 0`. -/
def start (a : Array Sign) : Array Sign := sweep a 0 0

/-- A score per constructor, like a rank function. -/
def val : Sign → Nat
  | .neg => 0
  | .zero => 1
  | .pos => 2

/-! # Part R · Reference entries -/

/-! ## Part 1: induction over the loop, permutations -/

/-! ### R1. `fun_induction f x y z` · goal list: one goal per branch of `f`, each with its own facts
`case1`: the guard `h✝`, the match fact `x✝ : a✝[i✝] = Sign.neg` and the IH `ih1✝` for the recursive
call; `case4`: the negated guard. Names with `✝` are inaccessible: name them with
`case case1 a lo i h hc ih => …`, or `fun_induction … with | case1 a lo i h hc ih => …`. -/
example (a : Array Sign) (lo i : Nat) : (sweep a lo i).size = a.size := by
  fun_induction sweep a lo i
  case case1 b lo i h hc ih => exact ih.trans Array.size_swap
  case case2 b lo i h hc ih => exact ih
  case case3 b lo i h hc ih => exact ih
  case case4 b lo i h => rfl

/-! ### R2. `Array.swap_perm` · `(xs.swap i j hi hj).Perm xs` · closes the goal
`xs.Perm ys`: `ys` is a rearrangement of `xs`. `xs.swap i j hi hj` exchanges cells `i` and `j`; `hi`,
`hj` are the bounds, printed `⋯`. Write `Array.swap_perm _ _` and Lean finds the bounds. -/
example {α : Type} (xs : Array α) (i j : Nat) (hi : i < xs.size) (hj : j < xs.size) :
    (xs.swap i j hi hj).Perm xs := by
  exact Array.swap_perm _ _

/-! ### R3. `Array.Perm.trans` · `xs.Perm ys → ys.Perm zs → xs.Perm zs` · goal: `xs.Perm zs` → `ys.Perm zs`
`ih.trans h` is dot notation for `Array.Perm.trans ih h`. -/
example {α : Type} (xs ys zs : Array α) (ih : xs.Perm ys) (h : ys.Perm zs) : xs.Perm zs := by
  apply Array.Perm.trans ih
  exact h

/-! ### R4. `Array.Perm.refl` · `xs.Perm xs` · closes the goal (write `.refl xs` when the type is known) -/
example {α : Type} (xs : Array α) : xs.Perm xs := by
  exact .refl xs

/-! ### R5. `unfold d` · goal: `d x` → the body of `d`
Not required before `exact`: Lean unfolds definitions itself when it checks a term against a goal. -/
example (a : Array Sign) (P : Array Sign → Prop) (h : P (sweep a 0 0)) : P (start a) := by
  unfold start
  exact h

/-! ## Part 2: a loop invariant -/

/-! ### R6. `fun_induction` with a hypothesis about the arguments · it moves into each IH as a premise
Here `hlo : lo ≤ i` mentions `lo` and `i`, so the IH becomes `lo✝ + 1 ≤ i✝ + 1 → …`. To use the IH
you prove the hypothesis for the NEW arguments: that is "the invariant is preserved". -/
example (a : Array Sign) (lo i : Nat) (hlo : lo ≤ i) : (sweep a lo i).size = a.size := by
  fun_induction sweep a lo i
  case case1 b lo i h hc ih => exact (ih (by omega)).trans Array.size_swap
  case case2 b lo i h hc ih => exact ih (by omega)
  case case3 b lo i h hc ih => exact ih (by omega)
  case case4 b lo i h => rfl

/-! ### R7. `obtain ⟨h1, h2, h3⟩ := h` · context: `h : A ∧ B ∧ C` → three hypotheses
It looks through a `def` whose body is a conjunction (an invariant such as `FlagInv`). -/
example (A B C G : Prop) (h : A ∧ B ∧ C) (g : A → B → C → G) : G := by
  obtain ⟨h1, h2, h3⟩ := h
  exact g h1 h2 h3

/-! ### R8. `apply ih` · goal: `Q` → `I` when `ih : I → Q` -/
example (I Q : Prop) (ih : I → Q) (hinv : I) : Q := by
  apply ih
  exact hinv

/-! ### R9. `refine ⟨by omega, ?_, ?_⟩` · goal list: each `by tac` part is proved now, each `?_` stays a goal
Also builds a `def` whose body is a conjunction. -/
example (lo i : Nat) (A B : Prop) (h : lo < i) (ha : A) (hb : B) : lo ≤ i ∧ A ∧ B := by
  refine ⟨by omega, ?_, ?_⟩
  exact ha
  exact hb

/-! ### R10. `omega` · closes linear arithmetic over `Nat`/`Int` from the hypotheses
`-` on `Nat` is truncated (`2 - 5 = 0`); `omega` knows. If the hypotheses contradict each other it
closes ANY goal, e.g. `a[lo] = Sign.neg`: that is how impossible index cases die. -/
example (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid < hi) : lo ≤ hi - 1 := by
  omega

example (i lo : Nat) (G : Prop) (h1 : i < lo + 1) (h2 : ¬i = lo) (h3 : lo ≤ i) : G := by
  omega

/-! ### R11. `Array.size_swap` · `(xs.swap i j hi hj).size = xs.size` · goal (simp uses it by itself) -/
example {α : Type} (xs : Array α) (i j n : Nat) (hi : i < xs.size) (hj : j < xs.size)
    (h : n ≤ xs.size) : n ≤ (xs.swap i j hi hj).size := by
  simp only [Array.size_swap]
  exact h

/-! ### R12. `intro k hk hlt` · goal `∀ k (hk : k < xs.size), k < n → P xs[k]` → context gains `k hk hlt`
`xs[k]` needs a proof of `k < xs.size` in scope; the bound binder `(hk : …)` supplies it. -/
example {α : Type} (xs : Array α) (n : Nat) (P : α → Prop) (h : ∀ k (hk : k < xs.size), P xs[k]) :
    ∀ k (hk : k < xs.size), k < n → P xs[k] := by
  intro k hk hlt
  exact h k hk

/-! ### R13. `Array.getElem_swap` · goal: a cell of a swapped array → a nested `if`
`(xs.swap i j hi hj)[k] = if k = i then xs[j] else if k = j then xs[i] else xs[k]` -/
example {α : Type} (xs : Array α) (i j k : Nat) (hi : i < xs.size) (hj : j < xs.size)
    (hk : k < (xs.swap i j hi hj).size) (hk' : k < xs.size) (P : α → Prop)
    (h : P (if k = i then xs[j] else if k = j then xs[i] else xs[k])) :
    P (xs.swap i j hi hj)[k] := by
  rw [Array.getElem_swap]
  exact h

/-! ### R14. `split` · goal list: `P (if c then x else y)` → `c ⊢ P x` and `¬c ⊢ P y`
The new hypothesis is named `h✝`; `next h => …` names it. -/
example {α : Type} (c : Prop) [Decidable c] (x y : α) (P : α → Prop) (hx : c → P x)
    (hy : ¬c → P y) : P (if c then x else y) := by
  split
  next h => exact hx h
  next h => exact hy h

/-! ### R15. `simpa using hk` · simplifies `hk` and the goal the same way, then closes the goal with `hk`
Typical use: turn a bound on the swapped array into a bound on the original one (R11). -/
example {α : Type} (xs : Array α) (i j k : Nat) (hi : i < xs.size) (hj : j < xs.size)
    (hk : k < (xs.swap i j hi hj).size) : k < xs.size := by
  simpa using hk

/-! ### R16. `by_cases h : p` · goal list: one goal with `h : p`, one with `h : ¬p` -/
example (p G : Prop) (g1 : p → G) (g2 : ¬p → G) : G := by
  by_cases h : p
  exact g1 h
  exact g2 h

/-! ### R17. `subst h` · `h : i = m` with `m` a variable: `m` is replaced by `i` everywhere, `h` disappears -/
example (i m : Nat) (P : Nat → Prop) (h : i = m) (hp : P i) : P m := by
  subst h
  exact hp

/-! ### R18. `simp only [e]` · change an array INDEX: `xs[n - 1]` → `xs[m]` when `e : n - 1 = m`
`rw [e]` fails here ("motive is not type correct"): the hidden bound proof inside `xs[n - 1]` mentions
`n - 1`. `simp only` rewrites the index and the proof together. -/
example {α : Type} (xs : Array α) (n m : Nat) (hn : n - 1 < xs.size) (hm : m < xs.size)
    (e : n - 1 = m) (P : α → Prop) (h : P xs[m]) : P xs[n - 1] := by
  simp only [e]
  exact h

/-! ### R19. `rw [hr k hk hlt]` · rewrite with a `∀`-hypothesis applied to arguments: `xs[k]` → `c` -/
example {α : Type} (xs : Array α) (n k : Nat) (c : α) (P : α → Prop)
    (hr : ∀ k (hk : k < xs.size), k < n → xs[k] = c) (hk : k < xs.size) (hlt : k < n) (h : P c) :
    P xs[k] := by
  rw [hr k hk hlt]
  exact h

/-! ### R20. `simp only [val]` · goal: `val` applied to a constructor → its number
`simp [val]` goes on and closes what is left when it is `0 ≤ _` (`Nat.zero_le`) or a numeral
comparison such as `1 ≤ 2`. On `val x` with `x` a variable it can only unfold to a `match`. -/
example (P : Nat → Prop) (h : P 0) : P (val Sign.neg) := by
  simp only [val]
  exact h

example (x : Sign) : val Sign.neg ≤ val x := by simp [val]

/-! ### R21. `Nat.le_refl` · `n ≤ n` · closes the goal (`rw` does not close `≤` goals by itself) -/
example (n : Nat) : n ≤ n := by
  exact Nat.le_refl _

/-! ### R22. `absurd h hn` · `absurd : a → ¬a → b`: from `h : a` and `hn : ¬a`, anything
Term-mode form of "this case cannot happen": `fun k _ h => absurd h (by omega)` for `h : k < 0`. -/
example (k : Nat) (G : Prop) (h : k < 0) : G := by
  exact absurd h (by omega)

example (P : Nat → Prop) : ∀ k, k < 0 → P k := fun _ h => absurd h (by omega)

/-! # Part W · Worked combinations (`sweep`, not the exercise's loop) -/

/-! ### W1. Permutation through the loop: R1, then R3 + R2 in the swap branch, R4 at the exit -/
example (a : Array Sign) (lo i : Nat) : (sweep a lo i).Perm a := by
  fun_induction sweep a lo i
  case case1 b lo i h hc ih => exact ih.trans (Array.swap_perm _ _)
  case case2 b lo i h hc ih => exact ih
  case case3 b lo i h hc ih => exact ih
  case case4 b lo i h => exact .refl b

/-! ### W2. One preservation step of a "prefix is `neg`" invariant across `swap lo i`: R12, R13, R14, R10 -/
example (a : Array Sign) (lo i : Nat) (hlo : lo ≤ i) (hi : i < a.size) (hc : a[i] = Sign.neg)
    (hr : ∀ k (hk : k < a.size), k < lo → a[k] = Sign.neg) :
    ∀ k (hk : k < (a.swap lo i).size), k < lo + 1 → (a.swap lo i)[k] = Sign.neg := by
  intro k hk hlt
  rw [Array.getElem_swap]
  split
  next h1 => exact hc
  next h1 =>
    split
    next h2 => omega
    next h2 => exact hr k (by simpa using hk) (by omega)

/-! ### W3. At the exit, the negated guard plus the invariant's bounds pin the index: R10 -/
example (a : Array Sign) (lo i : Nat) (h : ¬(lo ≤ i ∧ i < a.size)) (h1 : lo ≤ i) (h2 : i ≤ a.size) :
    i = a.size := by
  omega

end H011Guide
