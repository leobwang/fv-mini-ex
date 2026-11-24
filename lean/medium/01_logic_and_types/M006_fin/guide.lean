/- Guide for M006 (Fin n).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`shift`, `total`).
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M006Guide

/-! # Part R · Reference entries -/

/-! ## Building a `Fin n` -/

/-! ### R1. `⟨v, proof⟩` (constructor `Fin.mk`) · in tactic form `refine ⟨v, ?_⟩`: goal `Fin n` → `v < n`
A `Fin n` is a pair: a value `v : Nat` and a proof of `v < n`. -/
example (n v : Nat) (hv : v < n) : Fin n := by
  refine ⟨v, ?_⟩
  exact hv

/-! ### R2. `Fin.isLt` · `i.isLt : ↑i < n`; `have h := i.isLt` → context gains the bound
`↑i` is `i.val`, the value of `i` as a `Nat`. -/
example (n : Nat) (i : Fin n) (P : Prop) (hP : ↑i < n → P) : P := by
  have h := i.isLt
  exact hP h

/-! ### R3. `omega` · closes linear `Nat` goals; it adds `↑i < n` by itself for every `i : Fin n` it sees -/
example (n : Nat) (i : Fin n) : ↑i + 1 ≤ n := by
  omega

/-! ## Values of a constructed `Fin` -/

/-! ### R4. `rfl` · closes `↑⟨v, hv⟩ = v`: the value of a pair is its first component, by computation
It also unfolds definitions, so `(d x).val = e` is `rfl` when `d x` is defined as `⟨e, _⟩`. -/
example (n v : Nat) (hv : v < n) : (⟨v, hv⟩ : Fin n).val = v := by
  rfl

/-! ### R5. `apply Fin.ext` · goal `i = j` → `↑i = ↑j` (two `Fin`s are equal when their values are)
`Fin.ext : ↑a = ↑b → a = b`. -/
example (n : Nat) (i j : Fin n) (h : i.val = j.val) : i = j := by
  apply Fin.ext
  exact h

/-! ### R6. `simp [d]` · goal: `↑(d x)` → the value written in `d`'s body
Unfolds `d` (defined by `⟨e, proof⟩`) and takes the value of the pair. -/
def succ' {n : Nat} (i : Fin n) : Fin (n + 1) := ⟨i.val + 1, by omega⟩

example (n : Nat) (i : Fin n) (P : Nat → Prop) (h : P (↑i + 1)) : P ↑(succ' i) := by
  simp [succ']
  exact h

/-! ### R7. `omega` and truncated subtraction · on `Nat`, `a - b = 0` when `b ≥ a`; omega knows this -/
example (n : Nat) (i : Fin n) : n - (n - ↑i) = ↑i := by
  omega

/-! ## Induction on `n` with functions `Fin n → Nat` -/

/-! ### R8. `induction n with | zero => … | succ n ih => …` · goal list: one goal per case, `ih` in the second -/
example (P : Nat → Prop) (h0 : P 0) (hs : ∀ m, P m → P (m + 1)) (n : Nat) : P n := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0
  · exact hs n ih

/-! ### R9. `simp only [d]` on a recursive `d : (n : Nat) → (Fin n → Nat) → Nat` · goal: one equation unfolded
`Fin.last n : Fin (n + 1)` has value `n` (the top element). `i.castSucc : Fin (n + 1)` is `i : Fin n` with
the same value, seen one bigger. So `fun i => f i.castSucc : Fin n → Nat` is `f` with its last point dropped. -/
def total : (m : Nat) → (Fin m → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => total n (fun i => f i.castSucc) + f (Fin.last n)

example (n : Nat) (f : Fin (n + 1) → Nat) (P : Nat → Prop)
    (h : P (total n (fun i => f i.castSucc) + f (Fin.last n))) : P (total (n + 1) f) := by
  simp only [total]
  exact h

example (f : Fin 0 → Nat) (P : Nat → Prop) (h : P 0) : P (total 0 f) := by
  simp only [total]
  exact h

/-! ### R10. `rw [ih a]` with `ih : ∀ f, L f = R f` · goal: `L a` → `R a` (you choose the instance)
`rw [ih]` lets Lean pick `a` itself; naming it says which copy you mean. -/
example (n : Nat) (L R : (Fin n → Nat) → Nat) (ih : ∀ f, L f = R f) (g : Fin (n + 1) → Nat)
    (P : Nat → Prop) (h : P (R (fun i => g i.castSucc))) : P (L (fun i => g i.castSucc)) := by
  rw [ih (fun i => g i.castSucc)]
  exact h

/-! ## Arithmetic with products and unknown terms -/

/-! ### R11. `Nat.add_mul` · `(a + b) * c = a * c + b * c` · goal: distribute a product over `+` -/
example (a b c : Nat) (P : Nat → Prop) (h : P (a * c + b * c)) : P ((a + b) * c) := by
  rw [Nat.add_mul]
  exact h

/-! ### R12. `omega` with atoms · treats `x * y` and any non-arithmetic term (`F a`, `total n f`) as an unknown
It closes `x + A = A + x` for such an `A`, but it never multiplies out `(a + 1) * c`: use R11 first. -/
example (F : Nat → Nat) (a b c : Nat) : F a + b * c + (F b + c) = (F a + F b) + (c + b * c) := by
  omega

/-! ## Induction when the function's type mentions `n` -/

/-! ### R13. `induction n` with `f : Fin n → Nat` in the context · `f` is generalized: `ih : ∀ f, …`
`f`'s type mentions `n`, so `induction` reverts `f`; the IH holds for every function on `Fin n`. -/
example (Q : (m : Nat) → (Fin m → Nat) → Prop) (h0 : ∀ f, Q 0 f)
    (hs : ∀ m, (∀ f, Q m f) → ∀ f, Q (m + 1) f) (n : Nat) (f : Fin n → Nat) : Q n f := by
  induction n with | zero => ?_ | succ n ih => ?_
  · exact h0 f
  · exact hs n ih f

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Build, compute the value, compare: R1, R4, R5, R6 on `shift` -/
def shift {n : Nat} (i : Fin n) : Fin (n + 2) := ⟨i.val + 2, by omega⟩

example (n : Nat) (i : Fin n) : (shift i).val = i.val + 2 := rfl

example (n : Nat) : shift (Fin.last n) = Fin.last (n + 2) := by
  apply Fin.ext
  simp [shift]

/-! ### W2. Induction with a generalized `f`: R8 → R13 → R9 → R10 → R12 on `total` -/
example (n : Nat) (f : Fin n → Nat) : total n (fun i => 2 * f i) = 2 * total n f := by
  induction n with | zero => rfl | succ n ih => ?_
  simp only [total]
  rw [ih (fun i => f i.castSucc)]
  omega

end M006Guide
