/- Guide for E084 (Functional induction).
Part R: one reference entry per tactic the exercise needs, stated with typed placeholders. Put the
cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h…` in an entry is only there to finish the example; it shows what the goal became.
The case alternatives are written `| caseK … => ?_` so that every case stays open as a goal you can
inspect; in the exercise you write a tactic after `=>` instead (`| case1 => omega`).
Part W: worked combinations on `half`, `dbl`, `g` and `clamp` below, not on the exercise's
functions.
Assumed: Lean basics (E001–E033), recursive definitions by pattern matching (E002, E026), E048.
-/

namespace E084Guide

/-- `half n = ⌊n / 2⌋`: three equations, one recursive call. -/
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

/-- `dbl n = 2 * n`: two equations, one recursive call. -/
def dbl : Nat → Nat
  | 0 => 0
  | n + 1 => dbl n + 2

/-- Two recursive calls, the inner one inside the outer one's argument (`g m n = m + n`). -/
def g : Nat → Nat → Nat
  | 0, n => n
  | m + 1, n => g m (g m n + 1)

/-- Not recursive: `clamp n = n - 1`, except `clamp 0 = 1`. -/
def clamp : Nat → Nat
  | 0 => 1
  | n + 1 => n

/-! # Part R · Reference entries -/

/-! ## Splitting a goal along a function's equations -/

/-! ### R1. `fun_induction f n` · goal list: one goal per equation of `f`, with IHs
In each goal `n` is replaced by that equation's pattern and `f n` by its right-hand side; every
recursive call on the right-hand side gives one induction hypothesis `ih1✝ : P k (f k)`. The `✝`
marks a name you cannot type (R2 names them). -/
example (P : Nat → Nat → Prop) (h0 : P 0 0) (h1 : P 1 0)
    (h2 : ∀ k, P k (half k) → P (k + 2) (half k + 1)) (n : Nat) : P n (half n) := by
  fun_induction half n
  · exact h0
  · exact h1
  · exact h2 _ ‹_›

/-! ### R2. `fun_induction f n with | case1 => … | case3 k ih => …` · context: name variables and IHs
Cases are named `case1, case2, …` in the order of `f`'s equations. After the case name come the
pattern's variables, then the IHs, in the order the infoview lists them. -/
example (P : Nat → Nat → Prop) (h0 : P 0 0) (h1 : P 1 0)
    (h2 : ∀ k, P k (half k) → P (k + 2) (half k + 1)) (n : Nat) : P n (half n) := by
  fun_induction half n with
    | case1 => ?_
    | case2 => ?_
    | case3 k ih => ?_
  · exact h0
  · exact h1
  · exact h2 k ih

/-! ### R3. Nested recursive calls · context: one IH per call, the inner call's IH first
`g (m + 1) n = g m (g m n + 1)` calls `g` twice: inside on `(m, n)`, outside on `(m, g m n + 1)`.
`fun_induction g m n` takes both arguments and gives two IHs. -/
example (P : Nat → Nat → Nat → Prop) (h0 : ∀ n, P 0 n n)
    (h1 : ∀ m n, P m n (g m n) → P m (g m n + 1) (g m (g m n + 1)) → P (m + 1) n (g m (g m n + 1)))
    (m n : Nat) : P m n (g m n) := by
  fun_induction g m n with
    | case1 n => ?_
    | case2 m n ihIn ihOut => ?_
  · exact h0 n
  · exact h1 m n ihIn ihOut

/-! ### R4. A hypothesis about the variable · context: it is specialised in every case and becomes
a premise of every IH
`h : 0 < n` mentions `n`, so `fun_induction` moves it into the induction: each case gets its own
copy `h : 0 < (pattern)`, and each IH reads `0 < k → …`. -/
example (P : Nat → Nat → Prop) (h0 : 0 < 0 → P 0 0)
    (h1 : ∀ k, (0 < k → P k (dbl k)) → 0 < k + 1 → P (k + 1) (dbl k + 2))
    (n : Nat) (h : 0 < n) : P n (dbl n) := by
  fun_induction dbl n with
    | case1 => ?_
    | case2 k ih => ?_
  · exact h0 h
  · exact h1 k ih h

/-! ### R5. `fun_cases f n` · goal list: one goal per equation of `f`, no IHs
Use it when `f` is not recursive (there is nothing to induct on) or no IH is needed. Name the
variables with `with | case2 k => …` as in R2. -/
example (P : Nat → Nat → Prop) (h0 : P 0 1) (h1 : ∀ k, P (k + 1) k) (n : Nat) :
    P n (clamp n) := by
  fun_cases clamp n with
    | case1 => ?_
    | case2 k => ?_
  · exact h0
  · exact h1 k

/-! ## Closing the cases with `omega` -/

/-! ### R6. `omega` · closes a goal whose hypotheses contradict each other, such as `h : 0 < 0`
After R4, the case for the pattern `0` carries `h : 0 < 0`; `omega` closes any goal from it. -/
example (P : Prop) (h : 0 < 0) : P := by
  omega

/-! ### R7. `omega` · closes linear arithmetic; `f x` is an unknown number, `k.succ` is `k + 1`
Each distinct application such as `f a` or `f (f a)` is one opaque number to `omega`, so two IHs
`a < f a` and `f a < f (f a)` chain to `a < f (f a)`. Goals print `n + 2` as `k.succ.succ`. -/
example (f : Nat → Nat) (k : Nat) (ih1 : k < f k) (ih2 : f k < f (f k)) :
    k.succ < f (f k) + 1 := by
  omega

/-! ### R8. `omega` · uses an IH of the form `0 < k → Q`: it splits on whether `0 < k` holds
An IH whose premise you cannot prove (here `0 < k` when `k` may be `0`) is still fine to hand to
`omega`; it uses it only when the premise holds. -/
example (f : Nat → Nat) (k : Nat) (ih : 0 < k + 1 → 0 < f (k + 1)) : 0 < f k + f (k + 1) := by
  omega

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Three equations, one IH, every case by `omega`: R1, then R7 on each goal -/
example (n : Nat) : half n ≤ n := by
  fun_induction half n <;> omega

/-! ### W2. A carried hypothesis: R4, then R6 for the pattern `0` and R8 for `k + 1` -/
example (n : Nat) (h : 0 < n) : n < dbl n + 1 := by
  fun_induction dbl n with
    | case1 => omega
    | case2 k ih => omega

/-! ### W3. Two nested calls: R3, then R7 chains `ihIn` and `ihOut` -/
example (m n : Nat) : n ≤ g m n := by
  fun_induction g m n with
    | case1 n => omega
    | case2 m n ihIn ihOut => omega

/-! ### W4. A non-recursive function: R5, then `omega` -/
example (n : Nat) : n ≤ clamp n + 1 := by
  fun_cases clamp n <;> omega

end E084Guide
