/- Guide for E021 (have, show, suffices).
Part R: one reference entry per tactic or lemma the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`T G : Prop` are arbitrary propositions; `s g : Nat → Nat` are arbitrary functions on `Nat`;
`P : List α → Prop` stands for "the rest of the statement". A hypothesis `k` in an entry is only there
to finish the example.
Part W: worked combinations on functions and statements that are NOT the exercise's.
Assumed: E001–E020, in particular `intro`/`exact` (E003), `¬`/`False` (E008), `rw` (E009),
`simp` (E010) and `omega` (E011).
-/

namespace E021Guide

/-! # Part R · Reference entries -/

/-! ## Forward: adding facts with `have` -/

/-! ### R1. `have k : T := e` · context gains `k : T`; goal unchanged
`e` is any term whose type is `T`. Here `h 0 : s 0 ≤ s (0 + 1)`, and writing the type `s 0 ≤ s 1`
is accepted because `0 + 1` computes to `1` (the check is by computation, as for `rfl`). -/
example (s : Nat → Nat) (h : ∀ n, s n ≤ s (n + 1)) (G : Prop) (k : s 0 ≤ s 1 → G) : G := by
  have k0 : s 0 ≤ s 1 := h 0
  exact k k0

/-! ### R2. `have k := e` (no type) · context gains `k` with the type of `e` exactly as computed
Lean instantiates `n := 0` in `s n ≤ s (n + 1)` and does not simplify: you get `s (0 + 1)`. -/
example (s : Nat → Nat) (h : ∀ n, s n ≤ s (n + 1)) (G : Prop) (k : s 0 ≤ s (0 + 1) → G) : G := by
  have k0 := h 0
  exact k k0

/-! ### R3. `omega` · closes a linear-arithmetic goal over `Nat`/`Int`, using the hypotheses
`x < y` on `Nat` means `x + 1 ≤ y`. Function values such as `s 1` are treated as unknowns ("atoms");
`s 1` and `s (0 + 1)` are DIFFERENT atoms to `omega`, so facts made with R2 do not chain (use R1). -/
example (x y z : Nat) (h1 : x < y) (h2 : y < z) : x + 2 ≤ z := by
  omega

/-! ## Backward: reducing the goal with `suffices` -/

/-! ### R4. `suffices hs : T by e` · goal `G` → goal `T`
Read it as "it suffices to prove `T`": `e` must prove the OLD goal `G` using `hs : T` (inside `e`,
`hs` is in the context). Afterwards the goal is `T`. Core Lean requires the `by …` (or `from e`) part. -/
example (T G : Prop) (g : T → G) (t : T) : G := by
  suffices hs : T by exact g hs
  exact t

/-! ### R5. `exact m x y hxy` · closes `g x < g y` from `m : ∀ a b, a < b → g a < g b`
`m` is a function of two numbers and a proof: `m x y : x < y → g x < g y`, so `m x y hxy : g x < g y`.
An argument that is itself an expression needs parentheses: `m x (y + 1) h`. -/
example (g : Nat → Nat) (m : ∀ a b, a < b → g a < g b) (x y : Nat) (hxy : x < y) : g x < g y := by
  exact m x y hxy

/-! ## Restating the goal with `show`; `≠` -/

/-! ### R6. `show T` · goal `G` → goal `T`, when `T` is definitionally equal to `G`
`a ≠ b` is notation for `Ne a b`, which is defined as `a = b → False`, so `show` accepts it.
`show T` with a `T` that does not compute to `G` fails (Traps). -/
example {α : Type} (a b : α) (k : a = b → False) : a ≠ b := by
  show a = b → False
  exact k

/-! ### R7. `intro hx` on `a ≠ b` · goal `a ≠ b` → `False`; context gains `hx : a = b`
`intro` sees through `≠` (it unfolds to `a = b → False`) without a `show` first. -/
example {α : Type} (a b : α) (k : a = b → False) : a ≠ b := by
  intro hx
  exact k hx

/-! ## Rewriting and simplifying a hypothesis -/

/-! ### R8. `rw [hx] at h` (`hx : a = b`) · context: `h : P a` → `h : P b`; goal unchanged
Like `rw [hx]` (E009), but it rewrites inside the hypothesis `h` instead of the goal. -/
example {α : Type} (xs : List α) (P : List α → Prop) (hx : xs = []) (h : P xs) : P [] := by
  rw [hx] at h
  exact h

/-! ### R9. `List.length_nil` · `[].length = 0` · context: `h : P [].length` → `h : P 0`
`xs.length` is `List.length xs`; `[]` is the empty list. `simp` uses this lemma by itself. -/
example {α : Type} (G : Prop) (h : ([] : List α).length = 2) (k : (0 : Nat) = 2 → G) : G := by
  rw [List.length_nil] at h
  exact k h

/-! ### R10. `simp at h` · when `h` simplifies to `False`, closes the goal (whatever it is)
`simp` evaluates `[].length` to `0` (R9) and `0 = 2` to `False`; a hypothesis `False` proves anything. -/
example {α : Type} (G : Prop) (h : ([] : List α).length = 2) : G := by
  simp at h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R1 twice, then R3, on a sequence that grows by at least 2 per step -/
example (s : Nat → Nat) (h : ∀ n, s n + 2 ≤ s (n + 1)) : s 0 + 4 ≤ s 2 := by
  have k0 : s 0 + 2 ≤ s 1 := h 0
  have k1 : s 1 + 2 ≤ s 2 := h 1
  omega

/-! ### W2. R4 with R5 inside the `by`, then R3 for the new goal -/
example (g : Nat → Nat) (m : ∀ a b, a < b → g a < g b) (n : Nat) : g n < g (n + 3) := by
  suffices hs : n < n + 3 by exact m n (n + 3) hs
  omega

/-! ### W3. R7, R6, R8, R10 on a number instead of a list -/
example (n : Nat) (h : 2 * n = 6) : n ≠ 0 := by
  intro hx
  show False
  rw [hx] at h
  simp at h

end E021Guide
