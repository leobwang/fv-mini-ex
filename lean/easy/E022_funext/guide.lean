/- Guide for E022 (funext).
Part R: one reference entry per tactic or lemma the exercise needs, stated with typed placeholders.
Put the cursor before and after the step to see the proof state change in the infoview.
`{α β γ : Type}` are arbitrary types; `F G : α → β` arbitrary functions; `P : β → Prop` stands for
"the rest of the goal". A hypothesis `k` in an entry is only there to finish the example.
Part W: worked combinations on functions that are NOT the exercise's.
Assumed: E001–E021, in particular `rfl` (E001), `rw` (E009), `simp [h]` with a `∀`-hypothesis (E010 R9),
`omega` (E011) and lists (E015).
-/

namespace E022Guide

/-! # Part R · Reference entries -/

/-! ## Function equality → pointwise equality -/

/-! ### R1. `funext x` (lemma `funext`) · goal `F = G` → `F x = G x`; context gains `x : α`
`funext : (∀ x, F x = G x) → F = G`: two functions are equal when they agree at every input.
The tactic `funext x` applies it backwards and introduces the input under the name `x`. -/
example {α β : Type} (F G : α → β) (k : ∀ x, F x = G x) : F = G := by
  funext x
  exact k x

/-! ### R2. `funext x` when a side is `fun n => e n` · that side becomes `e x` (β-reduction)
Applying `fun n => e n` to `x` and substituting `x` for `n` is β-reduction; `funext` does it for you,
so you see `x * c`, not `(fun n => n * c) x`. -/
example (c : Nat) (F : Nat → Nat) (k : ∀ x, x * c = F x) : (fun n => n * c) = F := by
  funext x
  exact k x

/-! ## Closing by computation -/

/-! ### R3. `id_eq` · `id a = a` · goal: `id a` → `a`
`id : α → α` is the identity function, defined as `fun a => a`. `rfl` sees through it (R4);
`simp` uses `id_eq` by itself. -/
example {α : Type} (a : α) (P : α → Prop) (k : P a) : P (id a) := by
  rw [id_eq]
  exact k

/-! ### R4. `rfl` · closes `a + b + 0 = id (a + b)`: both sides compute to `a + b`
`Nat` addition recurses on its second argument, so `t + 0` computes to `t` for ANY `t`, even a variable
(E001 R4). `id t` computes to `t`. No rewriting needed. -/
example (a b : Nat) : a + b + 0 = id (a + b) := by
  rfl

/-! ## Anonymous-function notation -/

/-! ### R5. `(· + c)` notation · after `funext x` that side is `x + c`
`(· + c)` is shorthand for `fun t => t + c`: the `·` marks where the argument goes. So R2 applies to it. -/
example (c : Nat) (F : Nat → Nat) (k : ∀ x, F x = x + c) : F = (· + c) := by
  funext x
  exact k x

/-! ## Composition `∘` -/

/-! ### R6. `Function.comp_apply` · `(f ∘ g) x = f (g x)` · goal: an applied composition → nested calls
`f ∘ g` (typed `\comp` or `\o`) is `Function.comp f g`, the function "first `g`, then `f`".
`funext` does NOT unfold it: after `funext x` you still see `(f ∘ g) x`. `simp` uses this lemma by itself. -/
example {α β γ : Type} (f : β → γ) (g : α → β) (x : α) (P : γ → Prop) (k : P (f (g x))) :
    P ((f ∘ g) x) := by
  rw [Function.comp_apply]
  exact k

/-! ## Using a hypothesis about a function -/

/-! ### R7. `rw [h]` with `h : ∀ x, s x = e x` · goal: ONE instance `s t` → `e t`
`rw` picks the value of `x` from the first match it finds, here the outer call `s (s a)` (`x := s a`),
and rewrites only that instance. A second `rw [h]` rewrites the inner `s a`. -/
example (s : Nat → Nat) (h : ∀ x, s x = 2 * x) (a : Nat) (P : Nat → Prop) (k : P (2 * s a)) :
    P (s (s a)) := by
  rw [h]
  exact k

/-! ### R8. `simp [h]` with `h : ∀ x, s x = e x` · goal: every `s t` → `e t`, plus R6 and arithmetic
As in E010 R9, but `simp` also applies R6 by itself and finishes `a + 3 + 3 = a + 6` (E010 R11). -/
example (s : Nat → Nat) (h : ∀ x, s x = x + 3) (a : Nat) : (s ∘ s) a = a + 6 := by
  simp [h]

/-! ## Lists -/

/-! ### R9. `List.map_map` · `List.map g (List.map f l) = List.map (g ∘ f) l` · goal: two maps → one
`List.map f l` applies `f` to every element of `l`. `List.map f` alone (no list yet) is a function
`List α → List β`. Mapping `f`, then `g`, is mapping `g ∘ f` once. `simp` uses this lemma by itself. -/
example {α β γ : Type} (f : α → β) (g : β → γ) (l : List α) (P : List γ → Prop)
    (k : P (List.map (g ∘ f) l)) : P (List.map g (List.map f l)) := by
  rw [List.map_map]
  exact k

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. R1 with R2 on the left, then `simp` (it knows `xs ++ [] = xs` and R3) -/
example : (fun xs : List Nat => xs ++ []) = id := by
  funext xs
  simp

/-! ### W2. R1 with R5 on the right, R8, then `omega` for what `simp` leaves -/
example (g : Nat → Nat) (hg : ∀ x, g x = 2 * x) : g ∘ g = (4 * ·) := by
  funext x
  simp [hg]
  omega

/-! ### W3. R1 + R5, R6, then R7 twice instead of `simp`
The last `rw` leaves `x + 5 + 5 = x + 10`, which its own `rfl` closes (E009 R3): both sides compute
to the same number. -/
example (g : Nat → Nat) (hg : ∀ x, g x = x + 5) : g ∘ g = (· + 10) := by
  funext x
  rw [Function.comp_apply]
  rw [hg]
  rw [hg]

/-! ### W4. Three maps: R1, then R6 and R9 (twice) through `simp` -/
example (f g h : Nat → Nat) :
    List.map f ∘ List.map g ∘ List.map h = List.map (f ∘ g ∘ h) := by
  funext xs
  simp [List.map_map]

end E022Guide
