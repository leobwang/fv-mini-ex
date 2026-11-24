/- Guide for M011 (Lawvere's fixed-point theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal" and `G` for an arbitrary goal; `k` or `h…` hypotheses in an
entry are only there to finish the example and show what the goal or context became.
Part W: worked combinations on objects that are NOT the exercise's (Nat-valued diagonals, `True`).
Core Lean only, no Mathlib. Assumed: Lean basics (E001–E033), in particular `intro`/`exact`/`apply`
(E003–E004), `⟨_, _⟩` and `obtain` (E005, E007), `∃` (E007), `¬` (E008), `simp` (E010), `cases` on
`Bool` (E016), `funext` (E022).
-/

namespace M011Guide

/-! # Part R · Reference entries -/

/-! ## Using a surjectivity hypothesis -/

/-! ### R1. `obtain ⟨c, h⟩ := hF d0` · context gains a witness `c` and `h : F c = d0`
`hF : ∀ d, ∃ c, F c = d` says `F` reaches every `d`. Applying it to the `d0` you choose gives an
`∃`, and `obtain` opens it. Choosing `d0` well (a diagonal) is the whole idea of the exercise. -/
example {γ δ : Type} (F : γ → δ) (hF : ∀ d : δ, ∃ c, F c = d) (d0 : δ) (G : Prop)
    (k : ∀ c, F c = d0 → G) : G := by
  obtain ⟨c, h⟩ := hF d0
  exact k c h

/-! ### R2. `congrFun` · `{f g : (x : α) → β x} (h : f = g) (a : α) : f a = g a` · context gains `h'`
An equation between functions gives an equation between their values at any point. When `g` is a
`fun`, Lean β-reduces: `(fun y => s (u y)) x` is shown as `s (u x)`. -/
example {α β : Type} (v u : α → β) (s : β → β) (h : v = fun y => s (u y)) (x : α) (G : Prop)
    (k : v x = s (u x) → G) : G := by
  have h' := congrFun h x
  exact k h'

/-! ### R3. `Eq.symm` · `(h : a = b) : b = a` · closes a goal that is `h` flipped; written `h.symm` -/
example {β : Type} (a b : β) (h : a = b) : b = a := by
  exact h.symm

/-! ### R4. `exact ⟨w, hw⟩` · closes `∃ b, Q b`: the witness `w` may be any term, here a computed one -/
example {β : Type} (Q : β → Prop) (w : β) (hw : Q w) : ∃ b, Q b := by
  exact ⟨w, hw⟩

/-! ## A diagonal that differs from every row -/

/-! ### R5. `refine ⟨w, fun n h => ?_⟩` · goal `∃ g, ∀ n, F n ≠ g` → context `n`, `h : F n = w`, goal `False`
`a ≠ b` is notation for `a = b → False` (`Ne a b`), so a proof of `∀ n, F n ≠ w` is a function of
`n` and of `h : F n = w` that returns `False`. -/
example {γ : Type} (F : Nat → γ) (w : γ) (hw : ∀ n, F n = w → False) : ∃ g, ∀ n, F n ≠ g := by
  refine ⟨w, fun n h => ?_⟩
  exact hw n h

/-! ### R6. `cases hb : e` · goal list: one goal per value of the Bool term `e`, with `hb` recording it
`e` may be any `Bool` expression (`f n n`), not only a variable. `hb : e = false` / `hb : e = true`
is added to the context; hypotheses that mention `e` are NOT rewritten (use R7 for that). -/
example (e : Bool) (G : Prop) (h0 : e = false → G) (h1 : e = true → G) : G := by
  cases hb : e
  exact h0 hb
  exact h1 hb

/-! ### R7. `simp [hb] at h` · context: `h` rewritten with `hb` and simplified; if `h` becomes `False`, the goal closes
`!b` is Bool negation (`not b`); `simp` evaluates `!true` to `false` and turns `true = false` into `False`. -/
example (e : Bool) (hb : e = true) (h : e = !e) : False := by
  simp [hb] at h

/-! ## Russell: comprehension as an equation of predicates -/

/-! ### R8. `intro hc` on `¬ A` · `¬ A` is `A → False`: context gains `hc : A`, goal becomes `False`
In term mode the same proof is `fun hc => …`, e.g. `have hn : ¬ A := fun ha => …`. -/
example (A : Prop) (k : A → False) : ¬ A := by
  intro hc
  exact k hc

/-! ### R9. `funext` · `(h : ∀ x, u x = v x) : u = v` · goal: equality of functions → pointwise equality
Term form: `funext fun x => (proof of u x = v x)`. -/
example {α β : Type} (u v : α → β) (h : ∀ x, u x = v x) : u = v := by
  apply funext
  exact h

/-! ### R10. `propext` · axiom `{a b : Prop} : (a ↔ b) → a = b` · goal: equality of Props → `↔` -/
example (A B : Prop) (h : A ↔ B) : A = B := by
  apply propext
  exact h

/-! ### R11. Instantiate a lemma at `Not : Prop → Prop` · context gains `q : Prop`, `hq : (¬q) = q`
`Not` is the function behind `¬`, so it can be passed wherever a `Prop → Prop` is expected.
`(¬q) = q` is an equation in `Prop`: "the proposition `¬q` is the proposition `q`". -/
example (L : ∀ F : Prop → Prop, ∃ q : Prop, F q = q) (G : Prop)
    (k : ∀ q : Prop, (¬q) = q → G) : G := by
  obtain ⟨q, hq⟩ := L Not
  exact k q hq

/-! ### R12. `cast` · `(h : A = B) (a : A) : B` · closes `B` from a proof of `A` and `h : A = B`
For Props this is "rewrite the statement": `cast h.symm` goes from `B` back to `A`. -/
example (A B : Prop) (h : A = B) (ha : A) : B := by
  exact cast h ha

/-! ### R13. `exact hn ha` · closes `False` from `hn : ¬ A` and `ha : A` (a negation is a function to `False`) -/
example (A : Prop) (hn : ¬ A) (ha : A) : False := by
  exact hn ha

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A Nat-valued diagonal differs from every row: R5, R2, then `omega` (linear arithmetic) -/
example (f : Nat → Nat → Nat) : ∃ g : Nat → Nat, ∀ n, f n ≠ g := by
  refine ⟨fun n => f n n + 1, fun n h => ?_⟩
  have h' := congrFun h n
  omega

/-! ### W2. Two predicates with the same truth values are equal: R9, then R10 at each point -/
example : (fun n : Nat => n + 0 = n) = (fun _ => True) := by
  apply funext
  intro n
  apply propext
  exact ⟨fun _ => trivial, fun _ => rfl⟩

/-! ### W3. Transport along an equation of Props in the other direction: R12 with R3 -/
example (p : Prop) (h : p = True) : p := by
  exact cast h.symm trivial

end M011Guide
