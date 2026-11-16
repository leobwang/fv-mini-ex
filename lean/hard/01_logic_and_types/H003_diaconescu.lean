/- H003 | Diaconescu: choice implies excluded middle | 45-60 min | Classical foundations, funext, propext, proof irrelevance, subst, AXIOMS
GOAL
  Given a choice operator `choose` (picks a witness of any `∃ x, P x`, with spec `choose_spec`),
  derive `p ∨ ¬p` for an arbitrary proposition `p` using only function and propositional
  extensionality. Lean's own `Classical.choice` axiom is off limits (see AXIOMS).

REFERENCE
  example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := funext h     -- function extensionality
  example (p q : Prop) (h1 : p → q) (h2 : q → p) : p = q := propext ⟨h1, h2⟩   -- equal iff equivalent
  example (P : Nat → Prop) (h1 h2 : ∃ x, P x) : h1 = h2 := rfl   -- any two proofs are equal, by `rfl`
  example (h : true = false) : False := Bool.noConfusion h          -- distinct constructors
  example (P Q : Nat → Prop) (h : P = Q) (hQ : ∃ x, Q x) : ∃ x, P x := by subst h; exact hQ
  -- ^ `subst h` swaps the local `Q` for `P` everywhere, even inside other hypotheses' types;
  --   `rw [h]` on a goal mentioning `choose Q hQ` fails with "motive is not type correct".
  example (p q : Prop) (h : p ∨ q) : q ∨ p := by rcases h with h | h; exact .inr h; exact .inl h
  -- Check yourself: `#print axioms H003.diaconescu` must list only `propext` and `Quot.sound`.
AXIOMS: propext, Quot.sound
NOTE: `Classical.*`, `by_cases`/`by_contra` on a bare Prop, `grind`, `decide` and some `simp` lemmas use `Classical.choice`.
-/

namespace H003

-- MILESTONE (optional: change or delete)
theorem choose_congr
    (choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α)
    {α : Type} (P Q : α → Prop) (hP : ∃ x, P x) (hQ : ∃ x, Q x) (h : P = Q) :
    choose P hP = choose Q hQ := by
  sorry

-- MILESTONE (optional: change or delete)
theorem key
    (choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α)
    (p : Prop) (hU : ∃ x, x = true ∨ p) (hV : ∃ x, x = false ∨ p) :
    p → choose (fun x => x = true ∨ p) hU = choose (fun x => x = false ∨ p) hV := by
  sorry

-- BEGIN SPEC
theorem diaconescu
    (choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α)
    (choose_spec : ∀ {α : Type} (P : α → Prop) (h : ∃ x, P x), P (choose P h))
    (p : Prop) : p ∨ ¬ p :=
-- END SPEC
  sorry

end H003

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Choose from two predicates on `Bool`: `U x := x = true ∨ p` and `V x := x = false ∨ p`. Both are inhabited without knowing anything about `p`.
H2. If `p` holds, `U = V` (funext + propext), so the two choices coincide (`key`). Now case on `choose_spec U _` and `choose_spec V _`: an `inr` branch gives `p`; if both are `inl`, the choices are `true` and `false`, so `p` would force `true = false`, hence `¬p`.
H3. `choose_congr`: `subst h; rfl`. Main proof's last branch: `exact .inr fun hp => by have := key choose p hU hV hp; rw [hut, hvf] at this; exact Bool.noConfusion this`.
-/
