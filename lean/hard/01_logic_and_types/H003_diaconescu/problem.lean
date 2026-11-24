/- H003 | Diaconescu: choice implies excluded middle | 45-60 min | Classical foundations, funext, propext, proof irrelevance, subst, AXIOMS
GOAL
  Given a choice operator `choose` (picks a witness of any `∃ x, P x`, with spec `choose_spec`),
  derive `p ∨ ¬p` for an arbitrary proposition `p` using only function and propositional
  extensionality. Lean's own `Classical.choice` axiom is off limits (see AXIOMS).
AXIOMS: propext, Quot.sound

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H003

/- SKELETON · choose_congr   (prove this first; used in `key`)
  1. Replace `Q` by `P` everywhere, in the type of `hQ` too (`rw [h]` fails here):   R1
  2. The two sides now differ only in the proof argument (`hP` vs `hQ`):              R2
-/
-- MILESTONE (optional: change or delete)
theorem choose_congr
    (choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α)
    {α : Type} (P Q : α → Prop) (hP : ∃ x, P x) (hQ : ∃ x, Q x) (h : P = Q) :
    choose P hP = choose Q hQ := by
  sorry

/- SKELETON · key   (prove this second, from `choose_congr`; used in `diaconescu`)
  1. Assume `hp : p`:                                                     intro hp
  2. Reduce to an equation of predicates with the milestone:              R3 (apply choose_congr choose)
  3. Predicates are equal pointwise:                                      R4
  4. At each `x`, the two propositions are equivalent:                    R5
  5. Split the `↔` (`constructor`, as in E005): goals `mp` and `mpr`.
     In each, `intro _` (ignore the hypothesis), prove the right side `p`:  R6 (with `hp`)
-/
-- MILESTONE (optional: change or delete)
theorem key
    (choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α)
    (p : Prop) (hU : ∃ x, x = true ∨ p) (hV : ∃ x, x = false ∨ p) :
    p → choose (fun x => x = true ∨ p) hU = choose (fun x => x = false ∨ p) hV := by
  sorry

/- SKELETON · diaconescu   (uses milestone `key` in step 4)
  1. After `by` (the statement ends in `:=`), inhabit both predicates
     on `Bool` with two `have`s:                                          R7, R6
       hU : ∃ x, x = true ∨ p      hV : ∃ x, x = false ∨ p
  2. Case on `choose_spec _ hU`:                                           R8
       goals: `inl` with `hut : choose … hU = true`, then `inr` with `hp : p`
  3. In `inl`: case on `choose_spec _ hV`:                                 R8
       goals: `inl.inl` with `hvf : choose … hV = false`, then `inl.inr` with `hp : p`
  4. `inl.inl` (both choices known): prove `¬p`:                           R6, R9
       from `hp : p`, milestone `key` gives the two choices equal:         R10
       rewrite them to `true = false`, then contradiction:                 R11 → R12
  5. `inl.inr`, then `inr`: you have `hp : p`, take the left side:         R6
-/
-- BEGIN SPEC
theorem diaconescu
    (choose : {α : Type} → (P : α → Prop) → (∃ x, P x) → α)
    (choose_spec : ∀ {α : Type} (P : α → Prop) (h : ∃ x, P x), P (choose P h))
    (p : Prop) : p ∨ ¬ p :=
-- END SPEC
  sorry

end H003

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Choose from two predicates on `Bool`: `U x := x = true ∨ p` and `V x := x = false ∨ p`. Both are inhabited (R7) without knowing anything about `p`.
H2. `choose_congr` is R1 then R2. `key`: with `choose_congr` (R3) it suffices that `U = V` when `p` holds (R4, R5, R6). Main proof: case on `choose_spec U _` and `choose_spec V _` (R8); an `inr` branch gives `p`; if both are `inl`, the choices are `true` and `false`, so `p` would force `true = false`, hence `¬p` (R9 → R12).
H3. `choose_congr`: `subst h; rfl`. `key`: `exact funext fun x => propext ⟨fun _ => .inr hp, fun _ => .inr hp⟩` after `apply choose_congr choose`. Main proof's last branch: `exact .inr fun hp => by have := key choose p hU hV hp; rw [hut, hvf] at this; exact Bool.noConfusion this`.
-/
