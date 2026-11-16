/- H004 | Well-founded relations: Acc, lex, descending chains | 45-75 min | WellFounded, Acc, Prod.Lex, classical choice, Nat.rec
GOAL
  Work with `Acc` and `WellFounded` by hand: a well-founded relation is irreflexive, the
  lexicographic product of two well-founded relations is well-founded, and `r` is well-founded
  iff there is no infinite descending chain `f : Nat → α`, `r (f (n+1)) (f n)` for every `n`
  (the ← direction needs choice).

REFERENCE
  -- `Acc r a`: every r-descending path from a is finite. `WellFounded r`: every `a` is `Acc`.
  example {α : Type} (r : α → α → Prop) (a : α) (h : ∀ y, r y a → Acc r y) : Acc r a := .intro a h
  example {α : Type} (r : α → α → Prop) (h : ∀ a, Acc r a) : WellFounded r := ⟨h⟩   -- `h.apply a : Acc r a`
  -- `induction a using h.induction with | _ a ih => …`   (h : WellFounded r; ih : ∀ y, r y a → P y)
  -- `induction ha with | intro a _ ih => …`             (ha : Acc r a; same shape of ih)
  example {α β : Type} (r : α → α → Prop) (s : β → β → Prop) (a : α) (b b' : β) (h : s b b') :
      Prod.Lex r s (a, b) (a, b') := .right a h        -- `.left b₁ b₂ (h : r a₁ a₂)` for the first slot
  example {α : Type} (p : α → Prop) (h : ∃ x, p x) : p (Classical.choose h) := Classical.choose_spec h
  example (x : Nat) (g : Nat → Nat) : Nat → Nat := fun n => Nat.rec x (fun _ y => g y) n  -- x, g x, g (g x), …
  -- `Classical.byContradiction fun h => …` proves `p` from `¬p → False`.
BANNED: Prod.lexAccessible, Prod.lex, WellFounded.prod_lex, PSigma.lexNdepWf, PSigma.revLex, PSigma.revLexAccessible, Prod.instWellFoundedRelation, invImage, WellFoundedRelation, termination_by, decreasing_by, import, exact?, apply?, try?
NOTE: Core's ready-made lex lemmas and `termination_by` recursion are banned: prove `acc_lex` by `induction` on `Acc`.
-/

namespace H004

-- BEGIN SPEC
theorem wf_irrefl {α : Type} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
theorem acc_lex {α β : Type} {r : α → α → Prop} {s : β → β → Prop} (hs : WellFounded s)
    {a : α} (ha : Acc r a) (b : β) : Acc (Prod.Lex r s) (a, b) := by
  sorry

-- BEGIN SPEC
theorem wf_lex {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    (hr : WellFounded r) (hs : WellFounded s) : WellFounded (Prod.Lex r s) :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
theorem acc_not_in_chain {α : Type} {r : α → α → Prop} (f : Nat → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) {x : α} (hx : Acc r x) : ∀ n, f n ≠ x := by
  sorry

-- BEGIN SPEC
theorem no_descending_chain {α : Type} {r : α → α → Prop} (h : WellFounded r) :
    ¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n) :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
theorem not_acc_step {α : Type} {r : α → α → Prop} {x : α} (hx : ¬ Acc r x) :
    ∃ y, r y x ∧ ¬ Acc r y := by
  sorry

-- BEGIN SPEC
theorem wf_of_no_descending_chain {α : Type} {r : α → α → Prop}
    (h : ¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n)) : WellFounded r :=
-- END SPEC
  sorry

end H004

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything except the last theorem is an induction on `Acc` (or `h.induction`); the last one builds a chain from the non-accessible elements.
H2. `acc_lex`: induct on `ha` generalizing `b`, then inside do `hs.induction` on `b`, and split the `Prod.Lex` step into `left` (outer IH) and `right` (inner IH). Last theorem: if some `a` is not `Acc`, iterate `not_acc_step` from `a` with `Nat.rec`, carrying the proof of `¬ Acc` along (use the subtype `{x // ¬ Acc r x}`).
H3. `acc_lex` core: `constructor; intro p hp; cases hp with | left _ _ h => exact iha _ h _ | right _ h => exact ihb _ h`. Chain: `let next : {x // ¬ Acc r x} → {x // ¬ Acc r x} := fun x => ⟨Classical.choose (not_acc_step x.2), (Classical.choose_spec (not_acc_step x.2)).2⟩`, then `let f : Nat → {x // ¬ Acc r x} := fun n => Nat.rec ⟨a, ha⟩ (fun _ x => next x) n`.
-/
