/- H004 | Well-founded relations: Acc, lex, descending chains | 45-75 min | WellFounded, Acc, Prod.Lex, classical choice, Nat.rec
GOAL
  Work with `Acc` and `WellFounded` by hand: a well-founded relation is irreflexive, the
  lexicographic product of two well-founded relations is well-founded, and `r` is well-founded
  iff there is no infinite descending chain `f : Nat → α`, `r (f (n+1)) (f n)` for every `n`
  (the ← direction needs choice).
BANNED: Prod.lexAccessible, Prod.lex, WellFounded.prod_lex, PSigma.lexNdepWf, PSigma.revLex, PSigma.revLexAccessible, Prod.instWellFoundedRelation, invImage, WellFoundedRelation, termination_by, decreasing_by, import, exact?, apply?, try?

GUIDE
  Entries R1–R20: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H004

/- SKELETON · wf_irrefl
  1. Well-founded induction on `a` (nothing else to keep fixed):                      R1
       ih : ∀ y, r y a → ¬ r y y
  2. Assume `hr : r a a`; the goal becomes `False`:                                   R2
  3. `a` is its own predecessor: the IH at `y := a`, with the step `hr`, refutes `hr`: R3
-/
-- BEGIN SPEC
theorem wf_irrefl {α : Type} {r : α → α → Prop} (h : WellFounded r) (a : α) : ¬ r a a :=
-- END SPEC
  sorry

/- SKELETON · acc_lex   (milestone; prove it FIRST; wf_lex is one line from it)
  1. Outer induction on `ha`, generalizing `b`:                                       R4, R5
       iha : ∀ y, r y a → ∀ b, Acc (Prod.Lex r s) (y, b)
  2. Inner well-founded induction on `b` by `hs`:                                     R1
       ihb : ∀ y, s y b → Acc (Prod.Lex r s) (a, y)
  3. Show every lex-predecessor `p` of `(a, b)` is accessible:                        R6, intro p hp
  4. Split the lex step `hp`:                                                         R7
       left  (first component went down, `h : r _ a`):  outer IH                     R3
       right (first stays `a`, `h : s _ b`):             inner IH                     R3
-/
-- MILESTONE (optional: change or delete)
theorem acc_lex {α β : Type} {r : α → α → Prop} {s : β → β → Prop} (hs : WellFounded s)
    {a : α} (ha : Acc r a) (b : β) : Acc (Prod.Lex r s) (a, b) := by
  sorry

/- SKELETON · wf_lex
  0. Prove the milestone acc_lex first (used in step 2).
  1. Open `WellFounded`, splitting the point into a pair `(a, b)`:                   R8, R9
       put R9's pattern `⟨a, b⟩` in R8's binder; after a plain R8 the goal
       `Acc _ x` has no `∀` left, so a separate `intro ⟨a, b⟩` fails
  2. `Acc r a` from `hr`, then acc_lex with `hs`:                                    R10
-/
-- BEGIN SPEC
theorem wf_lex {α β : Type} {r : α → α → Prop} {s : β → β → Prop}
    (hr : WellFounded r) (hs : WellFounded s) : WellFounded (Prod.Lex r s) :=
-- END SPEC
  sorry

/- SKELETON · acc_not_in_chain   (milestone; prove it FIRST; no_descending_chain uses it at n = 0)
  1. Induction on `hx` (`f`, `hf` stay fixed):                                        R4
       ih : ∀ y, r y x → ∀ n, f n ≠ y
  2. Introduce `n` and `hn : f n = x` (`≠` is a `¬`); the goal is `False`:            R2
  3. `f (n + 1)` is a predecessor of `x`: `hf n` transported along `hn`:              R11
  4. The IH at `f (n + 1)`, that step, index `n + 1`, applied to `rfl`:               R3
-/
-- MILESTONE (optional: change or delete)
theorem acc_not_in_chain {α : Type} {r : α → α → Prop} (f : Nat → α)
    (hf : ∀ n, r (f (n + 1)) (f n)) {x : α} (hx : Acc r x) : ∀ n, f n ≠ x := by
  sorry

/- SKELETON · no_descending_chain
  0. Prove the milestone acc_not_in_chain first (used in step 2).
  1. Take the assumed chain apart into `f` and `hf`; the goal is `False`:            R12
  2. `f 0` is accessible (R10); acc_not_in_chain at index 0 says `f 0 ≠ f 0`;
     apply it to `rfl`:                                                              R10, R3
-/
-- BEGIN SPEC
theorem no_descending_chain {α : Type} {r : α → α → Prop} (h : WellFounded r) :
    ¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n) :=
-- END SPEC
  sorry

/- SKELETON · not_acc_step   (milestone; prove it FIRST; wf_of_no_descending_chain iterates it)
  1. By contradiction: `hno : ¬ ∃ y, r y x ∧ ¬ Acc r y`, goal `False`:                R13
  2. Refute `hx` by proving `Acc r x`, one predecessor `y`, `hy : r y x` at a time:  R15, R14
  3. Goal `Acc r y`: by contradiction again (`hy' : ¬ Acc r y`);
     then `⟨y, hy, hy'⟩` contradicts `hno`:                                          R13, R15
-/
-- MILESTONE (optional: change or delete)
theorem not_acc_step {α : Type} {r : α → α → Prop} {x : α} (hx : ¬ Acc r x) :
    ∃ y, r y x ∧ ¬ Acc r y := by
  sorry

/- SKELETON · wf_of_no_descending_chain
  0. Prove the milestone not_acc_step first (used in steps 2 and 4).
  1. Open `WellFounded` at a point `a`; by contradiction `ha : ¬ Acc r a`;
     reduce `False` to building a chain with `h`:                                    R8, R13, R15
  2. `let next : {x // ¬ Acc r x} → {x // ¬ Acc r x}`: from `z`, apply not_acc_step
     to `z.2`, take the witness and pack it with the `¬ Acc` half of its spec:       R19, R17, R18, R16
  3. `let f : Nat → {x // ¬ Acc r x}`: iterate `next` from `⟨a, ha⟩`:                 R19, R20, R16
  4. The chain is `fun n => (f n).1`; its step at `n` is the first half of the spec
     of not_acc_step at `(f n).2` (accepted by unfolding `f (n + 1)`):              R17, R18, R20
-/
-- BEGIN SPEC
theorem wf_of_no_descending_chain {α : Type} {r : α → α → Prop}
    (h : ¬ ∃ f : Nat → α, ∀ n, r (f (n + 1)) (f n)) : WellFounded r :=
-- END SPEC
  sorry

end H004

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The first three theorems are inductions on accessibility (R1 for `WellFounded`, R4 for `Acc`):
    a well-founded relation has no loop and no infinite chain, and lex inherits it. The last one is
    classical: from a point that is not accessible, keep choosing a non-accessible predecessor
    (not_acc_step) and you get an infinite descending chain.
H2. `acc_lex`: outer induction on `ha` generalizing `b` (R4, R5), inner `hs.induction` on `b` (R1),
    `constructor; intro p hp` (R6), then `cases hp` (R7): `left` uses the outer IH, `right` the inner.
    `acc_not_in_chain`: induction on `hx`; the IH at `f (n + 1)` with `hn ▸ hf n` (R11).
    Last theorem: by contradiction pick `ha : ¬ Acc r a`, then iterate a `next` map with `Nat.rec`
    on the subtype `{x // ¬ Acc r x}`, so the proof of `¬ Acc` travels with the point (R16–R20).
H3. `acc_lex` core: `cases hp with | left _ _ h => exact iha _ h _ | right _ h => exact ihb _ h`.
    `wf_lex`: `⟨fun ⟨a, b⟩ => acc_lex hs (hr.apply a) b⟩`. `not_acc_step`:
    `refine Classical.byContradiction fun hno => hx (.intro x fun y hy => ?_)`. Chain:
    `let next : {x // ¬ Acc r x} → {x // ¬ Acc r x} := fun x => ⟨Classical.choose (not_acc_step x.2), (Classical.choose_spec (not_acc_step x.2)).2⟩`,
    then `let f : Nat → {x // ¬ Acc r x} := fun n => Nat.rec ⟨a, ha⟩ (fun _ x => next x) n`.
-/
