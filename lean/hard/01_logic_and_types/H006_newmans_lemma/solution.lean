/- H006 | Newman's lemma | 1-1.5 h | abstract rewriting, confluence, well-founded induction, counterexample
GOAL
  Newman's lemma: if `R` terminates (no infinite chain a₀ → a₁ → …) and is locally confluent (any
  two one-step reducts can be rejoined), then it is confluent (any two many-step reducts can).
  Then show termination is needed: the 4-element system pa ← pb ⇄ pc → pd is locally confluent
  but not confluent.

REFERENCE
  -- `Star R a b`: zero or more R-steps. Build with `.refl a` and `.step (h : R a b) (hs : Star R b c)`.
  example (R : Nat → Nat → Prop) (h : R 0 1) : H006.Joinable R 0 1 := ⟨1, .step h (.refl 1), .refl 1⟩
  -- `induction a using ht.induction with | _ a ih => …`  (ht : Terminating R; ih : ∀ y, R a y → P y)
  -- `cases hb with | refl => … | step h hb' => …` on `hb : Star R a b`; `rename_i x y` names
  --   variables that show up as inaccessible (`b✝`).
  -- `obtain ⟨d, hbd, hcd⟩ := hl _ _ _ h1 h2` unpacks a `Joinable` (an `∃` of a pair).
  -- `cases h1 <;> cases h2` enumerates every pair of `R4` steps out of the same point.
  example (x : H006.P) (h : H006.R4 .pa x) : False := nomatch h   -- pa has no outgoing step
NOTE: State `star_trans` first; you will glue many-step paths together everywhere.
-/

namespace H006

-- BEGIN SPEC
variable {α : Type}

/-- Reflexive-transitive closure: zero or more `R`-steps. -/
inductive Star (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star R a a
  | step {a b c : α} : R a b → Star R b c → Star R a c

def Joinable (R : α → α → Prop) (b c : α) : Prop := ∃ d, Star R b d ∧ Star R c d

def LocallyConfluent (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → Joinable R b c

def Confluent (R : α → α → Prop) : Prop :=
  ∀ a b c, Star R a b → Star R a c → Joinable R b c

/-- No infinite R-chains: the converse of R is well-founded. -/
def Terminating (R : α → α → Prop) : Prop := WellFounded (fun b a => R a b)
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem star_trans {R : α → α → Prop} {a b c : α} (h1 : Star R a b) (h2 : Star R b c) :
    Star R a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

-- BEGIN SPEC
theorem newman (R : α → α → Prop) (ht : Terminating R) (hl : LocallyConfluent R) :
    Confluent R :=
-- END SPEC
  by
    -- WHY: `intro a` first, so the induction hypothesis quantifies over all pairs of paths.
    intro a
    induction a using ht.induction with
    | _ a ih =>
    intro b c hb hc
    cases hb with
    | refl => exact ⟨c, hc, .refl c⟩
    | step hab1 hb1 =>
    cases hc with
    | refl => exact ⟨_, .refl _, .step hab1 hb1⟩
    | step hac1 hc1 =>
    rename_i b1 c1
    obtain ⟨d, hb1d, hc1d⟩ := hl _ _ _ hab1 hac1
    obtain ⟨e, hbe, hde⟩ := ih b1 hab1 _ _ hb1 hb1d
    obtain ⟨f, hef, hcf⟩ := ih c1 hac1 _ _ (star_trans hc1d hde) hc1
    exact ⟨f, star_trans hbe hef, hcf⟩

-- BEGIN SPEC
/-- The classic counterexample: pa ← pb ⇄ pc → pd. -/
inductive P where
  | pa | pb | pc | pd

inductive R4 : P → P → Prop
  | ba : R4 .pb .pa
  | bc : R4 .pb .pc
  | cb : R4 .pc .pb
  | cd : R4 .pc .pd
-- END SPEC

-- BEGIN SPEC
theorem r4_locally_confluent : LocallyConfluent R4 :=
-- END SPEC
  by
    intro a b c hb hc
    cases hb <;> cases hc
    all_goals first
      | exact ⟨_, .refl _, .refl _⟩
      | exact ⟨.pa, .refl _, .step .cb (.step .ba (.refl _))⟩
      | exact ⟨.pa, .step .cb (.step .ba (.refl _)), .refl _⟩
      | exact ⟨.pd, .step .bc (.step .cd (.refl _)), .refl _⟩
      | exact ⟨.pd, .refl _, .step .bc (.step .cd (.refl _))⟩

-- MILESTONE (optional: change or delete)
theorem star_from_normal {R : α → α → Prop} {x y : α} (hn : ∀ z, ¬ R x z) (h : Star R x y) :
    y = x := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hn _)

-- BEGIN SPEC
theorem r4_not_confluent : ¬ Confluent R4 :=
-- END SPEC
  by
    intro h
    obtain ⟨e, ha, hd⟩ := h .pb .pa .pd (.step .ba (.refl _)) (.step .bc (.step .cd (.refl _)))
    have h1 := star_from_normal (fun z h => nomatch h) ha
    have h2 := star_from_normal (fun z h => nomatch h) hd
    subst h1
    cases h2

end H006

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Newman: well-founded induction on the peak `a` (bigger = closer to the start), then case-split both paths `a →* b` and `a →* c` on their first step. The counterexample: pa and pd are normal forms, and pb reaches both.
H2. If either path is `refl`, join trivially. Otherwise `a → b1 →* b` and `a → c1 →* c`: local confluence joins `b1, c1` at some `d`; the IH at `b1` joins `b` and `d` at `e`; the IH at `c1` joins `e` and `c`.
H3. `intro a; induction a using ht.induction with | _ a ih => …` so that `ih : ∀ y, R a y → ∀ b c, Star R y b → Star R y c → Joinable R b c`. Then `obtain ⟨d, hb1d, hc1d⟩ := hl _ _ _ hab1 hac1`; apply `ih` at `b1` to join `b` and `d` at some `e`, then `ih` at `c1` to join `e` and `c`, using `star_trans` to glue `c1 →* d →* e`. Non-confluence: apply the hypothesis to `pb →* pa` and `pb →* pd`, then `star_from_normal` twice.
-/
