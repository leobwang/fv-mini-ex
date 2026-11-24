/- H006 | Newman's lemma | 1-1.5 h | abstract rewriting, confluence, well-founded induction, counterexample
GOAL
  Newman's lemma: if `R` terminates (no infinite chain a₀ → a₁ → …) and is locally confluent (any
  two one-step reducts can be rejoined), then it is confluent (any two many-step reducts can).
  Then show termination is needed: the 4-element system pa ← pb ⇄ pc → pd is locally confluent
  but not confluent.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · star_trans   (milestone; prove it FIRST; newman uses it twice to glue paths)
  1. Induct on the derivation `h1` (not on a point), leaving `h2` in the context so
     that it becomes a premise of the IH:                                              R1, R3
  2. refl: the goal is exactly the type of `h2`:                                       exact h2
  3. step s _ ih: prepend the step `s` to the path that `ih` makes from `h2`:          R4
-/
-- MILESTONE (optional: change or delete)
theorem star_trans {R : α → α → Prop} {a b c : α} (h1 : Star R a b) (h2 : Star R b c) :
    Star R a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

/- SKELETON · newman
  0. Prove the milestone star_trans first (used in steps 4 and 5).
  1. Open `Confluent R`, but introduce only the peak `a`:                               R6
  2. Well-founded induction on `a`, naming the point and the IH:                       R7
       ih : ∀ y, R a y → ∀ b c, Star R y b → Star R y c → Joinable R b c
     then introduce `b c hb hc`.
  3. Split `hb` on its first step. refl (`b` is `a`): join at `c`:                      R5, R8 with R4
     Split `hc` the same way.     refl (`c` is `a`): join at `b`:                      R5, R8 with R4
  4. step/step, a → b1 →* b and a → c1 →* c. Name the two targets `b1 c1`:             R2
       local confluence `hl` joins b1, c1 at some d:                                   R9
       the IH at b1 joins b and d at some e:                                           R9
       the IH at c1 joins e and c at some f; its path c1 →* e is
       c1 →* d →* e by star_trans:                                                     R9
  5. Close with f; the path b →* f is b →* e →* f by star_trans:                       R8
-/
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

/- SKELETON · r4_locally_confluent
  1. Open `LocallyConfluent R4`: introduce `a b c hb hc`:                               R6
  2. Every pair of steps out of the same point: `cases hb <;> cases hc`:               R10
  3. One list of candidate joins tried on all goals: `all_goals first | … | …`:         R11
     candidates: both paths empty (same target), or a join at `.pa` or `.pd`
     through pc → pb → pa or pb → pc → pd, each in either order:                       R8 with R4
-/
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

/- SKELETON · star_from_normal   (milestone; r4_not_confluent uses it twice)
  1. Split the path `h` on its first step:                                             R5
  2. refl: `y` is `x`:                                                                 rfl
  3. step s _: `s : R x _` contradicts `hn _`:                                         R13
-/
-- MILESTONE (optional: change or delete)
theorem star_from_normal {R : α → α → Prop} {x y : α} (hn : ∀ z, ¬ R x z) (h : Star R x y) :
    y = x := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hn _)

/- SKELETON · r4_not_confluent
  0. Prove the milestone star_from_normal first (used in step 3).
  1. Assume confluence `h`; the goal becomes `False`:                                  R14
  2. Apply `h` at pb to the paths pb →* pa and pb →* pd; unpack the join `e`:          R4, R9
  3. pa and pd have no outgoing step, so `have` e = pa and e = pd from
     star_from_normal, with `hn := fun z h => nomatch h` (twice):                      R12
  4. Substitute `e`; the remaining equation between pa and pd is a constructor clash:  R15, R16
-/
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
H1. Prove `star_trans` first, by induction on the derivation `h1` (R1, R3). Newman: well-founded
    induction on the peak `a` (introduce only `a`, R6, R7), then split both paths `a →* b` and
    `a →* c` on their first step (R5). The counterexample: pa and pd are normal forms, and pb
    reaches both.
H2. If either path is `refl`, join trivially (R8). Otherwise `a → b1 →* b` and `a → c1 →* c`:
    local confluence joins `b1, c1` at some `d`; the IH at `b1` joins `b` and `d` at `e`; the IH at
    `c1` joins `e` and `c` (glue `c1 →* d →* e` with `star_trans`) (R9). Local confluence of R4:
    `cases hb <;> cases hc`, then `all_goals first | … | …` over the possible joins (R10, R11).
    Non-confluence: confluence at pb joins pa and pd at some `e`; `star_from_normal` forces
    `e = pa` and `e = pd` (R12–R16).
H3. `intro a; induction a using ht.induction with | _ a ih => …` so that
    `ih : ∀ y, R a y → ∀ b c, Star R y b → Star R y c → Joinable R b c`. In the step/step case,
    `rename_i b1 c1`, `obtain ⟨d, hb1d, hc1d⟩ := hl _ _ _ hab1 hac1`,
    `obtain ⟨e, hbe, hde⟩ := ih b1 hab1 _ _ hb1 hb1d`, then `ih c1 hac1 _ _ (star_trans hc1d hde) hc1`.
    Non-confluence: `obtain ⟨e, ha, hd⟩ := h .pb .pa .pd (.step .ba (.refl _)) (.step .bc (.step .cd (.refl _)))`,
    then `star_from_normal (fun z h => nomatch h) ha` and the same for `hd`.
-/
