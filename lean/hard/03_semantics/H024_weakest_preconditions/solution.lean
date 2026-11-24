/- H024 | Hoare logic: weakest preconditions and relative completeness | 40-60 min | Hoare logic, weakest liberal precondition, fixpoint equation, relative completeness, induction on commands
GOAL
  `wp c Q` holds in the states from which every terminating run of `c` ends in `Q`. Prove it
  distributes over `;`, satisfies the one-step unfolding equation of `while`, and is derivable as a
  precondition; conclude that every valid Hoare triple is derivable (relative completeness).

GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H024

-- BEGIN SPEC
abbrev State := Nat → Int

inductive AExp where
  | num (n : Int)
  | var (x : Nat)
  | plus (a b : AExp)
  | times (a b : AExp)

def aeval (s : State) : AExp → Int
  | .num n => n
  | .var x => s x
  | .plus a b => aeval s a + aeval s b
  | .times a b => aeval s a * aeval s b

inductive BExp where
  | tt
  | ff
  | le (a b : AExp)
  | not (b : BExp)
  | and (b1 b2 : BExp)

def beval (s : State) : BExp → Bool
  | .tt => true
  | .ff => false
  | .le a b => decide (aeval s a ≤ aeval s b)
  | .not b => !beval s b
  | .and b1 b2 => beval s b1 && beval s b2

inductive Com where
  | skip
  | assign (x : Nat) (a : AExp)
  | seq (c1 c2 : Com)
  | ite (b : BExp) (c1 c2 : Com)
  | while (b : BExp) (c : Com)

def update (s : State) (x : Nat) (v : Int) : State := fun y => if y = x then v else s y

inductive BigStep : Com → State → State → Prop
  | skip {s : State} : BigStep .skip s s
  | assign {s : State} {x : Nat} {a : AExp} : BigStep (.assign x a) s (update s x (aeval s a))
  | seq {c1 c2 : Com} {s s' s'' : State} :
      BigStep c1 s s' → BigStep c2 s' s'' → BigStep (.seq c1 c2) s s''
  | iteT {b : BExp} {c1 c2 : Com} {s s' : State} :
      beval s b = true → BigStep c1 s s' → BigStep (.ite b c1 c2) s s'
  | iteF {b : BExp} {c1 c2 : Com} {s s' : State} :
      beval s b = false → BigStep c2 s s' → BigStep (.ite b c1 c2) s s'
  | whileF {b : BExp} {c : Com} {s : State} :
      beval s b = false → BigStep (.while b c) s s
  | whileT {b : BExp} {c : Com} {s s' s'' : State} :
      beval s b = true → BigStep c s s' → BigStep (.while b c) s' s'' → BigStep (.while b c) s s''

abbrev Assn := State → Prop

/-- `{P} c {Q}` holds semantically (partial correctness). -/
def Valid (P : Assn) (c : Com) (Q : Assn) : Prop := ∀ s s', P s → BigStep c s s' → Q s'

/-- Hoare logic for partial correctness (assertions are Lean predicates on states). -/
inductive Derivable : Assn → Com → Assn → Prop
  | skip {P : Assn} : Derivable P .skip P
  | assign {Q : Assn} {x : Nat} {a : AExp} :
      Derivable (fun s => Q (update s x (aeval s a))) (.assign x a) Q
  | seq {P Q R : Assn} {c1 c2 : Com} :
      Derivable P c1 Q → Derivable Q c2 R → Derivable P (.seq c1 c2) R
  | ite {P Q : Assn} {b : BExp} {c1 c2 : Com} :
      Derivable (fun s => P s ∧ beval s b = true) c1 Q →
      Derivable (fun s => P s ∧ beval s b = false) c2 Q → Derivable P (.ite b c1 c2) Q
  | while {I : Assn} {b : BExp} {c : Com} :
      Derivable (fun s => I s ∧ beval s b = true) c I →
      Derivable I (.while b c) (fun s => I s ∧ beval s b = false)
  | conseq {P P' Q Q' : Assn} {c : Com} :
      (∀ s, P' s → P s) → Derivable P c Q → (∀ s, Q s → Q' s) → Derivable P' c Q'

/-- Weakest liberal precondition. -/
def wp (c : Com) (Q : Assn) : Assn := fun s => ∀ s', BigStep c s s' → Q s'
-- END SPEC

-- MILESTONE (optional: change or delete)
/- SKELETON · wp_while_body   (milestone 1: prove it first; used in wp_while and derivable_wp_while)
  1. The goal `wp c (wp (.while b c) Q) s` unfolds to two ∀s: introduce a state, a run of `c`
     from `s`, a final state, and a run of the loop from the middle state           R1
  2. `h.1 : wp (.while b c) Q s` is a function: give it the final state and a run of
     the whole loop from `s`                                                          R2
  3. Build that run with the rule `BigStep.whileT` from `h.2` and the two runs         R3
-/
theorem wp_while_body (b : BExp) (c : Com) (Q : Assn) (s : State)
    (h : wp (.while b c) Q s ∧ beval s b = true) : wp c (wp (.while b c) Q) s := by
  intro s1 h1 s2 h2
  exact h.1 s2 (.whileT h.2 h1 h2)

-- MILESTONE (optional: change or delete)
/- SKELETON · wp_while_exit   (milestone 2: used in wp_while and derivable_wp_while)
  1. `h.1` is a function: give it the final state `s` itself and a run of the loop
     from `s` to `s`                                                                  R2
  2. That run: the rule `BigStep.whileF` applied to `h.2`                              R3
-/
theorem wp_while_exit (b : BExp) (c : Com) (Q : Assn) (s : State)
    (h : wp (.while b c) Q s ∧ beval s b = false) : Q s := by
  exact h.1 s (.whileF h.2)

-- MILESTONE (optional: change or delete)
/- SKELETON · derivable_wp_while   (milestone 3: needs milestones 1, 2; used in wp_derivable)
  The loop invariant is `I := wp (.while b c) Q` itself. One term, from the outside in:
  1. Rule of consequence around the `while` rule: precondition unchanged, and the
     postcondition `I s ∧ beval s b = false → Q s` is milestone 2, partially applied  R4, R5
  2. The `while` rule: its conclusion's postcondition is fixed, `I s ∧ beval s b = false`  R6
  3. Its premise, the body: rule of consequence around `ih _` (Lean infers the
     assertion `I`; `ih (wp (.while b c) Q)` also works); the precondition
     `I s ∧ beval s b = true → wp c I s` is milestone 1, the postcondition `fun _ h => h`  R4, R5
-/
theorem derivable_wp_while (b : BExp) (c : Com) (Q : Assn)
    (ih : ∀ R, Derivable (wp c R) c R) : Derivable (wp (.while b c) Q) (.while b c) Q := by
  -- WHY: the loop invariant is `wp (.while b c) Q` itself.
  exact .conseq (fun _ h => h)
    (.while (.conseq (wp_while_body b c Q) (ih _) (fun _ h => h))) (wp_while_exit b c Q)

/- SKELETON · wp_seq
  1. Equality of assertions → pointwise equality → ↔ → two implications      R7 → R8 → R9
  2. (→) Introduce `h`, then the runs of `c1` and `c2` (through two `wp`s)    R1
     Apply `h` to the final state and a `seq` run built from the two runs     R2, R3
  3. (←) Introduce `h`, the final state and a run of `.seq c1 c2`             R1
     Invert the run: one case, `seq`, with an inaccessible middle state      R10
     Apply `h` to the middle state (`_`), the first run, the final state,
     and the second run                                                       R2
-/
-- BEGIN SPEC
theorem wp_seq (c1 c2 : Com) (Q : Assn) : wp (.seq c1 c2) Q = wp c1 (wp c2 Q) :=
-- END SPEC
  by
    funext s
    apply propext
    constructor
    · intro h s' h1 s'' h2
      exact h s'' (.seq h1 h2)
    · intro h s'' hc
      cases hc with
      | seq h1 h2 => exact h _ h1 _ h2

/- SKELETON · wp_while   (uses milestones 1 and 2)
  1. As in wp_seq: pointwise, ↔, two implications                           R7 → R8 → R9
  2. (→) Introduce `h`; the goal is a conjunction of two implications: build it with
     an anonymous constructor `⟨fun hb => …, fun hb => …⟩`, milestone 1 and
     milestone 2 fully applied, each given `⟨h, hb⟩`
  3. (←) Destructure the pair, then introduce the final state and the loop run   R11, R1
     Invert the loop run: two cases, `whileF` and `whileT`                   R12
     whileF: the final state became `s`; use the second component
     whileT: use the first component, applied to `hb` and then like a `wp`    R2
-/
-- BEGIN SPEC
theorem wp_while (b : BExp) (c : Com) (Q : Assn) :
    wp (.while b c) Q =
      fun s => (beval s b = true → wp c (wp (.while b c) Q) s) ∧ (beval s b = false → Q s) :=
-- END SPEC
  by
    funext s
    apply propext
    constructor
    · intro h
      exact ⟨fun hb => wp_while_body b c Q s ⟨h, hb⟩, fun hb => wp_while_exit b c Q s ⟨h, hb⟩⟩
    · intro ⟨h1, h2⟩ s' hw
      cases hw with
      | whileF hb => exact h2 hb
      | whileT hb hc hw => exact h1 hb _ hc _ hw

/- SKELETON · wp_derivable   (uses milestone 3)
  1. Induction on `c`, generalizing `Q`: the `seq` case needs the IH of `c1` at
     the postcondition `wp c2 Q`, not at `Q`. The loop case is named `«while»`     R13
  2. skip, assign: rule of consequence around the axiom `.skip` / `.assign`, with
     precondition side `fun s h => h _ <one-step run>`                         R4, R2, R3
  3. seq: rule of consequence around `.seq (ih1 _) (ih2 Q)`; precondition side:
     take the runs of `c1` and `c2` and rebuild a `seq` run                    R4, R1, R2, R3
  4. ite: the `ite` rule, each branch a consequence around `ih1 Q` / `ih2 Q` with
     the precondition side left as `?_`                                      R14
     Each side goal: destructure `wp … s ∧ beval s b = …`, then `iteT` / `iteF`   R11, R1, R2, R3
  5. «while»: milestone 3 applied to the IH
-/
-- BEGIN SPEC
theorem wp_derivable (c : Com) (Q : Assn) : Derivable (wp c Q) c Q :=
-- END SPEC
  by
    induction c generalizing Q with
    | skip => exact .conseq (fun s h => h s .skip) .skip (fun _ h => h)
    | assign x a => exact .conseq (fun s h => h _ .assign) .assign (fun _ h => h)
    | seq c1 c2 ih1 ih2 =>
      exact .conseq (fun s h s1 h1 s2 h2 => h s2 (.seq h1 h2)) (.seq (ih1 _) (ih2 Q)) (fun _ h => h)
    | ite b c1 c2 ih1 ih2 =>
      refine .ite (.conseq ?_ (ih1 Q) (fun _ h => h)) (.conseq ?_ (ih2 Q) (fun _ h => h))
      · intro s ⟨h, hb⟩ s' h'; exact h s' (.iteT hb h')
      · intro s ⟨h, hb⟩ s' h'; exact h s' (.iteF hb h')
    | «while» b c ih => exact derivable_wp_while b c Q ih

/- SKELETON · completeness   (uses wp_derivable)
  1. Rule of consequence around `wp_derivable c Q`                          R4
  2. Precondition side `∀ s, P s → wp c Q s`: take `s`, `hP`, then unfold `wp`
     (R1); `h : Valid P c Q` is a function too                               R2
  3. Postcondition side: `fun _ h => h`
-/
-- BEGIN SPEC
theorem completeness {P Q : Assn} {c : Com} (h : Valid P c Q) : Derivable P c Q :=
-- END SPEC
  .conseq (fun s hP s' hc => h s s' hP hc) (wp_derivable c Q) (fun _ h => h)

end H024

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `wp c Q s` is by definition `∀ s', BigStep c s s' → Q s'`: `intro` unfolds it, and a hypothesis
    `h : wp c Q s` is a function you apply to a state and a run (R1, R2). Equalities of assertions:
    `funext s; apply propext; constructor`; build runs with the `BigStep` rules one way and invert
    them with `cases` the other way. Completeness is one `.conseq` away from `wp_derivable`.
H2. `wp_derivable`: `induction c generalizing Q`. Each case applies the matching Hoare rule to the IHs
    and fixes the precondition with `.conseq`; the `«while»` case is `derivable_wp_while`, whose loop
    invariant is `wp (.while b c) Q` itself and whose two side conditions are the milestones
    `wp_while_body` and `wp_while_exit`.
H3. `derivable_wp_while` has the shape
    `.conseq _ (.while (.conseq (wp_while_body b c Q) (ih _) _)) (wp_while_exit b c Q)`; the two `_`
    that are proofs are `fun _ h => h`, the one in `ih _` is the assertion and is inferred. Completeness: `.conseq _ (wp_derivable c Q) (fun _ h => h)`, where the first `_`
    proves `∀ s, P s → wp c Q s` from `h` (`Valid` unfolded).
-/
