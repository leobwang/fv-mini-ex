/- H024 | Hoare logic: weakest preconditions and relative completeness | 40-60 min | Hoare logic, weakest liberal precondition, fixpoint equation, relative completeness, induction on commands
GOAL
  `wp c Q` holds in the states from which every terminating run of `c` ends in `Q`. Prove it
  distributes over `;`, satisfies the one-step unfolding equation of `while`, and is derivable as a
  precondition; conclude that every valid Hoare triple is derivable (relative completeness).

REFERENCE
  -- `Valid P c Q` is the meaning of `{P} c {Q}`; `Derivable P c Q` is provability in Hoare logic.
  example (f g : Nat → Prop) (h : ∀ n, f n ↔ g n) : f = g := funext fun n => propext (h n)
  -- Inversion: `cases hc with | seq h1 h2 => ...` on `hc : BigStep (.seq c1 c2) s s''`;
  -- `cases hw with | whileF hb => ... | whileT hb hc hw => ...` for a `while` run.
  -- Rule of consequence: `.conseq pre d post` strengthens the precondition / weakens the postcondition of `d`.
  example (P : H024.Assn) : H024.Derivable (fun s => P s ∧ True) .skip P := .conseq (fun _ h => h.1) .skip (fun _ h => h)
  -- `induction c generalizing Q with ...`: `while` is a keyword, so its case is `| «while» b c ih =>`.
NOTE: Soundness of these rules is M045; here you prove the converse direction.
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
theorem wp_while_body (b : BExp) (c : Com) (Q : Assn) (s : State)
    (h : wp (.while b c) Q s ∧ beval s b = true) : wp c (wp (.while b c) Q) s := by
  intro s1 h1 s2 h2
  exact h.1 s2 (.whileT h.2 h1 h2)

-- MILESTONE (optional: change or delete)
theorem wp_while_exit (b : BExp) (c : Com) (Q : Assn) (s : State)
    (h : wp (.while b c) Q s ∧ beval s b = false) : Q s := by
  exact h.1 s (.whileF h.2)

-- MILESTONE (optional: change or delete)
theorem derivable_wp_while (b : BExp) (c : Com) (Q : Assn)
    (ih : ∀ R, Derivable (wp c R) c R) : Derivable (wp (.while b c) Q) (.while b c) Q := by
  -- WHY: the loop invariant is `wp (.while b c) Q` itself.
  exact .conseq (fun _ h => h)
    (.while (.conseq (wp_while_body b c Q) (ih _) (fun _ h => h))) (wp_while_exit b c Q)

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

-- BEGIN SPEC
theorem completeness {P Q : Assn} {c : Com} (h : Valid P c Q) : Derivable P c Q :=
-- END SPEC
  .conseq (fun s hP s' hc => h s s' hP hc) (wp_derivable c Q) (fun _ h => h)

end H024

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Equalities of assertions: `funext s; apply propext; constructor`, then build runs with the `BigStep` rules one way and invert them with `cases` the other way. Completeness is one `conseq` away from `wp_derivable`.
H2. `wp_derivable`: induction on `c` generalizing `Q`. Each case applies the matching Hoare rule to the IHs and fixes the precondition with `conseq`; the `while` case is `derivable_wp_while`, whose loop invariant is `wp (.while b c) Q` itself.
H3. `derivable_wp_while` has the shape `.conseq _ (.while (.conseq (wp_while_body b c Q) (ih _) _)) (wp_while_exit b c Q)`. Completeness: `.conseq _ (wp_derivable c Q) _`, where the precondition side is `Valid` unfolded.
-/
