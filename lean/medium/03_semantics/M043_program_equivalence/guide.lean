/- Guide for M043 (Program equivalence in IMP).
Part R: one reference entry per tactic or proof move the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `f` or `h` in an entry is only there to finish the example; it shows what the goal became.
The inversion entries need a concrete inductive relation, so they use the toy language `Cmd`/`Run`
below (a counter machine), NOT the exercise's IMP.
Part W: worked combinations on `Cmd`/`Run`.
Assumed: Lean basics (E001–E033). No Mathlib.
-/

namespace M043Guide

/-! # The toy language used by the entries

A guard `Test` evaluates to a `Bool` in the current counter value `n : Nat`. A command `Cmd` either
does nothing, increments the counter, runs two commands in sequence, or loops while a guard holds.
`Run c n k` means: started with counter `n`, command `c` terminates with counter `k`. -/

inductive Test where
  | yes
  | no
  | below (k : Nat)

def test (n : Nat) : Test → Bool
  | .yes => true
  | .no => false
  | .below k => decide (n < k)

inductive Cmd where
  | nop
  | inc
  | seq (c d : Cmd)
  | loop (t : Test) (c : Cmd)

inductive Run : Cmd → Nat → Nat → Prop
  | nop {n : Nat} : Run .nop n n
  | inc {n : Nat} : Run .inc n (n + 1)
  | seq {c d : Cmd} {n m k : Nat} : Run c n m → Run d m k → Run (.seq c d) n k
  | loopF {t : Test} {c : Cmd} {n : Nat} : test n t = false → Run (.loop t c) n n
  | loopT {t : Test} {c : Cmd} {n m k : Nat} :
      test n t = true → Run c n m → Run (.loop t c) m k → Run (.loop t c) n k

/-! # Part R · Reference entries -/

/-! ## Opening an equivalence goal -/

/-- A definition whose body is a `∀`, used by R1. -/
def AllPairs {α : Type} (Q : α → α → Prop) : Prop := ∀ a b, Q a b

/-! ### R1. `intro a b` on a defined name · context gains `a b`; goal is the body of the definition
`intro` unfolds a definition by itself when its body starts with `∀`; no `unfold` is needed. -/
example {α : Type} (Q : α → α → Prop) (h : ∀ a b, Q a b) : AllPairs Q := by
  intro a b
  exact h a b

/-! ### R2. `constructor` on `↔` · goal list: `A ↔ B` → `A → B` and `B → A`
The two goals are tagged `mp` (left to right) and `mpr` (right to left). -/
example (A B : Prop) (f : A → B) (g : B → A) : A ↔ B := by
  constructor
  exact f
  exact g

/-! ## Inverting a derivation (`cases` on a hypothesis of an inductive relation) -/

/-! ### R3. `cases h with | seq h1 h2 => …` · context: `h` → the premises of the one rule that fits
Only `Run.seq` concludes `Run (.seq c d) n k`, so there is one case. Its premises get the names you
write; the intermediate counter is implicit in the rule and appears as `m✝` (write `| @seq _ _ _ m _ h1 h2`
to name it too). `?_` leaves the case open for the next tactic; in a proof write the tactics there. -/
example (c d : Cmd) (n k : Nat) (P : Nat → Nat → Prop) (f : ∀ m, Run c n m → Run d m k → P n k)
    (h : Run (.seq c d) n k) : P n k := by
  cases h with
    | seq h1 h2 => ?_
  exact f _ h1 h2

/-! ### R4. `cases h` on a rule without premises · context loses `h`; goal: the index is substituted
`Run.nop` concludes `Run .nop n n`, so `h : Run .nop n k` forces `k = n`: `cases` replaces `k` by `n`. -/
example (n k : Nat) (P : Nat → Nat → Prop) (hp : P n n) (h : Run .nop n k) : P n k := by
  cases h
  exact hp

/-! ### R5. `cases h with | loopF hb => … | loopT hb hc hw => …` · goal list: one goal per rule that fits
Two rules conclude `Run (.loop t c) n k`, so there are two goals. In `loopF` the end counter is the
start counter, so `k` becomes `n`. Write `_` for a premise you do not need. -/
example (t : Test) (c : Cmd) (n k : Nat) (P : Nat → Nat → Prop) (f : test n t = false → P n n)
    (g : ∀ m, test n t = true → Run c n m → Run (.loop t c) m k → P n k)
    (h : Run (.loop t c) n k) : P n k := by
  cases h with
    | loopF hb => ?_
    | loopT hb hc hw => ?_
  exact f hb
  exact g _ hb hc hw

/-! ## Building a derivation -/

/-! ### R6. `exact .seq h1 h2` · closes the goal with a rule applied to derivations of its premises
`.seq` means `Run.seq`: Lean reads the namespace off the goal `Run …`. The rule's implicit arguments
(`c d n m k`) are found by matching its conclusion with the goal and the premises with `h1`, `h2`.
Rules nest: `.seq h1 (.seq h2 h3)`; a rule without premises is just `.nop`. -/
example (c d : Cmd) (n m k : Nat) (h1 : Run c n m) (h2 : Run d m k) : Run (.seq c d) n k := by
  exact .seq h1 h2

/-! ## Using an `↔` hypothesis -/

/-! ### R7. `Iff.mp`: `(h a b).mp : Q a b → R a b` · goal `R a b` → `Q a b` (with `apply`)
`h a b` instantiates the `∀`; `_ _` lets Lean find `a b` from the goal. In a term write
`(h _ _).mp hq` directly. -/
example {α : Type} (Q R : α → α → Prop) (a b : α) (h : ∀ x y, Q x y ↔ R x y) (hq : Q a b) :
    R a b := by
  apply (h _ _).mp
  exact hq

/-! ### R8. `Iff.mpr`: `(h a b).mpr : R a b → Q a b` · goal `Q a b` → `R a b` (with `apply`) -/
example {α : Type} (Q R : α → α → Prop) (a b : α) (h : ∀ x y, Q x y ↔ R x y) (hr : R a b) :
    Q a b := by
  apply (h _ _).mpr
  exact hr

/-! ## Impossible cases and computed premises -/

/-! ### R9. `simp [f] at hb` · closes the goal when `hb` simplifies to `False`
`simp [test] at hb` unfolds `test` on the constructor `.no`: `hb : test n .no = true` becomes
`false = true`, which is `False`, and a goal with a `False` hypothesis is closed. -/
example (n : Nat) (P : Prop) (hb : test n .no = true) : P := by
  simp [test] at hb

/-! ### R10. `rfl` for a premise that computes · closes `test n .no = false`
`test n .no` reduces to `false` by its defining equation, so both sides are the same. As a rule
premise: `.loopF rfl`. -/
example (n : Nat) : test n .no = false := rfl

/-! # Part W · Worked combinations (on `Cmd`/`Run`, not the exercise's IMP) -/

/-! ### W1. Concrete runs: rules nest, `rfl` fills computed premises (R6, R10) -/
example : Run (.seq .inc .inc) 0 2 := .seq .inc .inc
example : Run (.loop .no .inc) 5 5 := .loopF rfl

/-! ### W2. `c; nop` runs exactly like `c`: R1, R2, then R3 → R4 one way, R6 the other -/
example (c : Cmd) : ∀ n k, Run (.seq c .nop) n k ↔ Run c n k := by
  intro n k
  constructor
  · intro h
    cases h with
    | seq hc hn => cases hn; exact hc
  · intro h
    exact .seq h .nop

/-! ### W3. A loop whose guard is false at 0 never runs its body: R5, then R9 on the impossible case -/
example (c : Cmd) (n k : Nat) (h : Run (.loop (.below 0) c) n k) : k = n := by
  cases h with
    | loopF _ => rfl
    | loopT hb _ _ => simp [test] at hb

end M043Guide
