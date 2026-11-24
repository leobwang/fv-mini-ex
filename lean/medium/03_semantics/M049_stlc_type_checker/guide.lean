/- Guide for M049 (A type checker for STLC).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `Q`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis such as `hp` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on a toy tree type `Tr` and a toy checker `lv` that are NOT the exercise's.
Assumed: Lean basics (E001–E033). Core Lean only, no Mathlib.
-/

namespace M049Guide

/-! ## Toy objects used by some entries (not the exercise's) -/

/-- A toy tree, shaped like a term: a leaf holds an index into a context, `tag k t` pushes `k`
onto the context for its subtree (like a binder), `node l r` has two subtrees. -/
inductive Tr where
  | leaf (n : Nat)
  | tag (k : Nat) (t : Tr)
  | node (l r : Tr)

/-- A toy relation on trees: `Lv xs t d` ("`t` has level `d` in the context `xs`"). -/
inductive Lv : List Nat → Tr → Nat → Prop
  | leaf {xs : List Nat} {n d : Nat} : xs[n]? = some d → Lv xs (.leaf n) d
  | tag {xs : List Nat} {k d : Nat} {t : Tr} : Lv (k :: xs) t d → Lv xs (.tag k t) (k + d)

/-- The same relation as a function (a toy checker). `node` is always rejected. -/
def lv : List Nat → Tr → Option Nat
  | xs, .leaf n => xs[n]?
  | xs, .tag k t =>
    match lv (k :: xs) t with
    | some d => some (k + d)
    | none => none
  | _, .node _ _ => none

/-! # Part R · Reference entries -/

/-! ## Induction on the term -/

/-! ### R1. `induction t generalizing xs with | leaf n => … | tag k t ih => … | node l r ihl ihr => …`
· goal list: one goal per constructor, one IH per recursive argument
`generalizing xs` first puts `xs` back under `∀`, so each IH holds for EVERY context, not only
the `xs` in the context. `leaf n` has no subtree, so no IH; `node l r` has two. -/
example (P : List Nat → Tr → Prop) (hl : ∀ xs n, P xs (.leaf n))
    (ht : ∀ k t, (∀ xs, P xs t) → ∀ xs, P xs (.tag k t))
    (hn : ∀ l r, (∀ xs, P xs l) → (∀ xs, P xs r) → ∀ xs, P xs (.node l r))
    (xs : List Nat) (t : Tr) : P xs t := by
  induction t generalizing xs with
    | leaf n => exact hl xs n
    | tag k t ih => exact ht k t ih xs
    | node l r ihl ihr => exact hn l r ihl ihr xs

/-! R1, one goal at a time: without `with` the new names are inaccessible (`n✝`, `a_ih✝`);
`rename_i` names them as the `with` patterns would. -/
example (P : List Nat → Tr → Prop) (hl : ∀ xs n, P xs (.leaf n))
    (ht : ∀ k t, (∀ xs, P xs t) → ∀ xs, P xs (.tag k t))
    (hn : ∀ l r, (∀ xs, P xs l) → (∀ xs, P xs r) → ∀ xs, P xs (.node l r))
    (xs : List Nat) (t : Tr) : P xs t := by
  induction t generalizing xs
  · exact hl _ _
  · rename_i k t ih
    exact ht k t ih xs
  · rename_i l r ihl ihr
    exact hn l r ihl ihr xs

/-! ### R2. `exact .ctor args` · closes the goal with a constructor of the goal's inductive type
`.leaf` means `Lv.leaf`: Lean reads the namespace off the goal `Lv …`. `h` is accepted although its
type says `lv xs (Tr.leaf n)`, not `xs[n]?`: the first equation of `lv` holds by definition. -/
example (xs : List Nat) (n d : Nat) (h : lv xs (.leaf n) = some d) : Lv xs (.leaf n) d := by
  exact .leaf h

/-! ## Reading off what the checker did -/

/-! ### R3. `simp only [f] at h` · context: `h` with one defining equation of `f` applied
It fires when the arguments of `f` match a pattern of its definition (here `.leaf n`). -/
example (xs : List Nat) (n d : Nat) (Q : Prop) (hq : xs[n]? = some d → Q)
    (h : lv xs (.leaf n) = some d) : Q := by
  simp only [lv] at h
  exact hq h

/-! ### R4. `split at h` on a `match` · goal list: one goal per branch, the branch fact in the context
In the `some` branch the matched value is a new inaccessible variable `y✝`, and `heq✝` records
`f a = some y✝`; in the `none` branch `heq✝ : f a = none`. -/
example {α β γ : Type} (f : α → Option β) (g : β → γ) (a : α) (z : γ) (Q : Prop)
    (h1 : ∀ y, f a = some y → some (g y) = some z → Q) (h2 : none = some z → Q)
    (h : (match f a with | some y => some (g y) | none => none) = some z) : Q := by
  split at h
  · exact h1 _ ‹_› h
  · exact h2 h

/-! ### R5. `cases h` on `h : some x = some y`, `y` a variable · context and goal: `h` is gone and
`y` is replaced by `x` everywhere (`some` is injective, so `cases` solves the equation) -/
example {α : Type} (x y : α) (P : α → Prop) (hp : P x) (h : some x = some y) : P y := by
  cases h
  exact hp

/-! ### R6. `‹T›` · a term: "the hypothesis of type `T`", also when its name is inaccessible (`h✝`)
`‹_›` lets Lean infer `T` from where the term is used. -/
example (A B : Prop) (f : A → B) : A → B := by
  intro _
  exact f ‹_›

/-! ### R7. `ih h` · apply a generalized IH whose binders are implicit `{…}`
The IH inherits the binder kind of the generalized variables: from `{xs : List Nat} {d : Nat}` you
get `ih : ∀ {xs : List Nat} {d : Nat}, …`, so you pass only the hypothesis; `xs`, `d` are unified. -/
example (R S : List Nat → Nat → Prop) (ih : ∀ {xs : List Nat} {d : Nat}, R xs d → S xs d)
    (ys : List Nat) (e : Nat) (h : R ys e) : S ys e := by
  exact ih h

/-! ### R8. `simp at h` · goal list: closes the goal when `h` is `none = some a`
Different constructors are never equal, so `h` simplifies to `False`, and a `False` hypothesis
proves anything. -/
example {α : Type} (a : α) (Q : Prop) (h : (none : Option α) = some a) : Q := by
  simp at h

/-! ### R9. `split at h` on a `match` with two scrutinees · goal list: the matching branch, and a
catch-all branch whose context says "the first pattern did not match" -/
example {α β : Type} (f g : α → Option β) (k : β → β → Option β) (a : α) (z : β) (Q : Prop)
    (h1 : ∀ x y, f a = some x → g a = some y → k x y = some z → Q)
    (h : (match f a, g a with | some x, some y => k x y | _, _ => none) = some z) : Q := by
  split at h
  · exact h1 _ _ ‹_› ‹_› h
  · simp at h

/-! ### R10. `split at h` on an `if` · goal list: two goals, with `h✝ : c` and `h✝ : ¬c`
`if a = b` needs `[DecidableEq α]`: Lean must be able to compute whether `a = b`. -/
example {α β : Type} [DecidableEq α] (a b : α) (t : Option β) (z : β) (Q : Prop)
    (h1 : a = b → t = some z → Q) (h : (if a = b then t else none) = some z) : Q := by
  split at h
  · exact h1 ‹_› h
  · simp at h

/-! ### R11. `subst_vars` · context and goal: every hypothesis `x = e` or `e = x` with `x` a local
variable is used to replace `x` everywhere, then deleted -/
example {α : Type} (a b c : α) (P : α → α → α → Prop) (hp : ∀ x, P x x x) (h1 : a = b)
    (h2 : b = c) : P a b c := by
  subst_vars
  exact hp _

/-! ## Induction on the derivation -/

/-! ### R12. `induction h with | leaf hn => … | tag hd ih => …` · goal list: one goal per rule
of the relation, one IH per premise that is itself a derivation. The pattern names only the
rule's explicit premises; its `{…}` arguments appear as `xs✝`, `d✝`. -/
example (Q : List Nat → Tr → Nat → Prop)
    (hl : ∀ {xs : List Nat} {n d : Nat}, xs[n]? = some d → Q xs (.leaf n) d)
    (ht : ∀ {xs : List Nat} {k d : Nat} {t : Tr}, Q (k :: xs) t d → Q xs (.tag k t) (k + d))
    (xs : List Nat) (t : Tr) (d : Nat) (h : Lv xs t d) : Q xs t d := by
  induction h with
    | leaf hn => exact hl hn
    | tag _ ih => exact ht ih

/-! R12, one goal at a time. -/
example (Q : List Nat → Tr → Nat → Prop)
    (hl : ∀ {xs : List Nat} {n d : Nat}, xs[n]? = some d → Q xs (.leaf n) d)
    (ht : ∀ {xs : List Nat} {k d : Nat} {t : Tr}, Q (k :: xs) t d → Q xs (.tag k t) (k + d))
    (xs : List Nat) (t : Tr) (d : Nat) (h : Lv xs t d) : Q xs t d := by
  induction h
  · rename_i hn
    exact hl hn
  · rename_i ih
    exact ht ih

/-! ### R13. `simpa [f] using h` · closes the goal when goal and `h` simplify to the same statement -/
example (xs : List Nat) (n d : Nat) (hn : xs[n]? = some d) : lv xs (.leaf n) = some d := by
  simpa [lv] using hn

/-! ### R14. `simp [ih]` through a `match` · closes the goal: `ih : f a = some b` turns the
scrutinee into `some b`, and `simp` then picks the `some` branch -/
example {α β γ : Type} (f : α → Option β) (k : β → Option γ) (a : α) (b : β) (c : γ)
    (ih : f a = some b) (hk : k b = some c) :
    (match f a with | some y => k y | none => none) = some c := by
  simp [ih, hk]

/-! ### R15. `simp` on `if a = a then t else e` · goal: the `if` → its `then` branch -/
example {α β : Type} [DecidableEq α] (a : α) (t e : β) (P : β → Prop) (hp : P t) :
    P (if a = a then t else e) := by
  simp
  exact hp

/-! ## Uniqueness: from two `some` equations to one equation -/

/-! ### R16. `rw [e] at h` · context: `h` rewritten with the equation `e` -/
example {α : Type} (o : Option α) (a b : α) (Q : Prop) (hq : some b = some a → Q)
    (e : o = some b) (h : o = some a) : Q := by
  rw [e] at h
  exact hq h

/-! ### R17. `Option.some.inj` · `some a = some b → a = b` · a term; closes `a = b` -/
example {α : Type} (a b : α) (h : some a = some b) : a = b := by
  exact Option.some.inj h

/-! ### R18. `h.symm` (`Eq.symm`) · `a = b → b = a` · a term; closes `b = a` -/
example {α : Type} (a b : α) (h : a = b) : b = a := by
  exact h.symm

/-! # Part W · Worked combinations on `Tr`, `Lv`, `lv` (not the exercise's objects) -/

/-! ### W1. Soundness of `lv`: R1, R2 (`leaf`); R3, R4, R5, R2, R7, R6, R8 (`tag`); R3 + R8 (`node`) -/
example {xs : List Nat} {t : Tr} {d : Nat} (h : lv xs t = some d) : Lv xs t d := by
  induction t generalizing xs d with
    | leaf n => exact .leaf h
    | tag k t ih =>
      simp only [lv] at h
      split at h
      · cases h
        exact .tag (ih ‹_›)
      · simp at h
    | node l r => simp [lv] at h

/-! ### W2. Completeness of `lv`: R12, R13 (`leaf`), R14 (`tag`) -/
example {xs : List Nat} {t : Tr} {d : Nat} (h : Lv xs t d) : lv xs t = some d := by
  induction h with
    | leaf hn => simpa [lv] using hn
    | tag _ ih => simp [lv, ih]

end M049Guide
