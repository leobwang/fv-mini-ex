/- H008 | Proof by reflection: a commutative-monoid normaliser | 45-75 min | reflection, decide, syntax vs semantics, List.Perm, type classes with laws
GOAL
  Prove equations in any commutative monoid by computation: write terms as syntax (`Expr`), normalise
  syntax to the sorted list of its atoms, and prove `norm e1 = norm e2 → e1.denote ρ = e2.denote ρ`.
  Then `decide` (the kernel computing two normal forms) replaces a chain of rewrites.

REFERENCE
  -- `l1.Perm l2`: l2 is a reordering of l1. Its constructors are `nil`, `cons`, `swap`, `trans`:
  #check @List.Perm.cons    -- (x : α) : l₁.Perm l₂ → (x :: l₁).Perm (x :: l₂)    (write `h.cons x`)
  #check @List.Perm.swap    -- (x y : α) (l : List α) : (y :: x :: l).Perm (x :: y :: l)
  #check @List.Perm.trans   -- l₁.Perm l₂ → l₂.Perm l₃ → l₁.Perm l₃           (and `.refl l`)
  -- `induction h with | nil => _ | cons x _ ih => _ | swap x y l => _ | trans _ _ ih1 ih2 => _`
  example : H008.norm (.op (.atom 1) (.atom 0)) = H008.norm (.op (.atom 0) (.atom 1)) := by decide
  #check @congrArg          -- (f : α → β) : a₁ = a₂ → f a₁ = f a₂
  -- `split` on a goal containing `if i ≤ j then … else …` makes one goal per branch
  -- the laws are terms: `CMon.op_comm a b : op a b = op b a`; `ρ : Nat → α` gives atom i the value ρ i
BANNED: ac_rfl, ac_nf, Associative, Commutative, grind, import, exact?, apply?, try?
NOTE: No imports, no `grind`, no search tactics (`exact?`, `apply?`, `try?`). `demo` is the payoff
  the GOAL advertises: prove it with `reflect` and `by decide`, not with a chain of rewrites.
-/

namespace H008

-- BEGIN SPEC
/-- A commutative monoid (self-contained: core Lean has no such class). -/
class CMon (α : Type) where
  op : α → α → α
  unit : α
  op_assoc : ∀ a b c : α, op (op a b) c = op a (op b c)
  op_comm : ∀ a b : α, op a b = op b a
  unit_op : ∀ a : α, op unit a = a

/-- Syntax of monoid expressions over atoms `0, 1, 2, …`. -/
inductive Expr where
  | atom (i : Nat)
  | unit
  | op (a b : Expr)

/-- Meaning of a syntax tree, given a value `ρ i` for each atom `i`. -/
def Expr.denote {α : Type} [CMon α] (ρ : Nat → α) : Expr → α
  | .atom i => ρ i
  | .unit => CMon.unit
  | .op a b => CMon.op (a.denote ρ) (b.denote ρ)

def Expr.atoms : Expr → List Nat
  | .atom i => [i]
  | .unit => []
  | .op a b => a.atoms ++ b.atoms

/-- Meaning of a list of atoms: their product, `ρ i₁ · (ρ i₂ · (… · unit))`. -/
def denoteList {α : Type} [CMon α] (ρ : Nat → α) : List Nat → α
  | [] => CMon.unit
  | i :: is => CMon.op (ρ i) (denoteList ρ is)

def insertSorted (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: js => if i ≤ j then i :: j :: js else j :: insertSorted i js

def sortList : List Nat → List Nat
  | [] => []
  | i :: is => insertSorted i (sortList is)

/-- The normal form: the sorted list of atoms. -/
def norm (e : Expr) : List Nat := sortList e.atoms
-- END SPEC

open CMon

-- MILESTONE (optional: change or delete)
theorem denoteList_append {α : Type} [CMon α] (ρ : Nat → α) (l1 l2 : List Nat) :
    denoteList ρ (l1 ++ l2) = op (denoteList ρ l1) (denoteList ρ l2) := by
  induction l1 with
  | nil => simp [denoteList, unit_op]
  | cons i is ih => simp [denoteList, ih, op_assoc]

-- MILESTONE (optional: change or delete)
theorem denote_atoms {α : Type} [CMon α] (ρ : Nat → α) (e : Expr) :
    denoteList ρ e.atoms = e.denote ρ := by
  induction e with
  | atom i => simp [Expr.atoms, denoteList, Expr.denote, op_comm _ (unit : α), unit_op]
  | unit => rfl
  | op a b iha ihb => simp [Expr.atoms, denoteList_append, iha, ihb, Expr.denote]

-- MILESTONE (optional: change or delete)
theorem denoteList_perm {α : Type} [CMon α] (ρ : Nat → α) {l1 l2 : List Nat} (h : l1.Perm l2) :
    denoteList ρ l1 = denoteList ρ l2 := by
  have op_left_comm : ∀ a b c : α, op a (op b c) = op b (op a c) := by
    intro a b c
    rw [← op_assoc, op_comm a b, op_assoc]
  induction h with
  | nil => rfl
  | cons x _ ih => simp [denoteList, ih]
  | swap x y l => simp [denoteList, op_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

-- MILESTONE (optional: change or delete)
theorem sortList_perm (l : List Nat) : (sortList l).Perm l := by
  have insertSorted_perm : ∀ (i : Nat) (l : List Nat), (insertSorted i l).Perm (i :: l) := by
    intro i l
    induction l with
    | nil => exact .refl _
    | cons j js ih =>
      simp only [insertSorted]
      split
      · exact .refl _
      · exact (ih.cons j).trans (.swap i j js)
  induction l with
  | nil => exact .refl _
  | cons i is ih => exact (insertSorted_perm i _).trans (ih.cons i)

-- BEGIN SPEC
theorem reflect {α : Type} [CMon α] (e1 e2 : Expr) (h : norm e1 = norm e2) (ρ : Nat → α) :
    e1.denote ρ = e2.denote ρ :=
-- END SPEC
  by
    rw [← denote_atoms, ← denote_atoms, ← denoteList_perm ρ (sortList_perm e1.atoms),
      ← denoteList_perm ρ (sortList_perm e2.atoms)]
    exact congrArg (denoteList ρ) h

-- MILESTONE (optional: change or delete)
-- The payoff: prove this with `reflect`, two syntax trees, `by decide` and a suitable `ρ`.
theorem demo {α : Type} [CMon α] (a b c d : α) :
    op (op a b) (op c (op d unit)) = op d (op (op c a) b) := by
  -- WHY: `denote` of these trees with this `ρ` is definitionally each side of the goal, so the
  -- only real check is `norm lhs = norm rhs`, which `decide` evaluates.
  exact reflect (.op (.op (.atom 0) (.atom 1)) (.op (.atom 2) (.op (.atom 3) .unit)))
    (.op (.atom 3) (.op (.op (.atom 2) (.atom 0)) (.atom 1))) (by decide)
    (fun i => [a, b, c, d].getD i unit)

end H008

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Go through lists: `e.denote ρ = denoteList ρ e.atoms`, sorting only permutes the list, and
    `denoteList` cannot see the order of its list because `op` is associative and commutative.
H2. Induction on `l1` for `denoteList_append` (uses `unit_op`, `op_assoc`); on `e` for `denote_atoms`
    (atom case: `op x unit = x` from `op_comm` and `unit_op`); on the `Perm` derivation for
    `denoteList_perm` (swap case: `op a (op b c) = op b (op a c)`); `insertSorted i l ~ i :: l` by induction.
H3. `reflect`: `rw [← denote_atoms, ← denote_atoms, ← denoteList_perm ρ (sortList_perm e1.atoms),
    ← denoteList_perm ρ (sortList_perm e2.atoms)]; exact congrArg (denoteList ρ) h`.
    `demo`: `reflect (.op (.op (.atom 0) (.atom 1)) …) (.op (.atom 3) …) (by decide) (fun i => [a, b, c, d].getD i unit)`.
-/
