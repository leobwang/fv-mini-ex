/- H008 | Proof by reflection: a commutative-monoid normaliser | 45-75 min | reflection, decide, syntax vs semantics, List.Perm, type classes with laws
GOAL
  Prove equations in any commutative monoid by computation: write terms as syntax (`Expr`), normalise
  syntax to the sorted list of its atoms, and prove `norm e1 = norm e2 → e1.denote ρ = e2.denote ρ`.
  Then `decide` (the kernel computing two normal forms) replaces a chain of rewrites.
BANNED: ac_rfl, ac_nf, Associative, Commutative, grind, import, exact?, apply?, try?

GUIDE
  Entries R1–R21: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · denoteList_append   (milestone 1; used in denote_atoms, case `op`)
  1. Induction on `l1`: goals `nil` and `cons i is ih`.                         R1
  2. nil: `[] ++ l2` → `l2`; unfold `denoteList ρ []` → `unit`; the law `unit_op`. R3, R2, R4
  3. cons: `i :: is ++ l2` is `(i :: is) ++ l2`: move `i` out first, then
     unfold `denoteList` on both conses, rewrite with `ih`, regroup with the
     law `op_assoc`.                                                             R3, R2, R5, R4
     (One `simp` given the definition, `ih` and the law performs all of step 3.)
-/
-- MILESTONE (optional: change or delete)
theorem denoteList_append {α : Type} [CMon α] (ρ : Nat → α) (l1 l2 : List Nat) :
    denoteList ρ (l1 ++ l2) = op (denoteList ρ l1) (denoteList ρ l2) := by
  induction l1 with
  | nil => simp [denoteList, unit_op]
  | cons i is ih => simp [denoteList, ih, op_assoc]

/- SKELETON · denote_atoms   (milestone 2; used in reflect, step 1)
  1. Induction on `e`: goals `atom i`, `unit`, `op a b iha ihb`.                 R6
  2. atom: unfold `Expr.atoms`, `denoteList`, `Expr.denote`; the left side is
     `op (ρ i) unit`. Swap it with `op_comm` fixed at `(unit : α)`, then `unit_op`. R2, R7, R4
  3. unit: both sides compute to `unit`.                                         rfl
  4. op: unfold `Expr.atoms`, split the append with milestone 1
     (`denoteList_append` as a rewrite rule), then `iha`, `ihb`, unfold `Expr.denote`. R2, R5, R5, R2
-/
-- MILESTONE (optional: change or delete)
theorem denote_atoms {α : Type} [CMon α] (ρ : Nat → α) (e : Expr) :
    denoteList ρ e.atoms = e.denote ρ := by
  induction e with
  | atom i => simp [Expr.atoms, denoteList, Expr.denote, op_comm _ (unit : α), unit_op]
  | unit => rfl
  | op a b iha ihb => simp [Expr.atoms, denoteList_append, iha, ihb, Expr.denote]

/- SKELETON · denoteList_perm   (milestone 3; used in reflect, step 2)
  1. BEFORE the induction, prove left-commutativity
       `have op_left_comm : ∀ a b c : α, op a (op b c) = op b (op a c)`
     by `intro a b c`, regroup left, swap `op a b` (explicit arguments), regroup
     right.                                                                      R8, R9, rw [op_assoc]
  2. Induction on the derivation `h`: four goals.                                R10
  3. nil: rfl.  cons: unfold `denoteList`, rewrite with `ih`.                     R2, R5
     swap: unfold `denoteList`, rewrite with `op_left_comm`.                     R2, R5
     trans: chain `ih1` and `ih2`.                                               R11
-/
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

/- SKELETON · sortList_perm   (milestone 4; used in reflect, step 2)
  1. Helper first: `have insertSorted_perm : ∀ (i : Nat) (l : List Nat),
       (insertSorted i l).Perm (i :: l)`, by `intro i l` and induction on `l`.   R1
       nil: `insertSorted i []` computes to `[i]`, so `exact` takes refl.       R12, R21
       cons j js ih: unfold `insertSorted`, split the `if`.                     R2, R13
       `i ≤ j`: R12.  `¬ i ≤ j`: `j :: insertSorted i js ~ j :: i :: js ~ i :: j :: js`:
       `ih` under `j`, then the swap, joined.                                    R14, R16, R15
  2. Main induction on `l`.                                                      R1
       nil: `sortList []` computes to `[]`.                                      R12, R21
       cons i is ih: `sortList (i :: is)` computes to `insertSorted i (sortList is)`
       (`exact` sees through it): `~ i :: sortList is` by the helper,
       `~ i :: is` by `ih` under `i`, joined.                                    R14, R15, R21
-/
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

/- SKELETON · reflect
  Prove the MILESTONES first, in file order: denoteList_append (used by denote_atoms),
  denote_atoms (step 1), denoteList_perm and sortList_perm (step 2).
  1. Each `Expr.denote ρ eₖ` → `denoteList ρ eₖ.atoms`: `rw [← denote_atoms]`
     once per side (the first match fixes `e`).                                  R17, R17
  2. Put the sort in on each side: rewrite `denoteList ρ eₖ.atoms` backwards
     with `denoteList_perm ρ (sortList_perm eₖ.atoms)`, for k = 1, then 2.      R17, R17
  3. The goal is `denoteList ρ (sortList e1.atoms) = denoteList ρ (sortList e2.atoms)`.
     `norm e` is `sortList e.atoms` by definition, so apply `denoteList ρ` to `h`. R18, R21
-/
-- BEGIN SPEC
theorem reflect {α : Type} [CMon α] (e1 e2 : Expr) (h : norm e1 = norm e2) (ρ : Nat → α) :
    e1.denote ρ = e2.denote ρ :=
-- END SPEC
  by
    rw [← denote_atoms, ← denote_atoms, ← denoteList_perm ρ (sortList_perm e1.atoms),
      ← denoteList_perm ρ (sortList_perm e2.atoms)]
    exact congrArg (denoteList ρ) h

/- SKELETON · demo   (the payoff; uses reflect; see guide W4)
  1. Write each side as an `Expr`: atom 0 for `a`, 1 for `b`, 2 for `c`, 3 for `d`,
     `.unit` for `unit`, `.op` for `op`.
  2. The assignment `ρ : Nat → α`: `i ↦` the i-th of `[a, b, c, d]`, default `unit`. R20
  3. `exact reflect <tree1> <tree2> (by decide) ρ`: `decide` computes both normal
     forms; `exact` accepts because `Expr.denote ρ <treeₖ>` unfolds to each side. R19, R21
-/
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
H1. Go through lists. `denote_atoms`: `e.denote ρ = denoteList ρ e.atoms`. `sortList_perm`: sorting only
    permutes the list. `denoteList_perm`: `denoteList` cannot see the order of its list, because `op` is
    associative and commutative. Together they give `reflect`; `reflect` plus `decide` gives `demo`.
H2. Five inductions. On `l1` for `denoteList_append` (laws `unit_op`, `op_assoc`). On `e` for
    `denote_atoms` (atom case `op (ρ i) unit = ρ i` from `op_comm _ (unit : α)` and `unit_op`; op case uses
    `denoteList_append`). On the `Perm` derivation for `denoteList_perm` (swap case needs
    `op a (op b c) = op b (op a c)`, proved before the induction). On `l` for `insertSorted i l ~ i :: l`
    (with `split` on the `if`), then on `l` again for `sortList_perm`.
H3. `reflect`: `rw [← denote_atoms, ← denote_atoms, ← denoteList_perm ρ (sortList_perm e1.atoms),
    ← denoteList_perm ρ (sortList_perm e2.atoms)]; exact congrArg (denoteList ρ) h`.
    Swap case: `simp [denoteList, op_left_comm]`; false branch: `exact (ih.cons j).trans (.swap i j js)`.
    `demo`: `reflect (.op (.op (.atom 0) (.atom 1)) …) (.op (.atom 3) …) (by decide) (fun i => [a, b, c, d].getD i unit)`.
-/
