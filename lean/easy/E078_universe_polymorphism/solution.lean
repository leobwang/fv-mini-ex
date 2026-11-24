/- E078 | Universe polymorphism | 2-3 min | universe, Type u, Sort u
GOAL
  Implement the universe-polymorphic `mapFst` (apply `f` to the first component of a pair) and
  `pick` (return the first argument), then use them on types themselves, such as `List` and `Nat`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E078

/- SKELETON · mapFst (def body)
  1. Read the binders: three types at three independent levels `u`, `v`, `w`; the body
     never mentions the levels:                                              R1
  2. The result `γ × β` is a pair:                                            R2
  3. First component: `f` applied to the first projection of `p`:            R3, R4
  4. Second component: the second projection of `p`:                          R3
-/
-- BEGIN SPEC
universe u v w

def mapFst {α : Type u} {β : Type v} {γ : Type w} (f : α → γ) (p : α × β) : γ × β :=
-- END SPEC
  (f p.1, p.2)

/- SKELETON · pick (def body)
  1. `{α : Sort u}`: `α` may be a proposition or a type at any level, and `_b` is
     an argument the body ignores:                                           R5
  2. Return the first argument (no projection, no case split).
-/
-- BEGIN SPEC
def pick {α : Sort u} (a _b : α) : α :=
-- END SPEC
  a

/- SKELETON · mapFst_id
  One step, `rfl` (R10). What it does, step by step (to watch it, write the
  steps as tactics after `by`):
  1. unfold `mapFst`                                                          R6
  2. compute `id` applied to the first projection                             R8
  3. a pair rebuilt from the projections of `p` is `p` (structure eta)        R9
     Written out, step 2 already closes the goal: `dsimp` ends by trying the
     check of R9 itself, so there is no step 3 to type.
-/
-- BEGIN SPEC
theorem mapFst_id {α : Type u} {β : Type v} (p : α × β) : mapFst id p = p :=
-- END SPEC
  rfl

/- SKELETON · mapFst_comp
  One step, `rfl` (R10). What it does, step by step (as tactics after `by`):
  1. unfold every `mapFst`; compute the projections of the inner pair         R6, R7
  2. `(g ∘ f) x` is `g (f x)` by definition                                    R11
  3. both sides are now the same pair; written out, step 2's `dsimp` notices
     this and closes the goal itself
-/
-- BEGIN SPEC
theorem mapFst_comp {α : Type u} {β : Type v} {γ δ : Type w} (f : α → γ) (g : γ → δ) (p : α × β) :
    mapFst g (mapFst f p) = mapFst (g ∘ f) p :=
-- END SPEC
  rfl

/- SKELETON · mapFst_types
  1. Nothing to choose: Lean takes `α := Type`, `γ := Type`, `β := Nat`, and since
     `Type : Type 1` it picks `u := 1`, `w := 1`, `v := 0`:                   R12, R13
  2. Then the definitions compute, as in mapFst_id:                           R10
-/
-- BEGIN SPEC
theorem mapFst_types : mapFst List (Nat, 3) = (List Nat, 3) :=
-- END SPEC
  rfl

/- SKELETON · pick_type
  1. `α := Type`, which lives in `Sort 2`, so `pick` is used at `u := 2`:      R5
  2. The definition computes:                                                 R10
-/
-- BEGIN SPEC
theorem pick_type : pick Nat Bool = Nat :=
-- END SPEC
  rfl

end E078

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The signatures already carry all the universe bookkeeping (R1, R5); you never write a level.
    The bodies are ordinary one-liners, and every theorem holds by the definitions alone.
H2. `mapFst` builds a new pair (R2) from `f` applied to the first projection and the second
    projection (R3, R4); `pick` returns its first argument and ignores `_b`. Each theorem is
    "unfold, compute, eta" (R6–R9, R11), which `rfl` does in one step (R10). In `mapFst_types`,
    `α := Type`, `γ := Type`, `β := Nat`, so `u = w = 1` and `v = 0` (R12, R13).
H3. `(f p.1, p.2)` and `a`; then `rfl` four times.
-/
