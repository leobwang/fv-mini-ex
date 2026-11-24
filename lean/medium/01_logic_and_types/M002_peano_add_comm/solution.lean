/- M002 | Peano addition is commutative | 10-15 min | inductive, helper lemmas, induction
GOAL
  On your own unary naturals, prove that addition is associative and commutative.
  You will need helper lemmas; the induction hypothesis alone is not enough.

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M002

-- BEGIN SPEC
inductive N where
  | zero : N
  | succ (n : N) : N

def add : N → N → N
  | n, .zero => n
  | n, .succ m => .succ (add n m)
-- END SPEC

theorem zero_add (n : N) : add .zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [add, ih]

theorem succ_add (a b : N) : add (.succ a) b = .succ (add a b) := by
  induction b with
  | zero => rfl
  | succ b ih => simp [add, ih]

/- SKELETON · add_assoc
  1. Induct on `c`, the argument `add` recurses on:                         R1
  2. `zero`: both sides compute to `add a b`:                               R2
  3. `succ c ih`: unfold `add` at `c.succ` on both sides, peel the outer
     `succ`, then the goal is `ih` (one `simp` call does all three):        R3 → R4 → R5 (R7)
-/
-- BEGIN SPEC
theorem add_assoc (a b c : N) : add (add a b) c = add a (add b c) :=
-- END SPEC
  by
    induction c with
    | zero => rfl
    | succ c ih => simp [add, ih]

/- SKELETON · add_comm
  0. MILESTONES first, as theorems of their own between `add` and this one
     (outside the spec regions), each by induction on its SECOND argument:
       zero_add (n : N)   : add .zero n = n                        R1, R2, R7
       succ_add (a b : N) : add (.succ a) b = .succ (add a b)      R1, R2, R7
     `zero_add` is used in step 2, `succ_add` in step 3.
  1. Induct on `b`:                                                         R1
  2. `zero`: unfold `add a .zero`; the right side `add .zero a` is stuck:
     rewrite it with `zero_add`:                                            R3 → R6
  3. `succ b ih`: unfold the left side to `(add a b).succ`; move the `succ`
     out of the right side with `succ_add`; peel `succ`, use `ih`:          R3 → R6 → R4 → R5 (R7)
-/
-- BEGIN SPEC
theorem add_comm (a b : N) : add a b = add b a :=
-- END SPEC
  by
    induction b with
    | zero => simp [add, zero_add]
    | succ b ih => simp [add, succ_add, ih]

end M002

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `add` recurses on its second argument: induct on that one (R1). `add_assoc` then goes through
    directly. `add_comm` gets stuck at `add .zero a` and at `add (.succ b) a`, where the inducted
    variable sits in the first position: those two facts are your helper lemmas.
H2. Prove `zero_add` and `succ_add` first, each by induction on its second argument: `rfl` for
    `zero`, `simp [add, ih]` for `succ` (R1, R2, R7). Then `add_comm` by induction on `b`, giving
    `simp` the definition and the helpers (R6, R7).
H3. `theorem succ_add (a b : N) : add (.succ a) b = .succ (add a b)` by `induction b`. In `add_comm`:
    `| zero => simp [add, zero_add]` and `| succ b ih => simp [add, succ_add, ih]`.
-/
