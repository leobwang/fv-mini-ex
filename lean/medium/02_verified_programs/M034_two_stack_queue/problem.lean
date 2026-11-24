/- M034 | Two-stack queue | 15-20 min | data abstraction, abstraction function, Option, split, amortized cost, potential function
GOAL
  A FIFO queue is two lists read as `toList q = front ++ back.reverse`. Prove `enqueue`/`dequeue`
  implement a list queue (dequeue fails exactly on the empty queue, else returns the head and the
  tail), then that any run of `k` operations costs at most `2k + back.length` (amortized O(1)).
BANNED: try?, grind

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M034

-- BEGIN SPEC
/-- A FIFO queue as two stacks: `front` in order, `back` reversed (newest element first). -/
structure Queue (α : Type) where
  front : List α
  back : List α

/-- Abstraction function: the list of elements, oldest first. -/
def Queue.toList {α : Type} (q : Queue α) : List α := q.front ++ q.back.reverse

def Queue.enqueue {α : Type} (x : α) (q : Queue α) : Queue α := ⟨q.front, x :: q.back⟩

def Queue.dequeue {α : Type} : Queue α → Option (α × Queue α)
  | ⟨x :: f, b⟩ => some (x, ⟨f, b⟩)
  | ⟨[], b⟩ =>
    match b.reverse with
    | [] => none
    | x :: f => some (x, ⟨f, []⟩)

inductive Op (α : Type) where
  | enq (x : α)
  | deq

/-- Apply one operation (a `deq` on the empty queue does nothing). -/
def Queue.step {α : Type} (q : Queue α) : Op α → Queue α
  | .enq x => q.enqueue x
  | .deq =>
    match q.dequeue with
    | some (_, q') => q'
    | none => q

/-- Cost model: one unit per operation, plus one per element moved when `deq` reverses `back`. -/
def Queue.cost {α : Type} (q : Queue α) : Op α → Nat
  | .enq _ => 1
  | .deq =>
    match q.front with
    | [] => q.back.length + 1
    | _ :: _ => 1

/-- Total cost of running `ops` from `q`. -/
def Queue.runCost {α : Type} (q : Queue α) : List (Op α) → Nat
  | [] => 0
  | op :: ops => q.cost op + (q.step op).runCost ops
-- END SPEC

/- SKELETON · toList_enqueue
  1. Unfold `Queue.toList` and `Queue.enqueue`; the record fields reduce:      R1
  2. Push `reverse` through the new head of `x :: q.back`:                     R2
  3. Reassociate `++`; both sides are then the same list:                      R3
     (`simp` with the two definitions does 1–3: R2 and R3 are simp lemmas)
-/
-- BEGIN SPEC
theorem toList_enqueue {α : Type} (x : α) (q : Queue α) :
    (q.enqueue x).toList = q.toList ++ [x] :=
-- END SPEC
  sorry

/- SKELETON · dequeue_some
  1. Destructure the queue into its fields `f b`:                              R4
  2. Split on the front list `f`:                                              R5
  3. `cons` arm (the first arm of `dequeue` fires):
       unfold `dequeue` in `h`, peel `some` and the pair:                      R6, R7, R8
       substitute `x` and `q'`:                                                R9
       both sides unfold to the same list:                                     rfl
  4. `nil` arm:
       unfold `dequeue` in `h`; a `match b.reverse with …` remains:            R6
       split that match:                                                       R10
       `[]` arm (`h : none = some _`):                                         R11
       `x :: f` arm: name the arm's variables and `hb : b.reverse = y :: f`:   R12
         then peel and substitute as in step 3:                                R7, R8, R9
         close with `simp` given `Queue.toList` and `hb`
-/
-- BEGIN SPEC
theorem dequeue_some {α : Type} (q q' : Queue α) (x : α) (h : q.dequeue = some (x, q')) :
    q.toList = x :: q'.toList :=
-- END SPEC
  sorry

/- SKELETON · dequeue_of_toList   (milestone: uses `dequeue_some`)
  1. Split on the value of `q.dequeue`, keeping the equation `hd`:             R13
  2. `none` arm, impossible because `h` says the queue is non-empty:
       destructure `q`, split on the front list:                               R4, R5
       `cons` arm: `simp` with `Queue.dequeue` at `hd` reaches `False`:       R14
       `nil` arm: unfold `dequeue` in `hd`, split its match:                   R6, R10
         `[]` arm: name `hb : b.reverse = []`:                                 R12
           then `simp` with `Queue.toList` and `hb` at `h` reaches `False`:    R14
         `_ :: _` arm (`hd : some _ = none`):                                  R11
  3. `some (y, q')` arm:
       `have h' := dequeue_some …` gives `q.toList = y :: q'.toList`
       rewrite it with `h`:                                                    R15
       split the `::` equation into `x = y` and `l = q'.toList`:               R16
       eliminate `y`:                                                          R17
       give the witness `q'`:                                                  R18
-/
-- BEGIN SPEC
theorem dequeue_of_toList {α : Type} (q : Queue α) (x : α) (l : List α) (h : q.toList = x :: l) :
    ∃ q', q.dequeue = some (x, q') ∧ q'.toList = l :=
-- END SPEC
  sorry

/- SKELETON · cost_step   (potential Φ q := q.back.length; milestone for `amortized`)
  1. Destructure the queue:                                                    R4
  2. Split on `op`:                                                            R5
  3. `enq x`: `simp` with `Queue.cost`, `Queue.step`, `Queue.enqueue`, then:   R22
  4. `deq`: split on the front list:                                           R5
       `cons`: `simp` with `Queue.cost`, `Queue.step`, `Queue.dequeue`
       `nil`: split on `b.reverse`, keeping `hb`:                              R19
         `nil`: turn `hb` into `b = []` and give it to that `simp`:            R20
         `cons`: give `hb` to that `simp`, then:                               R22
-/
-- BEGIN SPEC
/-- One step: actual cost plus the new potential is at most 2 plus the old potential. -/
theorem cost_step {α : Type} (q : Queue α) (op : Op α) :
    q.cost op + (q.step op).back.length ≤ 2 + q.back.length :=
-- END SPEC
  sorry

/- SKELETON · amortized   (milestone: `cost_step`, once per step)
  1. Induction on `ops`, generalizing `q` (the run goes on from `q.step op`):  R23
  2. `nil`: `simp` with `Queue.runCost`
  3. `cons op ops ih`:
       add the one-step bound at `(q, op)` and `ih` at `q.step op`:            have h1 := …, have h2 := …
       unfold one step of `runCost` and the length in the goal:                R6 (in the goal), R21
       linear arithmetic with `h1`, `h2`:                                      R22
-/
-- BEGIN SPEC
theorem amortized {α : Type} (q : Queue α) (ops : List (Op α)) :
    q.runCost ops ≤ 2 * ops.length + q.back.length :=
-- END SPEC
  sorry

end M034

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each `dequeue`/`cost`/`step` fact splits the way the definitions do: destructure `q`, then is `front`
    empty, and if so, is `back.reverse` empty? `dequeue_of_toList` reuses `dequeue_some`; `amortized` is
    an induction that uses `cost_step` once per step.
H2. `dequeue_some`: `simp only [Queue.dequeue] at h`, then `split at h`, peel `h` with `Option.some.injEq`
    and `Prod.mk.injEq`, and `obtain ⟨rfl, rfl⟩ := h`. `dequeue_of_toList`: `match hd : q.dequeue with`;
    the `none` arm contradicts `h` after the same splits; the `some` arm is `dequeue_some` + `injection`.
    `amortized`: `induction ops generalizing q` (the queue changes after each step).
H3. `cost_step`, empty-front `deq` case: `cases hb : b.reverse with`, then `simp [Queue.cost, Queue.step,
    Queue.dequeue, hb]` (with `List.reverse_eq_nil_iff.mp hb` instead of `hb` in the `nil` arm) and `omega`.
    `amortized`: `have := cost_step q op; have := ih (q.step op); simp only [Queue.runCost,
    List.length_cons]; omega`.
-/
