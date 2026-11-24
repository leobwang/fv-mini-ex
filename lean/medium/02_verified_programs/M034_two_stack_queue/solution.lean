/- M034 | Two-stack queue | 15-20 min | data abstraction, abstraction function, Option, split, amortized cost, potential function
GOAL
  A FIFO queue is two lists read as `toList q = front ++ back.reverse`. Prove `enqueue`/`dequeue`
  implement a list queue (dequeue fails exactly on the empty queue, else returns the head and the
  tail), then that any run of `k` operations costs at most `2k + back.length` (amortized O(1)).

REFERENCE
  #check @List.reverse_eq_nil_iff   -- xs.reverse = [] ↔ xs = []
  #check @List.reverse_append       -- (as ++ bs).reverse = bs.reverse ++ as.reverse
  -- `obtain ⟨f, b⟩ := q` then `cases f`: which arm of `dequeue` fires depends on `front`
  -- `split at h` splits the `match b.reverse with …` inside hypothesis `h`, one goal per arm,
  -- and names the arm's equation (`rename_i y f hb` to see `hb : b.reverse = y :: f`)
  -- `cases hb : b.reverse with | nil => _ | cons y f => _`  does the same split in the goal
  -- Potential method: with Φ q := q.back.length, a bound `cost + Φ after ≤ 2 + Φ before` for one
  -- step sums (telescopes) over a whole run.
BANNED: try?, grind
NOTE: `grind` is banned (every `try?` suggestion here is a `grind` call): do the case splits by hand.
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

-- BEGIN SPEC
theorem toList_enqueue {α : Type} (x : α) (q : Queue α) :
    (q.enqueue x).toList = q.toList ++ [x] :=
-- END SPEC
  by
    simp [Queue.toList, Queue.enqueue]

-- BEGIN SPEC
theorem dequeue_some {α : Type} (q q' : Queue α) (x : α) (h : q.dequeue = some (x, q')) :
    q.toList = x :: q'.toList :=
-- END SPEC
  by
    obtain ⟨f, b⟩ := q
    cases f with
    | cons y f =>
      simp only [Queue.dequeue, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | nil =>
      simp only [Queue.dequeue] at h
      split at h
      · contradiction
      · rename_i y f hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [Queue.toList, hb]

-- BEGIN SPEC
theorem dequeue_of_toList {α : Type} (q : Queue α) (x : α) (l : List α) (h : q.toList = x :: l) :
    ∃ q', q.dequeue = some (x, q') ∧ q'.toList = l :=
-- END SPEC
  by
    match hd : q.dequeue with
    | none =>
      obtain ⟨f, b⟩ := q
      cases f with
      | cons y f => simp [Queue.dequeue] at hd
      | nil =>
        simp only [Queue.dequeue] at hd
        split at hd
        · rename_i hb
          simp [Queue.toList, hb] at h
        · contradiction
    | some (y, q') =>
      have h' := dequeue_some q q' y hd
      rw [h] at h'
      injection h' with h1 h2
      subst h1
      exact ⟨q', rfl, h2.symm⟩

-- BEGIN SPEC
/-- One step: actual cost plus the new potential is at most 2 plus the old potential. -/
theorem cost_step {α : Type} (q : Queue α) (op : Op α) :
    q.cost op + (q.step op).back.length ≤ 2 + q.back.length :=
-- END SPEC
  by
    obtain ⟨f, b⟩ := q
    cases op with
    | enq x => simp [Queue.cost, Queue.step, Queue.enqueue]; omega
    | deq =>
      cases f with
      | cons y f => simp [Queue.cost, Queue.step, Queue.dequeue]
      | nil =>
        cases hb : b.reverse with
        | nil => simp [Queue.cost, Queue.step, Queue.dequeue, List.reverse_eq_nil_iff.mp hb]
        | cons y f => simp [Queue.cost, Queue.step, Queue.dequeue, hb]; omega

-- BEGIN SPEC
theorem amortized {α : Type} (q : Queue α) (ops : List (Op α)) :
    q.runCost ops ≤ 2 * ops.length + q.back.length :=
-- END SPEC
  by
    -- WHY: generalise `q`: after one step the run continues from `q.step op`.
    induction ops generalizing q with
    | nil => simp [Queue.runCost]
    | cons op ops ih =>
      have h1 := cost_step q op
      have h2 := ih (q.step op)
      simp only [Queue.runCost, List.length_cons]
      omega

end M034

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every `dequeue`/`cost`/`step` fact needs the same case split: is `front` empty, and if so, is `b.reverse`
    empty? `amortized` is induction on `ops`, using `cost_step` once per step.
H2. `dequeue_of_toList`: match on `q.dequeue` (`match hd : q.dequeue with`). `some` follows from
    `dequeue_some` plus `List.cons` injectivity; `none` contradicts `h` after the case split. In
    `amortized`, generalise `q` (the queue changes after each step).
H3. `cost_step`, empty-front `deq` case: `cases hb : b.reverse with`, then `simp [Queue.cost, Queue.step,
    Queue.dequeue, hb]` (plus `List.reverse_eq_nil_iff.mp hb` in the `nil` arm) and `omega`. `amortized`:
    `induction ops generalizing q`, then `have := cost_step q op; have := ih (q.step op); simp only
    [Queue.runCost, List.length_cons]; omega`.
-/
