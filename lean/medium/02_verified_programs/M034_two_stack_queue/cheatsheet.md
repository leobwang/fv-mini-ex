# M034 · Two-stack queue: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `List`, `::`, `++`, structures, `inductive`, pattern
matching, `simp`, `rw`, `rfl`, `have`. **New here:** proving facts about pattern-matching programs by
hand: destructuring a structure, splitting a `match` that sits inside a hypothesis, peeling equations
between constructors (`some`, pairs, `::`), and amortized cost by a potential function with `omega`.
Core Lean only (no Mathlib).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a goal the step leaves alone (the step works on the context).
- Placeholders are written as Lean binders. `{α : Type}` is any type (`Nat`, `Bool`, `List Nat`, …).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{ front := f, back := b }` | the queue `Queue.mk f b`, i.e. `⟨f, b⟩` (a structure value printed with its field names) |
| `q.toList`, `q.dequeue`, `q.cost op` | `Queue.toList q`, … (dot notation: `q.f a` is `Queue.f q a` when `q : Queue α`) |
| `{ front := f, back := b }.back` | a field of a literal record; `simp` reduces it to `b` (R1) |
| `Option (α × Queue α)` | either `none` or `some (x, q')`: a pair of an element and a queue |
| `(a, b)`, `α × β` | a pair (`Prod.mk a b`) and the pair type |
| `match e with \| [] => … \| x :: f => …` | an unevaluated case split on `e`; it stays until the shape of `e` is known (R6, R10) |
| `Op.deq`, `Op.enq x` | the two operations of the exercise's `inductive Op` |
| `x✝`, `f✝`, `heq✝` | inaccessible names: Lean made them, you cannot type them; name them with `rename_i` (R12) |
| `x✝¹` | an older inaccessible variable (the superscript counts back) |
| `case cons`, `case h_1`, `case refine_2` | tag of the goal: arm of a `cases`, of a `split`, of a `match` |
| `q'_1` | a bound variable renamed because a hypothesis already uses the name `q'` |
| `l.length`, `2 * k + n` | `List.length l`; `Nat` arithmetic (`omega` handles it, R22) |

**Amortized cost (the potential method).** Let the potential be $\Phi(q) = |q.\mathit{back}|$ (the
length of `back`). If one operation from $q$ to $q'$ with actual cost $c$ satisfies
$c + \Phi(q') \le 2 + \Phi(q)$, then summing over a run $q_0 \to q_1 \to \dots \to q_k$ of $k$ steps
telescopes: $\sum_i c_i + \Phi(q_k) \le 2k + \Phi(q_0)$, so $\sum_i c_i \le 2k + \Phi(q_0)$ because
$\Phi \ge 0$. `cost_step` is the one-step inequality, `amortized` the sum.

---

## Part 1 · `toList_enqueue`

Statement: the list view of `q.enqueue x` is the list view of `q` with `x` appended at the end.

**R1 · `simp only [d₁, d₂]`** changes the **goal**: each defined name becomes its body, and a field of a
literal record (`{ inp := a, out := b }.inp`) reduces to the value (`a`). Placeholders: the guide's own
`structure Buf (α : Type)` with fields `inp out : List α`, `(p : Buf α)`.

| Before | After |
|---|---|
| `⊢ P p.swap.all` | `⊢ P (p.out ++ p.inp)` |

**R2 · `rw [List.reverse_cons]`** changes the **goal**. The lemma is `(a :: as).reverse = as.reverse ++ [a]`.
Placeholders: `{α : Type} (a : α) (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as).reverse` | `⊢ P (as.reverse ++ [a])` |

**R3 · `rw [List.append_assoc]`** changes the **goal**. The lemma is `as ++ bs ++ cs = as ++ (bs ++ cs)`;
`++` groups to the left. Placeholders: `{α : Type} (as bs cs : List α)`. Both R2 and R3 are `simp` lemmas, so
`simp [d₁, d₂]` applies them by itself.

| Before | After |
|---|---|
| `⊢ P (as ++ bs ++ cs)` | `⊢ P (as ++ (bs ++ cs))` |

**W1** chains R2 and R3, then `rfl` closes it (`[a] ++ bs` and `a :: bs` are equal by unfolding):

```lean-goal
⊢ (a :: as).reverse ++ bs = as.reverse ++ a :: bs
⊢ as.reverse ++ [a] ++ bs = as.reverse ++ a :: bs
⊢ as.reverse ++ ([a] ++ bs) = as.reverse ++ a :: bs
```

---

## Part 2 · `dequeue_some`

Statement: if `q.dequeue = some (x, q')`, then the list view of `q` is `x` followed by the list view of `q'`.
`dequeue` decides by the shape of `front`, then (if `front = []`) by the shape of `back.reverse`; the proof
makes the same two splits.

**R4 · `obtain ⟨a, b⟩ := p`** changes the **context**: the structure variable `p` is replaced by its fields,
and every `p` in the goal and hypotheses becomes the literal record. Placeholders: `(p : Buf α)`.
On the exercise: `obtain ⟨f, b⟩ := q`.

| Before | After |
|---|---|
| `⊢ P p` | `a b : List α ⊢ P { inp := a, out := b }` |

**R5 · `cases l with | nil => … | cons y f => …`** changes the **goal list**: one goal per constructor, each
with `l` replaced by that constructor. Placeholders: `{α : Type} (l : List α)`. It works the same on
`op : Op α` (`| enq x => … | deq => …`).

| Before | After |
|---|---|
| `⊢ P l` | `⊢ P []`, `y : α, f : List α ⊢ P (y :: f)` |

**R6 · `simp only [d] at h`** changes the **context**: `d` is unfolded inside `h`, and the arm whose pattern
matches the argument is selected. Placeholders: the guide's `Buf.peek` (same shape as `dequeue`: first arm on
`x :: _`, second arm a `match o.reverse with …`). Use it in the goal too: `simp only [d]`.

| Before | After |
|---|---|
| `h : { inp := y :: f, out := o }.peek = some a` and goal `G` | `h : some y = some a ⊢ G` |

With an empty first list the inner `match` remains, because `o.reverse` has no known shape yet. The state
after `simp only [Buf.peek] at h` from `h : { inp := [], out := o }.peek = some a` is

```text
h :
  (match o.reverse with
    | [] => none
    | x :: tail => some x) =
    some a
```

**R7 · `simp only [Option.some.injEq] at h`** changes the **context**. The lemma is
`(some a = some b) = (a = b)` (`some` is injective). Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `h : some a = some b ⊢ G` | `h : a = b ⊢ G` |

**R8 · `simp only [Prod.mk.injEq] at h`** changes the **context**. The lemma is
`((a, b) = (c, d)) = (a = c ∧ b = d)`. Placeholders: `{α β : Type} (a c : α) (b d : β)`. R7 and R8 together:
`h : some (y, r) = some (x, q')` becomes `h : y = x ∧ r = q'`.

| Before | After |
|---|---|
| `h : (a, b) = (c, d)` and goal `G` | `h : a = c ∧ b = d ⊢ G` |

**R9 · `obtain ⟨rfl, rfl⟩ := h`** changes the **context**: `h : a = x ∧ s = y` is used up, and the local
variables `x`, `y` are replaced everywhere by `a`, `s`. Each side marked `rfl` needs one side that is a local
variable (on the exercise: `x` and `q'`). Placeholders: `{α : Type} (a x : α) (s y : List α)`.

| Before | After |
|---|---|
| `h : a = x ∧ s = y ⊢ P x y` | `⊢ P a s` |

**R10 · `split at h`** changes the **goal list**: one goal per arm of the `match` inside `h`. Each goal
records the arm in `heq✝`, and `h` shows that arm's value. Placeholders: `{α : Type} (l : List α) (a : α)`,
`h : (match l.reverse with | [] => none | x :: _ => some x) = some a`. Unfold first (R6) so the `match` is
visible in `h`.

| Before | After |
|---|---|
| `⊢ G` (with the `match` in `h`, as above) | `heq✝ : l.reverse = [], h : none = some a ⊢ G`, `heq✝ : l.reverse = x✝ :: tail✝, h : some x✝ = some a ⊢ G` |

**R11 · `contradiction`** **closes** the goal when a hypothesis equates two different constructors
(`none = some a`, `[] = x :: l`), or is `False`. Placeholders: `(a : α) (h : none = some a)`.

| Before | After |
|---|---|
| `h : none = some a ⊢ G` | no goals |

**R12 · `rename_i y t hb`** changes the **context**: the last three inaccessible hypotheses get the names `y`,
`t`, `hb`, in order. Earlier inaccessible ones keep a `✝` (here `x✝¹ : List α` becomes `x✝ : List α`).
Placeholders: as in R10, in the second goal.

| Before | After |
|---|---|
| `x✝ : α, tail✝ : List α, heq✝ : l.reverse = x✝ :: tail✝, h : some x✝ = some a ⊢ G` | `y : α, t : List α, hb : l.reverse = y :: t, h : some y = some a ⊢ G` |

On the exercise you then finish with `simp [Queue.toList, hb]`: `simp` uses `hb : b.reverse = y :: f` as a
rewrite rule, left to right.

---

## Part 3 · `dequeue_of_toList`

Statement: if the list view of `q` is `x :: l`, then `dequeue` succeeds with `x` and a queue whose list view is
`l`. Milestone: `dequeue_some` (Part 2) does most of the work in the `some` case.

**R13 · `match hd : e with | none => … | some (y, z) => …`** changes the **goal list and the context**: one goal
per pattern, `hd : e = pattern` added, and `e` in the goal replaced by the pattern. Placeholders:
`{α β : Type} (e : Option (α × β))`. On the exercise `e` is `q.dequeue`, and the goal's `q.dequeue` becomes
`none` or `some (y, q')`.

| Before | After |
|---|---|
| `⊢ P e` | `hd : e = none ⊢ P none`, `y : α, z : β ⊢ P (some (y, z))` with `hd : e = some (y, z)` |

**R14 · `simp [hb] at h`** **closes** the goal when `h` simplifies to `False`: after rewriting with `hb`,
`h : [] = x :: l` equates different constructors. The same happens with `h : some a = none`. Placeholders:
`{α : Type} (e l : List α) (x : α) (hb : e = [])`.

| Before | After |
|---|---|
| `hb : e = [], h : e = x :: l ⊢ G` | no goals |

**R15 · `rw [h] at h'`** changes the **context**: rewrites inside `h'` instead of the goal. Placeholders:
`{α : Type} (a b : α) (h : a = b)`. On the exercise: `h'` comes from `have h' := dequeue_some q q' y hd`, and
`rw [h] at h'` turns its left side `q.toList` into `x :: l`.

| Before | After |
|---|---|
| `h' : P a ⊢ P b` | `h' : P b ⊢ P b` |

**R16 · `injection h with h1 h2`** changes the **context**: an equation between two `::` cells becomes an
equation of heads and one of tails (`::` is injective). Placeholders: `{α : Type} (a b : α) (as bs : List α)`.

| Before | After |
|---|---|
| `h : a :: as = b :: bs ⊢ G` | `h1 : a = b, h2 : as = bs ⊢ G` |

**R17 · `subst h1`** changes the **context**: `h1 : x = y` with `y` a local variable is used up, and `y` is
replaced by `x` everywhere (goal and hypotheses). Placeholders: `{α : Type} (x y : α)`.

| Before | After |
|---|---|
| `h1 : x = y ⊢ P x y` | `⊢ P x x` |

**R18 · `exact ⟨w, rfl, h.symm⟩`** **closes** an `∃ v, A v ∧ B v` goal: `w` is the witness, `rfl` proves
`A w` when it is `t = t`, and `h.symm : b = a` (lemma `Eq.symm`) turns `h : a = b` around. `⟨w, p, q⟩` is
short for `⟨w, ⟨p, q⟩⟩`. Placeholders: `{α : Type} (w : α) (f : α → Nat) (c : Nat) (h : c = f w)`.

| Before | After |
|---|---|
| `⊢ ∃ v, some w = some v ∧ f v = c` | no goals |

---

## Part 4 · `cost_step`

Statement: for one operation `op`, actual cost plus the new potential is at most `2` plus the old potential:
`q.cost op + (q.step op).back.length ≤ 2 + q.back.length`. Split exactly as the definitions do: `op`
(R5), then `front` (R5), then `back.reverse` (R19).

**R19 · `cases hb : e with | nil => … | cons y f => …`** changes the **goal list and the context**: like R5,
but on an expression `e` that is not a variable, and `hb : e = pattern` is kept. If `e` does not occur in the
goal literally (on the exercise `b.reverse` is hidden inside `Queue.dequeue`), the goal stays the same and you
use `hb` afterwards with `simp [..., hb]`. Placeholders: `{α : Type} (l : List α)`. Plain `cases e` without
`hb :` loses the equation.

| Before | After |
|---|---|
| `⊢ G` | `hb : l.reverse = [] ⊢ G`, `y : α, f : List α, hb : l.reverse = y :: f ⊢ G` |

**R20 · `List.reverse_eq_nil_iff`** gives a **context** fact. The lemma is `xs.reverse = [] ↔ xs = []`; for
`h : A ↔ B`, `h.mp : A → B` and `h.mpr : B → A`. So `List.reverse_eq_nil_iff.mp hb : xs = []`. Pass it to
`simp` as a rewrite rule (`simp [..., List.reverse_eq_nil_iff.mp hb]`) to replace `xs` by `[]`.
Placeholders: `{α : Type} (xs : List α) (hb : xs.reverse = [])`.

| Before | After `have hx := List.reverse_eq_nil_iff.mp hb` | After `rw [hx]` |
|---|---|---|
| `hb : xs.reverse = [] ⊢ P xs` | `hx : xs = [] ⊢ P xs` | `⊢ P []` |

**R22 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int` (`+`, `*` by a numeral, `≤`, `<`,
`=`), using the hypotheses of that kind in the context. Any other subterm (`b.length`, `f n`,
`q.cost op`) is treated as an unknown number. It does not unfold definitions: `simp` first.

| Before | After |
|---|---|
| `⊢ 1 + (n + 1) ≤ 2 + n` | no goals |
| `h1 : c + f n ≤ 2 + n, h2 : r ≤ 2 * k + f n ⊢ c + r ≤ 2 * (k + 1) + n` | no goals |

**W3** (`tstep` in the guide) is a one-step bound for a different structure, a counter that resets:
`cases b`, `simp` with the definitions, `omega`.

---

## Part 5 · `amortized`

Statement: any run of `ops` from `q` costs at most `2 * ops.length + q.back.length`. Milestone: `cost_step`
(Part 4), used once per step.

**R23 · `induction l generalizing n with | nil => … | cons a l ih => …`** changes the **goal list**: one goal for
`[]`, one for `a :: l` with induction hypothesis `ih`. `generalizing n` makes `ih` hold for every `n`
(`∀ (n : Nat), …`), which you need because the run continues from a different queue (`q.step op`).
Placeholders: `{α : Type} (P : Nat → List α → Prop) (n : Nat) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P n l` | `n : Nat ⊢ P n []`, `a : α, l : List α, n : Nat ⊢ P n (a :: l)` with `ih : ∀ (n : Nat), P n l` |

**R21 · `rw [List.length_cons]`** changes the **goal**. The lemma is `(a :: as).length = as.length + 1`.
Placeholders: `{α : Type} (a : α) (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as).length` | `⊢ P (as.length + 1)` |

The step case: put the two facts in the context with `have` (TACTIC_STATES, "Adding facts"), the one-step
bound at `(q, op)` and `ih` at the next queue; unfold one step of `runCost` and the length in the goal
(R6 in the goal, R21); `omega` (R22) treats `q.cost op`, `(q.step op).back.length`,
`(q.step op).runCost ops` as unknowns and adds the two inequalities. W3 does the same for the counter.

---

## Traps

- `grind` is banned, and every `try?` suggestion here is a `grind` call: do the case splits by hand.
- `split at h` only sees a `match` that is written out in `h`. Unfold first: `simp only [Queue.dequeue] at h`.
- Destructure before splitting: `cases q.front` does not change `Queue.dequeue q`; after `obtain ⟨f, b⟩ := q`,
  `cases f` does.
- `rename_i` names the LAST inaccessible hypotheses. Count from the end (R12).
- `cases b.reverse` without `hb :` forgets which arm you are in; write `cases hb : b.reverse with`.
- `induction ops` without `generalizing q` gives an `ih` about the same `q` only: the step case is stuck.
- `omega` does not unfold `Queue.runCost` or `List.length`: unfold them (R6, R21) and add `cost_step` and `ih`
  instances to the context first.
- `obtain ⟨rfl, rfl⟩ := h` needs a local variable on one side of each equation; otherwise use `subst` or `rw`.
- In the `some` arm of `match hd : q.dequeue with`, the goal's bound `q'` prints as `q'_1` (your `q'` exists).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold definitions, reduce record fields | `simp only [Queue.toList, Queue.enqueue]` / `simp [...]` | R1 |
| `(a :: as).reverse` | `List.reverse_cons` | R2 |
| reassociate `++` | `List.append_assoc` | R3 |
| `q : Queue α` → fields | `obtain ⟨f, b⟩ := q` | R4 |
| split a list / `Op` | `cases f with \| nil => … \| cons y f => …` | R5 |
| unfold inside a hypothesis | `simp only [Queue.dequeue] at h` | R6 |
| `some a = some b` → `a = b` | `simp only [Option.some.injEq] at h` | R7 |
| `(a, b) = (c, d)` → `a = c ∧ b = d` | `simp only [Prod.mk.injEq] at h` | R8 |
| substitute variables from `h : a = x ∧ s = y` | `obtain ⟨rfl, rfl⟩ := h` | R9 |
| split a `match` inside `h` | `split at h` | R10 |
| `h : none = some _` | `contradiction` | R11 |
| name `x✝`, `heq✝` | `rename_i y f hb` | R12 |
| split on `q.dequeue`, keep the equation | `match hd : q.dequeue with` | R13 |
| `h` simplifies to `False` | `simp [hb] at h` | R14 |
| rewrite in a hypothesis | `rw [h] at h'` | R15 |
| `a :: as = b :: bs` → two equations | `injection h with h1 h2` | R16 |
| eliminate `y` using `h1 : x = y` | `subst h1` | R17 |
| prove `∃ v, A v ∧ B v` | `exact ⟨w, rfl, h.symm⟩` | R18 |
| split on `b.reverse`, keep the equation | `cases hb : b.reverse with` | R19 |
| `b.reverse = []` → `b = []` | `List.reverse_eq_nil_iff.mp hb` | R20 |
| `(a :: as).length` | `List.length_cons` | R21 |
| linear `Nat` arithmetic | `omega` | R22 |
| induction with a changing queue | `induction ops generalizing q with` | R23 |
| see the state | infoview | |
