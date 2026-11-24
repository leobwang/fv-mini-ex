# E085 · where and let rec: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl`, `rw`, `simp only`, `exact`, `omega`,
definitions by pattern matching and `induction … with`. **New here:** helper functions declared with `where`
and `let rec`, how to unfold them, accumulator invariants proved by `induction … generalizing`, and the list
lemmas `List.range_succ`, `List.append_assoc`, `List.singleton_append`, `List.append_nil`, `List.sum_nil`,
`List.sum_cons`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Nat → List Nat → Prop` for two arguments). The step
  changes only the part inside `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type (`Nat`, `List Nat`, …).
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

The guide's own functions: `ones n` (the list of `n` ones, helper `ones.aux` via `where`) and `len xs` (the
length, helper `len.run` via `let rec`). Neither is the exercise's.

## `where`, `let rec`, and the helper's name

```
def f (n : Nat) : T := aux n a₀        def g (xs : List Nat) : T :=
where                                     let rec run : List Nat → Nat → T
  aux : Nat → A → T                         | [], acc => …
    | 0, acc => …                           | x :: t, acc => run t …
    | k + 1, acc => aux k …               run xs 0
```

Both forms declare a **separate top-level function**: `f.aux` and `g.run` (`#check @f.aux` works). Each has
its own equations, used by `simp only [f.aux]` (R3, R11). The main function's equation is just
`f n = f.aux n a₀`, used by `simp only [f]` (R8, R15). Unfolding `f` does **not** unfold `f.aux`.

An **accumulator** is the extra argument `acc` that the helper changes on every recursive call. A statement
about `f.aux k acc` for one fixed `acc` is useless in the step, which calls `f.aux` at a different
accumulator. So the invariant is stated, and proved, for **every** `acc`.

## Reading the goals

| You see | It means |
|---|---|
| `countdown.go n acc`, `sumList.loop xs acc` | the helpers of `countdown` (`where`) and `sumList` (`let rec`) |
| `List.range n` | the list `[0, 1, …, n - 1]`; `List.range 0 = []` |
| `as ++ bs` | list concatenation; `as ++ bs ++ cs` is `(as ++ bs) ++ cs` |
| `x :: l` | the list with head `x` and tail `l` |
| `l ++ x :: acc` | `l ++ (x :: acc)`: `::` binds tighter than `++` |
| `[x]` | the one-element list `x :: []` |
| `xs.sum` | `List.sum xs`, the sum of the elements; `[].sum` is the sum of the empty list |
| `ih : ∀ (acc : List Nat), …` | an induction hypothesis that holds for every accumulator (R1) |
| `case zero`, `case succ`, `case nil`, `case cons` | goal tags made by `induction` |

---

## Part 1 · `go_spec`

Statement: `countdown.go n acc = List.range n ++ acc` for all `n` and all `acc`. In words: running the helper
for `n` steps from accumulator `acc` puts `[0, …, n - 1]` in front of `acc`. The step case is
`countdown.go (k + 1) acc = countdown.go k (k :: acc)`, so the induction hypothesis is needed at the
accumulator `k :: acc`, not at `acc`.

**R1 · `induction n generalizing acc with | zero => … | succ k ih => …`** changes the **goal list and the
context**: two goals, the `0` case and the `k + 1` case. `generalizing acc` removes `acc` from the context
before the induction and reintroduces it in each case, so `ih` is universally quantified over the
accumulator. In the guide the arms are `?_` so both goals stay open. Placeholders:
`(P : Nat → List Nat → Prop) (n : Nat) (acc : List Nat)`.

| Before | After | New hypothesis in `succ` |
|---|---|---|
| `⊢ P n acc` | `⊢ P 0 acc`, `k : Nat ⊢ P (k + 1) acc` | `ih : ∀ (acc : List Nat), P k acc` |

Without `generalizing acc`, the hypothesis is about the one `acc` of the context:

| Before | After (succ) |
|---|---|
| `⊢ P n acc` | `ih : P k acc ⊢ P (k + 1) acc` |

**R2 · `rfl`** **closes** the base case: `ones.aux 0 acc` computes to `acc` by the helper's first equation,
and `[] ++ acc` computes to `acc` too (likewise `List.range 0 ++ acc`). On `Nat`, `acc + 0` computes to
`acc` (addition recurses on its second argument), so `rfl` also closes `acc = acc + 0` (Part 3, `nil`), but
not `0 + acc = acc`: that needs R16. Placeholders: `(acc : List Nat)`.

| Before | After |
|---|---|
| `⊢ ones.aux 0 acc = [] ++ acc` | no goals |

**R3 · `simp only [f.aux]`** changes the **goal**: it rewrites with the equations of the `where` helper,
wherever the arguments have the shape of a pattern. Here `ones.aux (k + 1) acc = ones.aux k (1 :: acc)`.
Placeholders: `(k : Nat) (acc : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (ones.aux (k + 1) acc)` | `⊢ P (ones.aux k (1 :: acc))` |

**R4 · `rw [ih]`** with `ih : ∀ a, f a = g a` changes the **goal**: `rw` finds an instance `f x` in the goal,
sets `a := x`, and rewrites. This is where the generalized IH pays off: `x` is the new accumulator. A proved
theorem with arguments works the same way: `rw [thm]` (Parts 2 and 4). Placeholders:
`{α β : Type} (f g : α → β) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (f x)` | `⊢ P (g x)` |

**R5 · `List.range_succ`** changes the **goal**. The lemma is
`List.range_succ {n : Nat} : List.range (n + 1) = List.range n ++ [n]` (Lean states it with `n.succ`, which is
`n + 1`). Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.range (n + 1))` | `⊢ P (List.range n ++ [n])` |

**R6 · `List.append_assoc`** changes the **goal**. The lemma is
`List.append_assoc (as bs cs : List α) : as ++ bs ++ cs = as ++ (bs ++ cs)`. Placeholders:
`{α : Type} (as bs cs : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ bs ++ cs)` | `⊢ P (as ++ (bs ++ cs))` |

**R7 · `List.singleton_append`** changes the **goal**. The lemma is `List.singleton_append : [x] ++ l = x :: l`.
Placeholders: `{α : Type} (x : α) (l : List α)`. After R6 and R7, `l ++ [x] ++ acc` reads `l ++ x :: acc`.

| Before | After |
|---|---|
| `⊢ P ([x] ++ l)` | `⊢ P (x :: l)` |

`simp` applies R6 and R7 by itself (they are `simp` lemmas); `rw` needs them named.

**W1 (on `rev`, list reversal with an accumulator):** `rev.aux xs acc = xs.reverse ++ acc` by R10 (the list
version of R1), `rfl` for `nil`, then in the `cons x t ih` case R3, R4, `List.reverse_cons`
(`(a :: as).reverse = as.reverse ++ [a]`), R6, R7:

```lean-goal
⊢ rev.aux (x :: t) acc = (x :: t).reverse ++ acc
⊢ rev.aux t (x :: acc) = (x :: t).reverse ++ acc
⊢ t.reverse ++ x :: acc = (x :: t).reverse ++ acc
⊢ t.reverse ++ x :: acc = t.reverse ++ [x] ++ acc
```

The last `rw [List.append_assoc, List.singleton_append]` makes both sides the same and closes the goal.

---

## Part 2 · `countdown_eq`

Statement: `countdown n = List.range n`. `countdown n` is `countdown.go n []`, so this is Part 1 at
`acc := []`, followed by `l ++ [] = l`.

**R8 · `simp only [f]`** changes the **goal**: it replaces the main function by its body, the helper call.
It does not unfold the helper. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (ones n)` | `⊢ P (ones.aux n [])` |

Then **R4** with the Part 1 theorem: `rw [go_spec]` sets `n` and `acc := []` by matching.

**R9 · `List.append_nil`** changes the **goal**. The lemma is `List.append_nil (as : List α) : as ++ [] = as`.
Placeholders: `{α : Type} (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ [])` | `⊢ P as` |

**W2 (on `rev`):** R8, then R4 with W1's theorem, then R9:

```lean-goal
⊢ rev xs = xs.reverse
⊢ rev.aux xs [] = xs.reverse
```

---

## Part 3 · `loop_spec`

Statement: `sumList.loop xs acc = acc + xs.sum` for all `xs` and all `acc`. The step is
`sumList.loop (x :: xs) acc = sumList.loop xs (acc + x)`: again a different accumulator, so generalize it.

**R10 · `induction xs generalizing acc with | nil => … | cons x xs ih => …`** changes the **goal list and the
context**: the empty list and `x :: xs`, the latter with `ih` about the tail `xs` for every accumulator.
Placeholders: `{α : Type} (P : List α → Nat → Prop) (xs : List α) (acc : Nat)`.

| Before | After | New hypothesis in `cons` |
|---|---|---|
| `⊢ P xs acc` | `⊢ P [] acc`, `x : α, xs : List α ⊢ P (x :: xs) acc` | `ih : ∀ (acc : Nat), P xs acc` |

**R11 · `simp only [f.run]`** changes the **goal**: the equations of a `let rec` helper, used exactly like a
`where` helper's (R3). Here `len.run (x :: t) n = len.run t (n + 1)`. Placeholders: `(x n : Nat) (t : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (len.run (x :: t) n)` | `⊢ P (len.run t (n + 1))` |

**R12 · `List.sum_nil`** changes the **goal**. The lemma is `List.sum_nil : [].sum = 0` (for any element type
with `+` and `0`, such as `Nat`).

| Before | After |
|---|---|
| `⊢ P [].sum` | `⊢ P 0` |

**R13 · `List.sum_cons`** changes the **goal**. The lemma is `List.sum_cons : (a :: l).sum = a + l.sum`.
Placeholders: `(a : Nat) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (a :: l).sum` | `⊢ P (a + l.sum)` |

**R14 · `omega`** **closes** a goal of linear arithmetic over `Nat` (`+`, `*` by a literal, `=`, `<`, `≤`).
Any other term, such as `l.sum`, is one unknown number. Use it for regrouping a sum that `simp` leaves.
Placeholders: `(a b : Nat) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ a + b + l.sum = a + (b + l.sum)` | no goals |

**W3 (on `len`):** `len.run xs n = n + xs.length` by R10, `rfl` for `nil`, then R11 together with
`List.length_cons : (a :: l).length = l.length + 1`, R4, R14:

```lean-goal
⊢ len.run (x :: t) n = n + (x :: t).length
⊢ len.run t (n + 1) = n + (t.length + 1)
⊢ n + 1 + t.length = n + (t.length + 1)
```

---

## Part 4 · `sumList_eq`

Statement: `sumList xs = xs.sum`. `sumList xs` is `sumList.loop xs 0`, so this is Part 3 at `acc := 0`,
followed by `0 + s = s`.

**R15 · `simp only [f]`** on a function with a `let rec` helper changes the **goal**: the body is the helper
call. Placeholders: `(xs : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (len xs)` | `⊢ P (len.run xs 0)` |

Then **R4** with the Part 3 theorem: `rw [loop_spec]`.

**R16 · `Nat.zero_add`** changes the **goal**. The lemma is `Nat.zero_add (n : Nat) : 0 + n = n`.

| Before | After |
|---|---|
| `⊢ P (0 + n)` | `⊢ P n` |

**W3, second half:** `len xs = xs.length` by R15, R4 with `len_run_eq`, R16:

```lean-goal
⊢ len xs = xs.length
⊢ len.run xs 0 = xs.length
```

---

## Traps

- Without `generalizing acc` the IH is `ih : P k acc` for the original `acc` only (R1, second table), and the
  step, which needs it at `k :: acc` (or `acc + x`), gets stuck.
- `generalizing` names variables that are already in the context: here the theorem's parameter `acc`. Do not
  `intro` anything first.
- `simp only [countdown]` unfolds the main function only. The helper `countdown.go` has its own equations and
  must be named: `simp only [countdown.go]`. Unfolding a helper at a symbolic `n` (not `0` or `k + 1`) makes no
  progress: that is what the invariant is for.
- `rw [ih]` before unfolding fails: the goal has `countdown.go (k + 1) acc`, while `ih` is about
  `countdown.go k _`. Unfold one step first (R3, R11); then the call is at `k` (or the tail) and `rw` reads the
  new accumulator off it.
- `l ++ x :: acc` is `l ++ (x :: acc)`, not `(l ++ [x]) ++ acc`; the two agree only after R6 and R7.
- `grind`, `try?` and `exact?` are banned.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction, IH for every accumulator | `induction n generalizing acc with \| zero => … \| succ k ih => …` | R1 |
| base case that computes | `rfl` | R2 |
| one step of a `where` / `let rec` helper | `simp only [f.aux]` / `simp only [g.run]` | R3, R11 |
| use the IH (or a theorem) at a new accumulator | `rw [ih]` / `rw [thm]` | R4 |
| `List.range (n + 1)` → `List.range n ++ [n]` | `rw [List.range_succ]` | R5 |
| regroup `l ++ [x] ++ acc` → `l ++ x :: acc` | `rw [List.append_assoc, List.singleton_append]` | R6, R7 |
| main function → helper call | `simp only [f]` | R8, R15 |
| `l ++ []` → `l` | `rw [List.append_nil]` | R9 |
| list induction, IH for every accumulator | `induction xs generalizing acc with \| nil => … \| cons x xs ih => …` | R10 |
| `[].sum` → `0`, `(a :: l).sum` → `a + l.sum` | `rw [List.sum_nil]`, `rw [List.sum_cons]` | R12, R13 |
| regroup `+` | `omega` | R14 |
| `0 + n` → `n` | `rw [Nat.zero_add]` | R16 |
| all of a step at once | `simp [helper, ih, lemmas]` | R3–R7, R11–R13 |
| see the state | infoview | |
