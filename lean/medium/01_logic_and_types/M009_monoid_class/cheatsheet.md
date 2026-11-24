# M009 · A monoid class with laws: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rfl`, `decide`, `rw`, `simp only`,
`omega`, structural recursion on lists. **New here:** a `class` whose fields include proofs (laws), building an
`instance` of it (data fields plus one proof per law), how a class operation such as `MyMonoid.op` resolves to
the instance's field, proofs that hold in *every* instance (`{α : Type} [MyMonoid α]`), `induction` on a list,
and the core lemmas `List.nil_append`, `List.cons_append`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `MyMonoid.op a b` | the instance's `op` applied to `a`, `b` (for `Nat`: your `max a b`) |
| `MyMonoid.unit` | the instance's `unit` (for `Nat`: your `0`) |
| `[MyMonoid α]` | instance-implicit argument: "some instance of `MyMonoid α`", found by Lean, not passed by you |
| `inst✝ : MyMonoid α` | that instance in the context; `✝` marks a name you cannot type |
| `[]`, `[3, 1, 4, 1, 5]` | the empty list; a list literal, `3 :: 1 :: 4 :: 1 :: 5 :: []` |
| `x :: xs` | the list with head `x` and tail `xs` |
| `xs ++ ys` | `List.append`: `xs` followed by `ys` |
| `x :: xs ++ ys` | `(x :: xs) ++ ys`: `++` (append) binds weaker than `::` (R9) |
| `case nil`, `case cons` | the two goals after `induction xs` (R7) |
| `case refine_1`, `case refine_2` | the first, second `?_` goal after `refine` (R1) |
| `max a b`, `min a b` | maximum, minimum (`omega` understands both, R3) |
| `∀ (a b c : Nat), …` | how Lean prints a law field's obligation `∀ a b c : Nat, …` |

### Classes, instances, laws

A `class C (α : Type) where …` is a structure type indexed by `α`; its fields are the operations and, here,
the laws they must satisfy. A field whose type is a `Prop` (such as `∀ a, op unit a = a`) is a proof field:
an instance must prove it. `instance i : C T := …` builds one value of `C T` and registers it, so that
whenever Lean needs `C T` it finds `i` automatically (*type-class resolution*).

Each field becomes a global function or theorem with the instance as an instance-implicit argument `[self : C α]`
(R12):

| Field in `class Absorb` (guide) | Global name and type |
|---|---|
| `op : α → α → α` | `Absorb.op : {α : Type} → [self : Absorb α] → α → α → α` |
| `zero_op : ∀ a : α, op zero a = zero` | `Absorb.zero_op : ∀ {α : Type} [self : Absorb α] (a : α), Absorb.op Absorb.zero a = Absorb.zero` |

So `MyMonoid.op a b` with `a b : Nat` means "the `op` field of the `MyMonoid Nat` instance", which after your
instance is `max a b`; with `a b : α` and `[MyMonoid α]` it is an unknown operation that you only know through
the laws `MyMonoid.op_assoc`, `MyMonoid.unit_op`, `MyMonoid.op_unit`.

---

## Part 1 · `instMaxMonoid`

Statement: build `MyMonoid Nat` with `op := max` and `unit := 0`. The three proof fields become
`max (max a b) c = max a (max b c)`, `max 0 a = a` and `max a 0 = a`, each under `∀`.

**R1 · `refine { op := f, zero := z, op_comm := ?_, zero_op := ?_ }`** changes the **goal list**: the goal
`Absorb α` becomes one goal per proof field left as `?_`, with the data you chose substituted for `op` and
`zero`. You do not need `refine` in the exercise; it only shows the obligations. They are the goals you see with
the cursor inside `op_assoc := by …`. Placeholders: `{α : Type} (f : α → α → α) (z : α)`.

| Before | After |
|---|---|
| `⊢ Absorb α` | `⊢ ∀ (a b : α), f a b = f b a`, `⊢ ∀ (a : α), f z a = z` |

**R2 · `intro a b`** changes the **context and the goal**: the `∀`-bound variables become hypotheses.
Placeholders: `(Q : Nat → Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (a b : Nat), Q a b` | `a b : Nat ⊢ Q a b` |

**R3 · `omega`** **closes** a goal of linear arithmetic (`+`, `-`, `*` by a literal, `<`, `≤`, `=`) over `Nat`
and `Int`, and it knows `max` and `min`. Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `a b : Nat ⊢ max a b = max b a` | no goals |
| `a b : Nat ⊢ min a (max a b) = a` | no goals |

**R4 · `instance name : C T where …`** declares the instance: one line `field := value` per field, a
`by intro …; omega` block (R2, R3) for each law. The exercise's spec line already ends in `:=`, so there you write
the same fields as a term in braces, `{ op := …, unit := …, op_assoc := by …, … }` (one field per line, or
separated by `,`); `where` cannot follow `:=`.

---

## Part 2 · `op_is_max`

Statement: `MyMonoid.op a b = max a b` for `a b : Nat`.

**R5 · `rfl`** **closes** `C.op a b = g a b` when the instance found for that type has `op := g`: Lean unfolds
the projection of the instance to its field and sees the same term on both sides. Placeholders: `(a b : Nat)`,
the guide instance `instMinAbsorb` with `op := min`.

| Before | After |
|---|---|
| `a b : Nat ⊢ Absorb.op a b = min a b` | no goals |

---

## Part 3 · `mconcat_example`

Statement: `mconcat [3, 1, 4, 1, 5] = 5`. `mconcat` folds the list with `op` from `unit`; with your instance it
computes `max 3 (max 1 (… (max 5 0)))`.

**R6 · `rfl` / `decide`** **closes** an equation between closed terms (no variables) by evaluating both sides,
through the instance's fields and recursive definitions alike. `decide` evaluates a decidable proposition to
`true`.

| Before | After |
|---|---|
| `⊢ Absorb.op (Absorb.op 5 3) 8 = 3` | no goals |
| `⊢ List.foldr min 9 [4, 2, 7] = 2` | no goals |

---

## Part 4 · `mconcat_append`

Statement: in every `MyMonoid α`, `mconcat (xs ++ ys) = MyMonoid.op (mconcat xs) (mconcat ys)`. Here `op` is
unknown: only the laws are available. Induct on `xs`: `[] ++ ys` and `(x :: xs) ++ ys` both simplify, while
`ys` stays fixed.

**R7 · `induction xs with | nil => … | cons x xs ih => …`** changes the **goal list and the context**: one goal
per constructor of `List`. In `cons`, `x` is the head, `xs` the tail, and `ih` the statement for the tail.
Placeholders: `{α : Type} (P : List α → Prop) (xs : List α)`.

| Before | After |
|---|---|
| `xs : List α ⊢ P xs` | `⊢ P []`, `x : α, xs : List α, ih : P xs ⊢ P (x :: xs)` |

**R8 · `rw [List.nil_append]`** changes the **goal**. The lemma is
`List.nil_append : ∀ {α : Type u_1} (as : List α), [] ++ as = as`. Placeholders: `{α : Type} (ys : List α)`.

| Before | After |
|---|---|
| `⊢ P ([] ++ ys)` | `⊢ P ys` |

**R9 · `rw [List.cons_append]`** changes the **goal**. The lemma is
`List.cons_append : ∀ {α : Type u_1} {a : α} {as bs : List α}, a :: as ++ bs = a :: (as ++ bs)`: the head moves
out of the append. Placeholders: `{α : Type} (x : α) (xs ys : List α)`.

| Before | After |
|---|---|
| `⊢ P (x :: xs ++ ys)` | `⊢ P (x :: (xs ++ ys))` |

**R10 · `simp only [f]`** changes the **goal**: it rewrites with the defining equations of `f` where the argument
is literally `[]` or `_ :: _`. For `mconcat` these are `mconcat [] = MyMonoid.unit` and
`mconcat (x :: xs) = MyMonoid.op x (mconcat xs)`. `mconcat xs` with a variable `xs` is left alone.
Placeholders: `(x : Nat) (xs : List Nat)`, the guide function `total` (`total [] = 0`,
`total (x :: xs) = x + total xs`).

| Before | After |
|---|---|
| `⊢ P (total []) ∧ P (total (x :: xs))` | `⊢ P 0 ∧ P (x + total xs)` |

**R11 · `rw [ih]`** changes the **goal**: the induction hypothesis is an equation, so it rewrites like a lemma.
Its left side must appear literally: in the exercise that is `mconcat (xs ++ ys)`, which appears only after R9
and R10. Placeholders: `{α β : Type} (f : List α → β) (b : β) (ih : f xs = b)`.

| Before | After |
|---|---|
| `ih : f xs = b ⊢ P (f xs)` | `ih : f xs = b ⊢ P b` |

**R12 · `rw [C.law]`** changes the **goal**: a law of the class is a theorem valid in every instance, so it
rewrites inside a generic proof exactly like a library lemma. Arguments can be omitted (Lean finds the first
match) or given to pick an occurrence: `rw [MyMonoid.op_assoc a b c]`. `simp [MyMonoid.op_assoc]` also works,
and rewrites every occurrence. Placeholders: `{α : Type} [Absorb α] (a : α)`.

| Before | After |
|---|---|
| `inst✝ : Absorb α ⊢ P (Absorb.op Absorb.zero a)` | `⊢ P Absorb.zero` |

In the exercise, after R8/R9, R10 and (in `cons`) R11, each case is one law away from `rfl`: `nil` needs
`MyMonoid.unit_op`, `cons` needs `MyMonoid.op_assoc` (it reassociates the right side). `rw` closes the goal by
`rfl` once both sides agree.

### Worked combinations (W1–W2, on `Absorb` and `total`)

**W1: a generic fact from two laws.** `Absorb.op a Absorb.zero = Absorb.zero` in every instance:
`rw [Absorb.op_comm a Absorb.zero]` (R12 with explicit arguments), then `rw [Absorb.zero_op]` (R12).

| Before | After `rw [Absorb.op_comm a Absorb.zero]` |
|---|---|
| `⊢ Absorb.op a Absorb.zero = Absorb.zero` | `⊢ Absorb.op Absorb.zero a = Absorb.zero` |

**W2: `total (xs ++ ys) = total xs + total ys`.** Start from

```lean-goal
⊢ total (xs ++ ys) = total xs + total ys
```

then `induction xs with` (R7). Case `nil`: `rw [List.nil_append]` (R8), `simp only [total]` (R10), `omega`
(R3) on `total ys = 0 + total ys`. Case `cons`: `rw [List.cons_append]` (R9), `simp only [total]` (R10),
`rw [ih]` (R11), `omega` on `x + (total xs + total ys) = x + total xs + total ys`. In the exercise the last step
is a class law (R12) instead of `omega`, since `op` is not `+`.

---

## Traps

- `omega` does not know your class: on `MyMonoid.op a b = …` it fails, because `MyMonoid.op a b` is an opaque
  term to it. Use it inside the instance's law fields, where `op` has already been replaced by `max`.
- `omega` also closes the law goals with the `∀` still in front; `intro` (R2) only makes them readable.
- `x :: xs ++ ys` is `(x :: xs) ++ ys`, not `x :: (xs ++ ys)`; `List.cons_append` (R9) converts the first into
  the second.
- `rw [ih]` fails until the goal literally contains `mconcat (xs ++ ys)`: unfold `mconcat` first (R9, R10).
- In the generic theorem, `rfl` and `decide` cannot help: `op` is unknown, so nothing computes. Only the laws do.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see a law's obligation | cursor inside `field := by …`, or `refine { …, law := ?_ }` | R1 |
| name the `∀` variables | `intro a b c` | R2 |
| a law about `max`/`min`/`+` on `Nat` | `omega` | R3 |
| declare the instance | `instance i : C T where f := v …` or `:= { f := v, … }` | R4 |
| `C.op a b = g a b` for a concrete type | `rfl` | R5 |
| closed computation | `rfl` / `decide` | R6 |
| induction on a list | `induction xs with \| nil => … \| cons x xs ih => …` | R7 |
| `[] ++ ys → ys` | `rw [List.nil_append]` | R8 |
| `x :: xs ++ ys → x :: (xs ++ ys)` | `rw [List.cons_append]` | R9 |
| unfold `f []`, `f (x :: xs)` | `simp only [f]` | R10 |
| use the IH | `rw [ih]` | R11 |
| use a law in a generic proof | `rw [C.law]` / `rw [C.law a b c]` / `simp [C.law]` | R12 |
| everything at once (cons case) | `simp [f, ih, C.law]` | R9–R12 |
| see the state | infoview | |
