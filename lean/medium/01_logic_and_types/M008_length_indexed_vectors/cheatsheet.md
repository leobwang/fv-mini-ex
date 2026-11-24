# M008 · Length-indexed vectors: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, `def` by `match`, structural recursion,
`List`, `induction`, `simp`, `rfl`, `exact`. **New here:** an *indexed* inductive family (`Vec α n`, where the
length `n` is part of the type), *dependent* pattern matching on it (each branch sees the index refined), and
index arithmetic that must hold by computation. Core Lean only, no Mathlib.

## The objects

- **`Vec α n`**: a list of elements of `α` whose length `n : Nat` is an *index* of the type. `α` is a
  *parameter* (the same in every constructor); `n` is not: `nil : Vec α 0` and
  `cons x xs : Vec α (n + 1)` when `xs : Vec α n`. So `Vec α 3` and `Vec α 4` are different types.
- **`Vec.toList`** (given): forgets the length.
- **Holes:** `head : Vec α (n + 1) → α` (total: no empty case exists), `map f : Vec α n → Vec β n` and
  `append : Vec α n → Vec α m → Vec α (m + n)`; then four theorems relating them to `List`.
- The guide teaches on a toy family `Bits n` (exactly `n` booleans; constructors `e : Bits 0` and
  `b bit rest : Bits (n + 1)`) with functions `toList`, `tail`, `flip` (negate every bit) and `pad`.
  These are **not** the exercise's objects.

## How to read an entry

Each entry is one tactic, one construct used in a `def`, or one lemma used with `rw`/`simp`. It says what
changes (**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. `∅` means
  the goal is closed.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Nat → Type` when it builds a type). The step changes
  only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders: `{α : Type}` is any type, `{n : Nat}` any length.
- A `def` is not a proof, but its body is built like one: `refine match v with | … => ?_` in the guide turns
  each `match` branch into a goal, so you can see what each branch of your `def` must produce.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Vec α n`, `Bits n` | a vector (bit string) of length exactly `n` |
| `Vec.nil`, `Vec.cons x xs` | the constructors; in a pattern or with a known expected type write `.nil`, `.cons x xs` |
| `v.toList` | `Vec.toList v` (dot notation: `v`'s type names the namespace) |
| `Vec.map f v` | `v.map f`; Lean prints the prefix form because the first explicit argument is `f`, not `v` |
| `v.append w`, `Bits.pad k v` | `Vec.append v w`, `v.pad k` |
| `n✝`, `x✝`, `xs✝`, `xs_ih✝` | inaccessible names made by `induction`/`match`; name them with `with \| cons x xs ih` |
| `n n✝ : Nat` (in `case cons`) | two numbers: the old `n`, now unrelated to the goal, and the length `n✝` of `xs` |
| `List.map f l` | `l.map f` |
| `a :: l`, `l₁ ++ l₂` | list cons and append; `a :: as ++ bs` means `(a :: as) ++ bs` (`::` binds tighter) |
| `!b` | Boolean negation (guide only) |
| `case nil`, `case cons` | the goal for that constructor after `induction` |

---

## Part 1 · `Vec.head`

Statement: from `v : Vec α (n + 1)` return its first element. Write the body as a `match` with one branch.

**R1 · `match v with | .b bit rest => …`** (index `n + 1`) changes the **goal list and the context**: one
branch, whose context gains the constructor's fields. The `nil`-like constructor has index `0`, and `0` never
equals `n + 1`, so a single `cons` branch is a complete match. Placeholders: `{n : Nat} (v : Bits (n + 1))`.

| Before | After `refine match v with \| .b bit rest => ?_` |
|---|---|
| `v : Bits (n + 1) ⊢ Bits n` | `bit : Bool, rest : Bits n ⊢ Bits n` |

## Part 2 · `Vec.map`

Statement: apply `f : α → β` to every element; the length is unchanged (`Vec α n → Vec β n`). Recurse on `v`.

**R2 · `match v with | .e => … | .b bit rest => …`** (index `n`) changes the **goal list**: two branches, and
in each the result type's index is *refined* to that constructor's index. `n✝` is the constructor's implicit
`{n}`. Placeholders: `{n : Nat} (v : Bits n)`.

| Before | After (branch `e`) | After (branch `b`) |
|---|---|---|
| `v : Bits n ⊢ Bits n` | `⊢ Bits 0` | `n✝ : Nat, bit : Bool, rest : Bits n✝ ⊢ Bits (n✝ + 1)` |

**R3 · `.e`, `.b x r`** **close** the goal: constructor dot notation. `.b x r` means `Bits.b x r`; Lean reads the
namespace `Bits` off the expected type and infers the implicit index from `r`. In the exercise: `.nil`,
`.cons y ys`. Placeholders: `{n : Nat} (x : Bool) (r : Bits n)`.

| Before | After `exact .b x r` |
|---|---|
| `r : Bits n ⊢ Bits (n + 1)` | `∅` |

**R4 · the recursive call `rest.flip`** **closes** the goal of the `b` branch. `rest.flip` is `Bits.flip rest`.
Inside the definition of `flip` this call is allowed because `rest` is a sub-term of `v` (structural recursion);
it has the smaller index `n✝`, and `.b` lifts it back to `n✝ + 1`. Calling the function on `v` itself would
not terminate and is rejected. Placeholders: `{n : Nat} (bit : Bool) (rest : Bits n)`.

| Before | After `exact .b (!bit) rest.flip` |
|---|---|
| `rest : Bits n ⊢ Bits (n + 1)` | `∅` |

## Part 3 · `Vec.append`

Statement: `append v w : Vec α (m + n)` for `v : Vec α n`, `w : Vec α m`. Recurse on `v` (R2, R3, R4); the
branches type-check only because of R5.

**R5 · `show T'`** changes the **goal** to a *definitionally equal* one (equal by computation), and fails
otherwise. It makes visible why the branch types fit: `Nat.add` recurses on its **second** argument, so
`m + 0` computes to `m` and `m + (n + 1)` computes to `(m + n) + 1`. In `append`, the `nil` branch must build a
`Vec α (m + 0)` (and `w : Vec α m` is one), and the `cons` branch a `Vec α (m + (n✝ + 1))` (and
`.cons x (xs.append w) : Vec α (m + n✝ + 1)` is one). Placeholders: `(m n : Nat) (P : Nat → Type)`.

| Before | After `show P (m + n + 1)` |
|---|---|
| `x : P (m + n + 1) ⊢ P (m + (n + 1))` | `x : P (m + n + 1) ⊢ P (m + n + 1)` |

| Before | After `show P m` |
|---|---|
| `x : P m ⊢ P (m + 0)` | `x : P m ⊢ P m` |

The first argument does not compute: `(n + 1) + m` is **not** `(n + m) + 1` by computation (only by the lemma
`Nat.succ_add`). That is why the spec says `m + n` (see Traps).

**W1** in the guide defines `Bits.pad k v : Bits (n + k)` the same way: `| 0, v => v` and
`| k + 1, v => .b false (v.pad k)`, both accepted by R5's computation.

## Part 4 · `head_cons`

Statement: `(Vec.cons x v).head = x`.

**R6 · `rfl`** **closes** an equation that holds by computation. A `def` by `match` applied to a constructor
reduces by its matching branch, so `(Bits.b x r).tail` is `r`. It also closes the base cases of Parts 5–7:
`Bits.e.toList` computes to `[]`, `[].length` to `0`, `[] ++ l` to `l`. Placeholders: `{n : Nat} (x : Bool)
(r : Bits n) (w : Bits n)`.

| Before | After `rfl` |
|---|---|
| `⊢ (Bits.b x r).tail = r` | `∅` |
| `⊢ Bits.e.toList ++ w.toList = w.toList` | `∅` |

## Part 5 · `toList_length`

Statement: `v.toList.length = n`: forgetting the length gives a list of that length. Induction on `v`,
`rfl` for `nil`, unfold and use the IH for `cons`.

**R7 · `induction v`** changes the **goal list and the context**: one goal per constructor, the index refined in
each (`0` for `e`, `n✝ + 1` for `b`), plus the induction hypothesis for the recursive field. `P` is the
statement and may mention the index. Write `induction v with | e => … | b bit rest ih => …` to name the
fields (in the exercise: `| nil => … | cons x xs ih => …`; the implicit `{n}` gets no name). Placeholders:
`(P : (n : Nat) → Bits n → Prop) {n : Nat} (v : Bits n)`. (In the unnamed version of the guide example,
`‹_›` means "the hypothesis in the context whose type fits here", used because `rest_ih✝` cannot be typed.)

| Before | After (case `e`) | After (case `b`) |
|---|---|---|
| `v : Bits n ⊢ P n v` | `⊢ P 0 Bits.e` | `rest_ih✝ : P n✝ rest✝ ⊢ P (n✝ + 1) (Bits.b bit✝ rest✝)` |

In the exercise, after `induction v with | nil => … | cons x xs ih => …`, the `cons` case of
`toList_length` is

```
n n✝ : Nat
x : α
xs : Vec α n✝
ih : xs.toList.length = n✝
⊢ (Vec.cons x xs).toList.length = n✝ + 1
```

The outer `n` stays in the context but is no longer connected to the goal; the vector's length is `n✝`.
The `nil` case is `⊢ Vec.nil.toList.length = 0` (R6).

**R8 · `simp only [Bits.toList]`** changes the **goal**: it rewrites a `def` applied to a constructor by that
definition's matching equation. In the exercise name every function you need unfolded: `Vec.toList`, and
`Vec.map` or `Vec.append`. Placeholders: `{n : Nat} (x : Bool) (r : Bits n) (P : List Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Bits.b x r).toList` | `⊢ P (x :: r.toList)` |

In `toList_length` this turns `(Vec.cons x xs).toList.length` into `(x :: xs.toList).length`.

R9–R11 are core `List` lemmas that `simp` applies by itself; you never need to name them, but they are the
steps between the unfolded goal and the IH (and you can apply them one at a time with `rw` to watch).
Placeholders: `{α β : Type} (f : α → β) (a : α) (l as bs : List α)`.

**R9 · `List.length_cons`** changes the **goal**. Statement: `(a :: l).length = l.length + 1`.

| Before | After |
|---|---|
| `⊢ P (a :: l).length` | `⊢ P (l.length + 1)` |

In `toList_length` the goal becomes `xs.toList.length + 1 = n✝ + 1`, and the left part is the IH's left side.

**R12 · `simp [ih]`** **closes** the goal: it rewrites with the hypothesis `ih : l = l'` left to right, then
both sides agree. In the exercise one call does R8, the list lemma and R12 at once:
`simp [Vec.toList, …, ih]`. Placeholders: `{α : Type} (a : α) (l l' : List α)`.

| Before | After |
|---|---|
| `ih : l = l' ⊢ a :: l = a :: l'` | `∅` |

## Part 6 · `toList_map`

Statement: `(v.map f).toList = v.toList.map f`: mapping then forgetting equals forgetting then mapping.
Same shape as Part 5 (R7, R6, R8, R12); unfold both `Vec.map` and `Vec.toList`. After unfolding, the `cons`
goal is `f x :: (Vec.map f xs).toList = List.map f (x :: xs.toList)`, and R10 moves `f` inside the right side.

**R10 · `List.map_cons`** changes the **goal**. Statement: `(a :: l).map f = f a :: l.map f`.

| Before | After |
|---|---|
| `⊢ P (List.map f (a :: l))` | `⊢ P (f a :: List.map f l)` |

## Part 7 · `toList_append`

Statement: `(v.append w).toList = v.toList ++ w.toList`. Same shape again; only `v` is inducted on and `w`
stays fixed, so no `generalizing` is needed. After unfolding `Vec.append` and `Vec.toList`, the `cons` goal is
`x :: (xs.append w).toList = x :: xs.toList ++ w.toList`, which reads `x :: … = (x :: xs.toList) ++ w.toList`.

**R11 · `List.cons_append`** changes the **goal**. Statement: `(a :: as) ++ bs = a :: (as ++ bs)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**W2** (`v.flip.flip = v`) and **W3** (`(v.pad k).toList = List.replicate k false ++ v.toList`, induction on
`k`) in the guide run the whole pattern: induction, `rfl` for the base case, `simp [definitions, ih]` for the
step. `List.replicate k a` is the list of `k` copies of `a`; W3 also hands `simp` the core lemma
`List.replicate_succ : List.replicate (k + 1) a = a :: List.replicate k a`.

---

## Traps

- `append`'s type is `Vec α (m + n)`, **not** `n + m`. With `n + m` both branches fail, because the first
  argument of `+` does not compute (R5): the `nil` branch with `w has type Vec α m but is expected to have type
  Vec α (0 + m)`, the `cons` branch with `… has type Vec α (n✝ + m + 1) but is expected to have type
  Vec α (n✝ + 1 + m)`.
- In `head`, a `| .nil => …` branch is an error (`Type mismatch: Vec.nil has type Vec ?m 0 but is expected to
  have type Vec α (n + 1)`; `?m` is a not-yet-known type). Leave it out; the match is complete without it (R1).
- The recursive call goes on the field `xs`, never on `v` (R4).
- `simp [ih]` alone does not unfold your definitions; name them (`simp [Vec.toList, Vec.map, ih]`), or `simp`
  fails with `simp made no progress` on `(Vec.cons x xs).toList.length = n✝ + 1` (R8). Without `ih` it stops
  at `xs.toList.length = n✝`.
- `induction v with | cons x xs ih`: three names for `x`, `xs` and the IH; the implicit length `{n}` is not
  listed.
- The index of `v` is available as a value: in `def Vec.len {n : Nat} (_ : Vec α n) : Nat := n`, `n` is just
  an argument. You never need to compute a length.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| total function on non-empty vectors | `match v with \| .cons x _ => …` (no `nil` branch) | R1 |
| recurse over a vector | `match v with \| .nil => … \| .cons x xs => …` | R2 |
| build a vector | `.nil`, `.cons y ys` | R3 |
| recursive call | `xs.map f`, `xs.append w` (on the field `xs`) | R4 |
| why `m + (n + 1)` fits `(m + n) + 1` | `Nat.add` recurses on its 2nd argument; `show` to check | R5 |
| equation true by computation | `rfl` | R6 |
| prove a fact for every vector | `induction v with \| nil => … \| cons x xs ih => …` | R7 |
| unfold a definition on a constructor | `simp [Vec.toList, Vec.map]` | R8 |
| list facts on `::` | applied by `simp` | R9–R11 |
| use the IH | `simp [defs, ih]` | R12 |
| see the state | the infoview, cursor after a tactic | [TACTIC_STATES.md](../../../TACTIC_STATES.md) |
