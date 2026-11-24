# E019 · Add instance: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E018, in particular `rfl` (E001), `exact` and `apply` (E003), `⟨_, _⟩` for
`∧` (E004), `constructor` (E005), structures, projections `p.x`, structure-instance notation and
`dsimp only` (E017). **New here:** type classes and `instance` declarations, the classes `Add`/`Mul` behind
`+`/`*`, how `p + q` unfolds to your instance, the `@[ext]` attribute and its generated `T.ext` lemma, and
the core lemma `Int.add_comm`.

## How to read an entry

Each entry is one tactic, one term or one lemma. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P` is "the rest of your goal" (`P : Pair → Prop` or `P : Nat → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- The entries use the guide's structure `Pair` (fields `a b : Nat`, marked `@[ext]`) with the instance
  `instMulPair : Mul Pair := ⟨fun p q => ⟨p.a * q.a, p.b * q.b⟩⟩`. In the exercise, `V2` (fields
  `x y : Int`) plays the role of `Pair`, and `Add`/`+` the role of `Mul`/`*`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Type classes in one paragraph

A **type class** is a structure whose values Lean finds by itself. `Add α` has one field,
`add : α → α → α`; `Mul α` has one field `mul : α → α → α`. An **instance** is a declared value of a class,
`instance instAddV2 : Add V2 := …`; once it exists, Lean uses it whenever it needs `Add V2`. The notation
`p + q` is `HAdd.hAdd p q` (`HAdd α β γ` is the "heterogeneous" class for `+ : α → β → γ`), and Lean
builds `HAdd V2 V2 V2` from any `Add V2` (the core instance `instHAdd`). So `p + q` unfolds, by
definition, to `Add.add p q`, and then to the body of **your** instance. Without the instance,
`p + q` is an error: `failed to synthesize instance of type class HAdd V2 V2 ?m.3`.

## Reading the goals

| You see | It means |
|---|---|
| `@[ext] structure V2` | the attribute `@[ext]` makes Lean generate `V2.ext : x.x = y.x → x.y = y.y → x = y` (`{x y : V2}` implicit), used in R6 |
| `Add V2` (as the type of an `instance`) | you must build a value of the class: one function `V2 → V2 → V2` |
| `p + q` with `p q : V2` | `HAdd.hAdd p q`, i.e. `Add.add p q` with your instance `instAddV2` |
| `p.x + q.x` | addition of `Int`s (the fields are `Int`); a different `+`, from core |
| `(p + q).x` | the `x` field of the sum; reduces to whatever your instance stores there (R3–R5) |
| `Mul.mul p q` | the class function itself, what `p * q` unfolds to (R3) |
| `{ x := a, y := b }` | the value `V2.mk a b`, how `⟨a, b⟩` prints (E017) |
| `case x`, `case y` | after `apply V2.ext`: the goal for field `x`, for field `y` (R6) |
| `case left`, `case right` | after `constructor` on `A ∧ B`: the goal for `A`, for `B` (E005 R6) |
| `Int` | the integers (core Lean; no `ℤ` notation without Mathlib) |

---

## Part 1 · `instAddV2` (instance body)

Statement: `instAddV2 : Add V2`. You write the value after `:=`: a function that adds two vectors. What it
must compute is fixed by `add_fields`: coordinate-wise addition.

**R1 · `constructor` on `⊢ Mul α`** changes the **goal**: the class goal becomes the type of its one field,
a two-argument function. It shows what an instance body must contain. Placeholders:
`{α : Type} (f : α → α → α)`.

| Before | After |
|---|---|
| `f : α → α → α ⊢ Mul α` | `f : α → α → α ⊢ α → α → α` |

**R2 · `⟨f⟩`** is a **term** that **closes** `⊢ Mul α`: the anonymous constructor `Mul.mk f`, as for any
structure (E017). `{ mul := f }` names the field instead; for `Add` the field is `add`. In an instance body
`f` is a `fun p q => …` that builds the result, itself a structure value `⟨…, …⟩`. Placeholders:
`{α : Type} (f : α → α → α)`.

| Before | After |
|---|---|
| `f : α → α → α ⊢ Mul α` | no goals |

The guide then declares `instance instMulPair : Mul Pair := ⟨fun p q => ⟨p.a * q.a, p.b * q.b⟩⟩`, and from
that line on `p * q` type-checks for `p q : Pair`.

## Part 2 · `add_fields`

Statement: `(p + q).x = p.x + q.x ∧ (p + q).y = p.y + q.y`: each field of the sum is the sum of the fields.
Split the `∧` (generic: `⟨_, _⟩` or `constructor`, TACTIC_STATES "Structure"). Each half holds by
definition: `+` unfolds to your instance (R3), the instance body to a constructor value whose projection
reduces (R4). `rfl` does both (R5), so the term proof is a pair of `rfl`s.

**R3 · `dsimp only [HMul.hMul]`** changes the **goal**: the notation `p * q` becomes the class function
`Mul.mul p q`. For `+` the names are `HAdd.hAdd` and `Add.add`. Placeholders:
`(p q : Pair) (P : Pair → Prop)`.

| Before | After |
|---|---|
| `p q : Pair ⊢ P (p * q)` | `p q : Pair ⊢ P (Mul.mul p q)` |

**R4 · `dsimp only [Mul.mul]`** changes the **goal**: `Mul.mul p q` becomes the body of the instance,
`{ a := p.a * q.a, b := p.b * q.b }`, and `dsimp` reduces the projection `.a` of it at once (E017 R6).
Placeholders: `(p q : Pair) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Mul.mul p q).a` | `⊢ P (p.a * q.a)` |

**R5 · `rfl`** **closes** `(p * q).a = p.a * q.a`: both sides agree after unfolding `*` and the instance
and reducing the projection, which `rfl` does itself. You never need R3 and R4 in a proof; they show what
`rfl` sees. Placeholders: `(p q : Pair)`.

| Before | After |
|---|---|
| `p q : Pair ⊢ (p * q).a = p.a * q.a` | no goals |

## Part 3 · `add_comm_v2`

Statement: `p + q = q + p` for `p q : V2`. Two structures are equal when their fields are (R6). Each field
goal is an `Int` commutativity statement in disguise: it unfolds (R3, R4) to `p.x + q.x = q.x + p.x`, and
`exact` accepts a proof of that unfolded form directly (W1), so R7 closes it.

**R6 · `apply Pair.ext`** changes the **goal list**: one equation of structures becomes one equation per
field. The lemma is generated by the `@[ext]` attribute on the structure:
`Pair.ext : x.a = y.a → x.b = y.b → x = y`, with `{x y : Pair}` implicit (Lean infers them from the goal).
The goals are labelled by field name. The tactic `ext` does the same (W2). Placeholders:
`(x y : Pair) (ha : x.a = y.a) (hb : x.b = y.b)`.

| Before | After |
|---|---|
| `x y : Pair ⊢ x = y` | `⊢ x.a = y.a` (`case a`), `⊢ x.b = y.b` (`case b`) |

**R7 · `exact Int.add_comm a b`** **closes** the goal. The lemma is
`Int.add_comm (a b : Int) : a + b = b + a`; both arguments are explicit. Use `#check Int.add_comm` to see it.
Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `a b : Int ⊢ a + b = b + a` | no goals |

**W1: `exact` up to unfolding.** On `p * q = q * p` for `p q : Pair`, `apply Pair.ext` (R6) leaves goals
that still mention `*` on `Pair`, not on `Nat`:

```lean-goal
⊢ (p * q).a = (q * p).a
⊢ (p * q).b = (q * p).b
```

`exact Nat.mul_comm p.a q.a` (the `Nat` lemma `a * b = b * a`) closes the first anyway: `exact` checks the
proof's type against the goal up to unfolding definitions, and both unfold to `p.a * q.a = q.a * p.a`.
Naming the arguments (`p.a q.a`) states exactly which instance of the lemma you mean; `_ _` also works
here, since Lean finds them by unfolding the goal.

**W2:** the same proof with `ext` instead of `apply Pair.ext`, and `·` to focus each goal.

---

## Traps

- `V2`'s fields are `Int`, so the lemma is `Int.add_comm`, not `Nat.add_comm`.
- The `+` in `p + q` (on `V2`, your instance) and the `+` in `p.x + q.x` (on `Int`, core) are different
  functions that print the same. Rewriting with `Int.add_comm` directly on `p + q = q + p` fails: there is
  no `Int` addition in that goal until you split it with R6.
- `dsimp only [HAdd.hAdd]` unfolds **every** `+` in the goal, the `Int` ones too (they turn into
  `Add.add p.x q.x`, and after `dsimp only [Add.add]` into `p.x.add q.x`). That is why R3/R4 are shown inside
  `P (…)`; in a real proof use `rfl` (R5) instead.
- `apply V2.ext` exists only because of `@[ext]` on the structure. Without the attribute you would
  `cases p; cases q` and work on constructor values.
- The instance body is a term after `:=`: `⟨fun p q => ⟨…, …⟩⟩` (or `{ add := fun p q => … }`). The
  field order in the inner `⟨…, …⟩` is the declaration order, `x` then `y`.
- After `apply V2.ext` there are two goals: `exact …` closes only the first; give the second its own
  `exact` (or focus each with `·`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see what an instance must contain | `constructor` on an `Add V2` goal | R1 |
| an instance value | `⟨fun p q => ⟨…, …⟩⟩` or `{ add := fun p q => … }` | R2 |
| see `p + q` as the class function | `dsimp only [HAdd.hAdd]` | R3 |
| see the instance body | `dsimp only [Add.add]` | R4 |
| a field of a sum, by definition | `rfl` | R5 |
| split `A ∧ B` into two `rfl`s | `⟨rfl, rfl⟩` | TACTIC_STATES |
| structure equality → field equalities | `apply V2.ext` (or `ext`) | R6 |
| `a + b = b + a` in `Int` | `exact Int.add_comm a b` | R7 |
| a proof whose type matches after unfolding | `exact` (it unfolds) | W1 |
| see a lemma's statement | `#check Int.add_comm` | |
| see the state | infoview | |
