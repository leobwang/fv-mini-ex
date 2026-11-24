# E023 · Implicit arguments: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E022, in particular `exact` and `apply` (E003), term-mode proofs (E004), `rw` (E009) and
`have` (E021).
**New here:** how arguments are passed. A binder in curly braces, `{n : Nat}`, is **implicit**: you do not
write that argument; Lean infers it by **unification**, i.e. by matching the types of the arguments you do
write (and the goal) against the lemma's statement. A binder in parentheses, `(h1 : a ≤ b)`, is
**explicit**: you write it. Three ways to take control:

- `L (m := b)`: a **named argument** sets the argument whose binder is called `m`, implicit or not.
- `@L`: the **`@` prefix** turns every implicit binder of `L` into an explicit one, so `@L a b c h1 h2`
  passes all five arguments in order; `_` in a slot asks Lean to infer that one.
- Hypotheses can have implicit binders too: `h : ∀ {n : Nat}, f n = n`, used as `@h 3 : f 3 = 3`.

`#check @L` prints `L`'s full signature with all binders and their names; use it to look up the names for
`(name := …)` and the order for `@`.

## How to read an entry

Each entry is one way to use a lemma or hypothesis. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `L` is the core lemma `Nat.lt_of_lt_of_le : ∀ {n m k : Nat}, n < m → m ≤ k → n < k` (it stands in for
  the exercise's `my_le_trans`, which has the same shape with `≤` twice).
- `{α : Type}` is any type; `P : α → Prop` is "the rest of the goal": the step changes only what is inside
  `P (…)`.
- A hypothesis `k` only finishes the example. "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{a b c : Nat}` in a signature | three implicit arguments: Lean infers them, you do not write them |
| `(h1 : a ≤ b)` in a signature | an explicit argument: a proof of `a ≤ b` you must pass |
| `∀ {n : Nat}, f n = n` | a hypothesis whose `n` is implicit: `h` alone means "at an `n` Lean will infer" |
| `∀ (a b c : Nat), …` | the same quantifier with explicit binders: a function you feed `a b c` |
| `@my_le_trans` | `my_le_trans` with all binders made explicit; its type has `(…)` where the original has `{…}` |
| `?m`, `?b` | a **metavariable**: an argument Lean has not been able to infer yet, named after its binder (`?b` for `my_le_trans`'s `{b}`); a later step fills it in |
| `case h1`, `case b` | labels of the goals `apply` makes, named after the binder: a premise (`h1`) or a missing argument (`b`). An unnamed premise, as in `Nat.lt_of_lt_of_le`, is labelled `case a` |
| `e1.trans e2` | dot notation: `e1 : x = y` has type `Eq …`, so this is `Eq.trans e1 e2` |

---

## Part 0 · `my_le_trans` (given, nothing to fill)

Statement: `{a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c`. It is already proved (by the core lemma
`Nat.le_trans`). The four parts below *use* it. Its `a b c` are implicit, so `my_le_trans h1 h2` needs only
the two proofs.

## Part 1 · `use_inferred`

Statement: from `h1 : x ≤ 5` and `h2 : 5 ≤ 7`, conclude `x ≤ 7`. Pass the two proofs and let Lean infer
`a b c` (R1).

**R1 · `exact L h1 h2`** **closes** the goal. Only the explicit arguments are written; Lean unifies
`n < m` with the type of `h1` (`a < b`, so `n := a`, `m := b`) and `m ≤ k` with the type of `h2`
(`k := c`). Placeholders: `(a b c : Nat) (h1 : a < b) (h2 : b ≤ c)`. In term mode you write the same thing
without `exact`.

| Before | After |
|---|---|
| `h1 : a < b, h2 : b ≤ c ⊢ a < c` | no goals |

## Part 2 · `use_named`

Statement: from `h1 : 2 ≤ 4` and `h2 : 4 ≤ 9`, conclude `2 ≤ 9`. The point is to write the middle number
yourself, by the binder's name (R2); R3 is the all-explicit alternative.

**R2 · `apply L (m := b)`** changes the **goal list**: with the middle argument named, `apply` matches the
conclusion `n < k` against `a < c` and leaves one goal per premise. The name `m` is the binder name in
`L`'s signature (in `my_le_trans` the middle one is called `b`). Placeholders: `(a b c : Nat)`. As a term,
`L (m := b) h1 h2` closes the goal at once.

| Before | After |
|---|---|
| `⊢ a < c` | `⊢ a < b`, `⊢ b ≤ c` |

Without the name, `apply L` cannot see `m` in the goal `a < c` and leaves it as a hole `?m` (W1):

| Before | After `apply Nat.lt_of_lt_of_le` | After `exact h1` |
|---|---|---|
| `⊢ a < c` | `⊢ a < ?m`, `⊢ ?m ≤ c`, `⊢ Nat` | `⊢ b ≤ c` |

`exact h1` fills `?m := b`, which also closes the third goal (`Nat`, "which number is `?m`?").

**R3 · `exact @L a b c h1 h2`** **closes** the goal. After `@`, the implicit arguments are passed in
signature order, then the explicit ones. `@L _ b _ h1 h2` writes only `m` and lets Lean infer the `_`s.
Placeholders: `(a b c : Nat) (h1 : a < b) (h2 : b ≤ c)`.

| Before | After |
|---|---|
| `h1 : a < b, h2 : b ≤ c ⊢ a < c` | no goals |

## Part 3 · `use_explicit`

Statement: `∀ (a b c : Nat), a ≤ b → b ≤ c → a ≤ c`. This is `my_le_trans`'s statement with `(…)` in place
of `{…}`: exactly the type of `@my_le_trans` (R4).

**R4 · `exact @L`** **closes** a `∀`-goal with explicit binders that is `L`'s statement. `@L` with no
arguments is the function of all five arguments. Plain `exact L` fails here: Lean replaces `n m k` by holes
at once and gets `?n < ?m → ?m ≤ ?k → ?n < ?k`, which is not the `∀ (n m k : Nat), …` the goal asks for
("Type mismatch"). Placeholders: none.

| Before | After |
|---|---|
| `⊢ ∀ (n m k : Nat), n < m → m ≤ k → n < k` | no goals |

Alternative: `intro a b c h1 h2` (E003) turns the goal into Part 1's shape, then R1.

## Part 4 · `hyp_implicit`

Statement: from `h : ∀ {n : Nat}, f n = n`, conclude `f (f 3) = 3`. Get `f 3 = 3` from `h` (R5); apply `f` to
both sides (R6) to get `f (f 3) = f 3`; chain the two equations (R7). Or rewrite with `@h 3` twice (R8).

**R5 · `have k := @h a`** changes the **context**: `@h a` is `h` at `x := a`. Placeholders:
`{α : Type} (P : α → Prop) (h : ∀ {x : α}, P x) (a : α)`; `h` stays in the context. `h (x := a)` is the
same by name. Plain `h` with nothing to infer `x` from (as in `have k := h`) leaves `x` unknown.

| Before | After |
|---|---|
| `a : α ⊢ P a` | `k : P a ⊢ P a` |

**R6 · `congrArg g e`** changes the **context** here (`have k := congrArg g e`). The lemma is
`congrArg : ∀ {α β} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂`: applying a function to both sides of
an equation. The function is explicit, the two sides are implicit. Placeholders:
`{α β : Type} (g : α → β) (x y : α) (e : x = y)`.

| Before | After |
|---|---|
| `e : x = y ⊢ g x = g y` | `k : g x = g y ⊢ g x = g y` |

**R7 · `exact e1.trans e2`** **closes** `x = z`. The lemma is `Eq.trans : ∀ {α} {a b c : α}, a = b → b = c →
a = c`, every argument but the two proofs implicit; the middle `y` must be the same expression in both.
Placeholders: `{α : Type} (x y z : α) (e1 : x = y) (e2 : y = z)`.

| Before | After |
|---|---|
| `e1 : x = y, e2 : y = z ⊢ x = z` | no goals |

**R8 · `rw [@h a]`** changes the **goal**: `@h a : f a = a`, so every `f a` becomes `a`. Placeholders:
`{α : Type} (f : α → α) (h : ∀ {x : α}, f x = x) (a : α) (P : α → Prop)`. `rw` closes the goal by itself
when it ends as `t = t` (E009). Plain `rw [h]` also works: `rw` fills `x` with the first `f _` it meets,
reading from the outside in.

| Before | After |
|---|---|
| `⊢ P (f a)` | `⊢ P a` |

**W3** (R5, R6 twice, R7) on an involution `g`, `hg : ∀ {x : α}, g (g x) = x`, proving
`g (g (g (g a))) = a`:

| Step | State |
|---|---|
| start | `⊢ g (g (g (g a))) = a` |
| `have k1 := @hg a` | `k1 : g (g a) = a ⊢ g (g (g (g a))) = a` |
| `have k2 := congrArg g (congrArg g k1)` | `k2 : g (g (g (g a))) = g (g a) ⊢ g (g (g (g a))) = a` |
| `exact k2.trans k1` | no goals |

---

## Traps

- Binder names are part of the lemma: `my_le_trans (m := 4)` fails because its middle binder is `b`.
  `#check @my_le_trans` shows the names.
- `@` makes **every** implicit argument explicit, in order. `@my_le_trans 4 h1 h2` is wrong: `4` lands in
  `a`'s slot and `h1` in `b`'s. Write `_` for the ones you skip: `@my_le_trans _ 4 _ h1 h2`.
- `exact my_le_trans` on a goal `∀ (a b c : Nat), …` is a type mismatch (R4): the implicit arguments are
  filled with holes before the comparison. Use `@my_le_trans`.
- `congrArg f (@h 3)` has type `f (f 3) = f 3`, not `f (f 3) = 3`: one more step (R7) is needed.
- `omega`, `grind` and `simp` are banned: the point is to pass the arguments yourself.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use a lemma, let Lean infer `{…}` | `L h1 h2` / `exact L h1 h2` | R1 |
| set one implicit argument | `L (m := b) h1 h2` / `apply L (m := b)` | R2 |
| pass every argument | `@L a b c h1 h2`, `_` to skip one | R3 |
| goal is `L`'s statement with `(…)` binders | `@L` / `exact @L` | R4 |
| instantiate `h : ∀ {x}, P x` at `a` | `@h a` or `h (x := a)` | R5 |
| `x = y` → `g x = g y` | `congrArg g e` | R6 |
| chain `x = y` and `y = z` | `e1.trans e2` (`Eq.trans e1 e2`) | R7 |
| rewrite with an implicit hypothesis | `rw [@h a]` (or `rw [h]`) | R8 |
| see all binders of `L` | `#check @L` | |
| see the state | infoview (cursor after a tactic) | |
