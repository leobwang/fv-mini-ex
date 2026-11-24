# E065 · contrapose! and by_contra!: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `exact`, `have`, `rw [h]`, applying a `∀`/`→` hypothesis to
arguments, `¬ p` as `p → False`, bounded quantifiers `∀ ε > 0, …` (E025).
**New here:** Mathlib's tactics `contrapose!`, `by_contra!`, `ring` (also E034), `linarith` (also E035), the lemma `lt_irrefl`, and the
real numbers `ℝ`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[LinearOrder α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- A hypothesis `g` in an example only finishes it: it shows what the goal became.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers. Literals such as `0`, `2` in a real goal are reals |
| `x ^ 2` | `x` squared (`^` with a natural-number exponent) |
| `a ≠ b` | `¬ (a = b)`, i.e. `a = b → False` |
| `¬ p` | `p → False` |
| `∀ ε > 0, P ε` | `∀ ε, ε > 0 → P ε`: apply it as `h e he` with `he : e > 0` |
| `∀ c < a, P c` | `∀ c, c < a → P c`: how Lean prints the hypothesis of `le_of_lt_imp`; apply it as `h e he` with `he : e < a` |
| `x / 2` | real division; `linarith` treats it as `(1/2) * x` |
| `a > b` | `b < a` (the same proposition, written the other way round) |
| `False` | the goal after `by_contra!`: derive a contradiction from the context |
| `this` | the name `have := …` gives a fact when you do not name it |
| `inst✝ : LinearOrder α` | the type-class assumption from a `[LinearOrder α]` binder, shown unnamed |

**What `!` does.** Both tactics run `push_neg` on the new negation: they push `¬` inward until it sits on an atom
and then remove it where a positive form exists.

| Negation | Becomes |
|---|---|
| `¬ (a ≠ b)` | `a = b` |
| `¬ (a = b)` | `a ≠ b` |
| `¬ (a < b)` | `b ≤ a` (in a linear order: `ℕ`, `ℤ`, `ℝ`) |
| `¬ (a ≤ b)` | `b < a` |
| `¬ (∀ x, P x)` | `∃ x, ¬ P x` |
| `¬ (P → Q)` | `P ∧ ¬ Q` |

---

## Part 1 · `ne_zero_contra`

Statement: for `x : ℝ`, `x ^ 2 ≠ 0` implies `x ≠ 0`. Contrapositive: `x = 0` implies `x ^ 2 = 0`, which is a
computation.

**R1 · `contrapose! h`** changes the **context and the goal**. From `h : P ⊢ Q` it makes `h : ¬ Q ⊢ ¬ P`
(contrapositive; the new hypothesis keeps the name `h`), then pushes the negations. With `≠` on both sides the
`¬`'s cancel: `¬ (c ≠ d)` becomes `c = d`. Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `h : a ≠ b ⊢ c ≠ d` | `h : c = d ⊢ a = b` |

Then `rw [h]` (TACTIC_STATES, "Rewriting") replaces the variable by `0`.

**R2 · `ring`** **closes** an equation that holds in every commutative ring (`ℕ`, `ℤ`, `ℝ`, `ℂ`): it normalises
both sides as polynomials, so `0 ^ 2 = 0` and `(a - a) ^ 3 = 0` are both in reach. It does not use hypotheses.
Placeholders: `{R : Type} [CommRing R] (a : R)`.

| Before | After |
|---|---|
| `⊢ (a - a) ^ 3 = 0` | no goals |

**W1.** On `2 * x ≠ 0 → x ≠ 0`: R1, then `rw [h]`, then R2:

```lean-goal
⊢ 2 * x = 0
⊢ 2 * 0 = 0
```

---

## Part 2 · `mono_contra`

Statement: if `f : ℕ → ℕ` is monotone (`hf : ∀ a b, a ≤ b → f a ≤ f b`) and `f a < f b`, then `a < b`.
Contrapositive: `b ≤ a` implies `f b ≤ f a`, which is `hf` itself.

**R3 · `contrapose! h`** on strict inequalities changes the **context and the goal**. `¬ (x < y)` is pushed to
`y ≤ x`, so both sides swap. Placeholders: `{α : Type} [LinearOrder α] (a b c d : α)` (`α` is totally ordered;
`ℕ`, `ℤ`, `ℝ` qualify).

| Before | After |
|---|---|
| `h : a < b ⊢ c < d` | `h : d ≤ c ⊢ b ≤ a` |

**R4 · `exact g u v h`** **closes** the goal by applying a hypothesis `g : ∀ x y, Q x y → S x y`. The arguments
follow the binders in order: the values `u v` first, then the proof `h : Q u v`; the result has type `S u v`.
Placeholders: `{α : Type} (Q S : α → α → Prop) (u v : α)`. Read the statement of `hf` to see which value goes
first: here they come out swapped compared with the names `a b` of the theorem.

| Before | After |
|---|---|
| `h : Q u v ⊢ S u v` | no goals |

---

## Part 3 · `le_of_forall_pos`

Statement: a real `x` with `x ≤ ε` for every `ε > 0` is `≤ 0`. By contradiction: if `0 < x`, take `ε = x / 2`,
which is positive, and `x ≤ x / 2` contradicts `0 < x`.

**R5 · `by_contra! h`** changes the **context and the goal**. It adds the negated goal as `h` (pushed: `¬ (a ≤ b)`
becomes `b < a`) and the goal becomes `False`. Placeholders: `{α : Type} [LinearOrder α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≤ b` | `h : b < a ⊢ False` |

**R6 · `have := h e he`** changes the **context**: it adds `this : Q e`, the instance of
`h : ∀ ε > z, Q ε` at the value `e`, given `he : e > z`. Any term can stand for `he`, including `(by linarith)`
(R7), which proves the side condition in place. Placeholders: `{α : Type} [LT α] (z e : α) (Q : α → Prop)`.

| Before | After |
|---|---|
| `he : e > z ⊢ Q e` | `this : Q e ⊢ Q e` |

**R7 · `linarith`** **closes** a goal `t < s`, `t ≤ s`, `t = s` (or `>`, `≥`) that follows from the hypotheses
by adding up positive multiples of them. Multiplication or division by a numeral, such as `x / 3`, is linear; a
product of two variables is not. Works over ordered fields such as `ℝ` (and `ℕ`, `ℤ`).

| Before | After |
|---|---|
| `hx : 0 < x ⊢ x / 3 > 0` | no goals |

**R8 · `linarith`** with goal `False` **closes** it when the hypotheses are contradictory by the same linear
reasoning: the last step after `by_contra!`.

| Before | After |
|---|---|
| `h1 : x + y < 0, h2 : 0 ≤ x, h3 : 0 ≤ y ⊢ False` | no goals |

**W2.** On `(∀ ε > 0, x < ε + 1) → x ≤ 1`: R5, then R6 at `ε := x - 1` with `(by linarith)` for `x - 1 > 0`,
then R8:

```lean-goal
⊢ False
```

with `hx : 1 < x` and then `this : x < x - 1 + 1` in the context.

---

## Part 4 · `le_of_lt_imp`

Statement: for `a b : ℕ`, if every `c < a` satisfies `c < b`, then `a ≤ b`. By contradiction: if `b < a`, then
`c := b` gives `b < b`, which is impossible.

R5 again turns the goal `a ≤ b` into `False` with `h' : b < a`.

**R9 · `lt_irrefl`** is the lemma `lt_irrefl (a : α) : ¬ a < a`. Since `¬ p` is `p → False`, `lt_irrefl a h`
with `h : a < a` is a proof of `False`, and `exact` **closes** the goal. Placeholders:
`{α : Type} [Preorder α] (a : α)` (`α` has `≤` and `<` that behave as an order; `ℕ`, `ℤ`, `ℝ` qualify).

| Before | After |
|---|---|
| `h : a < a ⊢ False` | no goals |

The proof of `b < b` itself is an application of `h`, which the infoview shows as `h : ∀ c < a, c < b`: as in R6,
`h b h'` has type `b < b`. Write it inside the `exact` (or first as `have := h b h'`).

**W3.** On `(∀ c, s c < a → s c < s c) → a ≤ s 0`: R5 gives `h' : s 0 < a`, and R9 is applied to `h 0 h'`.

---

## Traps

- `intro`, `fun`, `λ`, `mt`, `absurd` and the lambda shorthand `(f · x)` are banned: the point is to let
  `contrapose!` / `by_contra!` build the contrapositive, not to build it by hand. This also bans `·` goal
  bullets; no proof here needs one.
- `simp`, `norm_num`, `omega` and the library one-liners for these exact statements are banned too. Close numeric
  goals with `ring` (equations) or `linarith` (inequalities, `False`).
- Without `!`, `contrapose h` and `by_contra h` leave the raw `¬ (x ≠ 0)` or `¬ (x ≤ 0)`, which `rw` and
  `linarith` cannot use directly. Write the `!`.
- `contrapose! h` needs the hypothesis's name. It replaces `h`; the old `h` is gone.
- `¬ (a < b)` is pushed to `b ≤ a`, with the sides swapped: read the new goal before choosing the arguments of `hf`.
- `h (x / 2)` alone has type `x / 2 > 0 → x ≤ x / 2`: you still owe the positivity proof as the second argument.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `P → Q` from `¬ Q → ¬ P` | `contrapose! h` | R1, R3 |
| prove the goal by contradiction | `by_contra! h` | R5 |
| close a ring identity | `ring` | R2 |
| apply `∀ x y, Q x y → S x y` | `exact g u v h` | R4 |
| instance of `∀ ε > 0, Q ε` | `have := h e (by linarith)` | R6, R7 |
| linear goal or `False` from linear facts | `linarith` | R7, R8 |
| `False` from `h : a < a` | `exact lt_irrefl a h` | R9 |
| rewrite with an equation | `rw [h]` | TACTIC_STATES |
| see the state | infoview | |
