# M106 · Bisection invariants: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `induction`, `refine ⟨…, ?_⟩`, `have`, `rw`, `simp`,
`<;>`. **New here:** Mathlib's real numbers `ℝ`, pairs `ℝ × ℝ`, `if … then … else` inside a goal
(`split_ifs`), the power and division lemmas `pow_succ`, `div_div`, and the arithmetic closers `ring` and
`linarith`. The proof idea: a *loop invariant*, a property of the state after `n` steps proved by
induction on `n`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid M]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers. `noncomputable def` marks a definition over `ℝ` that cannot be run, only reasoned about |
| `ℝ × ℝ` | pairs of reals; here an interval `(lo, hi)` |
| `(x, y)` | the pair with first component `x`, second `y` (`Prod.mk x y`) |
| `I.1`, `I.2` | the first and second component of the pair `I` (`Prod.fst I`, `Prod.snd I`) |
| `(x, y).1` | a projection not yet reduced; `simp only` turns it into `x` (R7) |
| `(bisect f a b n).1` | `lo` after `n` steps; `(bisect f a b n).2` is `hi` |
| `2 ^ n` | `2` to the natural-number power `n : ℕ`, computed in `ℝ` |
| `if c then x else y` | `x` when `c` holds, else `y`; Lean needs a `Decidable c` instance to form it |
| `inst✝ : Decidable c` | that instance, as an unnamed hypothesis; ignore it |
| `¬c` | `c → False`; for `¬x ≤ 0` read "`0 < x`" (`linarith` does, R11) |
| `case zero`, `case succ` | the two goals after `induction n` (R1) |
| `case pos`, `case neg` | the `then` and `else` goals after `split_ifs` (R6) |
| `h✝` | a hypothesis you did not name (`split_ifs` without `with`); name it with `split_ifs with hm` |
| `n✝ n : ℕ` | two variables called `n`: the older one (the theorem's `n`) is shadowed by the `n` from `intro n` or `succ n` and prints as `n✝` |
| `case refine_1`, `case neg.refine_2` | the goals `refine ⟨…, ?_⟩` left open, numbered in order, prefixed by the enclosing case |
| `f (x, y).1` | `f ((x, y).1)`: `.1` binds tighter than applying `f` |
| `(b - a) / 2 ^ n / 2` | `((b - a) / (2 ^ n)) / 2`: `^` binds tighter than `/`, and `/` groups to the left |

---

## Part 1 · `bisect_invariant`

Statement: for every `n`, the interval `(lo, hi) = bisect f a b n` has `f lo ≤ 0`, `0 ≤ f hi` and width
`hi - lo = (b - a) / 2 ^ n`, given `f a ≤ 0 ≤ f b`. Induction on `n`; in the step case unfold one step, split
on the `if`, and halve the width.

### Induction and the base case

**R1 · `induction n with | zero => … | succ n ih => …`** changes the **goal list and the context**: the goal
`P n` becomes `P 0` and `P (n + 1)`, the second with the induction hypothesis `ih : P n`. Placeholders:
`(P : ℕ → Prop) (n : ℕ)`. Put the alternatives on their own lines, indented under `induction`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, ih : P n ⊢ P (n + 1)` |

**R2 · `simp only [D]` on a recursive definition** changes the **goal**: it rewrites with the defining
equations of `D`, one per `|` clause. It only fires where the argument is literally `0` or `n + 1`;
`D … n` with a variable `n` is left alone, which is why the step case shows `bisect f a b n` inside.
Placeholders: `{α : Type} (g : α → α) (x : α) (n : ℕ)` and the guide's
`orbit g x : ℕ → α` (`orbit g x 0 = x`, `orbit g x (n + 1) = g (orbit g x n)`).

| Before | After |
|---|---|
| `⊢ P (orbit g x (n + 1))` | `⊢ P (g (orbit g x n))` |
| `⊢ P (orbit g x 0)` | `⊢ P x` |

**R3 · `pow_zero`, `div_one`** change the **goal**. `pow_zero a : a ^ 0 = 1` (any `[Monoid M]`: `ℕ`, `ℝ`),
`div_one a : a / 1 = a` (`ℝ` qualifies). `simp` applies both by itself, so the base case closes with
`simp [bisect, ha, hb]`. Placeholders: `(a : ℝ)`.

| Before | After `rw [pow_zero]` | After `rw [div_one]` |
|---|---|---|
| `⊢ P (a / 2 ^ 0)` | `⊢ P (a / 1)` | `⊢ P a` |

### The step case

**R4 · `obtain ⟨h1, h2, h3⟩ := h`** changes the **context**: a hypothesis `A ∧ B ∧ C` is replaced by its three
parts. Use it on `ih`. Placeholders: `(A B C : Prop) (h : A ∧ B ∧ C)`.

| Before | After |
|---|---|
| `h : A ∧ B ∧ C ⊢ G` | `h1 : A, h2 : B, h3 : C ⊢ G` |

**R5 · `simp only [D]` on a definition whose body is an `if`** changes the **goal**: the name becomes its body,
an `if … then … else …`. `simp only [bisect, step]` does R2 and R5 at once. Placeholders:
`{α : Type} (c : Prop) [Decidable c] (p : α × α)` and the guide's
`swapIf c p := if c then (p.2, p.1) else p`. `[Decidable c]` says `c` can be tested; `x ≤ y` on `ℝ` has an
instance (classically).

| Before | After |
|---|---|
| `⊢ P (swapIf c p)` | `⊢ P (if c then (p.2, p.1) else p)` |

**R6 · `split_ifs with hc`** changes the **goal list and the context**: it finds an `if` anywhere in the goal
and makes one goal per branch, with `hc : c` in the `then` goal and `hc : ¬c` in the `else` goal. Every copy
of the same `if` is replaced at once. Projections `.1`, `.2` around it stay (R7 removes them).
Placeholders: `{α : Type} (c : Prop) [Decidable c] (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (if c then (x, y) else (y, x)).1` | `hc : c ⊢ P (x, y).1`, `hc : ¬c ⊢ P (y, x).1` |

**R7 · `simp only`** (no lemmas) changes the **goal**: it reduces a projection of a literal pair,
`(x, y).1` to `x` and `(x, y).2` to `y`. After `refine ⟨hm, h2, ?_⟩` the width goal still has these.
Placeholders: `{α β : Type} (x : α) (y : β)`.

| Before | After |
|---|---|
| `⊢ P (x, y).1 (x, y).2` | `⊢ P x y` |

**R8 · `rw [pow_succ]`** changes the **goal**. The lemma is `pow_succ a n : a ^ (n + 1) = a ^ n * a`.
Placeholders: `{M : Type} [Monoid M] (a : M) (n : ℕ)` (a type with an associative `*` and a `1`; `ℕ`, `ℝ`
qualify).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R9 · `rw [← div_div]`** changes the **goal**. The lemma is `div_div a b c : a / b / c = a / (b * c)`; `←`
uses it right to left, splitting one division into two. `/` groups to the left: `a / b / c` is
`(a / b) / c`. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b c : α)` (commutative `*` with `/`;
`ℝ` qualifies). After R8 and R9 the goal contains `(b - a) / 2 ^ n`, the right side of `h3`, so `rw [← h3]`
replaces it by the old width `hi - lo`.

| Before | After |
|---|---|
| `⊢ P (a / (b * c))` | `⊢ P (a / b / c)` |

**R10 · `ring`** **closes** an equation that holds in every commutative ring. In `ℝ`, division by a numeral
is multiplication by a constant, so `x - (x - y) / 2 = (x + y) / 2` is in scope. It does not use
hypotheses: first `rw [← h3]` so that only `lo`, `hi` remain. Placeholders: `(x y : ℝ)`.

**R11 · `linarith`** **closes** a linear goal `t ≤ u`, `t < u` or `t = u` over `ℝ` by combining hypotheses
in the context with nonnegative coefficients. It reads `¬x ≤ y` as `y < x`, and it sees through a literal
pair projection such as `(x, y).2`. It does not split `∧` or look inside an `if`; do those first (`refine`,
R6). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `h : ¬x ≤ 0 ⊢ 0 ≤ x` | closed |
| `h : x ≤ y ⊢ x ≤ (x + y) / 2` | closed |

### Worked combinations (W1, W2, on objects that are not the exercise's)

**W1: a closed form by induction.** `orbit (fun t => t / 2) x n = x / 2 ^ n`. Base case `simp [orbit]`
(R2, R3). Step case `simp only [orbit]` (R2), then `rw [pow_succ, ← div_div, ← ih]` (R8, R9, then the
induction hypothesis right to left) closes it, since `rw` tries `rfl` at the end. The step case, with
`ih : orbit (fun t => t / 2) x n = x / 2 ^ n`, after each of `simp only [orbit]`, `rw [pow_succ]`,
`rw [← div_div]` (the last `rw [← ih]` turns the right side into the left side):

```lean-goal
⊢ orbit (fun t => t / 2) x (n + 1) = x / 2 ^ (n + 1)
⊢ orbit (fun t => t / 2) x n / 2 = x / 2 ^ (n + 1)
⊢ orbit (fun t => t / 2) x n / 2 = x / (2 ^ n * 2)
⊢ orbit (fun t => t / 2) x n / 2 = x / 2 ^ n / 2
```

The bisection width goal goes through the same `pow_succ`, `← div_div`, `rw [← h3]` chain.

**W2: one loop step.** A trisection step `trisect c I` keeps the left or right two thirds. To show the left
end does not move left, unfold (R5), split (R6), reduce the pairs (R7), and `linarith` (R11). The states
after R5 and R6:

```lean-goal
⊢ I.1 ≤ (if c then ((2 * I.1 + I.2) / 3, I.2) else (I.1, (I.1 + 2 * I.2) / 3)).1
⊢ I.1 ≤ ((2 * I.1 + I.2) / 3, I.2).1
⊢ I.1 ≤ (I.1, (I.1 + 2 * I.2) / 3).1
```

---

## Part 2 · `bisect_nested`

Statement: given `a ≤ b`, `a ≤ lo n ≤ lo (n + 1)` and `hi (n + 1) ≤ hi n ≤ b`, where `lo n, hi n` are the
components of `bisect f a b n`. Not provable by `induction n` directly: the statement relates steps `n`
and `n + 1`, and every halving step needs `lo ≤ hi` (the midpoint lies between the ends only then), which
the statement never mentions. Prove a stronger fact first, about one step count at a time.

**Milestone `inv`.** `have inv : ∀ n, lo n ≤ hi n ∧ a ≤ lo n ∧ hi n ≤ b := by intro n; induction n …`.
Its step case is R4, `simp only [bisect, step]` (R2, R5), `split_ifs` (R6), `simp only` (R7), then split the
three conjuncts with `refine ⟨?_, ?_, ?_⟩` and close each with `linarith` (R11): the midpoint of
`lo ≤ hi` lies between them. Then `obtain ⟨h1, h2, h3⟩ := inv n` (R4) gives the first and last conjunct
of the goal directly; the middle two are one step of R2, R5, R6, R7, R11.

**W3: strengthening, on a different loop.** For `xₙ = orbit (fun t => t / 2) x n` with `0 ≤ x`, the claim
`xₙ₊₁ ≤ xₙ` needs `0 ≤ xₙ`. Prove `inv : ∀ k, 0 ≤ orbit (fun t => t / 2) x k` by induction, take
`have h0 := inv n`, unfold one step, and `linarith`:

```lean-goal
⊢ orbit (fun t => t / 2) x (n + 1) ≤ orbit (fun t => t / 2) x n
⊢ orbit (fun t => t / 2) x n / 2 ≤ orbit (fun t => t / 2) x n
```

---

## Traps

- `grind` and `try?` are banned here: `fun_induction bisect <;> grind` would close both theorems. The
  exercise is writing the invariant yourself.
- `induction n` on `bisect_nested` as stated gets stuck: the step needs `lo n ≤ hi n`, which is not in `ih`.
  Strengthen first (Part 2).
- `simp only [bisect]` does not unfold `bisect f a b n` for a variable `n` (R2). Only the outer `n + 1`
  unfolds, which is what you want.
- After `split_ifs`, the goals still contain `(x, y).1`. Run `simp only` (R7) before reading or rewriting the
  goal: the reduced goal is stated in `lo`, `hi`, `mid` and is what `ring` should see.
- `ring` ignores hypotheses: rewrite with `h3` before calling it. `rw [← h3]` needs `(b - a) / 2 ^ n`
  literally, so do R8 and R9 first.
- `refine ⟨hm, h2, ?_⟩` works before `simp only`: the goal says `f (mid, hi).1 ≤ 0`, `hm` says `f mid ≤ 0`,
  and `refine`/`exact` accept a term whose type equals the goal after reducing projections. `rw` does not:
  it needs the literal text, so run `simp only` (R7) before `rw`.
- `split_ifs` without `with` names the branch fact `h✝`, which you cannot mention. `linarith` still uses it.
- `t1 ; t2` runs `t2` on the first goal only. After `split_ifs` or `refine ⟨?_, ?_⟩`, use `<;>` or `·`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∀ n` / a loop invariant | `induction n with \| zero => … \| succ n ih => …` | R1 |
| unfold one loop step | `simp only [bisect, step]` | R2, R5 |
| base case `b - a = (b - a) / 2 ^ 0` | `simp [bisect, ha, hb]` | R2, R3 |
| take `ih` apart | `obtain ⟨h1, h2, h3⟩ := ih` | R4 |
| case on the `if` | `split_ifs with hm` | R6 |
| `(x, y).1 → x` | `simp only` | R7 |
| `a ^ (n + 1) → a ^ n * a` | `rw [pow_succ]` | R8 |
| `a / (b * c) → a / b / c` | `rw [← div_div]` | R9 |
| put the old width back | `rw [← h3]` | TACTIC_STATES |
| algebraic identity, no hypotheses | `ring` | R10 |
| linear inequality from hypotheses | `linarith` | R11 |
| split `A ∧ B ∧ C`, filling some parts | `refine ⟨hm, h2, ?_⟩` | TACTIC_STATES |
| statement not inductive | `have inv : ∀ n, … := by intro n; induction n …`, then `inv n` | W3 |
