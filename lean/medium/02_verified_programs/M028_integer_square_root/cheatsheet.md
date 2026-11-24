# M028 · Integer square root: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular definitions by `match`, `induction`,
`simp only [f]`, `refine` and `omega`. **New here:** a recursive `def` whose step uses `let` and
`if … then … else`; `split` on an `if` in the goal and `rename_i` for the hypothesis it introduces;
expanding products of sums with `Nat.add_mul` / `Nat.mul_add` so that `omega` can treat `r * r` as one
unknown. No Mathlib.

The guide teaches on its own functions: `tri n = 0 + 1 + … + n`, `sqPlus n = (n + 1)² + (n + 1)`, and
`div3 n = ⌊n / 3⌋` computed by counting up (same `let`/`if` step shape as the exercise, different
condition).

## How to read an entry

Each entry is one tactic, one lemma used with `rw`/`simp`, or one term construct. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : α → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `if c then a else b` | `a` when the condition `c` holds, `b` otherwise; `c` must be decidable (`≤`, `=` on `Nat` are) |
| `h✝ : c` | a hypothesis with no usable name (made by `split`); `rename_i h` names it (R8) |
| `case succ.isTrue` | the `succ` case of `induction`, then the `then` branch of `split` (`isFalse`: the `else` branch) |
| `inst✝ : Decidable c` | the instance that lets Lean evaluate `if c …`; you never touch it |
| `isqrt n` after `simp only [isqrt]` | the `let r := isqrt n` was substituted: there is no `r` in the goal |
| `isqrt n + 1 + 1` | `(isqrt n + 1) + 1`: `+` groups to the left; in the `then` branch the root `isqrt n + 1` got a `+ 1` |
| `1 * a`, `a * 1`, `2 * 2` | left as-is by `simp only [Nat.add_mul, Nat.mul_add]`; `omega` reads them |
| `a * a` | to `omega`: one unknown number (an *atom*), not a product it can reason about |
| a goal spread over several lines | long goals are broken for printing only; it is one proposition |

---

## Part 1 · `isqrt`

Statement: write `isqrt n`, the largest `r` with `r * r ≤ n`. Recurse on `n`: `isqrt 0 = 0`; for `n + 1`,
call `r := isqrt n` and step up to `r + 1` exactly when `(r + 1) * (r + 1)` still fits under `n + 1`.
(The root of `n + 1` is `r` or `r + 1`, never more: `(r + 2)² > r² + 2r + 1 + 1 ≥ n + 1`.)

**R1 · `match n with | 0 => … | n + 1 => … f n …`** is a **term**: structural recursion on `Nat`. Lean
accepts the call `f n` in the arm `n + 1` because the argument shrinks; no termination proof is needed.
Each arm becomes an equation for `simp [f]` / `simp only [f]` (R5, R6). Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `tri 4` | `10` (by `rfl`) |

**R2 · `let x := e`** is a **term**: it names a value inside a definition. Put the `let` on its own line
and the body under it at the same indentation. Placeholders: `(n : Nat)`, with `let m := n + 1`.

| Before | After |
|---|---|
| `sqPlus 2` (`m := 3`, then `m * m + m`) | `12` (by `rfl`) |

**R3 · `if c then a else b`** is a **term**: it picks `a` or `b` by a decidable `Prop` `c`. With R1 and R2,
`div3`'s step is `let q := div3 n; if 3 * (q + 1) ≤ n + 1 then q + 1 else q`. Placeholders:
`(c : Prop) [Decidable c]` (a condition Lean can evaluate; `x ≤ y` on `Nat` qualifies), `(a b : α)`.

| Before | After |
|---|---|
| `div3 7`, `div3 9` | `2`, `3` (by `rfl`) |

---

## Part 2 · `isqrt_spec`

Statement: `isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1)`, i.e. $r^2 \le n < (r+1)^2$ for
$r = $ `isqrt n`. Induct on `n`. In the step, unfold `isqrt (n + 1)` and split the `if`; each branch is
linear arithmetic in the atoms `isqrt n * isqrt n` and `isqrt n` once every product of sums is expanded.

**R4 · `induction n with | zero => … | succ n ih => …`** changes the **goal list and the context**: two
goals, and the second has `ih`, the statement at `n`. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P 0`, `ih : P n ⊢ P (n + 1)` |

**R5 · `simp [f]`** **closes** the base case: it rewrites `f 0` by the `0` arm, then the arithmetic on
numerals is trivial. In the exercise: `simp [isqrt]`.

| Before | After |
|---|---|
| `⊢ div3 0 * 3 ≤ 0 ∧ 0 < (div3 0 + 1) * 3` | no goals |

**R6 · `simp only [f]`** changes the **goal**: `f (n + 1)` becomes the `n + 1` arm, and the `let` is
substituted, so every `q` is written `div3 n`. It rewrites every occurrence (the exercise's goal has
four copies of `isqrt (n + 1)`, so four copies of the `if`). Placeholders: `(n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (div3 (n + 1))` | `⊢ P (if 3 * (div3 n + 1) ≤ n + 1 then div3 n + 1 else div3 n)` |

**R7 · `split`** changes the **goal list and the context**: an `if c then a else b` in the goal becomes two
goals. The first has `a` in place of the `if` and a nameless `h✝ : c`; the second has `b` and `h✝ : ¬c`.
All copies of the same `if` are replaced together. Placeholders:
`{α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h✝ : c ⊢ P a`, `h✝ : ¬c ⊢ P b` |

**R8 · `rename_i h`** changes the **context**: the newest nameless hypothesis `h✝` is now called `h`. Use it
at the start of each branch, so that you can write `h` in `refine ⟨h, ?_⟩` (R9) or `at h` (R12).
Placeholders: `(c : Prop) [Decidable c] (n : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h✝ : c ⊢ P (n + 1) ∨ ¬c` | `h : c ⊢ P (n + 1) ∨ ¬c` |

**R9 · `refine ⟨h, ?_⟩`** changes the **goal**: a conjunction whose left part is exactly a hypothesis `h`
loses that part. In the `then` branch of the exercise, the condition of the `if` IS the first conjunct.
Placeholders: `(A B : Prop) (h : A)`.

| Before | After |
|---|---|
| `h : A ⊢ A ∧ B` | `⊢ B` |

**R10 · `Nat.add_mul`** changes the **goal**. The lemma is `Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c`.
Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R11 · `Nat.mul_add`** changes the **goal**. The lemma is `Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c`.
Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * (b + c))` | `⊢ P (a * b + a * c)` |

**R12 · `simp only [Nat.add_mul, Nat.mul_add] at h ⊢`** changes the **context and the goal**: R10 and R11
are applied repeatedly, in `h` and in the goal, until no product contains a sum. `(a + 2) * (a + 2)`
becomes `a * a + 2 * a + (a * 2 + 2 * 2)`; the only product of two variables left is `a * a`. List every
hypothesis you need expanded (`at ih h ⊢`): `omega` must see the same atom everywhere. Placeholders:
`(a m : Nat) (h : (a + 2) * (a + 2) ≤ m)`.

| Before | After |
|---|---|
| `h : (a + 2) * (a + 2) ≤ m ⊢ P (a * (a + 1))` | `h : a * a + 2 * a + (a * 2 + 2 * 2) ≤ m ⊢ P (a * a + a * 1)` |

**R13 · `omega`** **closes** a goal of linear arithmetic over `Nat`/`Int` (`+`, `-`, `*` by a numeral, `<`,
`≤`, `=`, `∧`, `∨`, `¬`), using the hypotheses. A product of two variables such as `a * a` is one unknown
number to it, so the facts below are linear in the two unknowns `a * a` and `a`: subtracting gives
`2 * a + 1 < 3`, hence `a = 0`. Placeholders: `(a m : Nat)`.

| Before | After |
|---|---|
| `h1 : a * a + 1 * a + (a * 1 + 1 * 1) ≤ m, h2 : m < a * a + 3 ⊢ a = 0` | no goals |

### Worked combinations (not the exercise's objects)

**W1 (`3 * div3 n ≤ n`).** R4; `zero`: R5; `succ n ih`: R6, R7, then in each branch R13 (the `then`
branch after R8, to show where the name goes). The statement starts at

```lean-goal
⊢ 3 * div3 n ≤ n
```

and the branches are `3 * (div3 n + 1) ≤ n + 1` (with `h : 3 * (div3 n + 1) ≤ n + 1`) and
`3 * div3 n ≤ n + 1`: `omega` multiplies by the numeral `3` itself, so no expansion is needed here.

**W2 (square of a sum against a bound).** Only `h` has a product of sums: R12 `at h`, then R13.

| Before | After `simp only [Nat.add_mul, Nat.mul_add] at h` |
|---|---|
| `h : (a + 2) * (a + 2) ≤ m ⊢ a * a + 4 * a + 4 ≤ m` | `h : a * a + 2 * a + (a * 2 + 2 * 2) ≤ m ⊢ a * a + 4 * a + 4 ≤ m` |

---

## Traps

- `omega` without expanding fails: it reads `(isqrt n + 1) * (isqrt n + 1)` and `isqrt n * isqrt n` as two
  unrelated unknowns. Expand in the goal AND in `ih` and `h` (R12).
- `split` names its hypothesis `h✝`, which you cannot type. `rename_i h` (R8) before you use it.
- After `simp only [isqrt]` there is no `r` in the goal: the `let` was substituted (R6). Work with `isqrt n`.
- In the definition, the arm `| n + 1 =>` introduces a NEW `n` (the predecessor), shadowing the argument;
  call the function on that `n`. A call like `isqrt (n - 1)` is not structural and needs a termination proof.
- `omega` does not case on an `if`: right after `simp only [isqrt]` it treats each
  `if … then isqrt n + 1 else isqrt n` product as one more unknown and fails. `split` first (R7).
- `t1 ; t2` runs `t2` on the first goal only. After `split`, handle the two branches with `·`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| recursion on `Nat` | `match n with \| 0 => … \| n + 1 => … f n …` | R1 |
| name the recursive result | `let r := f n` (on its own line) | R2 |
| choose by a condition | `if c then a else b` | R3 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R4 |
| base case | `simp [f]` | R5 |
| unfold `f (n + 1)`, `let` substituted | `simp only [f]` | R6 |
| case on the `if` in the goal | `split` | R7 |
| name `h✝` | `rename_i h` | R8 |
| drop a conjunct that is a hypothesis | `refine ⟨h, ?_⟩` | R9 |
| `(a + b) * c`, `a * (b + c)` | `Nat.add_mul`, `Nat.mul_add` | R10, R11 |
| expand in `ih`, `h` and the goal | `simp only [Nat.add_mul, Nat.mul_add] at ih h` with the goal symbol after `h` | R12 |
| linear arithmetic, `r * r` as an atom | `omega` | R13 |
| see the state | infoview | |
