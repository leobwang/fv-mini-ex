# M006 · Fin n: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): structures and the anonymous constructor `⟨_, _⟩`,
definitions by pattern matching, `rfl`, `exact`, `have`, `simp`, `rw`, `omega`. **New here:** the type
`Fin n` (a natural number bundled with a proof that it is `< n`, a *dependent type*: its type mentions the
number `n`), its value `↑i`, `Fin.ext`, `Fin.last`, `Fin.castSucc`, and induction on `n` when a function
`f : Fin n → Nat` is in the context. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n` | the numbers `0, …, n - 1`. A value is a structure with two fields: `val : Nat` and `isLt : val < n` |
| `↑i` | `i.val`, the value of `i : Fin n` as a `Nat` (Lean prints the coercion `Fin n → Nat` as `↑`) |
| `⟨v, hv⟩ : Fin n` | the element with value `v`, built from `v` and a proof `hv : v < n` |
| `⋯` | a proof term the infoview hides, e.g. `⟨↑i + 1, ⋯⟩` |
| `Fin.last n` | the largest element of `Fin (n + 1)`; its value is `n` |
| `i.castSucc` | `Fin.castSucc i`: `i : Fin n` seen as an element of `Fin (n + 1)`, same value |
| `fun i => f i.castSucc` | for `f : Fin (n + 1) → Nat`: the function `Fin n → Nat` that is `f` without its last point |
| `(sumFin n fun i => …)` | `sumFin n (fun i => …)`: Lean drops the parentheses around a trailing `fun` and wraps the whole application instead |
| `fun x => c` | the constant function; Lean renamed your `_` to `x` |
| `n - m` (on `Nat`) | truncated subtraction: `0` when `m ≥ n` |
| `case zero`, `case succ` | the two goals of `induction n` |

---

## Part 1 · `flip`

Definition to write: `flip (i : Fin n) : Fin n`, the mirror image `n - 1 - ↑i`. You must supply the value
and a proof that it is `< n`.

**R1 · `⟨v, proof⟩`** (the constructor `Fin.mk`) builds a `Fin n`. In tactic form `refine ⟨v, ?_⟩` changes
the **goal**: you chose the value, and the bound remains. In a `def` body write the term `⟨v, by tac⟩`.
Placeholders: `(n v : Nat) (hv : v < n)`.

| Before | After |
|---|---|
| `⊢ Fin n` | `⊢ v < n` |

**R2 · `Fin.isLt`** changes the **context**: `i.isLt : ↑i < n` is the bound stored in `i`, and
`have h := i.isLt` makes it a hypothesis. Placeholders: `(n : Nat) (i : Fin n)`.

| Before | After |
|---|---|
| `⊢ P` | `h : ↑i < n ⊢ P` |

**R3 · `omega`** **closes** linear goals over `Nat` and `Int` (`+`, `-`, `*` by a numeral, `<`, `≤`, `=`).
For every `i : Fin n` it meets, it adds `↑i < n` by itself (R2 is then unnecessary). From `↑i < n` it also
learns `n ≥ 1`. Placeholders: `(n : Nat) (i : Fin n)`.

| Before | After |
|---|---|
| `i : Fin n ⊢ ↑i + 1 ≤ n` | no goals |

## Part 2 · `flip_val`

Statement: `(flip i).val = n - 1 - i.val`: the value of `flip i` is what Part 1 put in the pair.

**R4 · `rfl`** **closes** `↑⟨v, hv⟩ = v`: taking `.val` of a pair computes to its first component.
`rfl` also unfolds definitions, so `(d x).val = e` is `rfl` whenever `d x` is defined as `⟨e, _⟩` (W1).
Placeholders: `(n v : Nat) (hv : v < n)`.

| Before | After |
|---|---|
| `⊢ ↑⟨v, hv⟩ = v` | no goals |

## Part 3 · `flip_flip`

Statement: `flip (flip i) = i`. Two elements of `Fin n` are equal when their values are, so the work is the
`Nat` identity `n - 1 - (n - 1 - ↑i) = ↑i`, true because `↑i < n`.

**R5 · `apply Fin.ext`** changes the **goal**: an equation of `Fin`s becomes an equation of values. The lemma is
`Fin.ext : ↑a = ↑b → a = b`. Placeholders: `(n : Nat) (i j : Fin n)`.

| Before | After |
|---|---|
| `⊢ i = j` | `⊢ ↑i = ↑j` |

**R6 · `simp [d]`** changes the **goal**: it unfolds the definition `d` and takes the value of the pair, so
`↑(d x)` becomes the expression in `d`'s body. Applied to a nested `d (d x)` it unfolds both. Placeholders:
`(n : Nat) (i : Fin n)`, `succ' (i : Fin n) : Fin (n + 1) := ⟨i.val + 1, by omega⟩`.

| Before | After |
|---|---|
| `⊢ P ↑(succ' i)` | `⊢ P (↑i + 1)` |

**R7 · `omega` with truncated subtraction** **closes** goals with `Nat` `-`: it splits each `a - b` into the
cases `b ≤ a` and `b > a` itself. With the bound `↑i < n` from R3, `n - (n - ↑i) = ↑i` holds (without it, it
would fail for `↑i > n`). Placeholders: `(n : Nat) (i : Fin n)`.

| Before | After |
|---|---|
| `i : Fin n ⊢ n - (n - ↑i) = ↑i` | no goals |

**W1 (on `shift i = ⟨↑i + 2, _⟩ : Fin (n + 2)`, not the exercise's `flip`).** `(shift i).val = i.val + 2` is
`rfl` (R4). For `shift (Fin.last n) = Fin.last (n + 2)`: R5, then `simp [shift]` (R6) closes it; `simp` also
knows `↑(Fin.last n) = n`.

```lean-goal
⊢ shift (Fin.last n) = Fin.last (n + 2)
⊢ ↑(shift (Fin.last n)) = ↑(Fin.last (n + 2))
```

---

## Part 4 · `sumFin_const`

Statement: `sumFin n (fun _ => c) = n * c`, where `sumFin 0 f = 0` and
`sumFin (n + 1) f = f (Fin.last n) + sumFin n (fun i => f i.castSucc)`: the last term plus the sum of the
first `n`.

**R8 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list and the context**: one goal
per case of `Nat`, and the `succ` case gets `ih`, the statement for `n`. The `?_` arms leave both cases as
goals; write `· tac` for each. An arm may also hold its tactics directly, one arm per line:
`induction n with`, then `| zero => tac₀`, then `| succ n ih => tac₁` (indent a multi-line `tac₁` under its
`|`). Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n : Nat, ih : P n ⊢ P (n + 1)` |

**R9 · `simp only [d]`** for a recursive `d : (n : Nat) → (Fin n → Nat) → Nat` changes the **goal**: each
`d 0 f` or `d (n + 1) f` is replaced by the right side of the matching equation. `d n f` with a bare variable
`n` matches neither and is left alone. With `simp [d]` instead, `simp` also tidies what is left (`0 * c` → `0`).
Placeholders: `(n : Nat) (f : Fin (n + 1) → Nat)`, and `total` defined like `sumFin` but adding the last
term on the right:

```
def total : (m : Nat) → (Fin m → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => total n (fun i => f i.castSucc) + f (Fin.last n)
```

| Before | After |
|---|---|
| `⊢ P (total (n + 1) f)` | `⊢ P ((total n fun i => f i.castSucc) + f (Fin.last n))` |
| `⊢ P (total 0 f)` | `⊢ P 0` |

**R10 · `rw [ih a]`** (and `simp [ih]`) changes the **goal**: it replaces `L a` by `R a` using the induction
hypothesis. When `ih : ∀ f, L f = R f`, `ih a` is the instance at `a`. In `simp [d, ih]` the IH is used in the
same pass as the unfolding. Placeholders: `(L R : (Fin n → Nat) → Nat) (ih : ∀ f, L f = R f)
(g : Fin (n + 1) → Nat)`.

| Before | After |
|---|---|
| `⊢ P (L fun i => g i.castSucc)` | `⊢ P (R fun i => g i.castSucc)` |

**R11 · `rw [Nat.add_mul]`** changes the **goal**. The lemma is `Nat.add_mul : (a + b) * c = a * c + b * c`.
`simp [Nat.add_mul]` does the same and also turns `1 * c` into `c`. Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R12 · `omega` with atoms** **closes** a goal that is linear once every non-arithmetic subterm is read as an
unknown: `F a`, `sumFin n f`, `f (Fin.last n)`, and also `b * c` (a product of two variables). Each distinct
such term is a separate unknown, so `(n + 1) * c` and `n * c` are unrelated to it: multiply out first (R11).
Placeholders: `(F : Nat → Nat) (a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ F a + b * c + (F b + c) = F a + F b + (c + b * c)` | no goals |

---

## Part 5 · `sumFin_add`

Statement: `sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g` for all `f g : Fin n → Nat`.

**R13 · `induction n` with `f : Fin n → Nat` in the context** changes the **goal list and the context** like
R8, but `f` is generalized. The type of `f` mentions `n`, so `induction` must take `f` out of the context
first and put it back in each case; the IH then holds for **every** function on `Fin n`. That is what you need:
after unfolding, the sums on the right are about `fun i => f i.castSucc`, not `f`. (A variable whose type does
not mention `n`, like `c : Nat` in Part 4, stays fixed.) Placeholders:
`(Q : (m : Nat) → (Fin m → Nat) → Prop) (n : Nat) (f : Fin n → Nat)`.

| Before | After |
|---|---|
| `f : Fin n → Nat ⊢ Q n f` | `f : Fin 0 → Nat ⊢ Q 0 f`, then `ih : ∀ (f : Fin n → Nat), Q n f` and `f : Fin (n + 1) → Nat ⊢ Q (n + 1) f` |

**W2 (on `total` and `2 * f`, not the exercise's `sumFin`).** `total n (fun i => 2 * f i) = 2 * total n f`:
R8/R13 (the `zero` case is `rfl`), then R9, R10 with `ih (fun i => f i.castSucc)`, then R12:

```lean-goal
⊢ (total (n + 1) fun i => 2 * f i) = 2 * total (n + 1) f
⊢ (total n fun i => 2 * f i.castSucc) + 2 * f (Fin.last n) = 2 * ((total n fun i => f i.castSucc) + f (Fin.last n))
⊢ (2 * total n fun i => f i.castSucc) + 2 * f (Fin.last n) = 2 * ((total n fun i => f i.castSucc) + f (Fin.last n))
```

---

## Traps

- `Nat` subtraction truncates, so `n - 1 - (n - 1 - x) = x` is false for `x ≥ n` (`n = 2, x = 5`:
  `1 - 0 = 1 ≠ 5`). It holds for `x = ↑i` only because `↑i < n`. That is a job for `omega`, which adds the
  bound itself (R3, R7); `rfl` and `decide` cannot prove it for a variable `n`.
- `rfl` proves `flip_val` only if `flip`'s value is written exactly as `n - 1 - i.val`. A value that is
  merely equal (say `n - (i.val + 1)`) needs `simp [flip]; omega`.
- The proof inside `⟨v, by omega⟩` is checked where it is written: it sees `i` and `n`, nothing else.
- `omega` never multiplies two variables: `(n + 1) * c` and `n * c + c` are different unknowns to it (R11, R12).
- `induction n` generalizes only hypotheses whose type mentions `n` (R13). To generalize another one, write
  `induction n generalizing x`.
- `rw [ih]` without arguments rewrites the first match it finds. Naming the instance, `ih (fun i => f i.castSucc)`,
  makes clear which sum you mean.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| build an element of `Fin n` | `⟨v, by omega⟩` | R1, R3 |
| see the bound of `i` | `have h := i.isLt` (gives `h : ↑i < n`) | R2 |
| `Nat` arithmetic with `↑i`, truncated `-` | `omega` | R3, R7 |
| value of a pair, by computation | `rfl` | R4 |
| `i = j` in `Fin n` → values | `apply Fin.ext` | R5 |
| unfold `d` and take the value | `simp [d]` | R6 |
| induction on `n` | `induction n with \| zero => ?_ \| succ n ih => ?_` | R8 |
| IH for every `f : Fin n → Nat` | automatic when `f`'s type mentions `n` | R13 |
| one equation of a recursive def | `simp only [d]` / `simp [d]` | R9 |
| use the IH at a chosen function | `rw [ih (fun i => f i.castSucc)]`, or `simp [d, ih]` | R10 |
| `(a + b) * c` → `a * c + b * c` | `rw [Nat.add_mul]` / `simp [Nat.add_mul]` | R11 |
| rearrange sums of unknown terms | `omega` | R12 |
| see the state | infoview | |
