# M027 · Fast exponentiation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw [h]`, `simp`, `·`, `<;>`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` with `if … then … else`, `rw`, `simp`, `omega`,
`exact`. E084 (functional induction) helps but is not needed.
**New here:** core Lean only (no Mathlib): `fun_induction` on a function defined by well-founded
recursion (`termination_by e`) whose body has a `let`; local definitions `r : Nat := …` in the
context and `show` to unfold them; `congr 1`; the core lemmas `Nat.pow_zero`, `Nat.pow_two`,
`Nat.pow_mul`, `Nat.pow_succ'`.

The problem in one paragraph. `powFast b e` computes `b ^ e` by repeated squaring:
$b^0 = 1$, and for $e > 0$ it computes $r = (b^2)^{\lfloor e/2 \rfloor}$ recursively and returns $r$
if $e$ is even, $b \cdot r$ if $e$ is odd. The recursion is on `e` (it halves), which Lean accepts
from `termination_by e`. The proof follows the function's three branches. In each recursive branch
the IH gives `powFast (b * b) (e / 2) = (b * b) ^ (e / 2)`; the work is to turn `(b * b) ^ (e / 2)`
into a single power `b ^ (2 * (e / 2))` and then show the exponent is `e` (even) or `e - 1` (odd).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`, or `P : Nat → Nat → Nat → Prop` for a statement
  about `a`, `e` and the result). The step changes only the part inside `P (…)`. A hypothesis `h…`
  in an example is there only to finish it.
- The guide's recursive function, not the exercise's: `walk a e`, with the same branch shape as
  `powFast` (`if e = 0 then a else let r := walk (a + 1) (e / 2); if e % 2 = 0 then r else a + r`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `b ^ e` | natural-number power $b^e$ (`Nat.pow`); `b ^ 0 = 1` by definition |
| `e / 2`, `e % 2` | floor division $\lfloor e/2 \rfloor$ and remainder $e \bmod 2$ on `Nat` |
| `case case1`, `case case2`, `case case3` | the goals `fun_induction` makes: `e = 0`, even `e`, odd `e` |
| `he : ¬e = 0` | the `else` of `if e = 0` |
| `h2 : e % 2 = 0`, `h2 : ¬e % 2 = 0` | the `then` / `else` of the parity test |
| `r : Nat := powFast (b * b) (e / 2)` | the `let` of the definition, kept as a **local definition**: `r` is a name for that value (R3) |
| `ih : powFast (b * b) (e / 2) = (b * b) ^ (e / 2)` | the induction hypothesis (IH): the theorem for the recursive call's arguments |
| `a✝`, `h✝¹`, `ih1✝` | names Lean chose; `✝` means you cannot type them. Name them in the `with` arms (R1) |
| `n.succ` | `Nat.succ n`, that is `n + 1`; it appears after `rw [← Nat.pow_succ']` (R8) |
| `case case2.e_a`, `case case3.e_a` | the goal `congr 1` makes inside `case2` / `case3` for the arguments that differ, here the exponents (R6) |
| `let r := v; G` (as a goal) | a goal that starts with a `let`; `intro r` turns it into the local definition `r : Nat := v` (R3) |
| `¬p` | "not `p`", that is `p → False` |

---

## Part 1 · `powFast_eq`

Statement: `powFast b e = b ^ e` for all `b e : Nat`.

### Following the branches

**R1 · `fun_induction walk a e with | case1 a => … | case2 a e he r h2 ih => … | case3 a e he r h2 ih => …`**
changes the **goal list**: one goal per branch of the function. It applies the induction principle
Lean generates for every recursive definition (`#check @walk.induct` shows it). In each goal the call
`walk a e` is replaced by that branch's right-hand side. `case1` is the `e = 0` branch, and there `e`
is replaced by `0` everywhere, so its arm names only `a`. The other arms name, in order: the
arguments `a e`, the condition `he : ¬e = 0`, the `let` variable `r`, the parity condition `h2`, and
the IH `ih` (the goal at the recursive call's arguments `(a + 1, e / 2)`). Placeholders:
`(a e : Nat) (P : Nat → Nat → Nat → Prop)`. For `powFast` the arms are `| case1 b => …`,
`| case2 b e he r h2 ih => …`, `| case3 b e he r h2 ih => …`.

| Before | After |
|---|---|
| `a e : Nat ⊢ P a e (walk a e)` | `a : Nat ⊢ P a 0 a`, `he : ¬e = 0, r : Nat := walk (a + 1) (e / 2), h2 : e % 2 = 0, ih : P (a + 1) (e / 2) (walk (a + 1) (e / 2)) ⊢ P a e r`, `he : ¬e = 0, r : Nat := walk (a + 1) (e / 2), h2 : ¬e % 2 = 0, ih : P (a + 1) (e / 2) (walk (a + 1) (e / 2)) ⊢ P a e (a + r)` |

### `case1`: `e = 0`

**R2 · `Nat.pow_zero`** changes the **goal**. The lemma is `Nat.pow_zero : n ^ 0 = 1`. `simp` applies
it by itself, so `simp` closes `1 = b ^ 0` in one step. Placeholders: `(a : Nat)`.

| Before | After `rw [Nat.pow_zero]` |
|---|---|
| `⊢ P (a ^ 0)` | `⊢ P 1` |

### `case2`, `case3`: the recursive calls

**R3 · `show G'`** changes the **goal**: it replaces the goal by `G'`, which must be the same up to
unfolding definitions. Its use here: `r : Nat := f x` is a local definition, so `r` and `f x` are
the same by definition and `show` accepts the goal with `f x` written in place of `r`. You need it
because `rw [ih]` looks for the text `powFast (b * b) (e / 2)`, and the goal says `r`. Placeholders:
`(f : Nat → Nat) (x : Nat) (P : Nat → Prop)`. In the guide, `intro r` on the goal `let r := f x; P r`
produces the same local definition `fun_induction` does.

| Before | After `intro r` | After `show P (f x)` |
|---|---|---|
| `⊢ let r := f x; P r` | `r : Nat := f x ⊢ P r` | `r : Nat := f x ⊢ P (f x)` |

After `show`, `rw [ih]` turns `powFast (b * b) (e / 2)` into `(b * b) ^ (e / 2)`.

**R4 · `rw [← Nat.pow_two]`** changes the **goal**. The lemma is `Nat.pow_two : a ^ 2 = a * a`, and
`←` uses it right to left: a square written as a product becomes a power, which R5 can then merge.
Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * a)` | `⊢ P (a ^ 2)` |

**R5 · `rw [← Nat.pow_mul]`** changes the **goal**. The lemma is `Nat.pow_mul : a ^ (m * n) = (a ^ m) ^ n`,
so right to left a power of a power becomes one power with the product exponent,
$(a^m)^n = a^{mn}$. Placeholders: `(a m n : Nat)`.

| Before | After |
|---|---|
| `⊢ P ((a ^ m) ^ n)` | `⊢ P (a ^ (m * n))` |

**R6 · `congr 1`** changes the **goal**: an equation `f x = f y` becomes `x = y`, one level down. On
`a ^ x = a ^ y` it makes `a = a` (closed by `rfl` on the spot) and `x = y`, named `case e_a`. It also
closes a goal by `assumption` if it can. Placeholders: `(a x y : Nat)`.

| Before | After |
|---|---|
| `h : y = x ⊢ a ^ x = a ^ y` | `h : y = x ⊢ x = y` |

**R7 · `omega`** **closes** a linear-arithmetic goal over `Nat`, using the hypotheses. It handles `/`
and `%` by a numeral (it knows $n = 2\lfloor n/2 \rfloor + n \bmod 2$) and reads `k.succ` as `k + 1`.
So `h2 : e % 2 = 0` closes `2 * (e / 2) = e`, and `h2 : ¬e % 2 = 0` closes `(2 * (e / 2)).succ = e`.
`omega` also sees through local definitions such as `r` (unlike `rw`), but not through the
definition of `powFast`.

**R8 · `rw [← Nat.pow_succ']`** (odd case only) changes the **goal**. The lemma is
`Nat.pow_succ' : m ^ n.succ = m * m ^ n`, so right to left the lone factor `b` in `b * b ^ k` is
absorbed into the power, $m \cdot m^n = m^{n+1}$. The exponent prints as `n.succ`, which is `n + 1`.
Placeholders: `(m n : Nat)`. (Do not confuse it with `Nat.pow_succ : m ^ (n + 1) = m ^ n * m`, which
puts the factor on the right.)

| Before | After |
|---|---|
| `⊢ P (m * m ^ n)` | `⊢ P (m ^ n.succ)` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `a ≤ walk a e`: R1 with named arms; in the recursive arms `show` puts `walk (a + 1) (e / 2)`
in place of `r` (R3), and `omega` closes every case using `ih` (R7).

**W2: a tower of powers, collapsed.** `((c * c) ^ k) ^ 2 = c ^ (4 * k)`: R4, R5 twice, R6, R7.
`rw [← Nat.pow_mul]` rewrites the outermost power of a power first:

```lean-goal
⊢ ((c * c) ^ k) ^ 2 = c ^ (4 * k)
⊢ ((c ^ 2) ^ k) ^ 2 = c ^ (4 * k)
⊢ (c ^ 2) ^ (k * 2) = c ^ (4 * k)
⊢ c ^ (2 * (k * 2)) = c ^ (4 * k)
⊢ 2 * (k * 2) = 4 * k
```

**W3: a lone factor, absorbed.** `c * c ^ (k + k) = c ^ (2 * k + 1)`: R8, R6, R7.

```lean-goal
⊢ c * c ^ (k + k) = c ^ (2 * k + 1)
⊢ c ^ (k + k).succ = c ^ (2 * k + 1)
⊢ (k + k).succ = 2 * k + 1
```

---

## Traps

- `rw [ih]` right after `fun_induction` fails with "Did not find an occurrence of the pattern": the goal
  says `r` (or `b * r`), not `powFast (b * b) (e / 2)`. Unfold `r` with `show` first (R3).
- In `show`, write the goal exactly with `r` replaced by its value: `show powFast (b * b) (e / 2) = b ^ e`
  (even), `show b * powFast (b * b) (e / 2) = b ^ e` (odd).
- `rw [← Nat.pow_two]` rewrites the first `x * x` it finds. In the odd case the goal
  `b * (b * b) ^ (e / 2)` has only one, `b * b`; `b * (…)` does not match since the two factors differ.
- `Nat.pow_succ'` puts the extra factor on the **left** (`m * m ^ n`), matching `b * …`;
  `Nat.pow_succ` puts it on the right.
- Do not try to prove `2 * (e / 2) = e` by `rw`: hand it to `omega` with `h2` in the context.
- The arm names follow the infoview order; `case1` has only `b`, because `e` became `0`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per branch, with IH | `fun_induction powFast b e with \| case1 b => … \| case2 b e he r h2 ih => … \| case3 …` | R1 |
| `b ^ 0 → 1` / close `1 = b ^ 0` | `rw [Nat.pow_zero]` / `simp` | R2 |
| replace a `let` variable by its value | `show <goal with r unfolded>` | R3 |
| use the IH | `rw [ih]` (after `show`) | |
| `a * a → a ^ 2` | `rw [← Nat.pow_two]` | R4 |
| `(a ^ m) ^ n → a ^ (m * n)` | `rw [← Nat.pow_mul]` | R5 |
| `m * m ^ n → m ^ n.succ` | `rw [← Nat.pow_succ']` | R8 |
| `a ^ x = a ^ y` from `x = y` | `congr 1` | R6 |
| `2 * (e / 2) = e` from `e % 2 = 0` (and the odd version) | `omega` | R7 |
| see the state | infoview | |
