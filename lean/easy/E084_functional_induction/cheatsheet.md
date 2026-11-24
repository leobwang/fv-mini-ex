# E084 · Functional induction: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`<;>`, `decide`, `·`) are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): recursive definitions by pattern matching (E002, E026), `omega`
(E011), `decide`. E048 (a theorem that calls itself) helps but is not needed. **New here:** the
tactics `fun_induction` and `fun_cases`, which split a goal along a function's own equations.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Nat → Prop`, a property of an argument and a value).
  The step changes only what sits inside `P (…)`.
- The guide's functions, none of them the exercise's: `half n = ⌊n / 2⌋` (equations `0`, `1`, `n + 2`),
  `dbl n = 2n` (equations `0`, `n + 1`), `g m n = m + n` with the nested call
  `g (m + 1) n = g m (g m n + 1)`, and the non-recursive `clamp` (`clamp 0 = 1`, `clamp (n + 1) = n`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `case case3` | the goal for the third equation of the function (equations are counted from 1, top to bottom) |
| `n✝`, `ih1✝` | a variable or IH that Lean named itself; the `✝` means you cannot type the name. Name it with `with` (R2) |
| `ih1✝ : P k (f k)` | an induction hypothesis (IH): the statement for the argument of one recursive call |
| `k.succ`, `k.succ.succ` | `k + 1`, `k + 2` (`Nat.succ k` is `k + 1`). The pattern `k + 2` of an equation prints this way |
| `0 < k → P k (f k)` | an IH that kept a hypothesis `h : 0 < n` as a premise (R4) |
| `‹T›` | the hypothesis of type `T`, found by `assumption`; `‹_›` lets Lean infer `T` from where it is used |
| `motive` | in `#check @f.induct`: the property being proved, a function `Nat → Prop` |

---

## Part 1 · `lt_ack`

Statement: `n < ack m n` for the Ackermann function `ack`, whose third equation calls `ack` twice,
one call nested inside the other's argument. Plain induction needs an induction on `n` inside one on
`m`; functional induction follows `ack`'s three equations directly.

**R1 · `fun_induction f n`** changes the **goal list**: one goal per equation of `f`. In each goal `n`
becomes that equation's pattern, `f n` becomes its right-hand side, and every recursive call on the
right-hand side adds an IH. It applies the induction principle that Lean generates for every
recursive definition; `#check @half.induct` shows it:
`∀ (motive : Nat → Prop), motive 0 → motive 1 → (∀ (n : Nat), motive n → motive n.succ.succ) → ∀ (a : Nat), motive a`.
Give every argument of `f` (`fun_induction ack m n`), and they must be the variables the goal is about.
Placeholders: `(P : Nat → Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n (half n)` | `⊢ P 0 0`, `⊢ P 1 0`, `n✝ : Nat, ih1✝ : P n✝ (half n✝) ⊢ P n✝.succ.succ (half n✝ + 1)` |

**R2 · `fun_induction f n with | case1 => … | case3 k ih => …`** changes the **context**: it names the
pattern variables and IHs of each case. The case names are `case1, case2, …` in equation order (not
`zero`/`succ`). After the case name write the variables first, then the IHs, in the order the
infoview lists them. In the exercise each `=> …` holds the tactic that closes that case; the guide
writes `=> ?_` to keep the case open for viewing.

| Before | After |
|---|---|
| `⊢ P n (half n)` | `⊢ P 0 0`, `⊢ P 1 0`, `k : Nat, ih : P k (half k) ⊢ P k.succ.succ (half k + 1)` |

**R3 · nested recursive calls** change the **context**: one IH per recursive call. For
`g (m + 1) n = g m (g m n + 1)` the inner call `g m n` gives the first IH and the outer call
`g m (g m n + 1)` the second. Lean's own names count the other way (`ih2✝` is listed above `ih1✝`),
so name them by position with `with`. Placeholders: `(P : Nat → Nat → Nat → Prop) (m n : Nat)`.

| Before | After |
|---|---|
| `⊢ P m n (g m n)` | `n : Nat ⊢ P 0 n n`, `m n : Nat, ihIn : P m n (g m n), ihOut : P m (g m n + 1) (g m (g m n + 1)) ⊢ P m.succ n (g m (g m n + 1))` |

**R7 · `omega`** **closes** a linear-arithmetic goal over `Nat`. Each distinct application such as
`f k` or `f (f k)` is one unknown number to it, so it can chain `ih1 : k < f k` and
`ih2 : f k < f (f k)`. It reads `k.succ` as `k + 1`. Placeholders: `(f : Nat → Nat) (k : Nat)`.

| Before | After |
|---|---|
| `ih1 : k < f k, ih2 : f k < f (f k) ⊢ k.succ < f (f k) + 1` | closed |

**W1 · one IH, every case by `omega`.** `fun_induction half n <;> omega` proves `half n ≤ n`: R1, then
R7 in each of the three goals.

| Before | After |
|---|---|
| `⊢ half n ≤ n` | closed |

**W3 · two nested calls.** `n ≤ g m n`: R3 with `| case1 n => omega | case2 m n ihIn ihOut => omega`.
In `case2`, `omega` chains `ihIn : n ≤ g m n` and `ihOut : g m n + 1 ≤ g m (g m n + 1)` (R7).

| Before | After |
|---|---|
| `⊢ n ≤ g m n` | closed |

---

## Part 2 · `fib_pos`

Statement: `0 < n → 0 < fib n`, with the hypothesis `h : 0 < n` given before the colon. `fib`'s third
equation calls `fib` on `n` and on `n + 1`, so that case gets two IHs.

**R4 · a hypothesis about the induction variable** changes the **context** of every case. `fun_induction`
sees that `h : 0 < n` mentions `n` and takes it into the induction: each case gets its own
`h : 0 < (pattern)`, and each IH gains the premise, `0 < k → …`. Placeholders:
`(P : Nat → Nat → Prop) (n : Nat) (h : 0 < n)`.

| Before | After |
|---|---|
| `h : 0 < n ⊢ P n (dbl n)` | `h : 0 < 0 ⊢ P 0 0`, `ih : 0 < k → P k (dbl k), h : 0 < k.succ ⊢ P k.succ (dbl k + 2)` |

**R6 · `omega`** **closes** any goal whose hypotheses are contradictory. R4 puts `h : 0 < 0` into the
case for the pattern `0`; that case is impossible, and `omega` sees it. Placeholders: `(P : Prop)`.

| Before | After |
|---|---|
| `h : 0 < 0 ⊢ P` | closed |

**R8 · `omega` with an implication IH** **closes** the goal. Given `ih : 0 < k + 1 → 0 < f (k + 1)`,
`omega` splits on whether the premise holds; here it always does, so it gets `0 < f (k + 1)`. An IH
whose premise can fail (`0 < k → …` when `k` may be `0`) is harmless: `omega` uses it only when it
can. Placeholders: `(f : Nat → Nat) (k : Nat)`.

| Before | After |
|---|---|
| `ih : 0 < k + 1 → 0 < f (k + 1) ⊢ 0 < f k + f (k + 1)` | closed |

A case whose goal is a closed numeral statement such as `0 < 1` is closed by `decide` (or `omega`).

**W2 · a carried hypothesis.** `0 < n → n < dbl n + 1`: R4 with `| case1 => omega | case2 k ih => omega`.
`case1` has `h : 0 < 0` (R6); `case2` has `ih : 0 < k → k < dbl k + 1` (R8).

| Before | After |
|---|---|
| `h : 0 < n ⊢ n < dbl n + 1` | closed |

---

## Part 3 · `le_pred2_add`

Statement: `n ≤ pred2 n + 2`. `pred2` is not recursive, so there is nothing to induct on: you only need
one goal per equation.

**R5 · `fun_cases f n`** changes the **goal list**: one goal per equation of `f`, with `n` replaced by
the pattern and `f n` by the right-hand side, and no IHs. It also works on a recursive `f` when no IH
is needed. `with | case2 k => …` names variables as in R2. Placeholders: `(P : Nat → Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P n (clamp n)` | `⊢ P 0 1`, `k : Nat ⊢ P k.succ k` |

**W4 · a non-recursive function.** `fun_cases clamp n <;> omega` proves `n ≤ clamp n + 1`.

| Before | After |
|---|---|
| `⊢ n ≤ clamp n + 1` | closed |

---

## Traps

- `induction` is banned (also `grind`, `try?`, `exact?`) to steer you to `fun_induction` / `fun_cases`.
  A theorem that calls itself (E048) would also work, but is longer.
- `fun_induction ack m` fails: give every argument (`fun_induction ack m n`).
- Case names are `case1, case2, …` in equation order; `| zero` or `| succ` is rejected.
- IH order with nested calls: the inner call's IH is listed first (R3). In `with`, names bind by
  position, not by Lean's `ih1✝`/`ih2✝` numbering.
- With `h : 0 < n`, the IH for the smaller argument `n` reads `0 < n → …` and is useless when `n = 0`.
  In `fib`'s third case the IH for `n + 1` is the one that always applies (R8).
- Goals show the pattern `n + 2` as `n✝.succ.succ`. `omega` and `simp` read it fine; a `rw` with a
  lemma stated for `n + 2` may not find it.
- `t1 ; t2` runs `t2` on the first goal only; after `fun_induction` use `<;>` or one `with` alternative
  per case.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per equation, with IHs | `fun_induction f x y` | R1 |
| name the variables and IHs | `fun_induction f x with \| case1 => … \| case3 k ih => …` | R2 |
| two recursive calls | two IHs, inner call first: `\| case3 m n ihIn ihOut => …` | R3 |
| a hypothesis `h : 0 < n` | carried into each case; each IH becomes `0 < k → …` | R4 |
| one goal per equation, no IHs | `fun_cases f x` | R5 |
| impossible case (`h : 0 < 0`) | `omega` | R6 |
| chain IHs about `f k`, `f (f k)` | `omega` | R7 |
| IH with a premise | `omega` (splits on the premise) | R8 |
| close a numeral goal such as `0 < 1` | `decide` | TACTIC_STATES |
| same tactic in every case | `fun_induction f x <;> omega` | W1 |
| see the induction principle | `#check @f.induct` | R1 |
| see the state | infoview | |
