# M003 · Postage stamps: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `∃` and the anonymous constructor `⟨…⟩` (E007), `omega`
(E011), ordinary induction on `Nat` (E014), `have` (E021), `·` focusing. **New here:** **strong induction**
with core Lean's `Nat.strongRecOn`, how `induction` folds a hypothesis about `n` into the induction
hypothesis, peeling off base cases with `by_cases`, and destructuring an `∃` hypothesis with `obtain`.
Core Lean only, no Mathlib.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. "no goals"
  means the tactic closed the goal.
- `P`, `Q : Nat → Prop` are "the rest of your goal" as a function of the number; `G : Prop` is any goal.
- Hypotheses that contain `, ` (such as `ih : ∀ (m : Nat), m < n → P m`) are written next to the table
  instead of inside a `⊢` cell.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `∀ (m : Nat), m < n → P m` | for every `m` with `m < n`, `P m` (how Lean prints `∀ m < n, P m`) |
| `case ind` | the single goal made by `induction n using Nat.strongRecOn` |
| `case pos`, `case neg` | the two goals made by `by_cases h : p`: `h : p` resp. `h : ¬p` |
| `¬n = 8` | `n ≠ 8`, i.e. `n = 8 → False` |
| `∃ a b, n = 3 * a + 5 * b` | `∃ a, ∃ b, …`, with `a b : Nat` (types not printed) |
| `n - 3` | **truncated** subtraction on `Nat`: `n - 3 = 0` when `n < 3` |
| `a b : Nat` (in the context) | two hypotheses `a : Nat` and `b : Nat` printed on one line |
| `3 * a + 5 * b` | `(3 * a) + (5 * b)`: `*` binds tighter than `+` |

---

## Part 1 · `stamps`

Statement: `stamps (n : Nat) (h : 8 ≤ n) : ∃ a b : Nat, n = 3 * a + 5 * b`: every amount of at least 8 cents
is a sum of 3-cent and 5-cent stamps. Plan: strong induction on `n` (R1, R2); the base cases `n = 8, 9, 10`
by `by_cases` and explicit witnesses (R3, R4, R5); for `n ≥ 11`, use `ih` at `n - 3 ≥ 8` and add one 3-cent
stamp (R6, R7, R4, R5).

### The idea

Ordinary induction (E014) proves `P (k + 1)` from `P k` only. Here the step from `n` back to `n - 3` jumps
by 3, so you need **strong induction**: to prove `P n` you may assume `P m` for **every** `m < n`. In Lean:
`induction n using Nat.strongRecOn`, which gives one case (`ind`) with
`ih : ∀ (m : Nat), m < n → P m`. There is no separate base case in the principle: values of `n` for which
`ih` is useless (here `n = 8, 9, 10`, where `n - 3 < 8`) you handle yourself with `by_cases`.

### Strong induction

**R1 · `induction n using Nat.strongRecOn with | _ n ih => ?_`** changes the **context**: it adds
`ih : ∀ (m : Nat), m < n → P m`. The goal `P n` stays the same, now under `case ind`.
`Nat.strongRecOn (n : Nat) (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n` is core Lean's
strong-induction principle (`motive` is the `P` being proved). The `_` matches the one case `ind` without
naming it; in the exercise write the tactics after `=>` directly. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `n : Nat ⊢ P n`, plus `ih : ∀ (m : Nat), m < n → P m` |

**R2 · the same, with `h : c ≤ n` in the context** changes the **context**: `induction` first reverts every
hypothesis that mentions `n`, so the statement it proves is `c ≤ n → Q n`. After the step `h : c ≤ n` is back,
and the hypothesis is `ih : ∀ (m : Nat), m < n → c ≤ m → Q m`: it takes **three** arguments, the number `m`, a
proof of `m < n` and a proof of `c ≤ m`. In the exercise `c` is `8`. Placeholders: `(c : Nat) (Q : Nat → Prop)
(n : Nat) (h : c ≤ n)`.

| Before | After |
|---|---|
| `h : c ≤ n ⊢ Q n` | `h : c ≤ n ⊢ Q n`, plus `ih : ∀ (m : Nat), m < n → c ≤ m → Q m` |

### Base cases

**R3 · `by_cases h4 : n = 4`** changes the **goal list and the context**: two goals, `case pos` with
`h4 : n = 4` and `case neg` with `h4 : ¬n = 4`. `· tac` proves the first; the next unindented lines work on
the second. Chain three of them for `8, 9, 10`; the last goal then has all three negations, which `omega`
reads as `n ≥ 11` (together with `h`). Placeholders: `(n : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `n : Nat ⊢ G` | `h4 : n = 4 ⊢ G`, `h4 : ¬n = 4 ⊢ G` |

**R4 · `refine ⟨x, y, ?_⟩`** changes the **goal**: it supplies the witnesses of `∃ a b, R a b` and leaves
`R x y`. `exact ⟨x, y, by omega⟩` does R4 and R5 in one go. For `8` choose `a, b` with `3a + 5b = 8`, and so
on. Placeholders: `(n : Nat) (h : n = 7)`.

| Before | After |
|---|---|
| `h : n = 7 ⊢ ∃ a b, n = 2 * a + 3 * b` | `h : n = 7 ⊢ n = 2 * 2 + 3 * 1` |

**R5 · `omega`** **closes** a goal of linear arithmetic over `Nat` (`+`, `*` by a literal, `-`, `=`, `<`, `≤`,
`¬`, `∧`, `∨`), using every such hypothesis in the context. It knows that `n - 2` is truncated and splits on
`n < 2` by itself. In the exercise it proves the base-case equations from `h8 : n = 8`, the side conditions
`n - 3 < n` and `8 ≤ n - 3` from `h` and the three negations, and the final equation from `hab`.
Placeholders: `(n : Nat) (h : 4 ≤ n) (h4 : ¬n = 4) (h5 : ¬n = 5)`.

| Before | After |
|---|---|
| `h : 4 ≤ n, h4 : ¬n = 4, h5 : ¬n = 5 ⊢ 4 ≤ n - 2` | no goals |

### The step

**R6 · `have hm := ih m hlt hle`** changes the **context**: `ih` is a function; applied to `m`, a proof
`hlt : m < n` and a proof `hle : c ≤ m` (R2), it yields `hm : Q m`. In the exercise both proofs are
`(by omega)` written in place. Placeholders: `(n : Nat) (Q : Nat → Prop) (hlt : n - 2 < n) (hle : 4 ≤ n - 2)`,
with `ih : ∀ (m : Nat), m < n → 4 ≤ m → Q m`.

| Before | After |
|---|---|
| `⊢ Q n` | `hm : Q (n - 2) ⊢ Q n` |

**R7 · `obtain ⟨a, b, hab⟩ := e`** changes the **context**: `e : ∃ a b, Q a b` is replaced by `a b : Nat` and
`hab : Q a b`. `obtain ⟨a, b, hab⟩ := ih m p q` does R6 and R7 at once. Placeholders:
`(Q : Nat → Nat → Prop) (G : Prop) (e : ∃ a b, Q a b)`.

| Before | After |
|---|---|
| `e : ∃ a b, Q a b` `⊢ G` | `a b : Nat, hab : Q a b ⊢ G` |

Then R4 with one more 3-cent stamp than `hab` gives, and R5 (it uses `hab : n - 3 = 3 * a + 5 * b` and
`n ≥ 11`).

### Worked combination (W1, not the exercise's statement)

**W1: every `n` is even or odd**, `∃ k, n = 2 * k ∨ n = 2 * k + 1`, stepping back by 2. R1 (no hypothesis on
`n`, so `ih` takes only `m` and `m < n`), then `by_cases` for `0` and `1` (R3 → R4 → R5), then one `obtain`
on `ih (n - 2) (by omega)` (R6 + R7) and R4 → R5. The states of the main goal:

```lean-goal
⊢ ∃ k, n = 2 * k ∨ n = 2 * k + 1
```

| After `obtain ⟨k, hk⟩ := ih (n - 2) (by omega)` |
|---|
| `h0 : ¬n = 0, h1 : ¬n = 1, hk : n - 2 = 2 * k ∨ n - 2 = 2 * k + 1 ⊢ ∃ k, n = 2 * k ∨ n = 2 * k + 1` |

---

## Traps

- Plain `induction n` (E014) gives `ih` for `n - 1` only, which never helps here. Use `using Nat.strongRecOn`.
- `ih` has an extra premise `8 ≤ m` because `h : 8 ≤ n` mentioned `n` (R2): `ih (n - 3)` needs two proofs,
  `n - 3 < n` and `8 ≤ n - 3`, not one.
- `8 ≤ n - 3` holds only for `n ≥ 11`. Every `n` in `8, 9, 10` must be split off first (R3), or `omega`
  fails on the side condition.
- `n - 3` is truncated subtraction. Do not "move" it across `=` by hand; `omega` handles it.
- After `by_cases`, `·` proves the `pos` goal only; the next lines must not be indented under it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| assume the claim for all smaller `m` | `induction n using Nat.strongRecOn with \| _ n ih => …` | R1 |
| what `ih` looks like with `h : 8 ≤ n` around | `ih : ∀ (m : Nat), m < n → 8 ≤ m → …` | R2 |
| split off a base case | `by_cases h8 : n = 8` then `· …` | R3 |
| give the witnesses of `∃ a b` | `exact ⟨x, y, by omega⟩` / `refine ⟨x, y, ?_⟩` | R4 |
| linear `Nat` arithmetic, incl. `-` and `¬ =` | `omega` | R5 |
| apply `ih` | `ih m (by omega) (by omega)` | R6 |
| unpack an `∃` hypothesis | `obtain ⟨a, b, hab⟩ := e` | R7 |
| see the state | infoview | |
