# E072 · fin_cases and vectors: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`<;>`, `all_goals`, `rw`) are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's vector literal `![…]`, the
finite types `Fin n` and `ZMod n`, the cast `Fin n → ℕ`, and proving a statement about a variable of a
finite type by checking every value (`fin_cases`), with `simp`, `simp_all` and `rfl` closing the cases.

## How to read an entry

Each entry is one tactic or one lemma used by `simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n` | the type `{0, 1, …, n-1}`; an element is a natural number `k` with a proof of `k < n` |
| `⟨k, ⋯⟩` | the element `k` of `Fin n`; `⋯` is the hidden proof of `k < n` |
| `(fun i => i) ⟨2, ⋯⟩` | the index `2`, printed this way after `fin_cases`; `simp` turns it into `2` (R4) |
| `![a, b, c]` | the vector `(a, b, c)`: the function `Fin 3 → α` with `0 ↦ a`, `1 ↦ b`, `2 ↦ c` |
| `f i` | entry `i` of the vector `f`, counted from 0 |
| `↑i` | `Fin.val i : ℕ`, the number behind `i : Fin n`; you write it `(i : ℕ)` |
| `ZMod n` | the integers modulo `n`: `+`, `*` wrap around, so in `ZMod 3`, `2 + 2 = 1` and `3 = 0` |
| `case «0»` | the goal for the value `0` after `fin_cases` |

---

## Part 1 · `f_ge`

Statement: for every `i : Fin 3`, `f i ≥ 5`, where `f = ![5, 7, 9]`. `i` has three values: split into three
goals, then evaluate `f` at each and compare numbers.

**R1 · `rfl`** **closes** `![a, b, c] i = x` when `x` is entry `i`: Lean computes an entry of a vector
literal by unfolding. Placeholders: `{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `⊢ ![a, b, c] 2 = c` | no goals |

**R2 · `fin_cases i`** changes the **goal list and the context**: `i : Fin 3` leaves the context and there is
one goal for each value `0, 1, 2`. Placeholders: `(P : Fin 3 → Prop) (i : Fin 3)`. Follow it with `<;> tac`
to run `tac` on all three goals.

| Before | After |
|---|---|
| `i : Fin 3 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨2, ⋯⟩)` |

**R3 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. `simp [D]` does the same
and then keeps simplifying (R4–R6). Placeholders: `D` defined by `def g : Fin 3 → ℕ := ![2, 4, 6]`.

| Before | After |
|---|---|
| `⊢ P g` | `⊢ P ![2, 4, 6]` |

**R4 · `simp` on the printed index** changes the **goal**: `(fun i => i) ⟨2, ⋯⟩` is beta-reduced to `⟨2, ⋯⟩`,
and the *simprocs* `Fin.reduceFinMk` and `Fin.isValue` (built-in `simp` procedures that compute instead of
rewriting with a stated lemma) write it as the numeral `2`; for `0` and `1` the lemmas `Fin.zero_eta`,
`Fin.mk_one` do it. You never name any of them. Placeholders: `(P : Fin 3 → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((fun i => i) ⟨2, ⋯⟩)` | `⊢ P 2` |

**R5 · `simp` on an entry of a vector literal** changes the **goal**, using `Matrix.cons_val_zero`,
`Matrix.cons_val_one`, … (a vector literal is built with `Matrix.vecCons`, hence the names). Placeholders:
`{α : Type} (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (![a, b, c] 2)` | `⊢ P c` |

**R6 · `simp`** **closes** a comparison of `ℕ` numerals: it evaluates `+`, `*`, `^` and decides `≤`, `<`, `≥`,
`=` between numerals.

| Before | After |
|---|---|
| `⊢ 9 ≥ 5` | no goals |
| `⊢ 3 ^ 2 < 10` | no goals |

**W1.** `g i ≤ 6` with `g = ![2, 4, 6]`: `fin_cases i` (R2) gives three goals, the last one

```lean-goal
⊢ g ((fun i => i) ⟨2, ⋯⟩) ≤ 6
```

and `all_goals simp [g]` (R3–R6) closes all three.

---

## Part 2 · `f_eq_seven`

Statement: if `f i = 7` then `i = 1`. After the split, the hypothesis `h` reads `f 0 = 7` (that is, `5 = 7`) in
case `0`: that case is impossible, and you close it by simplifying `h` to `False`. In case `1` the goal is
`1 = 1`.

**R7 · `simp [D] at h`** changes the **context**: it simplifies the hypothesis `h` instead of the goal. If `h`
becomes `False`, the goal is closed (a false hypothesis proves anything). Placeholders: `(n : ℕ)`,
`D = g` as in R3.

| Before | After |
|---|---|
| `h : g 1 = n ⊢ P n` | `h : 4 = n ⊢ P n` |
| `h : g 0 = 4 ⊢ G` | no goals |

**R8 · `simp_all [D]`** **closes** the goal here. It simplifies every hypothesis and the goal, and uses each
simplified hypothesis to rewrite the others. In one call it covers both kinds of case: `h` false (closed as in
R7) and `h` true (the goal itself simplifies to `True`). `simp [D] at h` alone closes the false cases but
leaves the true one open, with `h : True` and the goal untouched. Placeholders: `(n : ℕ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `h : g 1 = n, hp : P 4 ⊢ P n` | no goals |

**W2.** `g i = 6 → (i : ℕ) = 2`: after `fin_cases i` the case goals are

```lean-goal
⊢ ↑((fun i => i) ⟨0, ⋯⟩) = 2
⊢ ↑((fun i => i) ⟨2, ⋯⟩) = 2
```

with `h : g ((fun i => i) ⟨0, ⋯⟩) = 6` and so on; `all_goals simp_all [g]` (R8) closes all three.

---

## Part 3 · `sq_lt`

Statement: for every `i : Fin 4`, `(i : ℕ) ^ 2 < 10`. The goal contains the cast `↑i`; after the split, `simp`
reads off the number behind each index and computes.

**R9 · `simp` on a cast** changes the **goal**: `↑⟨3, ⋯⟩`, the value of the `Fin` element `⟨3, ⋯⟩`, is `3`.
This holds by definition (`Fin.val` reads the first field of `⟨k, h⟩`; the lemma stating it is
`Fin.val_mk : (⟨k, h⟩ : Fin n).val = k`), and `simp` reduces it by itself, with no name. Placeholders:
`(P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ↑((fun i => i) ⟨3, ⋯⟩)` | `⊢ P 3` |

Then R6 closes the comparison of numerals.

**W3.** `(i : ℕ) * 3 < 7` for `i : Fin 3`: after `fin_cases i`,

```lean-goal
⊢ ↑((fun i => i) ⟨2, ⋯⟩) * 3 < 7
```

and `all_goals simp` (R9 then R6) closes each case.

---

## Part 4 · `zmod3_prod`

Statement: for every `x : ZMod 3`, `x * (x + 1) * (x + 2) = 0`: one of three consecutive numbers is divisible
by 3. `ZMod 3` has three elements, so split and compute.

**R10 · `fin_cases x`** for `x : ZMod 3` changes the **goal list and the context**, exactly as R2: for `n ≥ 1`,
`ZMod n` is *defined* as `Fin n`, so `fin_cases` lists the residues `0, 1, 2`. Placeholders:
`(P : ZMod 3 → Prop) (x : ZMod 3)`.

| Before | After |
|---|---|
| `x : ZMod 3 ⊢ P x` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨2, ⋯⟩)` |

**R11 · `rfl`** **closes** an equation between closed `ZMod n` expressions: both sides compute (by unfolding,
mod `n`) to the same residue. Example: `3 * 4 = 12 = 2 + 2·5`, so `(3 : ZMod 5) * 4 = 2`. It works on the
printed indices too, since `(fun i => i) ⟨4, ⋯⟩` unfolds to `4`.

| Before | After |
|---|---|
| `⊢ 3 * 4 = 2` | no goals |
| `⊢ (fun i => i) ⟨4, ⋯⟩ + 1 = 0` | no goals |

**W4.** `x * (x + 1) = 0` in `ZMod 2`: `fin_cases x` (R10) gives

```lean-goal
⊢ (fun i => i) ⟨0, ⋯⟩ * ((fun i => i) ⟨0, ⋯⟩ + 1) = 0
⊢ (fun i => i) ⟨1, ⋯⟩ * ((fun i => i) ⟨1, ⋯⟩ + 1) = 0
```

and `all_goals rfl` (R11) closes both.

---

## Traps

- `decide` is banned. It would check all cases at once here, but it only works when every value can be
  computed; `fin_cases` still works when the entries are real numbers (E074's matrices), where `decide` cannot.
- `simp` does not compute in `ZMod n`: on `zmod3_prod` it rewrites `a * b = 0` into `a = 0 ∨ b = 0` and stops at
  residues such as `1 + 2 = 0`, which it cannot evaluate. Use `rfl` (R11).
- `rfl` does not see through hypotheses: in `f_eq_seven` the false case needs `h`, so use `simp_all` (R8), not
  `simp` or `rfl`.
- `simp` with no `[f]` does not unfold `f`, so it cannot evaluate `f 0`. Pass the definition's name.
- `t1 ; t2` and a new line run `t2` on the first goal only. After `fin_cases`, use `<;>` or `all_goals`.
- `fin_cases` needs the variable's type to be finite and concrete: `Fin 4`, `ZMod 3`, not `Fin n` or `ZMod n`
  with a variable `n` (`ZMod 0` is `ℤ`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| read an entry of `![…]` | `rfl` | R1 |
| one goal per value of `i : Fin n` | `fin_cases i` | R2 |
| run a tactic on every case | `fin_cases i <;> tac` | TACTIC_STATES |
| unfold `f`, read entries, compare numbers | `simp [f]` | R3–R6 |
| use a hypothesis about `f i` in every case | `simp_all [f]` | R7, R8 |
| `↑⟨k, ⋯⟩ → k`, then compute | `simp` | R9, R6 |
| one goal per residue of `x : ZMod n` | `fin_cases x` | R10 |
| closed arithmetic in `ZMod n` | `rfl` | R11 |
| see the state | infoview | |
