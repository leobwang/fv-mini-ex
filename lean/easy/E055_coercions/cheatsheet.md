# E055 · Coercions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` (E001), anonymous constructors
`⟨_, _⟩` (E004), `Iff` and `.mp` (E005), `omega` (E011), `unfold` (E012, E030), structures, fields and
projections (E017), instances (E019), `have` (E021), `refine` (E031). **New here:** coercions: the class
`Coe α β`, the attribute `@[coe]`, the arrow `↑`, and how `rfl` and `exact` see through them. Two core
`Nat` lemmas. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `exact`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- All entries use the guide's own structure `Even2` (a `Nat` with a proof `val % 2 = 0`), whose coercion
  to `Nat` is `Even2.half e := e.val / 2`. That is deliberately not "the value itself", so you can see that
  `↑e` means *whatever function the instance holds*.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Coercions in one paragraph

A coercion is a function Lean inserts by itself when a term has type `α` but a `β` is expected. You
declare one with an instance of the class `Coe α β`, whose single field is the function `coe : α → β`:
`instance : Coe Even2 Nat := ⟨Even2.half⟩`. After that, `(e : Nat)` (a type ascription), `↑e` (an explicit
request) and `e + 1` (an expected `Nat`) all elaborate to `Even2.half e`. The instance is gone after
elaboration: the term is just the function applied. `@[coe]` on that function changes only printing:
the infoview shows `Even2.half e` as `↑e`. So `↑e` in a goal is an ordinary function call, and `unfold`,
`rfl` and `exact` treat it as one.

## Reading the goals

| You see | It means |
|---|---|
| `↑a` | the coercion function applied to `a`: in the exercise `Pos.toNat a`, in the guide `Even2.half a` |
| `((x : Pos) : Nat)` in source | first say `x` is a `Pos`, then ask for it as a `Nat`: prints as `↑x` |
| `{ val := n, pos := h }` | the structure value `⟨n, h⟩ : Pos` (`Pos.mk n h`) |
| `{ val := 6, even := ⋯ }` | `⋯` hides a proof term the infoview does not print |
| `{ val := n, even := hn }.val` | the `val` field of that value; it reduces to `n` (R6) |
| `a.val`, `a.pos` | `Pos.val a : Nat` (data field), `Pos.pos a : 0 < a.val` (proof field) |
| `a.add b` | `Pos.add a b` (dot notation: `a`'s type is `Pos`, so `a.add` looks up `Pos.add`) |
| `↑(a.add b)` | the coercion applied to `Pos.add a b` |
| `↑e.double` | `↑(e.double)`: function application binds tighter than `↑` |
| `{ val := 1, pos := Nat.one_pos }` | `one` after `unfold one`; `Nat.one_pos : 0 < 1` is the core proof stored in `one` (spec) |
| `Coe Pos Nat`, `@[coe]` in source | the coercion instance (its one field is the function `Pos → Nat`) and the print-as-`↑` attribute; see the paragraph above |
| `n ≠ 0`, `¬↑a = 0` | `¬ (n = 0)`, i.e. `n = 0 → False`; `simp` prints `↑a ≠ 0` in the second form |
| `e.val / 2`, `n % 2` (guide only) | `Nat` division rounded down (`7 / 2 = 3`) and remainder (`7 % 2 = 1`) |

---

## Part 1 · `Pos.toNat` (definition body)

Statement: `Pos.toNat (p : Pos) : Nat`, the function behind the coercion `instCoePosNat`. You write the body.
`coe_mk` says `↑⟨n, h⟩ = n`, so `toNat` must return the stored number.

**R1 · `e.val`** is a **term**: the data field `val` of a structure value, `Even2.val e : Nat`. As a tactic,
`exact e.val` **closes** a hole of type `Nat`. Placeholders: `(e : Even2)`.

| Before | After |
|---|---|
| `e : Even2 ⊢ Nat` | no goals |

## Part 2 · `Pos.add` (definition body)

Statement: `Pos.add (a b : Pos) : Pos`. A `Pos` is two things, a number and a proof that it is positive, so
the body must supply both: `⟨value, proof⟩`.

**R2 · `refine ⟨v, ?_⟩`** changes the **goal**: you give the data field `v` now, and the goal becomes the proof
field's statement about `v`. In term mode the same value is `⟨v, proof⟩`; a `def` body may also be `by …`.
Placeholders: `(e : Even2)`, `v := e.val + 2`.

| Before | After |
|---|---|
| `e : Even2 ⊢ Even2` | `⊢ (e.val + 2) % 2 = 0` |

**R3 · `have h := e.even`** changes the **context**: a proof field is a theorem about one particular value,
and `have` puts it in the context. In the exercise, `a.pos : 0 < a.val`. Placeholders: `(e : Even2)`.

| Before | After |
|---|---|
| `⊢ G` | `h : e.val % 2 = 0 ⊢ G` |

**R4 · `Nat.add_pos_left`** **closes** a positivity goal for a sum. The lemma is
`Nat.add_pos_left {m : Nat} (h : 0 < m) (n : Nat) : 0 < m + n`: `m` is implicit (read off `h`), `n` explicit.
Placeholders: `(m n : Nat) (h : 0 < m)`. Use it as a term, `Nat.add_pos_left h n`, directly inside `⟨_, _⟩`.
Alternative: R3 for each field, then `omega`.

| Before | After |
|---|---|
| `h : 0 < m ⊢ 0 < m + n` | no goals |

## Part 3 · `coe_mk`

Statement: `((⟨n, h⟩ : Pos) : Nat) = n`, shown as `↑{ val := n, pos := h } = n`. The coercion of a literal
constructor is the number inside it. Once `Pos.toNat` is written, both sides are the same term after
unfolding, so one `rfl` closes it. R5 and R6 show what `rfl` does behind the scenes.

**R5 · `unfold Even2.half`** changes the **goal**: `↑e` is the `@[coe]` function applied to `e`, so unfolding
that function replaces `↑e` by its body. In the exercise: `unfold Pos.toNat`. Placeholders:
`(e : Even2) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P ↑e` | `⊢ P (e.val / 2)` |

**R6 · `dsimp only`** changes the **goal**: a field of a literal constructor reduces to the value stored in
it, `{ val := n, even := hn }.val` → `n`. If both sides then agree, `dsimp only` closes the goal. Placeholders:
`(n : Nat) (hn : n % 2 = 0) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P { val := n, even := hn }.val` | `⊢ P n` |

**R7 · `rfl`** **closes** `a = b` when both sides are the same term after unfolding definitions. It unfolds
the coercion function (R5), other `def`s such as `one` or `Pos.add`, and constructor fields (R6) by itself.
Placeholders: `(e : Even2)`.

| Before | After |
|---|---|
| `e : Even2 ⊢ ↑e = e.val / 2` | no goals |

**W1: R5 then R6 by hand** on `↑⟨n, hn⟩ = n / 2` (`dsimp only` closes the last goal, since both sides agree):

```lean-goal
⊢ ↑{ val := n, even := hn } = n / 2
⊢ { val := n, even := hn }.val / 2 = n / 2
```

## Part 4 · `coe_one`

Statement: `((one : Pos) : Nat) = 1`. `one` is the `def` `⟨1, Nat.one_pos⟩`. Unfold `one`, the coercion, and the
field: `rfl` does all three (R7). To watch it happen, `unfold one Pos.toNat` (R5) leaves the field of a literal constructor,
`{ val := 1, pos := Nat.one_pos }.val = 1`, which R6 (`dsimp only`) reduces to `1 = 1` and closes.

## Part 5 · `coe_add`

Statement: `↑(a.add b) = ↑a + ↑b`: coercing the sum equals the sum of the coercions. With your `Pos.toNat` and
`Pos.add`, the left side unfolds to `(⟨a.val + b.val, _⟩ : Pos).val`, which reduces to `a.val + b.val`, and the
right side unfolds to the same. So `rfl` (R7) again. It works because `Pos.add` puts `a.val + b.val` (literally)
in the data field.

**W3: when `rfl` is not enough.** `Even2.double e := ⟨2 * e.val, _⟩`. Then `↑e.double = e.val` reduces to
`2 * e.val / 2 = e.val`, which is true but not the same term on both sides: `rfl` fails. Unfold (R5), reduce the
field (R6), then `omega`:

```lean-goal
⊢ ↑e.double = e.val
⊢ { val := 2 * e.val, even := ⋯ }.val / 2 = e.val
⊢ 2 * e.val / 2 = e.val
```

## Part 6 · `coe_ne_zero`

Statement: `(a : Nat) ≠ 0`, shown as `↑a ≠ 0`. The fact you have is the proof field `a.pos : 0 < a.val` (R3).
Turn `0 < x` into `x ≠ 0` (R8). The result is about `a.val`, the goal about `↑a`; `exact` accepts it because the
two agree after unfolding `↑` (R9).

**R8 · `Nat.pos_iff_ne_zero`** **closes** `n ≠ 0` from `h : 0 < n`. The lemma is
`Nat.pos_iff_ne_zero {n : Nat} : 0 < n ↔ n ≠ 0`; `.mp` is its left-to-right direction, a function
`0 < n → n ≠ 0`. Placeholders: `(n : Nat) (h : 0 < n)`. Alternative: `Nat.ne_of_gt h`.

| Before | After |
|---|---|
| `h : 0 < n ⊢ n ≠ 0` | no goals |

**R9 · `exact h` across `↑`** **closes** the goal when the type of `h` matches it only after unfolding the
coercion. `exact` checks types up to unfolding definitions, like `rfl`. Placeholders:
`(e : Even2) (h : e.val / 2 ≠ 0)`.

| Before | After |
|---|---|
| `h : e.val / 2 ≠ 0 ⊢ ↑e ≠ 0` | no goals |

**W4:** with `h4 : 4 ≤ e.val`, first `have h : 0 < e.val / 2 := by omega`, then
`exact Nat.pos_iff_ne_zero.mp h` closes `↑e ≠ 0` (R8, R9):

```lean-goal
⊢ ↑e ≠ 0
```

---

## Traps

- `↑a` is a function call, not a type annotation. `omega` and `simp` treat `↑a` as an unknown number and know
  nothing about it; `unfold Pos.toNat` (R5) first, or use `rfl` / `exact`, which unfold by themselves.
- `rfl` succeeds only when both sides are the same term after unfolding. `↑(a.add b) = ↑a + ↑b` is `rfl` because
  `Pos.add` stores `a.val + b.val` literally; with a body such as `b.val + a.val` it would need `Nat.add_comm`.
- A `Pos` needs both fields. `⟨a.val + b.val⟩` alone is a type error: the proof `0 < a.val + b.val` is missing.
- The proof field takes the value you chose: after `refine ⟨v, ?_⟩` the goal is about `v`, so choose `v` first.
- `Nat.add_pos_left` takes `h : 0 < m` first and `n` second; the result is `0 < m + n` with `m` on the left.
- `@[coe]` does not create a coercion; the `Coe` instance does. `@[coe]` only makes `Pos.toNat a` print as `↑a`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a data field of `p` | `p.val` | R1 |
| build a structure value | `⟨value, proof⟩`, or `by refine ⟨value, ?_⟩` | R2 |
| use a proof field | `a.pos`, or `have h := a.pos` | R3 |
| `0 < m + n` from `h : 0 < m` | `Nat.add_pos_left h n` | R4 |
| see what `↑a` is | `unfold Pos.toNat` | R5 |
| `⟨n, h⟩.val` → `n` | `dsimp only` | R6 |
| an equation that holds by unfolding (through `↑`) | `rfl` | R7 |
| `n ≠ 0` from `h : 0 < n` | `Nat.pos_iff_ne_zero.mp h` | R8 |
| a fact about `a.val` for a goal about `↑a` | `exact` | R9 |
| arithmetic under `↑` | `unfold` first, then `omega` | R5, W3 |
| see the state | infoview | |
