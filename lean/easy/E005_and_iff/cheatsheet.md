# E005 · And and Iff: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E004: `theorem`/`example`, tactic mode (`by`), `intro`, `exact`, `apply`, and the
term-mode facts that a proof of `A → B` is a function and a proof of `A ∧ B` is a pair `⟨ha, hb⟩`.
**New here:** the connectives `∧` (and) and `↔` (if and only if) in tactic mode. `constructor` splits a goal
built from either; `rintro` and `obtain` take a conjunction apart with a pattern; `.mp` / `.mpr` extract
the two directions of an `↔`. Also `·` to focus one goal, and `False`.

## How to read an entry

Each entry is one tactic or one proof term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change. With several goals open, a tactic acts on the first one; the others wait.
- `A B C G : Prop` are arbitrary propositions. `G` plays the role of "whatever the goal is".
- A hypothesis `k` only finishes the example.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `A ∧ B` | "A and B". A proof is a pair: a proof of `A` and a proof of `B` |
| `A ∧ B ∧ C` | `A ∧ (B ∧ C)`: `∧` nests to the right, so the spec's `P ∧ (Q ∧ R)` is printed `P ∧ Q ∧ R` |
| `(A ∧ B) ∧ C` | grouped on the left; a different proposition with the same meaning |
| `A ↔ B` | "A if and only if B": a pair of implications `A → B` and `B → A` |
| `h.mp`, `h.mpr` | for `h : A ↔ B`: the proofs of `A → B` and of `B → A` |
| `False` | the proposition with no proof. `k : B → False` says `B` cannot hold |
| `case mp`, `case mpr` | the two goals `constructor` makes from an `↔` (→ and ←) |
| `case left`, `case right` | the two goals `constructor` makes from an `∧` |
| `right✝ : B` | a hypothesis with no usable name (the `✝`); it came from a `_` in a pattern |

---

## Part 1 · `and_comm_iff`

Statement: `P ∧ Q ↔ Q ∧ P`: the order of a conjunction does not matter. Split the `↔` (R1), and in each
focused direction (R2) take the conjunction apart (R3) and build the swapped one (R5).

**R1 · `constructor`** on `A ↔ B` changes the **goal list**: one goal becomes two implications, `A → B`
(labelled `case mp`) and then `B → A` (`case mpr`). Each still needs an `intro` (or `rintro`).
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R2 · `· tacs`** changes the **goal list**: it focuses the first goal. The tactics in the block see only
that goal, and the block fails unless they close it. All lines of a block are indented under the `·`
(type `\.`). Placeholders: `(A B : Prop)`.

| Before | After the first `·` block |
|---|---|
| `⊢ A → B`, `⊢ B → A` | `⊢ B → A` |

**R3 · `rintro ⟨ha, hb⟩`** changes the **goal and the context**: `intro` plus destructuring. The goal
`A ∧ B → G` loses its premise; the two halves enter the context under the names in the pattern.
Placeholders: `(A B G : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B → G` | `ha : A, hb : B ⊢ G` |

**R4 · `obtain ⟨ha, hb⟩ := h`** changes the **context**: a conjunction already in the context is replaced by
its two halves; the goal stays. Use it after a plain `intro h`. Placeholders: `(A B G : Prop) (h : A ∧ B)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `ha : A, hb : B ⊢ G` |

**R5 · `exact ⟨ha, hb⟩`** **closes** `A ∧ B` with the anonymous constructor (E004): the brackets pair a
proof of each half, in the order of the goal. Placeholders: `(A B : Prop) (ha : A) (hb : B)`.

| Before | After |
|---|---|
| `ha : A, hb : B ⊢ A ∧ B` | no goals |

**R6 · `constructor`** on `A ∧ B` changes the **goal list**: one goal per half, `A` (`case left`) then `B`
(`case right`). It splits only the outermost `∧`. The step-by-step alternative to R5.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B` | `⊢ A`, `⊢ B` |

**W2** (R1, R2, R3, R5 on `A ∧ A ↔ A`):

| Step | Goals left |
|---|---|
| start | `⊢ A ∧ A ↔ A` |
| `constructor` | `⊢ A ∧ A → A`, `⊢ A → A ∧ A` |
| `· rintro ⟨ha, _⟩` / `exact ha` | `⊢ A → A ∧ A` |
| `· intro ha` / `exact ⟨ha, ha⟩` | no goals |

**W4** (R1 with `<;>`): on `A ↔ A`, `constructor <;> intro h <;> exact h` runs `intro h` on both goals and then
`exact h` on both. This works only when both directions take the same steps.

## Part 2 · `and_assoc_iff`

Statement: `(P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R)`: regrouping a conjunction does not matter. Same plan as Part 1, but the
patterns and the brackets must follow the grouping of each side.

**R7 · `rintro ⟨ha, hb, hc⟩`** changes the **goal and the context** on a right-nested conjunction.
`A ∧ B ∧ C` is `A ∧ (B ∧ C)`, and the flat pattern `⟨ha, hb, hc⟩` abbreviates `⟨ha, ⟨hb, hc⟩⟩`.
Placeholders: `(A B C G : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C → G` | `ha : A, hb : B, hc : C ⊢ G` |

**R8 · `rintro ⟨⟨ha, hb⟩, hc⟩`** changes the **goal and the context** on a left-grouped conjunction. The
inner brackets match the parentheses of `(A ∧ B) ∧ C`. Placeholders: `(A B C G : Prop)`.

| Before | After |
|---|---|
| `⊢ (A ∧ B) ∧ C → G` | `hc : C, ha : A, hb : B ⊢ G` |

**R9 · `exact ⟨ha, hb, hc⟩`** **closes** `A ∧ B ∧ C`: flat brackets nest to the right, like `∧`.
Placeholders: `(A B C : Prop) (ha : A) (hb : B) (hc : C)`.

| Before | After |
|---|---|
| `⊢ A ∧ B ∧ C` | no goals |

**R10 · `exact ⟨⟨ha, hb⟩, hc⟩`** **closes** `(A ∧ B) ∧ C`: the left group needs its own brackets.
Placeholders: as in R9.

| Before | After |
|---|---|
| `⊢ (A ∧ B) ∧ C` | no goals |

**W1** (R8, then R5 with a discarded part) on `(A ∧ B) ∧ C → C ∧ A`. The `_` throws the proof of `B` away;
Lean keeps it as an unnamed `right✝`:

| Step | State |
|---|---|
| start | `⊢ (A ∧ B) ∧ C → C ∧ A` |
| `rintro ⟨⟨ha, _⟩, hc⟩` | `hc : C, ha : A ⊢ C ∧ A` |
| `exact ⟨hc, ha⟩` | no goals |

## Part 3 · `iff_both_ways`

Statement: from `h : P ↔ Q`, `hp : P` and `hq' : Q → False`, conclude `False`: the hypotheses contradict each
other. Work backwards from `False` through `hq'` (R13), then get `Q` from `P` through `h` (R11).

**R13 · `apply k`** with `k : B → False` changes the **goal**: to prove `False` it suffices to prove `B`
(E003's `apply`, with conclusion `False`). Placeholders: `(B : Prop) (k : B → False)`.

| Before | After |
|---|---|
| `hb : B ⊢ False` | `hb : B ⊢ B` |

**R11 · `h.mp`** with `h : A ↔ B` is a proof of `A → B`, so `h.mp ha : B` for `ha : A` (`exact h.mp ha`).
`apply h.mp` changes the **goal** from `B` to `A`. `h.mp` is the same as `h.1`.
Placeholders: `(A B : Prop) (h : A ↔ B) (ha : A)`.

| Before | After |
|---|---|
| `ha : A ⊢ B` | `ha : A ⊢ A` |

**R12 · `h.mpr`** with `h : A ↔ B` is a proof of `B → A`, so `h.mpr hb : A` for `hb : B`. `apply h.mpr`
changes the **goal** from `A` to `B`. `h.mpr` is the same as `h.2`.
Placeholders: `(A B : Prop) (h : A ↔ B) (hb : B)`.

| Before | After |
|---|---|
| `hb : B ⊢ A` | `hb : B ⊢ B` |

**W3** (R11 twice, as one term): with `h1 : A ↔ B`, `h2 : B ↔ C`, `ha : A`, the goal `⊢ C` is closed by
`exact h2.mp (h1.mp ha)`. Read it inside out: `h1.mp ha : B`, then `h2.mp (h1.mp ha) : C`.

---

## Traps

- `constructor` on `A ↔ B` leaves **implications**: each goal still starts with `→` and needs `intro` or
  `rintro`.
- `constructor` on `A ∧ B ∧ C` splits only once: you get `A` and `B ∧ C`.
- Patterns and brackets follow the grouping. `⟨ha, hb, hc⟩` fits `A ∧ (B ∧ C)`; `(A ∧ B) ∧ C` needs
  `⟨⟨ha, hb⟩, hc⟩`. A wrong pattern either fails or leaves an unsplit `ha : A ∧ B`.
- `h.mp` goes left to right (`A → B` for `h : A ↔ B`), `h.mpr` right to left. `apply h.mp` needs the goal to
  be the right-hand side.
- After `constructor`, `t1 ; t2` and separate lines run on the first goal only. Use `·` blocks (or `<;>`)
  so it is clear which goal each tactic works on.
- `simp`, `simp_all`, `grind`, and the library facts `and_comm` and `and_assoc` are banned here: the point is
  to do each step by hand.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split goal `A ↔ B` into `A → B`, `B → A` | `constructor` | R1 |
| work on one goal at a time | `· tacs` (indented block) | R2 |
| goal `A ∧ B → G`: intro and split | `rintro ⟨ha, hb⟩` | R3 |
| split a hypothesis `h : A ∧ B` | `obtain ⟨ha, hb⟩ := h` | R4 |
| prove `A ∧ B` | `exact ⟨ha, hb⟩` | R5 |
| prove `A ∧ B` step by step | `constructor` (goals `A`, `B`) | R6 |
| intro and split `A ∧ B ∧ C` | `rintro ⟨ha, hb, hc⟩` | R7 |
| intro and split `(A ∧ B) ∧ C` | `rintro ⟨⟨ha, hb⟩, hc⟩` | R8 |
| prove `A ∧ B ∧ C` | `exact ⟨ha, hb, hc⟩` | R9 |
| prove `(A ∧ B) ∧ C` | `exact ⟨⟨ha, hb⟩, hc⟩` | R10 |
| use `h : A ↔ B` forwards | `h.mp ha : B`, or `apply h.mp` | R11 |
| use `h : A ↔ B` backwards | `h.mpr hb : A`, or `apply h.mpr` | R12 |
| goal `False`, have `k : B → False` | `apply k` (goal becomes `B`), or `exact k hb` | R13 |
| same tactics on every goal | `t <;> u` | W4 |
| see the state | infoview (cursor after a tactic) | |
