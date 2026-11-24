# E003 · intro, exact, apply: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001 (`theorem`/`example`, `rfl`, `decide`) and E002 (`def` on `Nat`).
**New here:** tactic mode and the three basic tactics. `by` starts a **tactic proof**: a sequence of
tactics, one per line (or separated by `;`), each of which transforms the **proof state** until no goal is
left. `intro` moves an assumption from the goal into the context, `exact` closes a goal with a proof
term, `apply` works backwards from a hypothesis's conclusion to its premises. Behind all three: a proof of
`A → B` is a **function** from proofs of `A` to proofs of `B`, and a proof of `∀ n, q n` is a function
from numbers `n` to proofs of `q n`.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that change. With several goals open, the tactic acts on the first one; the others wait.
- `A B C G : Prop` are arbitrary propositions (statements that may be true or false). `h : A` means "`h` is
  a proof of `A`". `q : Nat → Prop` is a predicate: `q 3` is a statement about the number `3`.
- A hypothesis `k` only finishes the example.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `P Q R : Prop` | three propositions, given as parameters of the theorem |
| `h : P → Q` | a proof that `P` implies `Q`; also a function turning proofs of `P` into proofs of `Q` |
| `P → Q → R` | `P → (Q → R)`: `→` nests to the right. "If `P` and `Q`, then `R`" |
| `(P → Q) → (Q → R) → P → R` | three premises `P → Q`, `Q → R`, `P`; conclusion `R` |
| `p : Nat → Prop` | a predicate on natural numbers |
| `step : ∀ (n : Nat), p n → p (n + 1)` | for every `n`, `p n` implies `p (n + 1)`; Lean prints `∀ n` as `∀ (n : Nat)` |
| `case a` | the label Lean prints on each goal when `apply` leaves several (`a` is its default name for an unnamed premise); a single new goal gets no label |
| `⊢ G` | the current goal: what is left to prove |

---

## Part 1 · `imp_trans`

Statement: `(P → Q) → (Q → R) → P → R`: implication is transitive. Introduce the three premises (R2), then
work backwards from `R` (R4, twice) until the goal is a hypothesis (R3).

**R1 · `intro h`** changes the **goal and the context**: the goal `A → B` loses its premise `A`, which
enters the context as `h : A`. The goal becomes `B`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A → B` | `h : A ⊢ B` |

**R2 · `intro h1 h2 h3`** changes the **goal and the context**: several `intro`s in one, one name per
premise, left to right. Placeholders: `(A B C G : Prop)`. You may stop early: `intro h1` leaves
`B → C → G` as the goal.

| Before | After |
|---|---|
| `⊢ A → B → C → G` | `h1 : A, h2 : B, h3 : C ⊢ G` |

**R4 · `apply h`** with `h : A → B` changes the **goal**: to prove `B` it suffices to prove `A`. The goal
must be the conclusion of `h`. Placeholders: `(A B : Prop) (h : A → B)`.

| Before | After |
|---|---|
| `h : A → B ⊢ B` | `h : A → B ⊢ A` |

**R3 · `exact h`** **closes** the goal when `h` proves exactly the goal. Placeholders: `(A : Prop) (h : A)`.

| Before | After |
|---|---|
| `h : A ⊢ A` | no goals |

**W1** (R2, R4, R3 on `(A → B) → A → B`):

| Step | State |
|---|---|
| start | `⊢ (A → B) → A → B` |
| `intro hab ha` | `hab : A → B, ha : A ⊢ B` |
| `apply hab` | `hab : A → B, ha : A ⊢ A` |
| `exact ha` | no goals |

## Part 2 · `two_premises`

Statement: from `h : P → Q → R`, `hp : P`, `hq : Q`, conclude `R`. The premises are already in the context:
apply `h` (R5), which leaves one goal per premise, and close each (R3).

**R5 · `apply h`** with `h : A → B → C → G` changes the **goal list**: the goal `G` is replaced by one goal
per premise of `h`, in order: `A`, then `B`, then `C`. Each is labelled `case a`. Placeholders:
`(A B C G : Prop) (h : A → B → C → G)`.

| Before | After |
|---|---|
| `h : A → B → C → G ⊢ G` | `⊢ A`, `⊢ B`, `⊢ C` |

The next tactic works on the first goal, `A`; once it is closed, `B` is first, and so on:

| Step | Goals left |
|---|---|
| `apply h` | `⊢ A`, `⊢ B`, `⊢ C` |
| `exact ka` | `⊢ B`, `⊢ C` |
| `exact kb` | `⊢ C` |
| `exact kc` | no goals |

**W2** (R5 then R4): a new goal from `apply` can itself be worked backwards. With
`h : A → B → C`, `f : G → A`, `g : G`, `kb : B`:

| Step | Goals left |
|---|---|
| start | `⊢ C` |
| `apply h` | `⊢ A`, `⊢ B` |
| `apply f` | `⊢ G`, `⊢ B` |
| `exact g` | `⊢ B` |
| `exact kb` | no goals |

## Part 3 · `swap_args`

Statement: `(P → Q → R) → (Q → P → R)`: the order of two premises does not matter. Introduce all three
premises (R2); the goal is then `R`, which `h` gives once fed its arguments in **its** order (R6).

**R6 · `exact h a b c`** **closes** `G` from `h : A → B → C → G`, `a : A`, `b : B`, `c : C`. `h a b c` is
function application: `h` takes a proof of `A`, then of `B`, then of `C`, and returns a proof of `G`.
Arguments are separated by spaces and must follow the order of `h`'s premises, not the order in which the
hypotheses were introduced. Placeholders: `(A B C G : Prop)`.

| Before | After |
|---|---|
| `a : A, b : B, c : C ⊢ G` | no goals |

`apply h` followed by one `exact` per premise (R5, R3) does the same job in several steps.

## Part 4 · `step_twice`

Statement: from `step : ∀ n, p n → p (n + 1)` and `h0 : p 0`, conclude `p 2`. Work backwards with `step`
(R8): `p 2` needs `p 1`, which needs `p 0`, which is `h0` (R3).

**R7 · `exact h 3`** with `h : ∀ n, q n` **closes** `q 3`: a proof of `∀ n, q n` is a function from
numbers to proofs, and `h 3 : q 3`. Placeholders: `(q : Nat → Prop) (h : ∀ n, q n)`, with `h` in the context.

| Before | After |
|---|---|
| `⊢ q 3` | no goals |

**R8 · `apply h`** with `h : ∀ n, q n → q (n + 1)` changes the **goal**. `apply` chooses `n` by matching
the conclusion `q (n + 1)` against the goal: for `q 5` it takes `n := 4`, since `4 + 1` computes to `5`
(the same computation `rfl` uses, E001). The goal becomes the premise `q 4`. Placeholders:
`(q : Nat → Prop) (h : ∀ n, q n → q (n + 1)) (k : q 4)`; `h` stays in the context unchanged.

| Before | After |
|---|---|
| `k : q 4 ⊢ q 5` | `k : q 4 ⊢ q 4` |

**W3** (R8 twice, R3) with a step of 2, `h : ∀ n, q n → q (n + 2)` and `k : q 1`:

| Step | State |
|---|---|
| start | `k : q 1 ⊢ q 5` |
| `apply h` | `k : q 1 ⊢ q 3` |
| `apply h` | `k : q 1 ⊢ q 1` |
| `exact k` | no goals |

**W4** (R6, R7): the same proof as one term, `exact h 3 (h 1 k)`. Read it inside out: `h 1 k : q 3`, then
`h 3 (h 1 k) : q 5`. Parentheses group an argument that is itself an application.

---

## Traps

- `intro` needs a `→` (or `∀`) at the front of the goal. On a goal `R` with no arrow it fails.
- `apply h` needs the goal to match the **conclusion** of `h` (the part after the last `→`). `apply hpq`
  on goal `R` with `hpq : P → Q` fails: `Q` is not `R`.
- `exact h` needs `h` to prove the goal **exactly**. To use `h : A → B` on goal `B`, write `apply h` or
  `exact h a`, not `exact h`.
- After `apply` with several premises, the goals are in premise order; each tactic works on the first one.
- `h a b` is application, written with spaces. `h (a, b)` means something else (a pair) and fails.
- `simp`, `simp_all` and `grind` are banned in this exercise: the point is to do each step by hand.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| move a premise `A` of goal `A → B` into the context | `intro h` | R1 |
| move several premises | `intro h1 h2 h3` | R2 |
| close the goal with a hypothesis that states it | `exact h` | R3 |
| goal `B`, have `h : A → B` | `apply h` (goal becomes `A`) | R4 |
| goal `G`, have `h : A → B → G` | `apply h` (goals `A`, then `B`) | R5 |
| feed proofs to an implication | `exact h a b` | R6 |
| use `h : ∀ n, q n` at a number | `exact h 3` | R7 |
| goal `q 5`, have `h : ∀ n, q n → q (n + 1)` | `apply h` (goal becomes `q 4`) | R8 |
| see the state | infoview (cursor after a tactic) | |
