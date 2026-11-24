# E028 · grind: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001 (`decide`), E003 (tactic mode, `exact`), E008 (`¬`, `False`, proof by contradiction),
E010 (`simp`), E011 (`omega`, `Nat` truncated subtraction, `Int`).
**New here:** the automated tactic `grind`. It works by contradiction: it adds the negation of the goal to
the context and tries to derive `False`. Several cooperating modules share one pool of facts:

- **congruence closure:** it groups terms known to be equal into classes and uses that a function applied
  to equal arguments gives equal results (`a = c` gives `f a = f c`);
- **linear arithmetic** over `Nat` and `Int` (the fragment of `omega`, E011), including truncated `-`;
- **ring normalisation:** polynomial identities in commutative (semi)rings, like the tactic `ring`;
- **case splits** on `if … then … else …`, `∧`, `∨`, `↔` and similar, refuting each case.

A fact derived by one module (say `x = y` from arithmetic) is passed to the others (congruence then gives
`g x = g y`). `grind` reads every hypothesis in the context by itself, and either closes the goal or fails
with a report of what it knew. It never leaves a changed goal behind, so every entry below goes from one
state to "no goals".

## How to read an entry

Each entry is one call of `grind` on one kind of goal. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter (the variables are left out).
- `{α β : Type}` are arbitrary types, `f : α → β` an arbitrary function (nothing is known about it but
  its type), `a b c : Nat` natural numbers, `x y : Int` integers.
- "no goals" means the tactic closed the goal: the **goal list** became empty.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `f : Nat → Nat` | an unknown function: only its type is given, so only congruence says anything about it |
| `f a` | `f` applied to `a` |
| `n - m` with `n m : Nat` | **truncated** subtraction: `n - m = 0` whenever `m ≥ n` (E011) |
| `a ≠ b` | `¬ (a = b)`, that is `a = b → False` |
| `if p then a else b` | `a` when the proposition `p` holds, `b` otherwise |
| `inst✝ : Decidable p` | an unnamed instance hypothesis: `p` can be decided, which `if p` needs |
| `∀ (x : Nat), f x = x + 1` | a fact about every `x`; `grind` instantiates it at terms it sees (W4) |
| `x * y` | product of two variables: fine for ring normalisation, opaque for linear arithmetic |

---

## Part 1 · `grind_congr`

Statement: with `h1 : f a = b`, `h2 : a = c`, `h3 : b + 1 = 5`, prove `f c = 4`. Congruence puts `f a`,
`f c` and `b` in one class (R1); arithmetic gets `b = 4` from `h3` (R2). One `grind` does both.

**R1 · `grind`, congruence closure** **closes** an equality between applications of the same function to
arguments that the context makes equal, through any chain of equalities. Placeholders:
`{α β : Type} (f : α → β) (a b c : α) (h1 : a = b) (h2 : b = c)`.

| Before | After |
|---|---|
| `h1 : a = b, h2 : b = c ⊢ f a = f c` | no goals |

**R2 · `grind`, linear arithmetic** **closes** a linear goal over `Nat` or `Int` from linear facts in the
context, as `omega` would (E011). Placeholders: `(a : Nat) (h : a + 3 = 8)`.

| Before | After |
|---|---|
| `h : a + 3 = 8 ⊢ a = 5` | no goals |

## Part 2 · `grind_antisymm`

Statement: with `h1 : x ≤ y`, `h2 : y ≤ x` over `Int`, prove `g x = g y` for an unknown `g`. Arithmetic
derives `x = y` (R4); that equality feeds congruence (R3).

**R3 · `grind`, arithmetic feeds congruence** **closes** `f x = f y` when `x = y` is not in the context but
follows from arithmetic. `omega` cannot do this (it knows nothing about `f`), and congruence alone cannot
(it does not do arithmetic). Placeholders: `{β : Type} (f : Int → β) (x y : Int) (h : x + 1 = y + 1)`.

| Before | After |
|---|---|
| `h : x + 1 = y + 1 ⊢ f x = f y` | no goals |

**R4 · `grind`, order facts** **closes** an equality from inequalities that pin both sides together.
Over `Int`, `x < y + 1` is `x ≤ y`. Placeholders: `(x y : Int) (h1 : x < y + 1) (h2 : y < x + 1)`.

| Before | After |
|---|---|
| `h1 : x < y + 1, h2 : y < x + 1 ⊢ x = y` | no goals |

## Part 3 · `grind_ring`

Statement: with `h : a = b + 2` over `Nat`, prove `(a - 1) * (a - 1) = (b + 1) * (b + 1)`. The `Nat`
subtraction `a - 1` is exact here (`a ≥ 2`), so `a - 1 = b + 1` (R5); then both products have equal
factors (R1), and ring normalisation (R6) handles any rearrangement.

**R5 · `grind` with `Nat` subtraction** **closes** the goal. As in `omega`, `a - 2` is split into the cases
`2 ≤ a` (true difference) and `a < 2` (`0`); here `h` rules out the second. Placeholders:
`(a b : Nat) (h : a = b + 3)`.

| Before | After |
|---|---|
| `h : a = b + 3 ⊢ a - 2 = b + 1` | no goals |

**R6 · `grind`, ring normalisation** **closes** an identity of commutative rings (`Int`) or semirings
(`Nat`, no subtraction) by expanding both sides into sums of monomials. Products of variables are allowed
here, unlike in linear arithmetic. Placeholders: `(x y : Int)`.

| Before | After |
|---|---|
| `⊢ (x - y) * (x + y) = x * x - y * y` | no goals |

**W1 · R5 then R1.** The subtraction becomes exact, then congruence goes through two functions:

| Before | After |
|---|---|
| `h : a = b + 2 ⊢ g (f (a - 2)) = g (f b)` | no goals |

**W2 · substitution then R6.** `h` replaces `x` by `y + 1` (one class), and both sides normalise to
`y * y + 2 * y + 1`:

| Before | After |
|---|---|
| `h : x = y + 1 ⊢ x * x = y * y + 2 * y + 1` | no goals |

## Part 4 · `grind_ite`

Statement: with `hf : f n = if n < 5 then 0 else n` and `h : f n ≠ 0`, prove `5 ≤ n`. `grind` assumes the
negated goal `¬ 5 ≤ n`, i.e. `n < 5` (R8), and splits the `if` (R7). Branch `n < 5`: `f n = 0` contradicts
`h`. Branch `¬ n < 5`: contradicts the negated goal.

**R7 · `grind`, `if` split** **closes** the goal by trying both cases `p` and `¬ p` of every
`if p then … else …` it sees, in hypotheses or goal, and refuting the wrong ones. Placeholders:
`(p : Prop) [Decidable p] (a b : Nat) (h : (if p then a else b) = a) (hab : a ≠ b)`. `[Decidable p]` is a
type-class requirement: `p` has a decision procedure. `n < 5`, `a = 0` on `Nat` or `Int` meet it.

| Before | After |
|---|---|
| `h : (if p then a else b) = a, hab : a ≠ b ⊢ p` | no goals |

In case `¬ p`, `h` says `b = a`, which contradicts `hab`; so only case `p` survives, and that is the goal.

**R8 · `grind`, negated goal and `≠`** **closes** the goal by adding its negation (`¬ a = 2`) and deriving
`False` with the disequalities in the context. Placeholders: `(a : Nat) (h1 : a < 3) (h2 : a ≠ 0) (h3 : a ≠ 1)`.

| Before | After |
|---|---|
| `h1 : a < 3, h2 : a ≠ 0, h3 : a ≠ 1 ⊢ a = 2` | no goals |

**W3 · R7 inside a hypothesis about `f`.** The `if` in `hf` is split; in each branch the facts are linear
(R2): `1 = 6` is false, and `2 * a = 6` gives `a = 3`.

| Before | After |
|---|---|
| `hf : f a = if a = 0 then 1 else 2 * a, h : f a = 6 ⊢ a = 3` | no goals |

### Beyond this exercise (W4)

**W4 · `∀` hypotheses.** `grind` instantiates a universally quantified hypothesis at terms in its pool
(here `x := 2`, because `f 2` appears), then arithmetic finishes. Context: `hf : ∀ (x : Nat), f x = x + 1`
(left out of the cell below, because its `,` would read as a hypothesis separator).

| Before | After |
|---|---|
| `⊢ f 2 = 3` | no goals |

To make `grind` use a lemma from the library, pass it: `grind [Nat.mul_comm]`.

---

## Traps

- `grind` does **no induction**. A goal that needs it (a property of every list, of every `n` by recursion)
  fails; set up the induction first (E014), then `grind` may close each case.
- `grind` does **not** prove **nonlinear inequalities** such as `x * x ≥ 0` over `Int`: ring normalisation
  handles equalities, linear arithmetic handles inequalities, and neither handles both at once.
- `grind` fails, it never half-succeeds: there is no partial progress to inspect. Read its failure
  report, which lists the equivalence classes and facts it had.
- It only sees what is in the context or passed in `grind [...]`. A definition you wrote is not unfolded
  unless you pass it (`grind [myDef]`).
- No setup is needed before it: no `intro`, `rw`, `split` or `constructor`. Doing them first does no harm.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `f a = f c` from a chain of equalities | `grind` | R1 |
| linear goal over `Nat`/`Int` | `grind` (or `omega`) | R2 |
| `f x = f y` where `x = y` follows by arithmetic | `grind` | R3 |
| equality from two inequalities | `grind` (or `omega`) | R4 |
| `Nat` `-` that is exact by a hypothesis | `grind` (or `omega`) | R5 |
| commutative-ring identity | `grind` (or `ring`, needs Mathlib) | R6 |
| goal depending on an `if` | `grind` | R7, W3 |
| contradiction from `≠` facts | `grind` | R8 |
| use a `∀` hypothesis at a term | `grind` | W4 |
| use a library lemma | `grind [lemma]` | |
| see the state | infoview (cursor after a tactic) | |
