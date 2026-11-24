# M010 · Decidable instance: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `refine`, `rw`, `constructor`, `rintro`
patterns, `decide` on closed arithmetic facts. **New here:** the class `Decidable p` and `DecidablePred p`,
building an instance with `decidable_of_iff`, the core instance `Nat.decidableExistsLE` for bounded `∃`, the
core lemma `Nat.le_mul_self`, and `decide` running *your* instance. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `exact`/`refine`/`rw`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Decidability in one paragraph

`Decidable p` (for `p : Prop`) is a class with two constructors: `isTrue (h : p)` and `isFalse (h : ¬ p)`.
A value of it is an *algorithm* that settles `p`. `DecidablePred p` (for `p : α → Prop`) abbreviates
`(a : α) → Decidable (p a)`: one decision per input. `decide` closes a closed goal `q` by finding an instance
`Decidable q` and *evaluating* it; if it evaluates to `isTrue`, the goal is proved. `IsSquare n := ∃ k, k * k = n`
ranges over all `k : Nat`, an infinite search, so core Lean has no instance for it; you supply one by
proving `IsSquare n` equivalent to a *bounded* search, which Lean can decide.

## Reading the goals

| You see | It means |
|---|---|
| `Decidable p` | a decision procedure for `p`: an `isTrue` proof or an `isFalse` disproof |
| `DecidablePred p` | `(n : Nat) → Decidable (p n)`, a decision for each `n` (R1) |
| `(n : Nat) → Decidable (p n)` | how Lean prints a hypothesis of type `∀ n, Decidable (p n)` (its values are data, not proofs) |
| `inst✝ : Decidable q` | an instance in the context, from a `[Decidable q]` binder; `✝` marks a name you cannot type |
| `∃ k, k ≤ n ∧ P k` | "some `k` in `0..n` satisfies `P`": a bounded search, decidable (R3) |
| `left✝ : A k` | the part `rintro` bound to `_`: kept, but with an unusable name (R5) |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` after `constructor` (R4) |
| `IsSquare n` | not unfolded in the infoview, but `rintro ⟨k, hk⟩` and `⟨k, hk⟩` see through it |

---

## Part 1 · `decIsSquare`

Statement: build `DecidablePred IsSquare`, i.e. for each `n` a decision of `∃ k, k * k = n`. Use the bounded
search `∃ k, k ≤ n ∧ k * k = n` (if `k * k = n` then `k ≤ k * k = n`), and prove the two equivalent.

### Building the instance

**R1 · `intro n`** (term mode `fun n => …`) changes the **context and the goal**: `DecidablePred p` is a
function type, so introducing its argument leaves a single `Decidable` goal. Placeholders: `(p : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ DecidablePred p` | `n : Nat ⊢ Decidable (p n)` |

**R2 · `refine decidable_of_iff q ?_`** changes the **goal**: a decision of `p` reduces to a decision of an
equivalent `q`, plus a proof of `q ↔ p`. Lemma:
`decidable_of_iff : {b : Prop} → (a : Prop) → (a ↔ b) → [Decidable a] → Decidable b`
(as `#check` prints it; here `a` is `q`, `b` is `p`). You write `q`
explicitly; Lean must find `Decidable q` by itself (R3). In the exercise you write it in term mode,
`decidable_of_iff q (by …)`, and the `by` block gets the `q ↔ p` goal. Placeholders: `(p q : Prop) [Decidable q]`.

| Before | After |
|---|---|
| `inst✝ : Decidable q ⊢ Decidable p` | `⊢ q ↔ p` |

**R3 · `Nat.decidableExistsLE`** (core instance) **closes** `Decidable (∃ k, k ≤ n ∧ P k)` via
`exact inferInstance`: Lean tries `k = 0, 1, …, n`. Its type:
`Nat.decidableExistsLE : {p : Nat → Prop} → [DecidablePred p] → DecidablePred fun n => ∃ m, m ≤ n ∧ p m`.
It needs `DecidablePred P`; for `P k := (k * k = n)` that is `instDecidableEqNat` (equality on `Nat` is
decidable). You never name R3: it is why `decidable_of_iff (∃ k, k ≤ n ∧ k * k = n) …` type-checks. The form
must be exactly `k ≤ n ∧ …` (or `k < n ∧ …`, `Nat.decidableExistsLT`). Placeholders:
`(n : Nat) (P : Nat → Prop) [DecidablePred P]`.

| Before | After |
|---|---|
| `inst✝ : DecidablePred P ⊢ Decidable (∃ k, k ≤ n ∧ P k)` | no goals |

### Proving the `↔`

**R4 · `constructor`** on an `↔` changes the **goal list**: one goal per direction (`Iff.intro`).
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B` (case `mp`), `⊢ B → A` (case `mpr`) |

**R5 · `rintro ⟨k, _, hk⟩`** changes the **context and the goal**: it introduces the hypothesis of an
implication and takes it apart along its nesting `∃ k, (A k ∧ B k)`. For `(∃ k, B k) → G`, including
`IsSquare n → G`, the pattern is `⟨k, hk⟩`. Placeholders: `(A B : Nat → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ (∃ k, A k ∧ B k) → G` | `k : Nat, left✝ : A k, hk : B k ⊢ G` |

**R6 · `refine ⟨x, ?_, hb⟩`** (or `exact ⟨x, ha, hb⟩`) changes the **goal**: it supplies the witness `x` and
the second conjunct, leaving the first. `⟨x, ha, hb⟩` is short for `⟨x, ⟨ha, hb⟩⟩`. In term mode write
`(by …)` where a `?_` would go. `⟨k, hk⟩` also builds `IsSquare n` directly. Placeholders:
`(A B : Nat → Prop) (x : Nat) (hb : B x)`.

| Before | After |
|---|---|
| `⊢ ∃ k, A k ∧ B k` | `⊢ A x` |

**R7 · `rw [← h]`** with `h : f k = n` changes the **goal**: every `n` becomes `f k`. In the exercise this
turns the bound `k ≤ n` into `k ≤ k * k`. Placeholders: `(f : Nat → Nat) (k n : Nat) (h : f k = n)`.

| Before | After |
|---|---|
| `⊢ P n` | `⊢ P (f k)` |

**R8 · `exact Nat.le_mul_self a`** **closes** the goal. Lemma: `Nat.le_mul_self : ∀ (n : Nat), n ≤ n * n`
(true at `0` and `1` too). Placeholders: `(a : Nat)`.

| Before | After |
|---|---|
| `⊢ a ≤ a * a` | no goals |

### Worked combination (W1, W2 on `IsDouble n := ∃ k, k + k = n`)

**W1.** The equivalence by R4, R5, R6, R7, with `Nat.le_add_right : ∀ (n k : Nat), n ≤ n + k` in place of
R8. States after `constructor`, then along case `mpr`:

```lean-goal
⊢ (∃ k, k ≤ n ∧ k + k = n) → IsDouble n
⊢ IsDouble n → ∃ k, k ≤ n ∧ k + k = n
⊢ ∃ k, k ≤ n ∧ k + k = n
⊢ k ≤ n
⊢ k ≤ k + k
```

**W2.** `instance decIsDouble : DecidablePred IsDouble := fun n => decidable_of_iff (∃ k, k ≤ n ∧ k + k = n)
(bounded_iff_isDouble n)`: R1, then R2 with the W1 theorem as the `↔` proof. You may prove your `↔` the
same way, as a helper theorem placed before the instance, or inline in `(by …)`.

---

## Part 2 · `square_49`

Statement: `IsSquare 49`. A closed goal: once `decIsSquare` exists, `decide` finds it and evaluates it.

**R9 · `decide`** **closes** a closed decidable goal `Q` by evaluating its `Decidable Q` instance to `isTrue`.
Here that instance is yours: `decidable_of_iff` hands the question to the bounded search (R3), which tries
`k = 0, …, 49` and finds `7`. In the guide: `∃ k, k ≤ 10 ∧ k + k = 10` and, through `decIsDouble`,
`IsDouble 12` (W3).

## Part 3 · `not_square_50`

Statement: `¬ IsSquare 50`. **R9 · `decide`** again: `¬ Q` is decidable when `Q` is
(`instDecidableNot`), and the search over `k = 0, …, 50` evaluates to `isFalse`. In the guide:
`¬ ∃ k, k ≤ 9 ∧ k + k = 9` and `¬ IsDouble 13` (W3).

---

## Traps

- `decide` *runs* the instance. An instance built from classical logic (`Classical.propDecidable`,
  `Classical.dec`) has no algorithm inside: `decide` reports that the instance "did not reduce to `isTrue` or
  `isFalse`" and got stuck at `Classical.choice`. Build it
  from `decidable_of_iff` and core instances only; the `↔` proof inside can be anything (proofs are not run).
- Without your instance in scope (or before its declaration), `decide` fails with
  "failed to synthesize", naming `Decidable (IsSquare 49)`.
- The bounded statement must match an instance syntactically: `∃ k, k ≤ n ∧ k * k = n` works; a bound such as
  `k * k ≤ n` or the conjuncts in the other order (`k * k = n ∧ k ≤ n`) does not.
- `rintro ⟨k, hk⟩` on `IsSquare n → …` binds `hk : k * k = n`. `rw [← hk]` then replaces `n` by `k * k`;
  `rw [hk]` would look for `k * k` in the goal `k ≤ n` and fail.
- `decidable_of_iff` wants `q ↔ p` with the *decidable* side first: `(bounded ↔ IsSquare n)`, not the reverse.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| start a `DecidablePred` | `fun n => …` / `intro n` | R1 |
| decide `p` via an equivalent `q` | `decidable_of_iff q (by …)` | R2 |
| a decidable stand-in for `∃ k, …` | `∃ k, k ≤ n ∧ …` | R3 |
| split `A ↔ B` | `constructor` | R4 |
| destructure `∃ k, A k ∧ B k` | `rintro ⟨k, _, hk⟩` | R5 |
| build `∃ k, A k ∧ B k` | `⟨k, ha, hb⟩` / `refine ⟨k, ?_, hb⟩` | R6 |
| replace `n` by `k * k` using `hk : k * k = n` | `rw [← hk]` | R7 |
| `k ≤ k * k` | `Nat.le_mul_self k` | R8 |
| a closed decidable fact or its negation | `decide` | R9 |
| see the state | infoview | |
