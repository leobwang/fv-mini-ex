# E057 · Prop vs Type: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `rfl` (E001), anonymous constructors
`⟨_, _⟩` (E004), `omega` (E011), `unfold` (E012), structures and projections (E017), `have` (E021),
`refine` (E031). **New here:** the split between `Prop` (propositions, whose elements are proofs) and
`Type` (data); proof irrelevance; subtypes `{ x // p x }` and `Subtype.ext`; Σ-types `(n : Nat) × T n`;
`Fin n` with `Fin.val` and `Fin.isLt`; `Nat.le_of_lt_succ`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- All entries use the guide's own types, not the exercise's: subtypes `{ m : Nat // n < m }` and
  `{ n : Nat // n < 10 }`, the Σ-type `(k : Nat) × Fin (2 * k + 1)`, and `bound s := 2 * s.1` on it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Prop vs Type in one paragraph

`Prop` is the universe of propositions; an element `h : P` of a proposition `P : Prop` is a proof. `Type`
is the universe of data (`Nat`, `Fin n`, pairs). Two rules separate them. (1) **Proof irrelevance:** any two
proofs `h1 h2 : P` of the same `P : Prop` are definitionally equal, so `rfl` proves `h1 = h2` (R2). Data has no
such rule: `(3 : Nat) = 4` is false. (2) **Elimination:** from a proof of `∃ n, p n` you can only build
another proof; a `def` returning `Nat` cannot `match` on it to extract `n`, because then the returned number
could depend on *which* proof was given, contradicting (1). To return a witness, carry it as data: a subtype
`{ x // p x }` (a value `x` plus a proof of `p x`) or a Σ-type `(n : Nat) × T n` (a value `n` plus a value of
type `T n`, which depends on `n`). `∃ n, p n : Prop` is the proof-only version of `{ n // p n } : Type`.

## Reading the goals

| You see | It means |
|---|---|
| `{ m // m = 2 * n }` | the subtype of `Nat`: pairs `⟨m, h⟩` with `m : Nat` and `h : m = 2 * n` (the `: Nat` is not printed) |
| `a.val` (subtype) | `Subtype.val a`, the number inside `a`; `a.property : p a.val` is its proof |
| `(n : Nat) × Fin (n + 1)` | the Σ-type (`Sigma`): pairs `⟨n, i⟩` with `n : Nat` and `i : Fin (n + 1)` |
| `s.fst`, `s.snd` | `s.1`, `s.2`: the first and second component; `s.snd : Fin (s.fst + 1)` |
| `Fin m` | the numbers `0, …, m - 1`: a `Nat` packed with a proof that it is `< m` |
| `↑i` (for `i : Fin m`) | `i.val`, the `Nat` inside `i` (`Fin.val i`) |
| `⟨k, i⟩.snd` | the second component of a literal pair; it reduces to `i` (R6) |
| `⟨n + 1, ⋯⟩` | a subtype value; `⋯` hides a proof term the infoview does not print |
| `n.succ` | `Nat.succ n`, which is `n + 1` |

---

## Part 1 · `double` (definition body)

Statement: `double (n : Nat) : { m : Nat // m = 2 * n }`. The result is data (`2 * n`) together with a proof
that it equals `2 * n`. Supply both: `⟨value, proof⟩`.

**R1 · `refine ⟨v, ?_⟩`** on a subtype changes the **goal**: you give the value `v` now, and the goal becomes
the predicate applied to `v`. In term mode the same is `⟨v, proof⟩`. Placeholders: `(n : Nat)`, the subtype
`{ m : Nat // n < m }`, `v := n + 1`.

| Before | After |
|---|---|
| `⊢ { m // n < m }` | `⊢ n < n + 1` |

The obligation in the exercise is `v = 2 * n` with `v` your value; choose `v` so that `rfl` closes it.

## Part 2 · `proof_irrel`

Statement: for any `P : Prop` and proofs `h1 h2 : P`, `h1 = h2`. This is proof irrelevance itself.

**R2 · `rfl`** **closes** `h1 = h2` for two proofs of the same `Prop`: Lean's definitional equality identifies
them. Placeholders: `(a b : Nat) (h1 h2 : a ≤ b)`. It works the same for any proposition in place of `a ≤ b`.

| Before | After |
|---|---|
| `h1 h2 : a ≤ b ⊢ h1 = h2` | no goals |

## Part 3 · `subtype_eq`

Statement: two elements `a b` of `{ n : Nat // n % 2 = 0 }` with `a.val = b.val` are equal. A subtype value is
a pair (number, proof); the numbers agree by `h` and the proofs agree by proof irrelevance.

**R3 · `apply Subtype.ext`** changes the **goal**: equality of subtype values becomes equality of their values.
The lemma is `Subtype.ext {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }} : a1.val = a2.val → a1 = a2`
(`Sort u` covers both `Prop` and `Type`). Placeholders: `(a b : { n : Nat // n < 10 })`; any predicate works.
As a term, `Subtype.ext h` proves `a = b` from `h : a.val = b.val` in one go.

| Before | After |
|---|---|
| `a b : { n // n < 10 } ⊢ a = b` | `⊢ a.val = b.val` |

**W2:** `apply Subtype.ext` on `above n = ⟨n + 1, by omega⟩`, then `rfl` (the numbers agree by definition):

```lean-goal
⊢ above n = ⟨n + 1, ⋯⟩
⊢ (above n).val = ⟨n + 1, ⋯⟩.val
```

## Part 4 · `secondOf` (definition body)

Statement: `secondOf (s : (n : Nat) × Fin (n + 1)) : Nat`. Return the number inside the second component.
`firstOf s := s.1` (given) is the model.

**R4 · `s.2`** (`Sigma.snd`) is a **term**: the second component. Its type depends on the first:
`s.2 : Fin (2 * s.1 + 1)` for the guide's Σ-type, `s.2 : Fin (s.1 + 1)` in the exercise. As a tactic,
`exact s.2` **closes** a goal of that type. Placeholders: `(s : (k : Nat) × Fin (2 * k + 1))`.

| Before | After |
|---|---|
| `s : (k : Nat) × Fin (2 * k + 1) ⊢ Fin (2 * s.fst + 1)` | no goals |

**R5 · `i.val`** (`Fin.val`) is a **term**: the `Nat` inside `i : Fin m`. It prints as `↑i`. `exact i.val`
**closes** a hole of type `Nat`. Placeholders: `(m : Nat) (i : Fin m)`. Chain R4 and R5: `s.2.val`.

| Before | After |
|---|---|
| `i : Fin m ⊢ Nat` | no goals |

## Part 5 · `secondOf_mk`

Statement: `secondOf ⟨n, i⟩ = i.val`. With your body of `secondOf`, the left side unfolds to the value of the
second component of the literal pair `⟨n, i⟩`, which reduces to `i.val`. One `rfl` (R7). R6 shows the
reduction step `rfl` performs.

**R6 · `dsimp only`** changes the **goal**: a projection of a literal pair reduces to the component,
`⟨k, i⟩.snd` → `i`. Placeholders: `(k : Nat) (i : Fin (2 * k + 1)) (P : Fin (2 * k + 1) → Prop)`.

| Before | After |
|---|---|
| `⊢ P ⟨k, i⟩.snd` | `⊢ P i` |

**R7 · `rfl`** **closes** `f ⟨a, b⟩ = value` when unfolding `f` and reducing the projections makes both sides
the same term. Placeholders: `(k : Nat) (i : Fin (2 * k + 1))`, with the guide's `bound s := 2 * s.1`.

| Before | After |
|---|---|
| `⊢ bound ⟨k, i⟩ = 2 * k` | no goals |

## Part 6 · `secondOf_le`

Statement: `secondOf s ≤ firstOf s`: the number in the second component is at most the first component. The
bound is stored in the type: `s.2 : Fin (s.1 + 1)`, so `s.2.isLt : ↑s.snd < s.fst + 1` (R9). Turn `x < n + 1`
into `x ≤ n` (R10). The result mentions `↑s.snd` and `s.fst`, the goal `secondOf s` and `firstOf s`; `exact`
accepts it because they agree after unfolding the definitions (R11). Alternative: R8 on both definitions,
then `omega` (see Traps for why the unfolding is needed).

**R8 · `unfold bound`** changes the **goal**: the defined name is replaced by its body. In the exercise,
`unfold secondOf firstOf` shows the goal in terms of `s.fst`, `s.snd`. Placeholders:
`(s : (k : Nat) × Fin (2 * k + 1)) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (bound s)` | `⊢ P (2 * s.fst)` |

**R9 · `have h := i.isLt`** changes the **context**: it adds the bound packed inside `i : Fin m`. The lemma is
`Fin.isLt {n : Nat} (self : Fin n) : ↑self < n`. Placeholders: `(m : Nat) (i : Fin m)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ↑i < m ⊢ G` |

**R10 · `Nat.le_of_lt_succ`** **closes** `m ≤ n` from `h : m < n + 1`. The lemma is
`Nat.le_of_lt_succ {m n : Nat} : m < n.succ → m ≤ n`; `n.succ` and `n + 1` are the same term. Placeholders:
`(m n : Nat) (h : m < n + 1)`. Alternative: `omega`.

| Before | After |
|---|---|
| `h : m < n + 1 ⊢ m ≤ n` | no goals |

**R11 · `exact h` across a `def`** **closes** the goal when the type of `h` matches it only after unfolding
definitions: `exact` checks types up to unfolding, like `rfl`. Placeholders:
`(s : (k : Nat) × Fin (2 * k + 1)) (h : 2 * s.1 ≤ 7)`.

| Before | After |
|---|---|
| `h : 2 * s.fst ≤ 7 ⊢ bound s ≤ 7` | no goals |

**W3: the same bound on the guide's type, the `omega` route.** `have h := s.2.isLt` (R9), `unfold bound`
(R8), then `omega` closes the goal:

| Start | After `have h := s.2.isLt` | After `unfold bound` |
|---|---|---|
| `⊢ ↑s.snd ≤ bound s` | `h : ↑s.snd < 2 * s.fst + 1 ⊢ ↑s.snd ≤ bound s` | `h : ↑s.snd < 2 * s.fst + 1 ⊢ ↑s.snd ≤ 2 * s.fst` |

The one-term route is `exact Nat.le_of_lt_succ s.2.isLt` (R9's lemma as a term, R10, R11).

---

## Traps

- An `∃` only eliminates into `Prop`. `def f (h : ∃ n, p n) : Nat := match h with | ⟨n, _⟩ => n` is rejected:
  a function returning data cannot read the witness out of a proof. Use a subtype or a Σ-type when the witness
  is needed later.
- A subtype value needs both parts. `⟨2 * n⟩` alone is a type error; `⟨2 * n, rfl⟩` works only because the
  obligation `2 * n = 2 * n` is syntactically true. `⟨n + n, rfl⟩` fails: `n + n = 2 * n` is true but not by
  definition (unfolding `2 * n` recurses on the variable `n` and gets stuck). Prove it with `by omega` instead.
- `omega` does not unfold `secondOf` or `firstOf`: on `secondOf s ≤ firstOf s` it fails even with `h` from R9
  in the context, because it treats `secondOf s` as an unknown number. `unfold` them first (R8). `rfl` and
  `exact` unfold by themselves (R7, R11).
- Once `↑s.snd` appears in the goal, `omega` adds the bound `↑s.snd < s.fst + 1` of a `Fin` by itself, so after
  R8 the `have` of R9 is optional for `omega`; it is still needed for the `exact` route (R10).
- `s.2` has type `Fin (s.1 + 1)`, not `Nat`. Where a `Nat` is expected Lean inserts the coercion `↑s.2`,
  which is `s.2.val`; writing `.val` yourself keeps the term readable and is what the infoview shows as `↑`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a subtype value | `⟨value, proof⟩`, or `by refine ⟨value, ?_⟩` | R1 |
| two proofs of one `Prop` are equal | `rfl` | R2 |
| equality of subtype values | `Subtype.ext h` / `apply Subtype.ext` | R3 |
| first / second component of a Σ-pair | `s.1` / `s.2` (`s.fst` / `s.snd`) | R4 |
| the number inside `i : Fin m` | `i.val` (prints `↑i`) | R5 |
| `⟨a, b⟩.snd` → `b` | `dsimp only` | R6 |
| an equation that holds by unfolding | `rfl` | R7 |
| see a definition's body in the goal | `unfold f g` | R8 |
| the bound of `i : Fin m` | `i.isLt : ↑i < m` | R9 |
| `x ≤ n` from `x < n + 1` | `Nat.le_of_lt_succ h` | R10 |
| a fact that matches the goal after unfolding | `exact` | R11 |
| see the state | infoview | |
