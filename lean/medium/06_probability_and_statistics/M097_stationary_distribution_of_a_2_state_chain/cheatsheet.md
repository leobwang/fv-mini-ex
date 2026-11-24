# M097 · Stationary distribution of a 2-state chain: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, vectors
`Fin 2 → ℝ` and their literals `![x, y]`, matrices and `Matrix.vecMul` (row vector times matrix), and the
tactics `field_simp`, `nlinarith`, `positivity`.

**The math.** A Markov chain on states `{0, 1}` has transition matrix
$P = \begin{pmatrix} 1-a & a \\ b & 1-b \end{pmatrix}$: row $i$ is the distribution of the next state
given the current state $i$. A row vector $\pi = (\pi_0, \pi_1)$ is *stationary* when it is a probability
vector ($\pi_i \ge 0$, $\pi_0 + \pi_1 = 1$) and $\pi P = \pi$, where
$(\pi P)_j = \sum_i \pi_i P_{ij}$. Coordinate 0 of $\pi P = \pi$ is
$\pi_0(1-a) + \pi_1 b = \pi_0$, i.e. $a\pi_0 = b\pi_1$; with $\pi_0 + \pi_1 = 1$ this forces
$\pi = \bigl(\tfrac{b}{a+b}, \tfrac{a}{a+b}\bigr)$ when $a + b > 0$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is a whole goal the step does not touch.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers |
| `Fin 2 → ℝ` | a vector with coordinates indexed by `Fin 2 = {0, 1}`; `π 0`, `π 1` are its coordinates |
| `![x, y]` | the vector with coordinates `x`, `y` (`![x, y] 0 = x`, `![x, y] 1 = y`) |
| `Matrix (Fin 2) (Fin 2) ℝ` | 2×2 real matrices; `M i j` is row `i`, column `j`, counted from 0 |
| `!![a, b; c, d]` | the matrix with rows `a b` and `c d` |
| `Matrix.vecMul v M` | the row vector `v` times the matrix `M`: coordinate `j` is `∑ i, v i * M i j` |
| `v ⬝ᵥ w` | `dotProduct v w = ∑ i, v i * w i` |
| `∑ x, f x` | the sum of `f x` over every `x` of the (finite) index type |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔`, after `constructor` |
| `case mp.«0»` | the coordinate-0 goal inside the `mp` half |
| `case refine_1` | the first `?_` of a `refine ⟨?_, …⟩` |
| `hab.ne'` | `LT.lt.ne' hab` (dot notation on `hab : 0 < a + b`) |

---

## Part 1 · `stationary_iff`

Statement: for `a b : ℝ` with `0 ≤ a`, `0 ≤ b`, `0 < a + b` and any vector `π : Fin 2 → ℝ`,
`IsStationary a b π ↔ π = ![b / (a + b), a / (a + b)]`. `IsStationary a b π` is defined as the
conjunction `(∀ i, 0 ≤ π i) ∧ π 0 + π 1 = 1 ∧ Matrix.vecMul π (P a b) = π`.

### Facts, `↔`, and taking hypotheses apart

**R1 · `LT.lt.ne'`** changes the **context** (used inside `have`). The lemma is `x < y → y ≠ x`;
`have hne : y ≠ x := hxy.ne'` adds the fact. Placeholders: `{α : Type} [Preorder α] (x y : α)`
(`α` has `<` and `≤`; `ℝ` qualifies), `(hxy : x < y)`. `field_simp` (R12) needs a denominator `≠ 0` fact,
and this one turns `0 < a + b` into `a + b ≠ 0`.

| Before | After |
|---|---|
| `⊢ G` | `hne : y ≠ x ⊢ G` |

**R2 · `constructor` on `↔`** changes the **goal list**: one goal becomes the two implications.
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R3 · `rintro ⟨-, hb, hc⟩`** changes the **goal and the context**: it introduces the premise of an
implication and splits it. The pattern sees through a definition (`Three A B C := A ∧ B ∧ C` in the
guide, `IsStationary` in the exercise). `-` discards a part; the nonnegativity part is not needed for (→).
Placeholders: `(A B C G : Prop)`.

| Before | After |
|---|---|
| `⊢ Three A B C → G` | `hb : B, hc : C ⊢ G` |

**R4 · `congrFun`** changes the **context** (used inside `have`). The lemma is
`congrFun : f = g → ∀ x, f x = g x`. A vector is a function, so `congrFun hfix 0` is coordinate 0 of the
vector equation `hfix`. Placeholders: `{α β : Type} (f g : α → β) (hfg : f = g) (x : α)`.

| Before | After |
|---|---|
| `⊢ G` | `hx : f x = g x ⊢ G` |

### Evaluating a row vector times a matrix

In the exercise one call does R5–R8 at once:
`simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] at h0`. It turns coordinate 0 of `π P = π` into
an equation between real numbers (H1 states it).

**R5 · `simp [D] at hx`** changes the **context**: it simplifies the hypothesis `hx` in place, unfolding
the definitions listed (`D`, or `P` in the exercise). Placeholders: `D` defined by
`def D : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 3, 4]`, `(x : ℝ)`.

| Before | After |
|---|---|
| `hx : D 1 0 = x ⊢ x = 3` | `hx : 3 = x ⊢ x = 3` |

**R6 · `Matrix.vecMul`, then `dotProduct`** change the **goal**: coordinate `j` of `v` times `M` becomes a
dot product with column `j`, then a sum. Placeholders: `(v : Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ)
(j : Fin 2)`.

| Before | After `simp only [Matrix.vecMul]` | After `simp only [dotProduct]` |
|---|---|---|
| `⊢ P (Matrix.vecMul v M j)` | `⊢ P (v ⬝ᵥ fun i => M i j)` | `⊢ P (∑ x, v x * M x j)` |

**R7 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. The lemma is
`∑ i, f i = f 0 + f 1`. Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)` (`β` has a commutative
`+` with `0`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R8 · entry of a matrix literal** changes the **goal**: `simp` reads `!![a, b; c, d] i j` for numeral
indices (lemmas `Matrix.of_apply`, `Matrix.cons_val_…`). Placeholders: `{α : Type} (a b c d : α)`.

| Before | After |
|---|---|
| `⊢ P (!![a, b; c, d] 1 0)` | `⊢ P c` |

### Vector equation → coordinates

**R9 · `ext i`** changes the **goal and the context**. It uses `funext`: two functions (vectors) are equal
when they agree at every argument. Placeholders: `(v w : Fin 2 → ℝ)`.

| Before | After |
|---|---|
| `⊢ v = w` | `i : Fin 2 ⊢ v i = w i` |

**R10 · `fin_cases i`** changes the **goal list and the context**. `i` leaves the context, and there is one
goal per value `0, 1`. Placeholders: `(P : Fin 2 → Prop)`.

| Before | After |
|---|---|
| `i : Fin 2 ⊢ P i` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)` |

**R11 · entry of a vector literal** changes the **goal**: `simp` reads `![x, y] k` (lemmas
`Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons`), and also turns the printed index
`(fun i => i) ⟨0, ⋯⟩` back into `0`. Placeholders: `{α : Type} (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (![x, y] 1)` | `⊢ P y` |

### Closing scalar goals

**R12 · `field_simp`** changes the **goal**: it multiplies out every denominator, so `x / y = z` becomes
`x = y * z`. It must be able to show each denominator is nonzero: it finds `hy : y ≠ 0` (or `0 < y`) in the
context. Without one it leaves the division in place. Placeholders: `{α : Type} [Field α] (x y z : α)`
(`ℝ`, `ℚ`, `ℂ` qualify). The exact shape it produces (`x * 3 = 2` or `3 * x = 2`) is not fixed: read it
off the infoview and finish with `ring`, `linarith` or `nlinarith`.

| Before | After |
|---|---|
| `hy : y ≠ 0 ⊢ x / y = z` | `hy : y ≠ 0 ⊢ x = y * z` |

**R13 · `nlinarith`** **closes** an equality or inequality over an ordered field such as `ℝ` that follows
linearly from the hypotheses *and their pairwise products*. `linarith` only combines hypotheses linearly,
so it fails on `c * x + c * y = c` from `x + y = 1`; `nlinarith` multiplies `hc : 0 ≤ c` with
`hs : x + y = 1` and succeeds. The multiplier must be in the context as a hypothesis (here `hb : 0 ≤ b` and
`ha : 0 ≤ a` are). Placeholders: `(x y c : ℝ) (hc : 0 ≤ c) (hs : x + y = 1)`.

**R14 · `rintro rfl`** changes the **goal and the context**: it introduces `y = e` and substitutes `e` for
the variable `y` everywhere; `y` leaves the context. In the exercise, `π` is replaced by the literal vector,
so `IsStationary a b ![…]` is what remains. Placeholders: `{α : Type} (f : α → α) (x y : α)`.

| Before | After |
|---|---|
| `y : α ⊢ y = f x → P y` | `⊢ P (f x)` |

**R15 · `refine ⟨?_, ?_, ?_⟩`** changes the **goal list**: one goal per conjunct. Like R3 it sees through a
definition that unfolds to `A ∧ B ∧ C` (`IsStationary` does). Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ Three A B C` | `⊢ A`, `⊢ B`, `⊢ C` |

**R16 · `positivity`** **closes** a goal `0 ≤ e` or `0 < e` (also `e ≠ 0`) where `e` is built from
`+`, `*`, `/`, powers and numerals, using hypotheses `0 ≤ x` / `0 < x` for the variables. Placeholders:
`(x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y)` for the goal `0 ≤ x / y`. It does not do subtraction: `0 ≤ 1 - a`
is out of reach.

`ring` (TACTIC_STATES) closes what `field_simp` leaves when it is a pure ring identity such as `b + a = a + b`.

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a vector equation by coordinates.** `v = ![5, 7]` with `ext i; fin_cases i` (R9, R10) gives, for
coordinate 0,

```lean-goal
⊢ v ((fun i => i) ⟨0, ⋯⟩) = ![5, 7] ((fun i => i) ⟨0, ⋯⟩)
```

and `simp` (R11) turns it into `v 0 = 5`.

**W2: one coordinate of a fixed-point equation.** For the swap chain `Sw = !![0, 1; 1, 0]` and
`hfix : Matrix.vecMul v Sw = v`, `have h0 := congrFun hfix 0` (R4), then
`simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Sw] at h0` (R5 with R6–R8) leaves:

```lean-goal
⊢ v 1 = v 0
```

with `h0 : Matrix.vecMul v Sw 0 = v 0` turned into `h0 : v 1 = v 0`.

**W3: clear a denominator, then use the hypotheses.** From `x + y = 1` and `x = 2 * y`, the goal
`x = 2 / 3` after `field_simp` (R12) is

```lean-goal
⊢ x * 3 = 2
```

which `linarith` closes.

**W4: checking a candidate vector.** For `v = ![(s - t) / (s + t), 2 * t / (s + t)]` and the goal
`v 0 + v 1 = 1`: `rintro rfl` (R14), then `simp` (R11), then `field_simp` (R12), then `ring`:

```lean-goal
⊢ ![(s - t) / (s + t), 2 * t / (s + t)] 0 + ![(s - t) / (s + t), 2 * t / (s + t)] 1 = 1
⊢ (s - t) / (s + t) + 2 * t / (s + t) = 1
⊢ s - t + t * 2 = s + t
```

Sometimes `field_simp` closes such a goal by itself; when it leaves a ring identity, finish with `ring`.

---

## Traps

- `field_simp` with no `≠ 0` (or `0 < …`) fact for a denominator in the context silently leaves the
  fraction. Put `hne : a + b ≠ 0` in the context before splitting the goal, so every branch has it.
- `linarith` fails on the (→) coordinates: the step needs `b * (π 0 + π 1) = b`, a product. Use
  `nlinarith`, and keep `ha`, `hb` in the context so it has something to multiply with.
- `simp` with no lemmas does not unfold `Matrix.vecMul` or `P`: name them, plus `dotProduct` and
  `Fin.sum_univ_two`, or the coordinate stays as `Matrix.vecMul π (P a b) 0`.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, use `<;>` or `·` for each case.
- The statement assumes only `0 ≤ a`, `0 ≤ b`, `0 < a + b`; `a ≤ 1` is never needed, so do not look for it.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a + b ≠ 0` from `hab : 0 < a + b` | `have hne : a + b ≠ 0 := hab.ne'` | R1 |
| split `A ↔ B` | `constructor` | R2 |
| take apart a conjunction premise | `rintro ⟨-, h1, h2⟩` | R3 |
| one coordinate of `v = w` | `have h0 := congrFun h 0` | R4 |
| evaluate `Matrix.vecMul v M j` in a hypothesis | `simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, M] at h0` | R5–R8 |
| vector equation → 2 coordinates | `ext i; fin_cases i` | R9, R10 |
| read `![x, y] k` | `simp` | R11 |
| clear denominators | `field_simp` | R12 |
| close using products of hypotheses | `nlinarith` | R13 |
| substitute `π = …` | `rintro rfl` | R14 |
| split `A ∧ B ∧ C` (through a definition) | `refine ⟨?_, ?_, ?_⟩` | R15 |
| `0 ≤ b / (a + b)` | `positivity` | R16 |
| ring identity | `ring` | TACTIC_STATES |
| see the state | infoview | |
