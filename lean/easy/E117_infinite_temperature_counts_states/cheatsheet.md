# E117 · Infinite temperature counts states: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `CanonicalEnsemble` and its
finite partition function `mathematicalPartitionFunctionBetaReal`; Mathlib's finite sums `∑ i, f i`,
`Fintype.card`, the scalar action `n • a` of a natural number, the cast `↑n : ℝ`, and `Real.exp`.

The physics: a canonical ensemble is a system with microstates `i` of energy `E_i` in contact with a heat
bath at inverse temperature `β = 1/(k_B T)`. With finitely many states and `k_B = 1`, the partition
function is `Z(β) = ∑_i e^{-β E_i}`, a sum of Boltzmann weights. If all states have the same energy `E`,
every weight is `e^{-βE}` and `Z = |ι| e^{-βE}`, where `|ι|` is the number of states. At `β = 0` (`T → ∞`)
every weight is `e^0 = 1`, so `Z = |ι|`: the partition function counts the states. In Lean both proofs are:
unfold `Z` into its sum (R1), make each term the same constant (R2, or R7–R9), then evaluate a sum of a
constant (R4–R6).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Ring α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it. `[Fintype ι]` says `ι`
  is a finite type, so `∑ i, …` over all of `ι` makes sense.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | Mathlib's real numbers (`Real`); `E b : ℝ` are plain reals |
| `inst✝¹ : Fintype ι`, `inst✝ : MeasurableSpace ι` | the unnamed type-class arguments `[Fintype ι]`, `[MeasurableSpace ι]` as hypotheses; `✝` marks a name you cannot refer to. Ignore them |
| `CanonicalEnsemble ι` | physlib structure: a system whose microstates are the elements of `ι`. Its field `energy : ι → ℝ` is used here; the other fields (`dof`, `phaseSpaceunit`, the measure `μ`) are not |
| `[MeasurableSpace ι]` | a σ-algebra on `ι`, required by `CanonicalEnsemble`'s measure; it plays no role in these proofs |
| `𝓒.energy i` | `CanonicalEnsemble.energy 𝓒 i`, the energy `E_i` of state `i` (dot notation, E017) |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b) = ∑ i, Real.exp (-b * 𝓒.energy i)`, with `b : ℝ` playing `β`. Lean treats the name as opaque until you unfold it (R1) |
| `∑ i, f i` | `Finset.sum Finset.univ f`: the sum of `f i` over every `i : ι`. `∑ x, …` and `∑ _i, …` are the same sum with another bound-variable name |
| `∑ _x ∈ s, c` | a sum over the finite set `s` of a term `c` that does not mention the bound variable |
| `Finset.univ` | the finite set of all elements of the finite type `ι` |
| `s.card` | `Finset.card s`, the number of elements of `s` |
| `Fintype.card ι` | the number of elements of the type `ι` (`|ι|`), a natural number |
| `n • a` | `n : ℕ` acting on `a`: `a + ⋯ + a` (`n` copies) |
| `↑(Fintype.card ι)` | that natural number cast into `ℝ`; the statement writes it as `Fintype.card ι` and Lean inserts the cast |
| `Real.exp x` | `e^x` on the reals |
| `-b * E`, `-0 * x` | `(-b) * E`, `(-0) * x`: negation binds tighter than `*`. `simp` rewrites `-b * E` to `-(b * E)` (R3); `-0` is the negation of `0 : ℝ` (R7) |

---

## Part 1 · `Z_degenerate`

Statement: if `h : ∀ i, 𝓒.energy i = E` (every state has energy `E`), then
`𝓒.mathematicalPartitionFunctionBetaReal b = ↑(Fintype.card ι) * Real.exp (-b * E)`, i.e. `Z(β) = |ι| e^{-βE}`.

### From the partition function to a sum

**R1 · `simp only [mathematicalPartitionFunctionBetaReal]`** changes the **goal**: the name is replaced by
its definition, `∑ i, Real.exp (-b * 𝓒.energy i)`. The short name works because of
`open CanonicalEnsemble`. `simp [mathematicalPartitionFunctionBetaReal, …]` does the same and keeps going.
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] (b : ℝ) (𝓒 : CanonicalEnsemble ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.mathematicalPartitionFunctionBetaReal b)` | `⊢ P (∑ i, Real.exp (-b * 𝓒.energy i))` |

**R2 · `simp only [hf]`** with `hf : ∀ i, f i = c` changes the **goal**: `simp` uses `hf` as a rewrite rule
for every instance `f i`, also under the `∑` binder where `i` is bound. `rw [hf]` fails there (Traps).
Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ) (c : ℝ) (g : ℝ → ℝ)`; in the exercise `f = 𝓒.energy`,
`c = E`, `g = fun t => Real.exp (-b * t)`, and `hf` is `h`.

| Before | After |
|---|---|
| `⊢ P (∑ i, g (f i))` | `⊢ P (∑ x, g c)` |

**R3 · `neg_mul`** changes the **goal**. The lemma is `neg_mul : -a * b = -(a * b)`. `simp` applies it by
itself, to both sides of the equation, so you never write it; it is here so that the `-(b * E)` you see in
the infoview is not a surprise. Placeholders: `{α : Type} [Ring α] (a b : α)` (`ℝ` and `ℂ` are rings).

| Before | After |
|---|---|
| `⊢ P (-a * b)` | `⊢ P (-(a * b))` |

### A sum of a constant

**R4 · `Finset.sum_const`** changes the **goal**. The lemma is `Finset.sum_const : ∑ _x ∈ s, c = s.card • c`:
a sum of `s.card` copies of `c`. Placeholders: `{ι β : Type} [Fintype ι] [AddCommMonoid β] (c : β)`; β has a
commutative `+` with `0`, as `ℕ`, `ℝ`, `ℂ` do.

| Before | After |
|---|---|
| `⊢ P (∑ _i, c)` | `⊢ P (Finset.univ.card • c)` |

**R5 · `Finset.card_univ`** changes the **goal**. The lemma is
`Finset.card_univ : Finset.univ.card = Fintype.card α`: the set of all elements has `|α|` elements.
Placeholders: as in R4.

| Before | After |
|---|---|
| `⊢ P (Finset.univ.card • c)` | `⊢ P (Fintype.card ι • c)` |

**R6 · `nsmul_eq_mul`** changes the **goal**. The lemma is `nsmul_eq_mul : n • a = ↑n * a`: adding `a` to
itself `n` times is multiplying by `n` cast into the ring. This produces the `↑(Fintype.card ι) * …` of the
statement. Placeholders: `{α : Type} [NonAssocSemiring α] (n : ℕ) (a : α)` (`ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (n • a)` | `⊢ P (↑n * a)` |

After R1, R2, R4, R5, R6 (and R3 on both sides) the two sides are identical, and `simp` closes the goal.

---

## Part 2 · `Z_at_beta_zero`

Statement: `𝓒.mathematicalPartitionFunctionBetaReal 0 = ↑(Fintype.card ι)`, i.e. `Z(0) = |ι|`. No
hypothesis about the energies is needed: at `b = 0` every exponent is `-0 * 𝓒.energy i = 0`. After R1, the
entries R7–R9 turn each term into `1`, then R4–R6 and R10 evaluate the sum. Apply R7–R9 with
`simp only [lemma]`: after R1 the terms sit under the `∑`, and `rw [zero_mul]` fails there (Traps). R4–R6
and R10 act on the whole sum, so `rw` works for them.

**R7 · `neg_zero`** changes the **goal**. The lemma is `neg_zero : -0 = 0`. Placeholders:
`{α : Type} [Ring α] (x : α)`.

| Before | After |
|---|---|
| `⊢ P (-0 * x)` | `⊢ P (0 * x)` |

**R8 · `zero_mul`** changes the **goal**. The lemma is `zero_mul : 0 * a = 0`. Placeholders: as in R7. In the
exercise `a` is `𝓒.energy i` with `i` bound by the `∑`, so write `simp only [zero_mul]`, not `rw`.

| Before | After |
|---|---|
| `⊢ P (0 * x)` | `⊢ P 0` |

**R9 · `Real.exp_zero`** changes the **goal**. The lemma is `Real.exp_zero : Real.exp 0 = 1`.

| Before | After |
|---|---|
| `⊢ P (Real.exp 0)` | `⊢ P 1` |

**R10 · `mul_one`** changes the **goal**. The lemma is `mul_one : a * 1 = a`; it removes the `* 1` that R6
leaves. Placeholders: `{α : Type} [Ring α] (a : α)`.

| Before | After |
|---|---|
| `⊢ P (a * 1)` | `⊢ P a` |

`simp` knows R3–R10 as simp lemmas; you only give it the definition name (and, in Part 1, `h`).

### Worked combinations (W1–W3, on sums that are not the exercise's)

**W1: constant terms, step by step.** `hf : ∀ i, f i = c` for a plain `f : ι → ℝ`. R2, R4, R5, then R6
(the last `rw` closes the goal, since both sides are then the same):

```lean-goal
⊢ ∑ i, Real.exp (f i) = ↑(Fintype.card ι) * Real.exp c
⊢ ∑ x, Real.exp c = ↑(Fintype.card ι) * Real.exp c
⊢ Finset.univ.card • Real.exp c = ↑(Fintype.card ι) * Real.exp c
⊢ Fintype.card ι • Real.exp c = ↑(Fintype.card ι) * Real.exp c
```

**W2: a zero exponent, step by step.** Over `Fin 3`: R7, R8, R9 (each with `simp only`, since the terms sit
under the `∑`), then R4, R5, R6, R10, and a last `simp` that evaluates `Fintype.card (Fin 3) = 3`:

```lean-goal
⊢ ∑ i, Real.exp (-0 * f i) = 3
⊢ ∑ x, Real.exp (0 * f x) = 3
⊢ ∑ x, Real.exp 0 = 3
⊢ ∑ x, 1 = 3
⊢ Finset.univ.card • 1 = 3
⊢ Fintype.card (Fin 3) • 1 = 3
⊢ ↑(Fintype.card (Fin 3)) * 1 = 3
⊢ ↑(Fintype.card (Fin 3)) = 3
```

**W3: all at once.** `simp [hf]` closes W1's goal and `simp` closes W2's in one step: `simp` finds R3–R10
on its own. In the exercise the only thing `simp` cannot find on its own is the definition (R1), plus `h`
in Part 1.

---

## Traps

- `simp` does not unfold `mathematicalPartitionFunctionBetaReal` unless you name it; without it, nothing
  happens to the left side.
- `rw [h]` with `h : ∀ i, 𝓒.energy i = E` fails after unfolding: the `𝓒.energy i` sits under the `∑` and
  mentions the bound `i`, and `rw` cannot rewrite under a binder ("did not find an occurrence"). Use
  `simp [h]` / `simp only [h]` (R2).
- The same holds for `rw [zero_mul]` in Part 2: after R1 and R7 the goal is
  `∑ x, Real.exp (0 * 𝓒.energy x) = ↑(Fintype.card ι)`, the pattern `0 * 𝓒.energy x` mentions the bound
  `x`, and `rw` reports "did not find an occurrence of the pattern 0 * ?a". `simp only [zero_mul]` works.
  (`rw [neg_zero]` and `rw [Real.exp_zero]` happen to work, since `-0` and `Real.exp 0` do not mention `x`.)
- Forgetting `h` in Part 1: `simp [mathematicalPartitionFunctionBetaReal]` stops at
  `∑ x, Real.exp (-(b * 𝓒.energy x)) = ↑(Fintype.card ι) * Real.exp (-(b * E))`, since it cannot know the
  energies are all `E`.
- The `Fintype.card ι` in the statement is a natural number cast into `ℝ` (`↑(Fintype.card ι)`); R6 is what
  produces that cast from `•`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `Z` into `∑ i, Real.exp (-b * 𝓒.energy i)` | `simp only [mathematicalPartitionFunctionBetaReal]` | R1 |
| use `h : ∀ i, f i = c` under `∑` | `simp only [h]` (not `rw`) | R2 |
| `-a * b` → `-(a * b)` | automatic in `simp` | R3 |
| `∑ _i, c` → `Finset.univ.card • c` | `rw [Finset.sum_const]` | R4 |
| `Finset.univ.card` → `Fintype.card ι` | `rw [Finset.card_univ]` | R5 |
| `n • a` → `↑n * a` | `rw [nsmul_eq_mul]` | R6 |
| `-0`, `0 * x`, `Real.exp 0`, `a * 1` | `simp only [neg_zero]`, `simp only [zero_mul]`, … (all in `simp`) | R7–R10 |
| everything after unfolding | `simp [definition, h]` | W3 |
| see the state | infoview | |
