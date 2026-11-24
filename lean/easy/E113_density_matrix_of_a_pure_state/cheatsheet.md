# E113 · Density matrix of a pure state: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). E112 (kets and bra-kets) helps but is not needed.
**New here:** physlib's mixed states `MState d` and the pure state `MState.pure ψ`; Mathlib's complex
conjugate `conj`, `Complex.normSq`, finite sums `∑`, and the cast `ℝ → ℂ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp only`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommMonoid α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `d : Type` with `[Fintype d] [DecidableEq d]` | the index set of the system: finitely many basis labels, with decidable `=` (e.g. `Fin 2` for a qubit) |
| `inst✝¹ : Fintype d`, `inst✝ : DecidableEq d` | how the infoview shows those two unnamed `[…]` assumptions; you never refer to them |
| `Ket d` | a pure state: a vector `vec : d → ℂ` with `∑ x, ‖vec x‖ ^ 2 = 1` (`‖z‖` is the absolute value of `z : ℂ`) |
| `ψ i` | entry `i` of the ket `ψ` (a complex number); `ψ` is used as a function `d → ℂ` |
| `MState d` | a mixed state (density matrix): a Hermitian, positive semidefinite matrix of trace 1 |
| `MState.pure ψ` | the pure-state density matrix ρ = \|ψ⟩⟨ψ\| |
| `ρ.m` | the raw matrix of the state `ρ`, of type `Matrix d d ℂ`; `ρ.m i j` is entry `(i, j)` |
| `conj z`, printed `(starRingEnd ℂ) z` | the complex conjugate of `z` (`conj` needs `open ComplexConjugate`) |
| `Complex.normSq z` | \|z\|² = (re z)² + (im z)², a real number (`ℝ`) |
| `↑r` | the real number `r` cast into `ℂ` |
| `∑ x, f x` | the sum of `f x` over all `x : d` (`Finset.sum Finset.univ f`) |

So the three statements are: ρ is Hermitian entrywise (`ρ_ji = conj ρ_ij`), its diagonal is the Born
probabilities (`ρ_ii = |ψ_i|²`), and its trace is 1. All three follow from one formula,
`ρ_ij = ψ_i · conj ψ_j` (R1).

---

## Part 1 · `pure_conj`

Statement: `(MState.pure ψ).m j i = conj ((MState.pure ψ).m i j)`: the density matrix of a pure state equals
its conjugate transpose, entry by entry.

**R1 · `rw [MState.pure_apply]`** changes the **goal**. The lemma is
`MState.pure_apply ψ : (MState.pure ψ).m i j = ψ i * conj (ψ j)`, with `i j` implicit, so `rw` takes them from the
first entry it finds. Each `rw` rewrites one entry pattern; with two different entries, write it twice.
Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (a b : d)`.

| Before | After |
|---|---|
| `⊢ P ((MState.pure ψ).m a b)` | `⊢ P (ψ a * (starRingEnd ℂ) (ψ b))` |

**R2 · `rw [map_mul]`** changes the **goal**. The lemma is `map_mul f x y : f (x * y) = f x * f y` for any map
`f` that respects `*` (a ring hom such as `conj` qualifies). Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (a * b))` | `⊢ P ((starRingEnd ℂ) a * (starRingEnd ℂ) b)` |

**R3 · `rw [Complex.conj_conj]`** changes the **goal**. The lemma is `conj (conj x) = x`. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ((starRingEnd ℂ) a))` | `⊢ P a` |

**R4 · `rw [mul_comm]`** changes the **goal**. The lemma is `mul_comm a b : a * b = b * a`. With no arguments,
`rw` rewrites the first product in the goal (reading left to right) and every copy of that same product; after
`rw`, the goal is closed by `rfl` if both sides now agree. Placeholders: `{α : Type} [CommMonoid α] (a b : α)`
(α has a commutative `*`; `ℂ`, `ℝ`, `ℕ` qualify).

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

**W1 · R2, R3, R4 in a row** on `conj (conj a * b) = conj b * a` (plain `a b : ℂ`, the conjugate on the
first factor). The last `rw` closes it by `rfl`:

```lean-goal
⊢ (starRingEnd ℂ) ((starRingEnd ℂ) a * b) = (starRingEnd ℂ) b * a
⊢ (starRingEnd ℂ) ((starRingEnd ℂ) a) * (starRingEnd ℂ) b = (starRingEnd ℂ) b * a
⊢ a * (starRingEnd ℂ) b = (starRingEnd ℂ) b * a
```

---

## Part 2 · `pure_diag`

Statement: `(MState.pure ψ).m i i = Complex.normSq (ψ i)`: the diagonal entry `i` is the Born probability
`|ψ_i|²`, cast into `ℂ`. The left side is in `ℂ` and `normSq` is in `ℝ`, so Lean inserts the cast: the
infoview shows the right side as `↑(Complex.normSq (ψ i))`.

R1 turns the entry into `ψ i * conj (ψ i)`; then one more lemma.

**R5 · `rw [Complex.mul_conj]`** changes the **goal**. The lemma is `Complex.mul_conj z : z * conj z = ↑(normSq z)`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * (starRingEnd ℂ) z)` | `⊢ P ↑(Complex.normSq z)` |

---

## Part 3 · `pure_trace`

Statement: `∑ i, (MState.pure ψ).m i i = 1`: the diagonal (the Born probabilities) sums to 1.

**R6 · `simp only [lemma]` under `∑`** changes the **goal**. `∑ x, f x` is `Finset.sum Finset.univ (fun x => f x)`,
so the summand sits under the binder `x`. `rw` cannot rewrite there and fails with "Did not find an occurrence
of the pattern"; `simp only [l₁, l₂]` rewrites inside the summand for every `x`. Here with R5 as the lemma.
Placeholders: `{d : Type} [Fintype d] (v : d → ℂ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, v x * (starRingEnd ℂ) (v x))` | `⊢ P (∑ x, ↑(Complex.normSq (v x)))` |

**R7 · `ψ.normalized`** (the lemma `Ket.normalized`) changes the **context** when used in a `have`. It states
`∑ x, Complex.normSq (ψ x) = 1`, an equation in `ℝ`. You can also pass `ψ.normalized` straight to a tactic
(R8) without the `have`. Placeholders: `{d : Type} [Fintype d] (ψ : Ket d)`.

| Before | After `have hψ := ψ.normalized` |
|---|---|
| `⊢ G` | `⊢ G`, with the new hypothesis `hψ : ∑ x, Complex.normSq (ψ x) = 1` |

**R8 · `exact_mod_cast h`** **closes** a goal that is `h` up to casts. Typical case: the goal sums casts in `ℂ`,
`h` is the same sum in `ℝ`. It moves casts outward on both sides (`∑ x, ↑(f x)` → `↑(∑ x, f x)`, `1` → `↑1`),
drops them with `↑a = ↑b ↔ a = b`, and then uses `h`. Placeholders: `{d : Type} [Fintype d] (f : d → ℝ)`
`(hf : ∑ x, f x = 1)`.

| Before | After |
|---|---|
| `⊢ ∑ x, ↑(f x) = 1`, with `hf : ∑ x, f x = 1` | no goals |

**W2 · R6 then R8** on a plain vector `v : d → ℂ` with `hv : ∑ x, Complex.normSq (v x) = 2`:

```lean-goal
⊢ ∑ x, v x * (starRingEnd ℂ) (v x) = 2
⊢ ∑ x, ↑(Complex.normSq (v x)) = 2
```

then `exact_mod_cast hv` closes it.

**W3 · what R8 does first.** `norm_cast` alone pulls the cast out of the sum and drops it (here `hf : 3 = ∑ x, f x`
is the wrong way round, so the goal stays open; the bound variable is renamed, which does not matter):

| Before `norm_cast` | After |
|---|---|
| `⊢ ∑ x, ↑(f x) = 3` | `⊢ ∑ i, f i = 3` |

---

## Traps

- `conj z` prints as `(starRingEnd ℂ) z`. They are the same term; write `conj` (with `open ComplexConjugate`).
- `MState.pure_apply` has implicit `i j`: one `rw [MState.pure_apply]` rewrites one entry (and its copies).
  `pure_conj` has two different entries `(j, i)` and `(i, j)`, so it needs R1 twice.
- `rw` cannot rewrite inside `∑ x, …`; use `simp only [...]` (R6).
- `Complex.normSq` lands in `ℝ`, the statements are in `ℂ`. After R5 the cast `↑` is already there; `Ket.normalized`
  is the uncast real sum, so close with `exact_mod_cast`, not `exact` (R8).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| entry of `MState.pure ψ` → `ψ i * conj (ψ j)` | `rw [MState.pure_apply]` | R1 |
| `conj (a * b)` → `conj a * conj b` | `rw [map_mul]` | R2 |
| `conj (conj a)` → `a` | `rw [Complex.conj_conj]` | R3 |
| `a * b` → `b * a` | `rw [mul_comm]` | R4 |
| `z * conj z` → `↑(normSq z)` | `rw [Complex.mul_conj]` | R5 |
| rewrite inside a sum `∑ x, …` | `simp only [lemmas]` | R6 |
| a ket's normalization in `ℝ` | `ψ.normalized : ∑ x, Complex.normSq (ψ x) = 1` | R7 |
| close a goal equal to `h` up to `ℝ → ℂ` casts | `exact_mod_cast h` | R8 |
| see casts pulled out | `norm_cast` | W3 |
| see the state | infoview | |
