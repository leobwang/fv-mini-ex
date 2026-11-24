# M139 · Mutual information of the Bell state: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw`, `have`, `ring`, `refine`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's quantum states (`MState`, `Ket`),
partial traces, von Neumann and Shannon entropy, and Mathlib's `Set.range`, `IsGreatest`, `upperBounds`,
`Finset.univ` and `linarith`. Every proof here is "rewrite with the right library lemma" or "collect
bounds, then `linarith`": no entropy is ever computed by hand.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`, or `P : MState d → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{d : Type}` is any type. A bracket is a requirement on it
  (a *type class*): `[Fintype d]` means `d` is finite (so sums over `d` and `d × d` matrices exist),
  `[DecidableEq d]` means equality of indices can be tested (needed to write the identity matrix),
  `[Nonempty d]` means `d` has an element (so `1/|d|` makes sense). `Fin n`, `Bool`, `Fin 2 × Fin 2` meet all three.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- To find a lemma yourself: state it as an `example … := by exact?`. To see what a definition unfolds to:
  `#print MState.uniform`.

## Reading the goals

| You see | It means |
|---|---|
| `inst✝² : Fintype d` (context) | the unnamed instance from the binder `[Fintype d]`; likewise `inst✝¹`, `inst✝` for `[DecidableEq d]`, `[Nonempty d]`. Ignore them |
| `d₁ × d₂` | the product type of pairs `(i, j)`: the index set of a two-party system `A ⊗ B` with `\|d₁ × d₂\| = \|d₁\|·\|d₂\|` |
| `MState d` | a mixed state (density matrix) on the finite index type `d`: a positive semidefinite Hermitian `d × d` complex matrix with trace 1 |
| `Ket d` | a unit vector `ψ ∈ ℂ^d` |
| `MState.pure ψ` | the pure state `\|ψ⟩⟨ψ\|` |
| `Ket.MES d : Ket (d × d)` | the maximally entangled state `Φ = (1/√\|d\|) Σᵢ \|i⟩\|i⟩` (the Bell state for `\|d\| = 2`) |
| `ρ.traceLeft` | the partial trace over the **left** factor: for `ρ : MState (d₁ × d₂)` it is `ρ_B : MState d₂` |
| `ρ.traceRight` | the partial trace over the **right** factor: `ρ_A : MState d₁` |
| `Sᵥₙ ρ` | von Neumann entropy `S(ρ) = −tr(ρ log ρ)`, defined as the Shannon entropy of the eigenvalues of `ρ` |
| `qMutualInfo ρ` | `I(A:B) = S(ρ_B) + S(ρ_A) − S(ρ)` for `ρ : MState (dA × dB)` (R1) |
| `ProbDistribution d` | a probability vector `p : d → [0,1]` with `Σ p = 1` |
| `Hₛ p` | Shannon entropy `H(p) = −Σₓ pₓ log pₓ` |
| `ProbDistribution.uniform` | `pₓ = 1/\|d\|` for every `x` |
| `MState.ofClassical p` | the diagonal state `diag(p)` |
| `MState.uniform` | the maximally mixed state `I/\|d\|`, defined as `ofClassical uniform` (R5) |
| `Real.log` | the natural logarithm (so entropies are in nats); `Real.log 0 = 0` by convention |
| `Finset.univ` | the finite set of all elements of a `Fintype`; `Finset.univ.card` is its size |
| `Fintype.card d` | `\|d\|`, the number of elements of `d`; equal to `Finset.univ.card` (R8) |
| `↑n` | the natural number `n` cast into `ℝ` |
| `Set.range f` | `{b \| ∃ x, f x = b}`, the image of `f` |
| `upperBounds s` | `{a \| ∀ b ∈ s, b ≤ a}` |
| `IsGreatest s a` | `a ∈ s ∧ a ∈ upperBounds s`: `a` is the maximum of `s` (R9) |
| `qMutualInfo (dA := d) (dB := d)` | `qMutualInfo` with its implicit type arguments named `dA`, `dB` set to `d`: the function `MState (d × d) → ℝ`. The infoview prints it as plain `qMutualInfo` |
| `case refine_1` | the first goal produced by `refine ⟨?_, ?_⟩` |

---

## Part 1 · `MES_mutual_info`

Statement: `I(Φ) = 2 log |d|`. Physics: `Φ` is pure, so `S(Φ) = 0`; both marginals of `Φ` are `I/|d|`,
whose entropy is `log |d|`. In Lean the whole proof is one `rw [...]` chain, R1 → R8, then `ring`.

**R1 · `rw [qMutualInfo]`** changes the **goal**: it unfolds the definition. Placeholders:
`{d₁ d₂ : Type} [Fintype dᵢ] [DecidableEq dᵢ] (ρ : MState (d₁ × d₂))`. Also used in Part 2, because
`linarith` does not unfold definitions.

| Before | After |
|---|---|
| `⊢ P (qMutualInfo ρ)` | `⊢ P (Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ)` |

**R2 · `rw [Sᵥₙ_of_partial_eq]`** changes the **goal**. The lemma is
`Sᵥₙ_of_partial_eq (ψ : Ket (d₁ × d₂)) : Sᵥₙ (MState.pure ψ).traceLeft = Sᵥₙ (MState.pure ψ).traceRight`:
the two marginals of a pure state have the same nonzero spectrum (Schmidt decomposition), hence the same entropy.
It only fires on a **pure** state. Placeholders: `(ψ : Ket (d₁ × d₂))`.

| Before | After |
|---|---|
| `⊢ P (Sᵥₙ (MState.pure ψ).traceLeft)` | `⊢ P (Sᵥₙ (MState.pure ψ).traceRight)` |

**R3 · `rw [traceRight_pure_MES]`** changes the **goal**. The lemma is
`traceRight_pure_MES (d : Type) [Fintype d] [DecidableEq d] [Nonempty d] : (MState.pure (Ket.MES d)).traceRight = MState.uniform`:
the marginal of the maximally entangled state is maximally mixed. `d` is explicit, but `rw` finds it in the
goal. `rw` rewrites **every** copy, so apply R2 first and both marginals become `MState.uniform` at once.

| Before | After |
|---|---|
| `⊢ P (MState.pure (Ket.MES d)).traceRight` | `⊢ P MState.uniform` |

**R4 · `rw [Sᵥₙ_of_pure_zero]`** changes the **goal**. The lemma is
`Sᵥₙ_of_pure_zero (ψ : Ket d) : Sᵥₙ (MState.pure ψ) = 0` (spectrum `(1, 0, …, 0)`). Placeholders: `(ψ : Ket d)`.

| Before | After |
|---|---|
| `⊢ P (Sᵥₙ (MState.pure ψ))` | `⊢ P 0` |

**R5 · `rw [MState.uniform]`** changes the **goal**: it unfolds the definition
`MState.uniform = MState.ofClassical ProbDistribution.uniform`, so that R6 can match. Placeholders:
`{d : Type} [Fintype d] [DecidableEq d] [Nonempty d]`.

| Before | After |
|---|---|
| `⊢ P MState.uniform` | `⊢ P (MState.ofClassical ProbDistribution.uniform)` |

**R6 · `rw [Sᵥₙ_ofClassical]`** changes the **goal**. The lemma is
`Sᵥₙ_ofClassical (dist : ProbDistribution d) : Sᵥₙ (MState.ofClassical dist) = Hₛ dist`: a diagonal state has
eigenvalues `p`, so its von Neumann entropy is the Shannon entropy of `p`. Placeholders: `(p : ProbDistribution d)`.

| Before | After |
|---|---|
| `⊢ P (Sᵥₙ (MState.ofClassical p))` | `⊢ P (Hₛ p)` |

**R7 · `rw [Hₛ_uniform]`** changes the **goal**. The lemma is
`Hₛ_uniform [Fintype α] [Nonempty α] : Hₛ ProbDistribution.uniform = Real.log ↑Finset.univ.card`
(`−Σ (1/n) log (1/n) = log n`). Placeholders: `{α : Type} [Fintype α] [Nonempty α]`.

| Before | After |
|---|---|
| `⊢ P (Hₛ ProbDistribution.uniform)` | `⊢ P (Real.log ↑Finset.univ.card)` |

**R8 · `rw [Finset.card_univ]`** changes the **goal**. The lemma is
`Finset.card_univ [Fintype α] : Finset.univ.card = Fintype.card α`. physlib states sizes with the left side,
the problem with the right side; `ring` and `linarith` treat them as different unknowns until you rewrite.
Placeholders: `{α : Type} [Fintype α]`.

| Before | After |
|---|---|
| `⊢ P Finset.univ.card` | `⊢ P (Fintype.card α)` |

After R1–R8 the goal is `log ↑|d| + log ↑|d| − 0 = 2 · log ↑|d|`, which `ring` closes (TACTIC_STATES, "Closing").

**W1: R1, R2, R4 on an arbitrary pure state.** For `ψ : Ket (d₁ × d₂)`, `I(ψ) = 2 S(ψ_A)`:

```lean-goal
⊢ qMutualInfo (MState.pure ψ) = 2 * Sᵥₙ (MState.pure ψ).traceRight
⊢ Sᵥₙ (MState.pure ψ).traceLeft + Sᵥₙ (MState.pure ψ).traceRight - Sᵥₙ (MState.pure ψ) = 2 * Sᵥₙ (MState.pure ψ).traceRight
⊢ Sᵥₙ (MState.pure ψ).traceRight + Sᵥₙ (MState.pure ψ).traceRight - Sᵥₙ (MState.pure ψ) = 2 * Sᵥₙ (MState.pure ψ).traceRight
⊢ Sᵥₙ (MState.pure ψ).traceRight + Sᵥₙ (MState.pure ψ).traceRight - 0 = 2 * Sᵥₙ (MState.pure ψ).traceRight
```

then `ring`.

---

## Part 2 · `MES_max_mutual_info`

Statement: `2 log |d|` is the greatest value of `I` on `MState (d × d)`. Two things to show: it is attained
(by `Φ`, which is Part 1) and it bounds every `I(ρ)`, because `I(ρ) = S(ρ_B) + S(ρ_A) − S(ρ)` with
`S(ρ_A), S(ρ_B) ≤ log |d|` and `S(ρ) ≥ 0`.

**R9 · `refine ⟨?_, ?_⟩`** changes the **goal list**: `IsGreatest s a` is by definition
`a ∈ s ∧ a ∈ upperBounds s`, so the `∧` pattern splits it. Placeholders: `{α : Type} [LE α] (s : Set α) (a : α)`
(`[LE α]`: α has `≤`; `ℝ` qualifies). You may fill the first `?_` directly with R10: `refine ⟨⟨_, h⟩, ?_⟩`.

| Before | After |
|---|---|
| `⊢ IsGreatest s a` | `⊢ a ∈ s`, `⊢ a ∈ upperBounds s` |

**R10 · `⟨_, h⟩`** **closes** `b ∈ Set.range f` given `h : f x = b`: membership in a range is an `∃`, and the
anonymous constructor supplies the witness `x` (written `_`, read off `h`) and the proof `h`. A theorem proved
earlier in the file can serve as `h`. Placeholders: `{α β : Type} (f : α → β) (x : α) (b : β)`.

| Before | After |
|---|---|
| `⊢ b ∈ Set.range f` | no goals |

**R11 · `rintro _ ⟨x, rfl⟩`** changes the **context and the goal**. `a ∈ upperBounds (Set.range f)` unfolds to
`∀ b, b ∈ Set.range f → b ≤ a`. `rintro` introduces `b` (named `_`, it is about to disappear) and the
membership, splits the membership into `x` and `f x = b`, and `rfl` replaces `b` by `f x` everywhere.
Placeholders: `{α : Type} (f : α → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ∈ upperBounds (Set.range f)` | `x : α ⊢ f x ≤ a` |

**R12 · `have hA := Sᵥₙ_le_log_d ρ`** changes the **context**. The lemma is
`Sᵥₙ_le_log_d (ρ : MState d) : Sᵥₙ ρ ≤ Real.log ↑Finset.univ.card` (entropy is at most log of the dimension).
`have h := e` without a type takes the type of `e`. Placeholders: `(ρ : MState d)`. Use it on `ρ.traceLeft`
and `ρ.traceRight`.

| Before | After |
|---|---|
| `⊢ G` | `hA : Sᵥₙ ρ ≤ Real.log ↑Finset.univ.card ⊢ G` |

**R13 · `have h0 := Sᵥₙ_nonneg ρ`** changes the **context**. The lemma is `Sᵥₙ_nonneg (ρ : MState d) : 0 ≤ Sᵥₙ ρ`.
Placeholders: `(ρ : MState d)`.

| Before | After |
|---|---|
| `⊢ G` | `h0 : 0 ≤ Sᵥₙ ρ ⊢ G` |

**R14 · `rw [Finset.card_univ] at hA hB`** changes the **context**: R8 applied inside the listed hypotheses;
the goal is untouched. Placeholders: `{α : Type} [Fintype α] (Q R : ℕ → Prop)`.

| Before | After |
|---|---|
| `hA : Q Finset.univ.card, hB : R Finset.univ.card ⊢ G` | `hA : Q (Fintype.card α), hB : R (Fintype.card α) ⊢ G` |

**R15 · `linarith`** **closes** a goal `t ≤ c`, `t < c` or `t = c` that is a linear consequence of hypotheses in
the context. Every non-linear piece (`Sᵥₙ ρ`, `Real.log ↑n`, `qMutualInfo ρ`) is an opaque unknown: it is
matched by syntax, never unfolded. Placeholders: `(x y z c : ℝ)`.

| Before | After |
|---|---|
| `hx : x ≤ c, hy : y ≤ c, hz : 0 ≤ z ⊢ x + y - z ≤ 2 * c` | no goals |

**W2: facts, then `linarith`.** `S(ρ_B) − S(ρ) ≤ log |d₂|` for `ρ : MState (d₁ × d₂)` (R12, R13, R14, R15):

```lean-goal
⊢ Sᵥₙ ρ.traceLeft - Sᵥₙ ρ ≤ Real.log ↑(Fintype.card d₂)
```

| Step | State after it |
|---|---|
| `have hB := Sᵥₙ_le_log_d ρ.traceLeft` | `hB : Sᵥₙ ρ.traceLeft ≤ Real.log ↑Finset.univ.card ⊢ Sᵥₙ ρ.traceLeft - Sᵥₙ ρ ≤ Real.log ↑(Fintype.card d₂)` |
| `have h0 := Sᵥₙ_nonneg ρ` | `h0 : 0 ≤ Sᵥₙ ρ ⊢ Sᵥₙ ρ.traceLeft - Sᵥₙ ρ ≤ Real.log ↑(Fintype.card d₂)` |
| `rw [Finset.card_univ] at hB` | `hB : Sᵥₙ ρ.traceLeft ≤ Real.log ↑(Fintype.card d₂) ⊢ Sᵥₙ ρ.traceLeft - Sᵥₙ ρ ≤ Real.log ↑(Fintype.card d₂)` |

then `linarith`.

**W3: the mirror image, `IsLeast`.** `IsLeast s a` is `a ∈ s ∧ a ∈ lowerBounds s`. For `ψ : Ket d`,
`0` is the least entropy: `refine ⟨⟨_, Sᵥₙ_of_pure_zero ψ⟩, ?_⟩` (R9 with R10 inside), then R11, then R13's lemma:

```lean-goal
⊢ IsLeast (Set.range Sᵥₙ) 0
⊢ 0 ∈ lowerBounds (Set.range Sᵥₙ)
⊢ 0 ≤ Sᵥₙ ρ
```

---

## Traps

- `traceLeft` traces **out** the left factor: `ρ.traceLeft` is `ρ_B`, `ρ.traceRight` is `ρ_A`.
- Order in Part 1: R2 before R3. R3 only matches `traceRight`; R2 turns the `traceLeft` copy into a
  `traceRight` copy, and then one `rw [traceRight_pure_MES]` handles both.
- `Sᵥₙ_ofClassical` does not see through `MState.uniform`: unfold it first (R5).
- `Finset.univ.card` and `Fintype.card d` are equal but are different text, so `ring`, `linarith` and `rw [h]`
  treat them as different. Rewrite with `Finset.card_univ` (R8 in the goal, R14 in hypotheses).
- `linarith` does not unfold `qMutualInfo`: `rw [qMutualInfo]` in the goal first (R1).
- Part 2 needs the value at `Φ`: that is exactly the Part 1 theorem, usable by name inside `⟨_, …⟩` (R10).
- `rintro _ ⟨ρ, rfl⟩`: the membership gives `h : qMutualInfo ρ = b` with the fresh variable `b` on one side, so
  `rfl` can substitute `b := qMutualInfo ρ` everywhere. `b` then disappears, which is why it is introduced as `_`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `I(ρ)` | `rw [qMutualInfo]` | R1 |
| `S(ψ_B) → S(ψ_A)` for pure `ψ` | `rw [Sᵥₙ_of_partial_eq]` | R2 |
| marginal of `Φ` | `rw [traceRight_pure_MES]` | R3 |
| `S(pure ψ) = 0` | `rw [Sᵥₙ_of_pure_zero]` | R4 |
| `I/d → ofClassical uniform` | `rw [MState.uniform]` | R5 |
| `S(diag p) = H(p)` | `rw [Sᵥₙ_ofClassical]` | R6 |
| `H(uniform) = log \|univ\|` | `rw [Hₛ_uniform]` | R7 |
| `Finset.univ.card → Fintype.card` | `rw [Finset.card_univ]` (`at h` in hypotheses) | R8, R14 |
| finish `a + a - 0 = 2 * a` | `ring` | TACTIC_STATES |
| split `IsGreatest s a` | `refine ⟨?_, ?_⟩` | R9 |
| `b ∈ Set.range f` | `⟨_, h⟩` with `h : f x = b` | R10 |
| bound every element of a range | `rintro _ ⟨x, rfl⟩` | R11 |
| `S(ρ) ≤ log \|univ\|` / `0 ≤ S(ρ)` | `have := Sᵥₙ_le_log_d ρ` / `have := Sᵥₙ_nonneg ρ` | R12, R13 |
| linear goal from hypotheses | `linarith` | R15 |
| find a lemma / see a definition | `exact?` / `#print name` | |
