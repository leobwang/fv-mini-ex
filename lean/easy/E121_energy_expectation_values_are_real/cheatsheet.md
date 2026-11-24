# E121 · Energy expectation values are real: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `have`, `exact`, `rw … at h` and `.mp` of
an `↔`. **New here:** physlib's tight-binding chain and its Hamiltonian, Mathlib's complex inner product
`⟪x, y⟫_ℂ`, complex conjugation `starRingEnd ℂ`, and `Complex.im`.

The physics: a Hermitian (self-adjoint) operator `H` satisfies `⟨Hψ, φ⟩ = ⟨ψ, Hφ⟩` for all states. The
energy expectation value in state `ψ` is `⟨ψ, Hψ⟩ ∈ ℂ`. Put `φ = ψ`: `⟨Hψ, ψ⟩ = ⟨ψ, Hψ⟩`, and conjugate
symmetry of the inner product, `⟨Hψ, ψ⟩ = conj ⟨ψ, Hψ⟩`, turns this into `conj z = z` for
`z = ⟨ψ, Hψ⟩`, i.e. `Im z = 0`. One library lemma per sentence: R1, R2, R3.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℂ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal or hypothesis. `G : Prop` is a goal the step leaves alone.
- Placeholders are written as Lean binders. `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]`
  is "any complex inner-product space `E`": the brackets are requirements on `E` (*type classes*);
  `T.HilbertSpace` (ℂ^N), `EuclideanSpace ℂ (Fin n)` and `ℂ` itself meet them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. A cell
  without `⊢` shows one hypothesis only (written with its name `h : …`).

## Reading the goals

| You see | It means |
|---|---|
| `TightBindingChain` | physlib structure `CondensedMatter.TightBindingChain`: fields `N : ℕ` (number of sites, `≠ 0`), `a : ℝ` (lattice spacing, `> 0`), `E0 : ℝ` (on-site energy), `t : ℝ` (hopping amplitude) |
| `T.HilbertSpace` | the state space of the chain: `QuantumMechanics.FiniteHilbertSpace (Fin T.N)`, i.e. ℂ^N with one basis state `\|n⟩` per site `n : Fin T.N`. It holds by `rfl`; you never need to unfold it |
| `T.hamiltonian` | `H = E0 · Σₙ \|n⟩⟨n\| − t · Σₙ (\|n⟩⟨n+1\| + \|n+1⟩⟨n\|)` (sites mod N), a value of type `T.HilbertSpace →ₗ[ℂ] T.HilbertSpace` |
| `V →ₗ[ℂ] V` | a ℂ-linear map from `V` to `V` |
| `T.hamiltonian ψ` | that linear map applied to the state `ψ` (Lean coerces a linear map to a function) |
| `⟪x, y⟫_ℂ` | `inner ℂ x y`, the inner product with scalars in `ℂ` (notation from `open InnerProductSpace`). Mathlib's convention: conjugate-linear in `x`, linear in `y` (physicists' `⟨x\|y⟩`) |
| `(starRingEnd ℂ) z` | the complex conjugate `conj z` (`star` as a ring map `ℂ → ℂ`) |
| `z.im`, `z.re` | `Complex.im z`, `Complex.re z : ℝ`, the imaginary and real parts |
| `(⟪ψ, T.hamiltonian ψ⟫_ℂ).im = 0` | `Im ⟨ψ\|H\|ψ⟩ = 0`: the expectation value is real. The `0` is `(0 : ℝ)` |

---

## Part 1 · `energy_real`

Statement: for a chain `T` and a state `ψ : T.HilbertSpace`, `(⟪ψ, T.hamiltonian ψ⟫_ℂ).im = 0`. In words:
the energy expectation value `⟨ψ|H|ψ⟩` is a real number.

### The physics input

**R1 · `have h := T.hamiltonian_hermitian ψ φ`** changes the **context**: it adds hermiticity for the two
states you pass. The lemma is
`CondensedMatter.TightBindingChain.hamiltonian_hermitian (T : TightBindingChain) (ψ φ : T.HilbertSpace) :
⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ`. Dot notation `T.hamiltonian_hermitian` supplies `T`;
`ψ`, `φ` are explicit, and you may pass the same state twice. Placeholders:
`(T : TightBindingChain) (ψ φ : T.HilbertSpace) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ` added; goal `G` unchanged |

### Conjugate symmetry

**R2 · `rw [← inner_conj_symm]`** changes the **goal**; with `at h` it changes the **context** (only `h`).
The lemma is `inner_conj_symm {𝕜 E} [RCLike 𝕜] … (x y : E) : (starRingEnd 𝕜) ⟪y, x⟫_𝕜 = ⟪x, y⟫_𝕜`
(`RCLike 𝕜`: `𝕜` is `ℝ` or `ℂ`; here `𝕜 = ℂ`). Left to right it removes a conjugate; right to left (`←`)
it turns the first `⟪x, y⟫_ℂ` it finds into the conjugate of the swapped product, and rewrites every copy
of that same term, no other inner product (W2). Placeholders:
`{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) (P : ℂ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ⟪x, y⟫_ℂ` | `⊢ P ((starRingEnd ℂ) ⟪y, x⟫_ℂ)` |
| `h : P ⟪x, y⟫_ℂ` (with `at h`) | `h : P ((starRingEnd ℂ) ⟪y, x⟫_ℂ)` |

### Real ⇔ self-conjugate

**R3 · `exact Complex.conj_eq_iff_im.mp h`** **closes** the goal `z.im = 0` from `h : conj z = z`. The lemma
is `Complex.conj_eq_iff_im {z : ℂ} : (starRingEnd ℂ) z = z ↔ z.im = 0`; `z` is implicit, read off from
`h`. `.mp` is the `→` direction (E005). Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `h : (starRingEnd ℂ) z = z ⊢ z.im = 0` | no goals |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: `⟪x, x⟫_ℂ` is real.** For any vector `x` of a complex inner-product space,
`have h := inner_conj_symm (𝕜 := ℂ) x x` gives `h : (starRingEnd ℂ) ⟪x, x⟫_ℂ = ⟪x, x⟫_ℂ` directly (R2
read forward; `(𝕜 := ℂ)` names the implicit scalar field, which `x x` does not determine), and R3 closes:

```lean-goal
⊢ (⟪x, x⟫_ℂ).im = 0
```

**W2: `rw [← inner_conj_symm]` on an equation touches one side.** For a linear map `A : E →ₗ[ℂ] E`, the
first inner product Lean meets is the left side `⟪A x, y⟫_ℂ`; only it is rewritten:

```lean-goal
⊢ ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ
⊢ (starRingEnd ℂ) ⟪y, A x⟫_ℂ = ⟪x, A y⟫_ℂ
```

In the exercise the same happens to `h` from R1: its left side becomes the conjugate of its right side,
which is exactly the `conj z = z` that R3 wants.

---

## Traps

- R1 takes the states explicitly: `T.hamiltonian_hermitian` alone is a `∀`, and R3 cannot use it; pass the
  state twice.
- `rw [inner_conj_symm] at h` (no `←`) fails: `h` has no `(starRingEnd ℂ) ⟪·, ·⟫_ℂ` to remove. You want `←`.
- Do not `simp` after R2: `inner_conj_symm` is a `simp` lemma, so `simp` undoes the rewrite. On `h` from R1,
  `simp at h` also unfolds the inner product of `T.HilbertSpace` to the underlying vectors
  (`⟪(T.hamiltonian ψ).val, ψ.val⟫_ℂ`), and `h` no longer matches the goal.
- `inner_conj_symm` used forward in a `have` needs the field named, `(𝕜 := ℂ)`, when the arguments do not
  fix it (W1). Inside `rw` the goal fixes it.
- Mathlib's inner product is conjugate-linear in the **first** argument; `⟪Hψ, ψ⟫_ℂ` and `⟪ψ, Hψ⟫_ℂ` are
  conjugates, not equal by definition.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| hermiticity for states `ψ`, `φ` | `have h := T.hamiltonian_hermitian ψ φ` | R1 |
| `⟪x, y⟫_ℂ` → `conj ⟪y, x⟫_ℂ` in the goal | `rw [← inner_conj_symm]` | R2 |
| the same inside `h` | `rw [← inner_conj_symm] at h` | R2 |
| `conj ⟪x, x⟫_ℂ = ⟪x, x⟫_ℂ` as a fact | `have h := inner_conj_symm (𝕜 := ℂ) x x` | R2, W1 |
| `z.im = 0` from `h : conj z = z` | `exact Complex.conj_eq_iff_im.mp h` | R3 |
| `z.im = 0` → goal `conj z = z` | `rw [← Complex.conj_eq_iff_im]` | R3 |
| see the state | infoview | |
