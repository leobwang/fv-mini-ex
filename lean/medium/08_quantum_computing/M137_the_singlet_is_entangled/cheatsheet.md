# M137 · The singlet is entangled: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's pure states `Ket`, the tensor
product of kets `⊗ᵠ`, the predicates `Ket.IsProd` / `Ket.IsEntangled`, and Mathlib's complex numbers
with real square roots cast into `ℂ`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal or hypothesis" (`P : ℂ → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits.
- Placeholders are written as Lean binders. `{d : Type}` is any type; `[Fintype d]` requires it to be
  finite (`Fin 2` and `Fin 2 × Fin 2` are). Kets are only defined over finite index types.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Ket d` | a pure state: a structure with a field `vec : d → ℂ` (amplitudes) and a proof `normalized'` that $\sum_x \lvert \mathrm{vec}\,x\rvert^2 = 1$ |
| `Fin 2` | `{0, 1}`, the qubit basis; `Ket (Fin 2)` is a qubit |
| `Fin 2 × Fin 2`, `(0, 1)` | pairs of basis labels; `(0, 1)` is $\lvert 01\rangle$ |
| `ψ i` | the amplitude of `ψ` at basis label `i`: a coercion of `ψ` to a function (`FunLike`); equal to `ψ.vec i` by `Ket.apply` (R4) |
| `ψ.vec i` | the same amplitude, read directly from the field |
| `ξ ⊗ᵠ φ` | `Ket.prod ξ φ`, the product state with $(\xi\otimes\varphi)(i,j) = \xi_i\,\varphi_j$ (R5) |
| `ψ.IsProd` | `∃ ξ φ, ψ = ξ ⊗ᵠ φ` |
| `ψ.IsEntangled` | `¬ ψ.IsProd` (R1) |
| `{ vec := …, normalized' := ⋯ }` | a `Ket` written as a structure literal; `⋯` is an elided proof |
| `x.1`, `x.2` | the two components of a pair `x` |
| `√2` | `Real.sqrt 2`, a real number |
| `↑√2` | that real number cast into `ℂ` (`Complex.ofReal`) |
| `(↑√2)⁻¹` | `1 / ↑√2`, as `simp` prints it (R8) |

---

## Part 1 · `singlet_entangled`

Statement: `singlet.IsEntangled`, where `singlet` has amplitude $1/\sqrt2$ at `(0, 1)`, $-1/\sqrt2$ at
`(1, 0)`, and `0` elsewhere. In words: there are no qubit kets `ξ φ` with `singlet = ξ ⊗ᵠ φ`. The argument:
such a decomposition gives $\xi_0\varphi_1 = 1/\sqrt2$, $\xi_1\varphi_0 = -1/\sqrt2$ and $\xi_0\varphi_0 = 0$;
the last forces $\xi_0 = 0$ or $\varphi_0 = 0$, which makes one of the first two zero.

### Entangled means "no product decomposition"

**R1 · `unfold Ket.IsEntangled Ket.IsProd`** changes the **goal**: it replaces the two definitions by their
bodies. Optional; it only shows what R2 is working with. Placeholders:
`{d₁ d₂ : Type} [Fintype d₁] [Fintype d₂] (ψ : Ket (d₁ × d₂))`.

| Before | After |
|---|---|
| `⊢ ψ.IsEntangled` | `⊢ ¬∃ ξ φ, ψ = ξ ⊗ᵠ φ` |

**R2 · `rintro ⟨ξ, φ, h⟩`** changes the **goal and the context**. `¬ A` is `A → False`, so the goal is an
implication; `rintro` introduces its hypothesis and destructs the `∃ ξ φ, …` in one step. It unfolds
`IsEntangled` and `IsProd` by itself, so R1 is not needed first. Placeholders as in R1.

| Before | After |
|---|---|
| `⊢ ψ.IsEntangled` | `ξ : Ket d₁, φ : Ket d₂, h : ψ = ξ ⊗ᵠ φ ⊢ False` |

### From an equation of kets to an equation of amplitudes

**R3 · `have hi := congrArg (fun χ : Ket d => χ i) h`** changes the **context**. The lemma is
`congrArg (f : α → β) : a = b → f a = f b`; with `f` = "amplitude at `i`" it turns `h : ψ = χ` into an
equation in `ℂ`. Write `Ket _` and Lean fills in the index type. Placeholders:
`{d : Type} [Fintype d] (ψ χ : Ket d) (i : d)`.

| Before | After |
|---|---|
| `h : ψ = χ ⊢ P (ψ i)` | `h : ψ = χ, hi : ψ i = χ i ⊢ P (ψ i)` |

**R4 · `Ket.apply`** changes the **context** (with `rw [Ket.apply] at h`; `simp` takes it too). The lemma is
`Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i`: the coerced amplitude is the `vec` field. `simp` needs it to
see into `ψ i`. Placeholders: `(ψ : Ket d) (i : d)`.

| Before | After |
|---|---|
| `h : P (ψ i) ⊢ P (ψ.vec i)` | `h : P (ψ.vec i) ⊢ P (ψ.vec i)` |

**R5 · `Ket.prod`, then `Ket.apply`** change the **goal** (with `at h`, the **context**): the amplitude of a product state at `(i, j)`
becomes the product of amplitudes. `Ket.prod` is a definition, so `simp [Ket.prod]` unfolds it to a
structure literal; `Ket.apply` then reads its `vec` at the pair. Placeholders:
`(ξ : Ket d₁) (φ : Ket d₂) (i : d₁) (j : d₂)`.

| Before | After `simp only [Ket.prod]` | After `simp only [Ket.apply]` |
|---|---|---|
| `⊢ P ((ξ ⊗ᵠ φ) (i, j))` | `⊢ P ({ vec := fun x => ξ x.1 * φ x.2, normalized' := ⋯ } (i, j))` | `⊢ P (ξ.vec i * φ.vec j)` |

**R6 · `simp only [D]`** changes the **goal** (with `at h`, the **context**): a ket you defined with `def D : Ket … where vec := …`
is replaced by its body, so `D.vec i` becomes the `if` expression. Do R4 first (or pass both to one `simp`).
Placeholders: `D` = the product state $\lvert 00\rangle$ defined in the guide, `(i : Fin 2 × Fin 2)`.

| Before | After `rw [Ket.apply]` | After `simp only [D]` |
|---|---|---|
| `⊢ P (D i)` | `⊢ P (D.vec i)` | `⊢ P (if i = (0, 0) then 1 else 0)` |

**R7 · `simp` on an `if` over concrete pairs** changes the **goal** (with `at h`, the **context**): `simp` decides each test
(`Prod.mk.injEq : (a, b) = (c, d) ↔ a = c ∧ b = d`, and `0 ≠ 1` in `Fin 2`) and keeps the branch that
applies (`if_pos` / `if_neg`). Placeholders: `(a b c : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (if (0, 0) = (0, 1) then a else if (0, 0) = (1, 0) then b else c)` | `⊢ P c` |

### Reading the amplitude equations

After one `simp [singlet, Ket.prod, Ket.apply] at …` (R4–R7 at once), each hypothesis is an equation in `ℂ`
whose right side is `ξ.vec i * φ.vec j`. Two more lemmas explain how `simp` prints them.

**R8 · `one_div`** changes the **context**. The lemma is `one_div (a : α) : 1 / a = a⁻¹`; `simp` applies it,
which is why `1 / Real.sqrt 2` appears as `(↑√2)⁻¹`. `-1 / ↑√2` is left as it is. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `h : P (1 / a) ⊢ P a⁻¹` | `h : P a⁻¹ ⊢ P a⁻¹` |

**R9 · `zero_eq_mul`** changes the **context**. The lemma is `zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0`
(`mul_eq_zero` is the same with `a * b = 0`); it holds in `ℂ` because `ℂ` has no zero divisors. `simp` applies
it, so an amplitude equation `0 = ξ.vec i * φ.vec j` arrives as a disjunction. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `h : 0 = a * b ⊢ P` | `h : a = 0 ∨ b = 0 ⊢ P` |

**R10 · `rcases h with h | h`** changes the **goal list and the context**: one goal per side of the `∨`, with
`h` holding that side. Placeholders: `(A B G : Prop)`. Follow it with `<;>` to run the same tactic in both.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `h : A ⊢ G`, `h : B ⊢ G` |

**R11 · `simp [h] at h1`** with `h : a = 0` changes the **context**: it substitutes `a := 0` in `h1` and
simplifies `0 * b` to `0` (`zero_mul`; `mul_zero` for `b * 0`). Placeholders: `(a b c : ℂ)`.

| Before | After |
|---|---|
| `h : a = 0, h1 : c = a * b ⊢ P` | `h : a = 0, h1 : c = 0 ⊢ P` |

**R12 · `simp at h`** with a false `h` changes the **goal list**: `simp` rewrites `h` to `False` and closes
the goal, whatever it is. For `(↑√3)⁻¹ = 0` it chains `inv_eq_zero : a⁻¹ = 0 ↔ a = 0`,
`Complex.ofReal_eq_zero : (↑x : ℂ) = 0 ↔ x = 0`, `Real.sqrt_eq_zero : 0 ≤ x → (√x = 0 ↔ x = 0)` (its side
condition `0 ≤ 3` by `Nat.ofNat_nonneg`) and `OfNat.ofNat_ne_zero : 3 ≠ 0`. For `-1 / ↑√3 = 0` it adds
`div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0`, `neg_eq_zero : -a = 0 ↔ a = 0` and `one_ne_zero : 1 ≠ 0`.
`simp? at h` prints the exact list. In the exercise
R11 and R12 happen in the same `simp [h] at h01 h10` call.

| Before | After |
|---|---|
| `h : (↑√3)⁻¹ = 0 ⊢ G` | no goals |
| `h : -1 / ↑√3 = 0 ⊢ G` | no goals |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: amplitudes of a decomposition of $\lvert 00\rangle$.** From `h : D = ξ ⊗ᵠ φ`, R3 at `(0, 0)` and `(0, 1)`
gives

```lean-goal
⊢ ξ.vec 0 * φ.vec 0 = 1
```

with `h00 : D (0, 0) = (ξ ⊗ᵠ φ) (0, 0)` and `h01 : D (0, 1) = (ξ ⊗ᵠ φ) (0, 1)` in the context. Then
`simp [D, Ket.prod, Ket.apply] at h00 h01` (R4–R7, and R9 on the zero amplitude) leaves
`h00 : 1 = ξ.vec 0 * φ.vec 0` and `h01 : ξ.vec 0 = 0 ∨ φ.vec 1 = 0`.

**W2: contradiction from amplitude equations.** With `h1 : 1 = a * b`, `h2 : 2 = c * d`, `h0 : 0 = a * d`:
`rw [zero_eq_mul] at h0` (R9), then `rcases h0 with h | h <;> simp [h] at h1 h2` (R10, then R11 → R12 in each
goal):

```lean-goal
⊢ False
```

is closed in both cases, because `a = 0` makes `h1` read `1 = 0`, and `d = 0` makes `h2` read `2 = 0`.

---

## Traps

- `rcases … <;> simp [h] at h01 h10` must list **both** equations: in the `ξ.vec 0 = 0` case the contradiction
  is in `h01`, in the `φ.vec 0 = 0` case it is in `h10`. With only `h01`, the second case fails with
  "`simp` made no progress" (`h01` does not mention `φ.vec 0`).
- Without `Ket.apply`, `simp` unfolds the kets but stops at structure literals applied to a pair,
  `{ vec := fun p => …, normalized' := ⋯ } (0, 1)`; it cannot read the `vec` field through the coercion.
- Without `singlet` in the `simp` list, `simp` does not unfold your definition; without `Ket.prod`, the right
  sides stay `(ξ ⊗ᵠ φ) (0, 1)`.
- The amplitude at `(0, 0)` is the one that gives the disjunction. Two nonzero amplitudes alone
  (`(0, 1)` and `(1, 0)`) contradict nothing: you need the zero one too.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see what `IsEntangled` means | `unfold Ket.IsEntangled Ket.IsProd` | R1 |
| assume a product decomposition | `rintro ⟨ξ, φ, h⟩` | R2 |
| ket equation → amplitude at `i` | `have hi := congrArg (fun χ : Ket _ => χ i) h` | R3 |
| `ψ i` → `ψ.vec i` | `Ket.apply` | R4 |
| `(ξ ⊗ᵠ φ) (i, j)` → `ξ.vec i * φ.vec j` | `simp [Ket.prod, Ket.apply] at h` | R5 |
| unfold your ket and its `if` | `simp [D, Ket.apply] at h` | R6, R7 |
| all of the above at once | `simp [D, Ket.prod, Ket.apply] at h1 h2 h3` | R4–R9 |
| `1 / a` printed as `a⁻¹` | `one_div` (by `simp`) | R8 |
| `0 = a * b` → `a = 0 ∨ b = 0` | `zero_eq_mul` / `mul_eq_zero` | R9 |
| case split on `∨` | `rcases h with h \| h` | R10 |
| substitute a zero and close | `simp [h] at h1 h2` | R11, R12 |
| same tactic in every goal | `t <;> u` | TACTIC_STATES |
