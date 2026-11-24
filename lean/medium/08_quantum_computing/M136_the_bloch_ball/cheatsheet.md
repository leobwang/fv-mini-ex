# M136 · The Bloch ball: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's mixed states `MState`, Mathlib's
`Matrix` with `det`, `trace`, `PosSemidef`, `IsHermitian`, complex numbers with `re`, `im`, `star`, the
order `≤` on `ℂ` (`open scoped ComplexOrder`), and the arithmetic closers `linarith`, `nlinarith`.

**The math.** A qubit state is a 2×2 complex matrix `ρ` that is Hermitian, positive semidefinite (PSD) and
has trace 1. Write `a = ρ₀₀`, `b = ρ₁₁` (real, because `ρ` is Hermitian) and `w = ρ₀₁`, so `ρ₁₀ = w̄`
(the conjugate). Then `x = 2 Re w`, `y = −2 Im w`, `z = a − b`, so `x² + y² + z² = 4|w|² + (a − b)²`.
The trace gives `a + b = 1`; PSD gives `det ρ = ab − |w|² ≥ 0`. Hence
`(a − b)² + 4|w|² = (a + b)² − 4(ab − |w|²) ≤ 1`. The Lean proof turns each of these facts into a real
hypothesis and lets `nlinarith` do the last line.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of the goal or hypothesis" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `G : Prop` is a goal the step does not touch. Most entries here change the **context** (a hypothesis),
  so their goal stays `G`.
- Placeholders are Lean binders. `{d : Type}` is any type; `[Fintype d] [DecidableEq d]` say `d` is finite
  with decidable equality (`Fin 2` and `Fin 3` qualify). `inst✝ : Fintype d` in the infoview is such an
  unnamed instance.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 2` | the type `{0, 1}`; `Fin n` is `{0, …, n − 1}`, used as row and column indices |
| `MState (Fin 2)` | a qubit mixed state (physlib): a PSD 2×2 complex matrix with trace 1 |
| `ρ.m` | its density matrix, of type `Matrix (Fin 2) (Fin 2) ℂ` |
| `ρ.m i j` | the entry `ρᵢⱼ`, row `i`, column `j`, counted from 0 |
| `z.re`, `z.im` | real and imaginary part of `z : ℂ`; `Complex.re z` is the same as `z.re` |
| `star z` | on `ℂ`, the complex conjugate `z̄`; `(starRingEnd ℂ) z` is the same thing |
| `A.det`, `A.trace` | determinant and trace of the square matrix `A` |
| `A.IsHermitian` | `A` equals its conjugate transpose: `star (A j i) = A i j` for all `i j` |
| `A.PosSemidef` | `A` is Hermitian and `v̄ᵀ A v ≥ 0` for every vector `v` |
| `0 ≤ z` with `z : ℂ` | the order from `ComplexOrder`: `z` is real and nonnegative (R12) |
| `Complex.re 1` | the real part of the complex number `1`; `simp` makes it `1` |
| `h.1`, `h.2` | the left and right halves of `h : A ∧ B` |
| `hdet :` followed by an indented line | one long hypothesis printed over two lines |

---

## Part 1 · `bloch_ball`

Statement: for every qubit state `ρ`, `blochX ρ ^ 2 + blochY ρ ^ 2 + blochZ ρ ^ 2 ≤ 1`, where
`blochX ρ = 2 Re ρ₀₁`, `blochY ρ = −2 Im ρ₀₁`, `blochZ ρ = Re ρ₀₀ − Re ρ₁₁` are real numbers.

### The facts a state carries

**R1 · `ρ.psd`** (lemma `MState.psd : ρ.m.PosSemidef`) changes the **context**: `have h := ρ.psd` adds that
the matrix of `ρ` is PSD. Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ρ : MState d)`.

| Before | After |
|---|---|
| `⊢ G` | `h : ρ.m.PosSemidef ⊢ G` |

**R2 · `Matrix.PosSemidef.det_nonneg`** changes the **context**. The lemma is `A.PosSemidef → 0 ≤ A.det`, with
`≤` on `ℂ` (R12). Use it with dot notation: `hA.det_nonneg`, or chained, `ρ.psd.det_nonneg`. Placeholders:
`{n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosSemidef)`.

| Before | After |
|---|---|
| `⊢ G` | `hdet : 0 ≤ A.det ⊢ G` |

**R3 · `ρ.tr'`** (lemma `MState.tr' : ρ.m.trace = 1`) changes the **context**. Placeholders as R1.

| Before | After |
|---|---|
| `⊢ G` | `htr : ρ.m.trace = 1 ⊢ G` |

**R4 · `ρ.Hermitian`** (lemma `MState.Hermitian : ρ.m.IsHermitian`) changes the **context**. Placeholders as R1.

| Before | After |
|---|---|
| `⊢ G` | `h : ρ.m.IsHermitian ⊢ G` |

### Hermitian entries

**R5 · `Matrix.IsHermitian.apply`** changes the **context**. The lemma is
`A.IsHermitian → ∀ i j, star (A j i) = A i j`: note the swapped indices on the left. Chained:
`ρ.Hermitian.apply 1 0 : star (ρ.m 0 1) = ρ.m 1 0`. Placeholders:
`{n : Type} (A : Matrix n n ℂ) (hA : A.IsHermitian) (i j : n)`.

| Before | After |
|---|---|
| `⊢ G` | `h : star (A j i) = A i j ⊢ G` |

**R6 · `h.symm`** changes the **context**: it turns `h : a = b` into a proof of `b = a`. Use it to get the
direction `rw` needs (`ρ.m 1 0 = star (ρ.m 0 1)`, so `rw` replaces `ρ.m 1 0`). Placeholders:
`{α : Type} (a b : α) (h : a = b)`.

| Before | After |
|---|---|
| `h : a = b ⊢ G` | `h' : b = a ⊢ G` |

**R7 · `congrArg Complex.im h`** changes the **context**: from `h : z = w` it gives `z.im = w.im` (apply the
function `Complex.im` to both sides). `congrArg Complex.re h` gives the real parts. Placeholders:
`(z w : ℂ) (h : z = w)`.

| Before | After |
|---|---|
| `h : z = w ⊢ G` | `h' : z.im = w.im ⊢ G` |

**R8 · `simp at h`** (it uses `RCLike.star_def`, `star z = conj z`, and `Complex.conj_im`, `(conj z).im = -z.im`)
changes the **context**: the imaginary part of a conjugate becomes minus the imaginary part. Placeholders:
`(z : ℂ)`.

| Before | After |
|---|---|
| `h : (star z).im = z.im ⊢ G` | `h : -z.im = z.im ⊢ G` |

**R9 · `linarith`** **closes** a goal that follows from the hypotheses by adding and scaling them (linear
arithmetic over an ordered field such as `ℝ`). Placeholders: `(a : ℝ)`.

| Before | After |
|---|---|
| `h : -a = a ⊢ a = 0` | closed |

R4 → R5 → R7 → R8 → R9 proves that a diagonal entry `ρᵢᵢ` is real: `(ρ.m i i).im = 0` (W2).

### Determinant and trace of a 2×2 matrix

**R10 · `rw [Matrix.det_fin_two] at h`** changes the **context**. The lemma is
`A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0` for `A : Matrix (Fin 2) (Fin 2) R` (`R` a commutative ring; `ℂ`
qualifies). `at h` rewrites the hypothesis `h` instead of the goal. Placeholders:
`(A : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop)`.

| Before | After |
|---|---|
| `h : P A.det ⊢ G` | `h : P (A 0 0 * A 1 1 - A 0 1 * A 1 0) ⊢ G` |

**R11 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h` with an equation
`e : a = b`. The left side `a` must appear literally in `h`. Placeholders:
`{α : Type} (a b : α) (P : α → Prop) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ G` | `h : P b ⊢ G` |

**R12 · `rw [Complex.nonneg_iff] at h`** changes the **context**. The lemma is
`0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im`. It needs `open scoped ComplexOrder`, which defines `≤` on `ℂ` by
`z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`. After it, the left half is a real inequality that `nlinarith` can use.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `h : 0 ≤ z ⊢ G` | `h : 0 ≤ z.re ∧ 0 = z.im ⊢ G` |

**R13 · `rw [Matrix.trace_fin_two] at h`** changes the **context**. The lemma is
`A.trace = A 0 0 + A 1 1`. Placeholders: `(A : Matrix (Fin 2) (Fin 2) ℂ) (P : ℂ → Prop)`.

| Before | After |
|---|---|
| `h : P A.trace ⊢ G` | `h : P (A 0 0 + A 1 1) ⊢ G` |

### Real parts

**R14 · `simp at h`** (it uses `Complex.add_re : (z + w).re = z.re + w.re` and `Complex.one_re : Complex.re 1 = 1`)
changes the **context**. This is what R7 with `Complex.re` leaves after R13. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `h : (z + w).re = Complex.re 1 ⊢ G` | `h : z.re + w.re = 1 ⊢ G` |

**R15 · `Complex.mul_re`** changes the **context**. The lemma is `(z * w).re = z.re * w.re - z.im * w.im`. With a
conjugate factor, `simp` then applies `Complex.conj_re : (conj w).re = w.re` and
`Complex.conj_im : (conj w).im = -w.im`. In the exercise, give `Complex.mul_re` to `simp` directly. Placeholders:
`(z w : ℂ) (P : ℝ → Prop)`.

| Before | After `rw [Complex.mul_re] at h` | After `simp at h` |
|---|---|---|
| `h : P (z * star w).re ⊢ G` | `h : P (z.re * (star w).re - z.im * (star w).im) ⊢ G` | `h : P (z.re * w.re + z.im * w.im) ⊢ G` |

So `(w * star w).re = w.re² + w.im² = |w|²`.

**R16 · `simp at h`** (it uses `sub_nonneg : 0 ≤ a - b ↔ b ≤ a`) changes the **context**: `simp` moves the
subtraction across. After R12 and R15 your `hdet.1` has this shape. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : 0 ≤ a - b ⊢ G` | `h : b ≤ a ⊢ G` |

**R17 · `simp [h₀] at h₁ h₂`** changes the **context**: it simplifies several hypotheses at once and uses the
hypothesis `h₀` as an extra rewrite rule. Here `h₀ : z.im = 0` kills the `z.im * …` terms. The simplified
hypotheses move to the **end** of the context. Placeholders: `(z w : ℂ) (P : ℝ → Prop) (h₀ : z.im = 0)`.

| Before | After |
|---|---|
| `h₁ : P (z * w).re, h₂ : P (z * w).im ⊢ G` | `h₁ : P (z.re * w.re), h₂ : P (z.re * w.im) ⊢ G` |

### Closing

**R18 · `simp only [D]`** changes the **goal**: it replaces a defined name by its body. Placeholders: `D`
defined by `def pop1 (ρ : MState (Fin 2)) : ℝ := (ρ.m 1 1).re`, `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (pop1 ρ)` | `⊢ P (ρ.m 1 1).re` |

**R19 · `nlinarith [t₁, …]`** **closes** a goal of polynomial (in)equalities over `ℝ`. It is `linarith` that
also multiplies pairs of hypotheses and of the extra facts `tᵢ` you pass in brackets. Pass the facts it would
not find in the context by itself, such as `h.1` (the left half of `h : A ∧ B`) or `sq_nonneg t : 0 ≤ t ^ 2`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : 0 ≤ a * b ∧ 0 ≤ b ⊢ (a - b) ^ 2 ≤ (a + b) ^ 2` | closed by `nlinarith [h.1]` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: the trace of a qutrit state in real parts.** `ρ : MState (Fin 3)`. R3, then
`rw [Matrix.trace_fin_three] at htr` (`A.trace = A 0 0 + A 1 1 + A 2 2`), then R7 with `Complex.re`, then R14:

| Step | Context after it |
|---|---|
| `have htr := ρ.tr'` | `htr : ρ.m.trace = 1 ⊢ (ρ.m 0 0).re + (ρ.m 1 1).re + (ρ.m 2 2).re = 1` |
| `rw [Matrix.trace_fin_three] at htr` | `htr : ρ.m 0 0 + ρ.m 1 1 + ρ.m 2 2 = 1 ⊢ (ρ.m 0 0).re + (ρ.m 1 1).re + (ρ.m 2 2).re = 1` |
| `have htr' := congrArg Complex.re htr` | `htr' : (ρ.m 0 0 + ρ.m 1 1 + ρ.m 2 2).re = Complex.re 1 ⊢ (ρ.m 0 0).re + (ρ.m 1 1).re + (ρ.m 2 2).re = 1` |
| `simp at htr'` | `htr' : (ρ.m 0 0).re + (ρ.m 1 1).re + (ρ.m 2 2).re = 1 ⊢ (ρ.m 0 0).re + (ρ.m 1 1).re + (ρ.m 2 2).re = 1` |

**W2: a diagonal entry of a qutrit state is real.** `have h := congrArg Complex.im (ρ.Hermitian.apply 2 2)`
(R4, R5, R7 in one line), then R8, then R9:

| Before | After `simp at h` |
|---|---|
| `h : (star (ρ.m 2 2)).im = (ρ.m 2 2).im ⊢ (ρ.m 2 2).im = 0` | `h : -(ρ.m 2 2).im = (ρ.m 2 2).im ⊢ (ρ.m 2 2).im = 0` |

**W3: `nlinarith` needs the right square.** From `h : a + b = 1` alone it cannot prove `a * b ≤ 1 / 4`; with the
hint `sq_nonneg (a - b)` it can, since `(a - b)² = (a + b)² − 4ab`.

```lean-goal
⊢ a * b ≤ 1 / 4
```

---

## Traps

- `rw [e] at h` needs the left side of `e` literally in `h`: `ρ.m 1 0` appears in `hdet` only **after**
  `Matrix.det_fin_two` (R10 before R11).
- `ρ.Hermitian.apply 1 0` is `star (ρ.m 0 1) = ρ.m 1 0`. To replace `ρ.m 1 0` you need the other direction (R6).
- Take real parts of `htr` **after** R13, so the sum `ρ.m 0 0 + ρ.m 1 1` is there for R14 to split.
- `ρ.m 0 0 : ℂ`. Its imaginary part is 0, but Lean does not know that until you prove it (R4 → R9). Without
  `(ρ.m 0 0).im = 0` and `(ρ.m 1 1).im = 0`, `Complex.mul_re` leaves `im * im` terms and `nlinarith` fails.
- `linarith` and `nlinarith` work over ordered fields such as `ℝ`, not over `ℂ`. A `≤` on `ℂ` (R2) must
  first become a real inequality (R12, then `.1`).
- `simp at h` can change more than you expect: `0 ≤ a - b` becomes `b ≤ a` (R16), and the hypothesis moves to the
  end of the context (R17). Look at the infoview before writing `hdet.1`.
- `nlinarith` only sees the conjuncts you hand it: a hypothesis `h : A ∧ B` in the context is not split. Pass
  `h.1`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `ρ.m` is PSD / Hermitian / has trace 1 | `ρ.psd` / `ρ.Hermitian` / `ρ.tr'` | R1, R4, R3 |
| `0 ≤ det` | `have hdet := ρ.psd.det_nonneg` | R1, R2 |
| entry relation of a Hermitian matrix | `ρ.Hermitian.apply i j : star (ρ.m j i) = ρ.m i j` | R5 |
| flip an equation | `h.symm` | R6 |
| real / imaginary part of an equation | `congrArg Complex.re h` / `congrArg Complex.im h` | R7 |
| `(star z).im → -z.im` | `simp at h` | R8 |
| linear arithmetic | `linarith` | R9 |
| 2×2 det / trace | `rw [Matrix.det_fin_two] at h` / `rw [Matrix.trace_fin_two] at h` | R10, R13 |
| rewrite a hypothesis | `rw [e] at h` | R11 |
| `0 ≤ z` on `ℂ` → real facts | `rw [Complex.nonneg_iff] at h` | R12 |
| real part of sums, products, conjugates | `simp [Complex.mul_re, h₀] at h₁ h₂` | R14, R15, R17 |
| `0 ≤ a - b → b ≤ a` | `simp at h` | R16 |
| unfold definitions | `simp only [D₁, D₂]` | R18 |
| polynomial inequality | `nlinarith [h.1, sq_nonneg t]` | R19 |
| see the state | infoview | |
