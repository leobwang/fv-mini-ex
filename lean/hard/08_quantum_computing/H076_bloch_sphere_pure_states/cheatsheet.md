# H076 · The Bloch sphere: pure iff on the sphere: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's qubit states (`MState`, `Ket`,
`MState.pure`); Mathlib's complex numbers (`re`, `im`, `conj`, `normSq`, casts `ℝ → ℂ`), `Real.sqrt`,
matrices `Matrix (Fin 2) (Fin 2) ℂ`, vector literals `![a, b]`; the tactics `linarith`, `nlinarith`,
`field_simp`, `push_cast`, `exact_mod_cast`, `rcases`/`obtain`/`rintro` patterns, `let`, `simpa`.

**The physics.** A qubit *density matrix* is a 2×2 complex matrix $\rho$ that is Hermitian
($\rho^\dagger = \rho$, $\dagger$ = conjugate transpose), positive semidefinite, and of trace 1. Write
$a = \operatorname{Re}\rho_{00}$, $b = \operatorname{Re}\rho_{11}$, $z = \rho_{01}$. Hermiticity gives real diagonal
entries and $\rho_{10} = \bar z$; trace 1 gives $a + b = 1$. The *Bloch vector* is
$r = (2\operatorname{Re} z,\ -2\operatorname{Im} z,\ a - b)$, so that $\rho = \tfrac12(1 + r_x X + r_y Y + r_z Z)$ with
$X, Y, Z$ the Pauli matrices. Then

$$|r|^2 = 4|z|^2 + (a-b)^2 = 4|z|^2 + (a+b)^2 - 4ab = 1 + 4\,(|z|^2 - ab),$$

so $|r| = 1 \iff |z|^2 = ab \iff \det\rho = 0$. $\rho$ is *pure* when $\rho = |\psi\rangle\langle\psi|$ for a unit
vector $\psi \in \mathbb C^2$ (a *ket*), i.e. $\rho_{ij} = \psi_i\,\overline{\psi_j}$. For a pure state
$|z|^2 = |\psi_0|^2|\psi_1|^2 = ab$. Conversely, given $a, b \ge 0$, $a + b = 1$, $|z|^2 = ab$, the ket
$\psi = (\sqrt a,\ \bar z/\sqrt a)$ (or $|1\rangle$ when $a = 0$) has $\psi\psi^\dagger = \rho$.

**How physlib encodes it.** `MState d` is a structure (a PSD Hermitian matrix of trace 1 on the basis `d`);
`ρ.m : Matrix d d ℂ` is its plain matrix. `Ket d` is a structure with `vec : d → ℂ` and a proof
`normalized' : ∑ x, ‖vec x‖ ^ 2 = 1`; it coerces to a function, so `ψ i : ℂ` is the `i`-th amplitude.
`MState.pure ψ` is $|\psi\rangle\langle\psi|$. Here `d = Fin 2 = {0, 1}`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℂ → Prop` or `P : ℝ → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. `G : Prop` with `g : … → G` is an arbitrary goal for entries
  that only add a fact.
- Placeholders are written as Lean binders. `{d : Type} [Fintype d] [DecidableEq d]` is any finite basis with
  decidable equality (the brackets are *type class* requirements; `Fin 2` meets them).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ρ : MState (Fin 2)` | a qubit density matrix |
| `ρ.m i j` | entry `(i, j)` of its matrix, a complex number; `i j : Fin 2` |
| `ψ : Ket (Fin 2)`, `ψ i` | a unit vector in ℂ², its `i`-th amplitude |
| `MState.pure ψ` | the pure state $\lvert\psi\rangle\langle\psi\rvert$ |
| `{ vec := ![u, v], normalized' := ⋯ }` | a ket built from amplitudes `u, v` (the proof is hidden as `⋯`) |
| `(starRingEnd ℂ) z` | the complex conjugate $\bar z$ (Lean's name for `conj z`) |
| `star z`, `star (A j i)` | also the conjugate (`star` is the general name; `simp` turns it into `starRingEnd`) |
| `z.re`, `z.im`, `Complex.re 1` | real and imaginary part (`Complex.re 1` is `(1 : ℂ).re`) |
| `Complex.normSq z` | $\lvert z\rvert^2 = (\operatorname{Re} z)^2 + (\operatorname{Im} z)^2$, a real number |
| `‖z‖` | the modulus $\lvert z\rvert$ |
| `↑x` | the real number `x` cast into `ℂ` |
| `√x` | `Real.sqrt x` (0 for `x < 0`) |
| `A.IsHermitian`, `A.trace` | $A^\dagger = A$; $\sum_i A_{ii}$ |
| `![a, b]` | the vector `Fin 2 → α` with `0 ↦ a`, `1 ↦ b` |
| `∑ x, f x` | the sum of `f x` over all `x` of a finite type (here `x : Fin 2`, so `f 0 + f 1`, R29) |
| `Ket.basis i` | the basis ket $\lvert i\rangle$ (amplitude 1 at `i`, 0 elsewhere) |
| `↑0`, `0 * b` | casts and products of numerals that `simp` has not yet cleaned up (`↑0 = 0`, `0 * b = 0`) |
| `ha✝` | an older `ha`, shadowed by a newer hypothesis with the same name |
| `ψ : Ket (Fin 2) := …` | a `let`-bound name: `ψ` together with its value |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` after `constructor` |
| `case inl`, `case inr` | the left / right case of an `∨` after `rcases` |
| `case refine_1`, `case inr.refine_2` | the goal for the 1st / 2nd `?_` of a `refine` (inside case `inr`) |

---

## Part 1 · `herm_facts` (milestone)

Statement: for `ρ : MState (Fin 2)`, `ρ.m 1 0 = conj (ρ.m 0 1)`, both diagonal entries are real, and their real
parts add to 1. Sources: Hermiticity (R1, R4) and trace 1 (R2, R3).

**R1 · `have hH := ρ.Hermitian`** changes the **context**. `MState.Hermitian : ρ.m.IsHermitian`.
Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ρ : MState d)`.

| Before | After |
|---|---|
| `⊢ G` | `hH : ρ.m.IsHermitian ⊢ G` |

**R2 · `have htr := ρ.tr'`** changes the **context**. `MState.tr' : ρ.m.trace = 1`. Placeholders as R1.

| Before | After |
|---|---|
| `⊢ G` | `htr : ρ.m.trace = 1 ⊢ G` |

**R3 · `rw [Matrix.trace_fin_two] at htr`** changes the **context**. `Matrix.trace_fin_two : A.trace = A 0 0 + A 1 1`.
Placeholders: `(A : Matrix (Fin 2) (Fin 2) ℂ)`.

| Before | After |
|---|---|
| `htr : A.trace = 1 ⊢ G` | `htr : A 0 0 + A 1 1 = 1 ⊢ G` |

**R4 · `have e := hH.apply i j`** changes the **context**. `Matrix.IsHermitian.apply : A.IsHermitian → star (A j i) = A i j`
(note the swapped indices on the left). Placeholders: `{n : Type} (A : Matrix n n ℂ) (hH : A.IsHermitian) (i j : n)`.

| Before | After |
|---|---|
| `hH : A.IsHermitian ⊢ G` | `e : star (A j i) = A i j ⊢ G` |

**R5 · `refine ⟨e.symm, ?_⟩`** changes the **goal list**: the first conjunct is proved by the flipped equation
(`Eq.symm : a = b → b = a`), the rest stays open. With `⟨e.symm, ?_, ?_, ?_⟩` it splits four conjuncts.
Placeholders: `{α : Type} (a b : α) (e : a = b) (Q : Prop)`.

| Before | After |
|---|---|
| `⊢ b = a ∧ Q` | `⊢ Q` |

**R6 · `have k := congrArg Complex.im e`** changes the **context**: apply a function to both sides of an
equation. `congrArg : (f : α → β) → a = b → f a = f b`. Placeholders: `(z w : ℂ) (e : z = w)`.

| Before | After |
|---|---|
| `e : z = w ⊢ G` | `k : z.im = w.im ⊢ G` |

**R7 · `simp at k`** changes the **context**: `star z` becomes the conjugate, and `(conj z).im = -z.im`
(`Complex.conj_im`). Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `k : (star z).im = z.im ⊢ G` | `k : -z.im = z.im ⊢ G` |

**R8 · `linarith`** **closes** a goal that is a linear combination of hypotheses (equalities and `≤`, `<` over
`ℝ`). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `k : -x = x ⊢ x = 0` | no goals |

**R9 · `simpa using k`** **closes** the goal: it simplifies `k` and the goal with the same `simp` set and
then uses `k`. Here `Complex.add_re : (z + w).re = z.re + w.re` and `Complex.one_re : (1 : ℂ).re = 1` do the work.
Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `k : (z + w).re = Complex.re 1 ⊢ z.re + w.re = 1` | no goals |

---

## Part 2 · `sphere_iff` (milestone)

Statement: `|r|² = 1 ↔ normSq ρ₀₁ = Re ρ₀₀ · Re ρ₁₁` (the $|r|^2 = 1 + 4(|z|^2 - ab)$ identity above). After
unfolding, both sides are polynomial in the real numbers `(ρ.m 0 1).re`, `(ρ.m 0 1).im`, `(ρ.m 0 0).re`,
`(ρ.m 1 1).re`, linked by `a + b = 1` from Part 1.

**R10 · `obtain ⟨-, -, hc⟩ := e`** changes the **context**: it destructures `e : A ∧ B ∧ C`, keeping only the
pieces you name; `-` drops a piece. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `e : A ∧ B ∧ C ⊢ G` | `hc : C ⊢ G` |

**R11 · `rw [Complex.normSq_apply]`** changes the **goal**. `Complex.normSq_apply : normSq z = z.re * z.re + z.im * z.im`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq z)` | `⊢ P (z.re * z.re + z.im * z.im)` |

**R12 · `simp only [f]`** changes the **goal**: unfold a definition (here `blochX`, `blochY`, `blochZ`).
Placeholders: `def twice (x : ℝ) : ℝ := 2 * x`.

| Before | After |
|---|---|
| `⊢ P (twice x)` | `⊢ P (2 * x)` |

**R13 · `constructor` on `↔`** changes the **goal list**: `A ↔ B` becomes the two implications. Follow with
`<;> intro h` to introduce the hypothesis in both. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R14 · `nlinarith`** **closes** polynomial goals over `ℝ`: it is `linarith` after adding products of pairs of
hypotheses (and squares). Here it needs `hs : a + b = 1` times itself. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : (a - b) ^ 2 = 1 ⊢ a * b = 0` | no goals |

---

## Part 3 · `pure_on_sphere` (milestone)

Statement: `MState.pure ψ` lies on the sphere. Use `sphere_iff` to turn the goal into
`normSq (ψ₀ conj ψ₁) = Re(ψ₀ conj ψ₀) · Re(ψ₁ conj ψ₁)` and evaluate both sides.

**R15 · `rw [e]` with `e : A ↔ B`** changes the **goal**: `rw` also rewrites with an `↔`, replacing the
proposition `A` by `B`. A milestone `sphere_iff ρ : … ↔ …` is used this way. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A` | `⊢ B` |

**R16 · `MState.pure_apply`** changes the **goal**: `(MState.pure ψ).m i j = ψ i * conj (ψ j)`.
Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ψ : Ket d) (i j : d)`.

| Before | After |
|---|---|
| `⊢ P ((MState.pure ψ).m i j)` | `⊢ P (ψ i * (starRingEnd ℂ) (ψ j))` |

**R17 · `Complex.normSq_mul`** changes the **goal**: `normSq (z * w) = normSq z * normSq w`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq (z * w))` | `⊢ P (Complex.normSq z * Complex.normSq w)` |

**R18 · `Complex.normSq_conj`** changes the **goal**: `normSq (conj z) = normSq z`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq ((starRingEnd ℂ) z))` | `⊢ P (Complex.normSq z)` |

**R19 · `Complex.mul_conj`** changes the **goal**: `z * conj z = ↑(normSq z)`, a real number cast into `ℂ`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * (starRingEnd ℂ) z)` | `⊢ P ↑(Complex.normSq z)` |

**R20 · `Complex.ofReal_re`** changes the **goal**: `(↑r).re = r`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑r).re` | `⊢ P r` |

All of R16–R20 are rewrites, so one `simp only [R16, R17, R18, R19, R20]` closes the goal (both sides become
`normSq (ψ 0) * normSq (ψ 1)`).

---

## Part 4 · `exists_ket` (milestone)

Statement: given reals `a, b` with `0 ≤ a`, `a + b = 1` and `z : ℂ` with `normSq z = a * b`, there is a ket with
`ψ₀ conj ψ₀ = a`, `ψ₀ conj ψ₁ = z`, `ψ₁ conj ψ₁ = b`. Split on `a = 0` (take `|1⟩`) or `a > 0` (take
`(√a, conj z / √a)`).

### The case split and the `a = 0` case

**R21 · `rcases ha.eq_or_lt with rfl | ha`** changes the **goal list and the context**.
`LE.le.eq_or_lt : a ≤ b → a = b ∨ a < b`. The pattern `rfl` substitutes `a := 0` in the first case; the
second case gets `ha : 0 < a` (the old `ha` becomes `ha✝`). Placeholders: `(a : ℝ) (ha : 0 ≤ a)`.

| Before | After |
|---|---|
| `ha : 0 ≤ a ⊢ P a` | `ha : 0 ≤ 0 ⊢ P 0`, `ha : 0 < a ⊢ P a` |

**R22 · `simp at hz`** changes the **context**: `zero_mul` gives `normSq z = 0`, and `map_eq_zero`
(`normSq z = 0 ↔ z = 0`) finishes. `have hz0 : z = 0 := by simpa using hz` does the same as a new fact.
Placeholders: `(z : ℂ) (b : ℝ)`.

| Before | After |
|---|---|
| `hz : Complex.normSq z = 0 * b ⊢ G` | `hz : z = 0 ⊢ G` |

**R23 · `Ket.basis i`, `simp [Ket.basis, Ket.apply]`** changes the **goal**. `Ket.basis i` is $\lvert i\rangle$,
with amplitude `if i = j then 1 else 0` at `j`; `Ket.apply : ψ i = ψ.vec i` lets `simp` see that function.
Placeholders: `(P : ℂ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((Ket.basis 1) 0)` | `⊢ P 0` |

### Facts about `√a` for `a > 0`

**R24 · `exact_mod_cast e`** **closes** a goal that is `e` with casts `ℝ → ℂ` added or removed (it normalises
casts in both, then compares). Placeholders: `(x : ℝ) (e : x ≠ 0)`.

| Before | After |
|---|---|
| `e : x ≠ 0 ⊢ ↑x ≠ 0` | no goals |

**R25 · `(Real.sqrt_pos.mpr hx).ne'`** is a term; with `have k := …` it changes the **context**. `Real.sqrt_pos : 0 < √x ↔ 0 < x`; `.mpr` goes right to left;
`LT.lt.ne' : a < b → b ≠ a`. Placeholders: `(x : ℝ) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ G` | `k : √x ≠ 0 ⊢ G` |

**R26 · `Real.mul_self_sqrt`** with `have` changes the **context**: `Real.mul_self_sqrt : 0 ≤ x → √x * √x = x`.
Cast into `ℂ` with R24: `have k : (√x : ℂ) * (√x : ℂ) = x := by exact_mod_cast Real.mul_self_sqrt hx`.
When you only have `ha : 0 < a`, pass `ha.le : 0 ≤ a` (`LT.lt.le : a < b → a ≤ b`). Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ G` | `k : ↑√x * ↑√x = ↑x ⊢ G` |

`field_simp` (R34) needs `(√a : ℂ) ≠ 0` and `(a : ℂ) ≠ 0` as hypotheses **over ℂ**: prove them with R24 + R25.

### Building the ket

**R27 · `refine ⟨![a, b], ?_⟩`** (or the term `⟨![a, b], by …⟩`) changes the **goal**: to build a
`Ket (Fin 2)` you give the amplitudes and then prove the normalization. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ Ket (Fin 2)` | `⊢ ∑ x, ‖![a, b] x‖ ^ 2 = 1` |

**R28 · `let ψ : Ket (Fin 2) := …`** changes the **context**: `ψ` is added *with its value* (unlike `have`,
which forgets it). `simp [ψ]` / `simp only [ψ]` unfolds it later. Placeholders: any value of type `Ket (Fin 2)`.

| Before | After |
|---|---|
| `⊢ P (Ket.basis 0)` | `ψ : Ket (Fin 2) := Ket.basis 0 ⊢ P (Ket.basis 0)` |

**R29 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)` (`β` has `+` and `0`; `ℝ`, `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R30 · `Matrix.cons_val_zero`, `Matrix.cons_val_one`** change the **goal**: entries of `![a, b]`.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (![a, b] 0) (![a, b] 1)` | `⊢ P a b` |

**R31 · `rw [← Complex.normSq_eq_norm_sq]`** changes the **goal**. The lemma is `normSq z = ‖z‖ ^ 2`;
right to left it turns the normalization's `‖·‖ ^ 2` into `normSq`, where R32, R33 apply. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (‖z‖ ^ 2)` | `⊢ P (Complex.normSq z)` |

**R32 · `Complex.normSq_div`** changes the **goal**: `normSq (z / w) = normSq z / normSq w`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq (z / w))` | `⊢ P (Complex.normSq z / Complex.normSq w)` |

**R33 · `Complex.normSq_ofReal`** changes the **goal**: `normSq ↑r = r * r`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq ↑r)` | `⊢ P (r * r)` |

**R34 · `field_simp`** changes the **goal**: it clears denominators, cancelling or cross-multiplying, using
hypotheses `ha : a ≠ 0` from the context (it fails to cancel without them). Over `ℝ` a hypothesis `0 < a` also
works; for a cast such as `↑√a` in `ℂ` you need `↑√a ≠ 0` itself (Traps). Placeholders: `(a c x : ℝ) (ha : a ≠ 0)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ c + a * x / a = 1` | `ha : a ≠ 0 ⊢ c + x = 1` |

### The three amplitude equations

**R35 · `map_div₀`** changes the **goal**: `conj (z / w) = conj z / conj w` (`conj` is a field map, and
`map_div₀ f a b : f (a / b) = f a / f b` holds for any such `f`). Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (z / w))` | `⊢ P ((starRingEnd ℂ) z / (starRingEnd ℂ) w)` |

**R36 · `Complex.conj_conj`** changes the **goal**: `conj (conj z) = z`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ((starRingEnd ℂ) z))` | `⊢ P z` |

**R37 · `Complex.conj_ofReal`** changes the **goal**: `conj ↑r = ↑r`. Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r)` | `⊢ P ↑r` |

**R38 · `div_mul_div_comm`** changes the **goal**: `a / b * (c / d) = a * c / (b * d)`. Placeholders:
`{α : Type} [DivisionCommMonoid α] (a b c d : α)` (commutative `*` with `/`; `ℂ`, `ℝ` qualify).

| Before | After |
|---|---|
| `⊢ P (a / b * (c / d))` | `⊢ P (a * c / (b * d))` |

**R39 · `rw [mul_comm a]`** changes the **goal**: `mul_comm a b : a * b = b * a`. Naming the first factor `a`
makes `rw` turn only products that start with `a`. Placeholders: `{α : Type} [CommMagma α] (a b c : α)`.

| Before | After |
|---|---|
| `⊢ P (a * b) (c * b)` | `⊢ P (b * a) (c * b)` |

**R40 · `push_cast`** changes the **goal**: casts move inward, `↑(x * y)` → `↑x * ↑y`, so that a cast fact
such as `hsq : ↑√a * ↑√a = ↑a` or a `≠ 0` fact over `ℂ` can match. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P ↑(x * y)` | `⊢ P (↑x * ↑y)` |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a concrete ket `(3/5, 4/5)`.** R27 leaves the normalization; R29 + R30, then R31 twice, then `simp`
(which expands `normSq` of a numeral), then `norm_num`:

```lean-goal
⊢ ∑ x, ‖![3 / 5, 4 / 5] x‖ ^ 2 = 1
⊢ ‖3 / 5‖ ^ 2 + ‖4 / 5‖ ^ 2 = 1
⊢ Complex.normSq (3 / 5) + Complex.normSq (4 / 5) = 1
⊢ 3 * 3 / (5 * 5) + 4 * 4 / (5 * 5) = 1
```

**W2: `normSq (w / √c)`.** R32 then R33 leave a `√c * √c`, which R26 removes:

```lean-goal
⊢ Complex.normSq (w / ↑√c) = Complex.normSq w / c
⊢ Complex.normSq w / (√c * √c) = Complex.normSq w / c
```

**W3: conjugating a quotient by a real square root.** `rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]`
(R35, R36, R37) closes `⊢ (starRingEnd ℂ) ((starRingEnd ℂ) w / ↑√c) = w / ↑√c`.

**W4: cancel `√c` in `ℂ`.** First `hs : ↑√c ≠ 0` by R24 + R25, then `field_simp` closes:

```lean-goal
⊢ 3 * w / ↑√c * ↑√c = 3 * w
```

---

## Part 5 · `bloch_sphere`

Statement: `(∃ ψ, ρ = MState.pure ψ) ↔ |r|² = 1`. `→` is `pure_on_sphere`. `←`: turn `|r|² = 1` into
`normSq z = a b` (`sphere_iff`), get the Part 1 facts, derive `0 ≤ a`, take the ket from `exists_ket`, and
compare matrices entry by entry.

**R41 · `rintro ⟨x, rfl⟩`** changes the **goal and the context**: it introduces the `∃` and, because the
equation is `a = f x` with a variable `a`, substitutes `a := f x` everywhere. Placeholders:
`{α : Type} (f : α → ℕ) (a : ℕ) (G : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ (∃ x, a = f x) → G a` | `x : α ⊢ G (f x)` |

**R42 · `rw [e] at h` with `e : A ↔ B`** changes the **context**: `h : A` becomes `h : B`. Placeholders:
`(A B : Prop)`.

| Before | After |
|---|---|
| `h : A ⊢ G` | `h : B ⊢ G` |

**R43 · `nlinarith [Complex.normSq_nonneg z]`** **closes** the goal after adding the listed facts to the
hypotheses. `Complex.normSq_nonneg z : 0 ≤ normSq z`. With `a + b = 1` and `normSq z = a * b` it gives `0 ≤ a`
(if `a < 0` then `b > 1` and `a b < 0`). Placeholders: `(a : ℝ) (z : ℂ)`.

| Before | After |
|---|---|
| `h : Complex.normSq z = a * a * a ⊢ 0 ≤ a * a * a` | no goals |

**R44 · `simp only [Fin.forall_fin_two]`** changes the **goal**: `Fin.forall_fin_two : (∀ i : Fin 2, p i) ↔ p 0 ∧ p 1`,
used twice. State a fact `key : ∀ i j, ρ.m i j = …` this way, then use it inside `ext i j` without `fin_cases`.
Placeholders: `(P : Fin 2 → Fin 2 → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (i j : Fin 2), P i j` | `⊢ (P 0 0 ∧ P 0 1) ∧ P 1 0 ∧ P 1 1` |

**R45 · `apply Complex.ext`** changes the **goal list**: `Complex.ext : z.re = w.re → z.im = w.im → z = w`. As a
term, `Complex.ext rfl h` proves `z = ↑z.re` from `h : z.im = 0` (`(↑r).im` is `0` by definition). Placeholders:
`(z : ℂ) (r : ℝ)`.

| Before | After |
|---|---|
| `⊢ z = ↑r` | `⊢ z.re = (↑r).re`, `⊢ z.im = (↑r).im` |

**R46 · `map_mul`** changes the **goal**: `conj (z * w) = conj z * conj w`. `simp` applies it by itself;
`simp [mul_comm]` then closes `conj (ψ₀ conj ψ₁) = ψ₁ conj ψ₀` (R36 and commutativity). Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (z * w))` | `⊢ P ((starRingEnd ℂ) z * (starRingEnd ℂ) w)` |

**R47 · `apply MState.ext_m`** changes the **goal**: `MState.ext_m : ρ₁.m = ρ₂.m → ρ₁ = ρ₂`. Follow with `ext i j`
(TACTIC_STATES) for entries. Placeholders: `{d : Type} [Fintype d] [DecidableEq d] (ρ₁ ρ₂ : MState d)`.

| Before | After |
|---|---|
| `⊢ ρ₁ = ρ₂` | `⊢ ρ₁.m = ρ₂.m` |

---

## Traps

- `fin_cases` leaves indices as `(fun i => i) ⟨0, ⋯⟩`, which `rw` with a hypothesis about `ψ 0` or `ρ.m 0 1`
  cannot see. Prove a `∀ i j` fact with `Fin.forall_fin_two` (R44) and rewrite with it instead.
- `0 ≤ a` is not given in `bloch_sphere`: derive it (R43) before calling `exists_ket`.
- `field_simp` only uses `≠ 0` facts (over `ℝ` also `0 < ·`) that are already in the context and stated over the right type. Over `ℂ`,
  `(√a : ℂ) ≠ 0` must be a hypothesis; a real `√a ≠ 0` does not count (R24, R25).
- `Real.sqrt` of a negative number is `0`, so `√a * √a = a` needs `0 ≤ a` (R26); after the split you have
  `0 < a`, use `ha.le`.
- `have ψ : Ket (Fin 2) := …` forgets the value and you cannot compute `ψ 0`; use `let` (R28).
- `Ket.normalized'` is stated with `‖·‖ ^ 2`; `Ket.normalized` uses `normSq`. Convert with R31.
- Hermiticity is `star (A j i) = A i j`: indices are swapped, so `hH.apply 1 0` is about `ρ.m 0 1` on the left.
- `ring` and `linarith` do not know `I * I = -1` or `√a * √a = a`; supply such facts as hypotheses.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `ρ` Hermitian / trace 1 | `have hH := ρ.Hermitian`, `have htr := ρ.tr'` | R1, R2 |
| trace of a 2×2 | `rw [Matrix.trace_fin_two] at htr` | R3 |
| one Hermiticity equation | `hH.apply i j : star (A j i) = A i j` | R4 |
| im / re of an equation | `congrArg Complex.im e`, then `simp at k` | R6, R7 |
| linear arithmetic | `linarith` | R8 |
| simplify a fact into the goal | `simpa using k` | R9 |
| keep one part of `A ∧ B ∧ C` | `obtain ⟨-, -, hc⟩ := e` | R10 |
| `normSq z` → re/im | `rw [Complex.normSq_apply]` | R11 |
| unfold `blochX` | `simp only [blochX, blochY, blochZ]` | R12 |
| prove `↔` | `constructor <;> intro h` | R13 |
| polynomial arithmetic | `nlinarith [facts]` | R14, R43 |
| use an `↔` milestone | `rw [sphere_iff]`, `rw [sphere_iff] at h` | R15, R42 |
| entries of `pure ψ` | `MState.pure_apply` | R16 |
| `normSq` algebra | `Complex.normSq_mul`, `_conj`, `_div`, `_ofReal` | R17, R18, R32, R33 |
| `z * conj z` | `Complex.mul_conj` | R19 |
| `(↑r).re` | `Complex.ofReal_re` | R20 |
| split `0 ≤ a` | `rcases ha.eq_or_lt with rfl \| ha` | R21 |
| `normSq z = 0 → z = 0` | `simpa using hz` | R22 |
| basis ket `\|i⟩` | `Ket.basis i`, `simp [Ket.basis, Ket.apply]` | R23 |
| move a fact between ℝ and ℂ | `exact_mod_cast` | R24 |
| `√x ≠ 0`, `√x * √x = x` | `(Real.sqrt_pos.mpr hx).ne'`, `Real.mul_self_sqrt hx.le` | R25, R26 |
| build a ket | `let ψ : Ket (Fin 2) := ⟨![u, v], by …⟩` | R27, R28 |
| normalization of `![u, v]` | `simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ← Complex.normSq_eq_norm_sq, …]` | R29–R33 |
| clear denominators | `field_simp` (with `≠ 0` facts over ℂ) | R34 |
| `conj` of a quotient / of `conj` / of a real | `map_div₀`, `Complex.conj_conj`, `Complex.conj_ofReal` | R35–R37 |
| regroup quotients / products | `div_mul_div_comm`, `mul_comm a` | R38, R39 |
| casts inward | `push_cast` | R40 |
| `→` of an `∃ … = …` | `rintro ⟨ψ, rfl⟩` | R41 |
| `∀ i j : Fin 2` fact | `simp only [Fin.forall_fin_two]` | R44 |
| `z = ↑r` | `Complex.ext rfl h` | R45 |
| `conj (z * w)` | `map_mul` (inside `simp`) | R46 |
| equal states | `MState.ext_m`, then `ext i j` | R47 |
