# H100 · The tight-binding spectrum is the band: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `rw`, `simp`, `have`,
`obtain`/`rcases` patterns, anonymous constructors `⟨_, _⟩`, `fun x => …`, `·` bullets. **New here:**
Mathlib's complex inner product spaces (`⟪x, y⟫_ℂ`, the conjugate `starRingEnd ℂ`), finite sums `∑`,
linear algebra (`Submodule.span`, `LinearIndependent`, `Module.finrank`, bases), three notions of
cardinality (`Set.ncard`, `Nat.card`, `Fintype.card`), the tactics `by_contra`, `push Not`,
`exact_mod_cast`, `positivity`, `induction … using`, `haveI`, and physlib's `TightBindingChain` with
its Hilbert space, Hamiltonian, Bloch states and band energies.

**The physics, in symbols.** A ring of `N ≥ 1` sites `n ∈ Fin N = {0, …, N-1}` with spacing `a > 0`.
The Hilbert space is `ℂ^N` with orthonormal site basis `|n⟩`. The Hamiltonian (periodic, `n + 1` taken
mod `N`) is
$H = E_0 \sum_n |n⟩⟨n| - t \sum_n (|n⟩⟨n+1| + |n+1⟩⟨n|)$, with on-site energy $E_0$ and hopping $t$
(real). The allowed wavenumbers are
$K = \{\tfrac{2\pi}{aN}(n - \lfloor N/2 \rfloor) : n \in \mathrm{Fin}\,N\}$, $|K| = N$. For $k \in K$
the Bloch state is $\psi_k = \sum_n e^{i k n a}|n⟩$, and $H\psi_k = E(k)\psi_k$ with the real band energy
$E(k) = E_0 - 2t\cos(ka)$. The claim: if $H\psi = E\psi$ with $\psi \ne 0$ ($E \in ℂ$), then $E = E(k)$
for some $k \in K$. Proof: suppose not. Since $H$ is Hermitian and $E(k)$ is real,
$E(k)⟨\psi_k,\psi⟩ = ⟨H\psi_k,\psi⟩ = ⟨\psi_k,H\psi⟩ = E⟨\psi_k,\psi⟩$, so $⟨\psi_k,\psi⟩ = 0$ for every $k$.
The $\psi_k$ are pairwise orthogonal with $⟨\psi_k,\psi_k⟩ = N \ne 0$, so they are linearly
independent; there are $N = \dim ℂ^N$ of them, so they span. By linearity $⟨\phi,\psi⟩ = 0$ for every
$\phi$ in the span, in particular $⟨\psi,\psi⟩ = 0$, so $\psi = 0$: contradiction.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℂ → Prop`, `P : ℕ → Prop`, …). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves
  alone.
- Lemmas that produce a fact are shown as `have h := lemma args`, so the context gains `h` and you see its
  type. In the exercise you often pass them as arguments instead (`(mul_eq_zero.mp h').resolve_left …`).
- `{E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]` is "any complex inner product space":
  a complex vector space with a norm and an inner product `⟪x, y⟫_ℂ`. `T.HilbertSpace` is one, and every
  inner-product lemma below applies to it with `E := T.HilbertSpace`.
- `[Fintype ι]` says the type `ι` is finite (so `Fintype.card ι` is defined). `Fin n` is one.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `T : TightBindingChain` | physlib's chain: fields `T.N : ℕ` (sites, with an instance `NeZero T.N`, i.e. `T.N ≠ 0`), `T.a : ℝ` (spacing, `T.a_pos : 0 < T.a`), `T.E0 : ℝ`, `T.t : ℝ` |
| `T.HilbertSpace` | `ℂ^N`: physlib's `FiniteHilbertSpace (Fin T.N)`, a complex inner product space of dimension `N` |
| `localizedState n` | the site state `\|n⟩` (physlib notation); `localizedState` is an `OrthonormalBasis (Fin T.N) ℂ T.HilbertSpace` (R36) |
| `⟪x, y⟫_ℂ` | the inner product, conjugate-linear in `x`, linear in `y` (R4, R5). Physlib writes `⟨m\|n⟩` for `⟪\|m⟩, \|n⟩⟫_ℂ` |
| `(starRingEnd ℂ) z` | complex conjugation `conj z` (a ring homomorphism `ℂ → ℂ`, hence `map_mul`) |
| `T.QuantaWaveNumber` | the set `K ⊆ ℝ` of allowed wavenumbers, a `Set ℝ` (R15) |
| `k : ↑T.QuantaWaveNumber` | `k` is an element of the subtype `↑K = {x : ℝ // x ∈ K}`: a real number with a proof it lies in `K` |
| `↑x` | a cast (coercion) into a bigger number type: `↑T.a : ℂ` is the real `T.a` as a complex number, `↑T.N` is the natural number `T.N` in `ℝ` or `ℂ`, `↑(T.N / 2)` divides in `ℕ` first (rounding down) and then casts. The infoview hides which target type; hover to see it |
| `↑↑k`, `↑↑n` | double casts: `k : ↑K → ℝ → ℂ`, and `n : Fin N → ℕ → ℂ` (or `→ ℝ`) |
| `T.energyEigenstate k` | the Bloch state `ψ_k = ∑ n, exp (I k n a) • \|n⟩` (R1) |
| `T.energyEigenvalue k` | the band energy `E(k) = T.E0 - 2 * T.t * Real.cos (↑k * T.a)`, a REAL number; `↑(T.energyEigenvalue k)` is it cast into `ℂ` |
| `T.hamiltonian` | `H`, a `ℂ`-linear map `T.HilbertSpace →ₗ[ℂ] T.HilbertSpace`; `T.hamiltonian ψ` is `H ψ` |
| `E • ψ` | scalar times vector. `r • v` with `r : ℝ` is a real scalar (R41) |
| `Complex.I`, `Real.pi` | `i` and `π` |
| `if m = n then 1 else 0` | the Kronecker delta `δ_{mn}` |
| `∑ i, f i`, `∑ i ∈ s, f i` | sum over all `i` of a finite type, sum over a finite set `s : Finset ι`; lemmas use the second form with `s = Finset.univ` |
| `n • c` (`n : ℕ`) | `c + ⋯ + c` (`n` times); `Finset.univ.card` is the number of elements of the type |
| `Set.range f` | the image `{f i : i}`; `x ∈ Set.range f` unfolds to `∃ i, f i = x` |
| `s.ncard` | `Set.ncard s : ℕ`, the number of elements of `s : Set α`; `0` when `s` is infinite |
| `Nat.card α`, `Fintype.card α` | number of elements of a type; `Fintype.card` needs `[Fintype α]`, `Nat.card` does not (`0` if infinite) |
| `s.Finite` | `Set.Finite s`, a `Prop`; it gives an instance `Fintype ↑s` by R28 |
| `Function.Injective f` | `∀ a b, f a = f b → a = b` (R20) |
| `Pairwise r` | `∀ i j, i ≠ j → r i j` |
| `LinearIndependent ℂ v` | no nontrivial finite `ℂ`-linear combination of the `v i` is `0`. Also printed `LinearIndependent (ι := ↑T.QuantaWaveNumber) ℂ T.energyEigenstate`, naming the index type |
| `Submodule.span ℂ S` | all finite `ℂ`-linear combinations of vectors in `S`, a subspace (`Submodule`) |
| `⊤` | the whole space, as a `Submodule` (the top element) |
| `Module.finrank ℂ E` | the dimension of `E` over `ℂ` (a natural number) |
| `Module.Basis ι ℂ E` | a basis of `E` indexed by `ι` |
| `x✝`, `a✝¹`, `hx✝` | inaccessible names Lean made up; name them with `with` or `case` (R49) |
| `case lin_ind`, `case card_eq` | the goals `apply` leaves, named after the lemma's hypotheses (R29) |
| `case mem`, `zero`, `add`, `smul` | the four goals of span induction (R49) |

---

## Part 1 · `bloch_norm_sq` (milestone)

Statement: `⟪ψ_k, ψ_k⟫_ℂ = ↑T.N`. Expanding both sides of the inner product gives
$\sum_n e^{ikna} \sum_m \overline{e^{ikma}}\,\delta_{mn}$; the delta collapses the inner sum, each term
is $\overline{e^{ikna}}e^{ikna} = e^{-ikna + ikna} = 1$, and there are `N` terms. Used in Part 3 to show
`ψ_k ≠ 0`. (This is M168.)

**R1 · `simp only [TightBindingChain.energyEigenstate]`** changes the **goal**: the name `ψ_k` is replaced by
its definition. `simp only` (not `rw`) because the sum has a bound variable. Placeholders:
`(T : TightBindingChain) (k : ↑T.QuantaWaveNumber)`, `P : T.HilbertSpace → Prop`.

| Before | After |
|---|---|
| `⊢ P (T.energyEigenstate k)` | `⊢ P (∑ n, Complex.exp (Complex.I * ↑↑k * ↑↑n * ↑T.a) • localizedState n)` |

**R2 · `sum_inner`** changes the **goal**. `⟪∑ i ∈ s, f i, x⟫_ℂ = ∑ i ∈ s, ⟪f i, x⟫_ℂ`.
Placeholders: `{ι E : Type}`, `E` an inner product space, `(s : Finset ι) (f : ι → E) (x : E)`.

| Before | After |
|---|---|
| `⊢ P ⟪∑ i ∈ s, f i, x⟫_ℂ` | `⊢ P (∑ i ∈ s, ⟪f i, x⟫_ℂ)` |

**R3 · `inner_sum`** changes the **goal**. `⟪x, ∑ i ∈ s, f i⟫_ℂ = ∑ i ∈ s, ⟪x, f i⟫_ℂ`. Same placeholders.

| Before | After |
|---|---|
| `⊢ P ⟪x, ∑ i ∈ s, f i⟫_ℂ` | `⊢ P (∑ i ∈ s, ⟪x, f i⟫_ℂ)` |

**R4 · `inner_smul_left`** changes the **goal**. `⟪r • x, y⟫_ℂ = conj r * ⟪x, y⟫_ℂ`: a scalar leaves the
left slot conjugated. Placeholders: `(x y : E) (r : ℂ)`. The scalar must be complex (R41).

| Before | After |
|---|---|
| `⊢ P ⟪r • x, y⟫_ℂ` | `⊢ P ((starRingEnd ℂ) r * ⟪x, y⟫_ℂ)` |

**R5 · `inner_smul_right`** changes the **goal**. `⟪x, r • y⟫_ℂ = r * ⟪x, y⟫_ℂ`. Placeholders as R4.

| Before | After |
|---|---|
| `⊢ P ⟪x, r • y⟫_ℂ` | `⊢ P (r * ⟪x, y⟫_ℂ)` |

**R6 · `localizedState_orthonormal_eq_ite`** changes the **goal**. `⟪|m⟩, |n⟩⟫_ℂ = if m = n then 1 else 0`.
Placeholders: `(T : TightBindingChain) (m n : Fin T.N)`.

| Before | After |
|---|---|
| `⊢ P ⟪localizedState m, localizedState n⟫_ℂ` | `⊢ P (if m = n then 1 else 0)` |

R1–R6 go in one `simp only [...]` (under the sums `rw` would fail). After it the goal is a double sum
over `x x_1 : Fin T.N` of `exp (I k x a) * (conj (exp (I k x_1 a)) * if x_1 = x then 1 else 0)`, equal to
`↑T.N`. W1 shows the same shape on other coefficients.

**R7 · `simp` on a Kronecker-delta sum** changes the **goal**: `∑ m, f m * if m = j then 1 else 0` becomes
`f j`. `simp` does this by itself (`mul_ite`, `mul_one`, `mul_zero`, then `Finset.sum_ite_eq'`:
`∑ x ∈ s, (if x = a then b x else 0) = if a ∈ s then b a else 0`, and `Finset.mem_univ`). Placeholders:
`(n : ℕ) (f : Fin n → ℂ) (j : Fin n)`.

| Before | After |
|---|---|
| `⊢ P (∑ m, f m * if m = j then 1 else 0)` | `⊢ P (f j)` |

**R8 · `rw [← Complex.exp_conj]`** changes the **goal**. `Complex.exp (conj z) = conj (Complex.exp z)`, used
right to left. `simp` does not do this direction by itself, so name it: `simp [← Complex.exp_conj, …]`.
Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) (Complex.exp z))` | `⊢ P (Complex.exp ((starRingEnd ℂ) z))` |

**R9 · `Complex.conj_ofReal`** changes the **goal**: `conj ↑r = ↑r` for a real `r`. Placeholders: `(r : ℝ)`.
Also used in Part 4.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) ↑r)` | `⊢ P ↑r` |

**R10 · `map_mul`, `Complex.conj_I`** change the **goal**: `conj (z * w) = conj z * conj w` (true for any ring
homomorphism) and `conj I = -I`. `simp` applies both (and `map_natCast`: `conj ↑n = ↑n`). Placeholders:
`(z : ℂ)`.

| Before | After `rw [map_mul]` | After `rw [Complex.conj_I]` |
|---|---|---|
| `⊢ P ((starRingEnd ℂ) (Complex.I * z))` | `⊢ P ((starRingEnd ℂ) Complex.I * (starRingEnd ℂ) z)` | `⊢ P (-Complex.I * (starRingEnd ℂ) z)` |

**R11 · `rw [← Complex.exp_add]`** changes the **goal**: `exp x * exp y` becomes `exp (x + y)`. Name it in the
`simp` call. Placeholders: `(x y : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.exp x * Complex.exp y)` | `⊢ P (Complex.exp (x + y))` |

**R12 · `add_neg_cancel`, `Complex.exp_zero`** change the **goal**: `a + -a = 0`, `exp 0 = 1`. `simp` applies
both. Placeholders: `(z : ℂ)`.

| Before | After `rw [add_neg_cancel]` | After `rw [Complex.exp_zero]` |
|---|---|---|
| `⊢ P (Complex.exp (z + -z))` | `⊢ P (Complex.exp 0)` | `⊢ P 1` |

**R13 · `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, `nsmul_eq_mul`** change the **goal**: a sum
of `n` ones is `↑n`. `Finset.sum_const : ∑ _x ∈ s, c = s.card • c`, `Finset.card_univ : Finset.univ.card =
Fintype.card α`, `Fintype.card_fin : Fintype.card (Fin n) = n` (R19), `nsmul_eq_mul : n • a = ↑n * a`. `simp`
applies all of them. Placeholders: `(n : ℕ)`.

| Before | `Finset.sum_const` | `Finset.card_univ` | `Fintype.card_fin` | `nsmul_eq_mul, mul_one` |
|---|---|---|---|---|
| `⊢ P (∑ _i, 1)` | `⊢ P (Finset.univ.card • 1)` | `⊢ P (Fintype.card (Fin n) • 1)` | `⊢ P (n • 1)` | `⊢ P ↑n` |

So the second step of Part 1 is a single `simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofReal]`:
it does R7, R8, R10, R9, R11, R12, R13 in that order.

---

## Part 2 · `card_wavenumbers` (milestone)

Statement: `T.QuantaWaveNumber.ncard = T.N`. Write `K` as the range of
`g n = 2π/(a N) · (n − ⌊N/2⌋)` on `Fin N`, then `|range g| = |Fin N| = N` because `g` is injective (an
affine map with nonzero slope `2π/(aN)`). Used twice in Part 3. (This is M170.)

**R14 · `ext x`** (lemma `Set.ext`) changes the **goal and the context**: two sets are equal when they have
the same members. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s = t` | `x : α ⊢ x ∈ s ↔ x ∈ t` |

**R15 · `simp only [TightBindingChain.QuantaWaveNumber]`** changes the **goal**: `K` is replaced by its
set-builder definition. Placeholders: `(T : TightBindingChain) (x : ℝ)`, `P : Prop → Prop`. Before and after:

```lean-goal
⊢ P (x ∈ T.QuantaWaveNumber)
⊢ P (x ∈ {x | ∃ n, 2 * Real.pi / (T.a * ↑T.N) * (↑↑n - ↑(T.N / 2)) = x})
```

`↑(T.N / 2)` is the natural-number quotient `⌊N/2⌋` cast into `ℝ`.

**R16 · `Set.mem_setOf_eq`, `Set.mem_range`** let `simp` **close** an `↔` whose sides unfold to the same `∃`:
`x ∈ {y | p y} ↔ p x` and `x ∈ Set.range f ↔ ∃ n, f n = x`. Placeholders: `{α β : Type} (f : α → β) (x : β)`.
Closed by `simp`:

```lean-goal
⊢ x ∈ {y | ∃ n, f n = y} ↔ x ∈ Set.range f
```

In the exercise, R14 then one `simp [TightBindingChain.QuantaWaveNumber]` (R15 and R16 together) proves
`hset : T.QuantaWaveNumber = Set.range (fun n : Fin T.N => …)`.

**R17 · `rw [Set.ncard_range_of_injective]`** changes the **goal list**.
`Function.Injective f → (Set.range f).ncard = Nat.card α`: the goal is rewritten and the side goal
`Function.Injective f` is added at the end. Placeholders: `{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ P (Set.range f).ncard` | `⊢ P (Nat.card α)`, `⊢ Function.Injective f` |

**R18 · `Nat.card_eq_fintype_card`** changes the **goal**. `Nat.card α = Fintype.card α` when `[Fintype α]`.
Right to left (`← Nat.card_eq_fintype_card`) in Part 3. Placeholders: `{α : Type} [Fintype α]`.

| Before | After |
|---|---|
| `⊢ P (Nat.card α)` | `⊢ P (Fintype.card α)` |

**R19 · `Fintype.card_fin`** changes the **goal**. `Fintype.card (Fin n) = n`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin n))` | `⊢ P n` |

**R20 · `intro m n h`** on `Function.Injective f` changes the **goal and the context**: `Function.Injective f`
is a definition that unfolds to `∀ a b, f a = f b → a = b`, and `intro` sees through it. Placeholders:
`{α β : Type} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Function.Injective f` | `m n : α, h : f m = f n ⊢ m = n` |

When `f` is a `fun`, `h` shows unreduced: `h : (fun n => …) m = (fun n => …) n` (W2). Lemmas still apply to it,
since the two forms are equal by definition; `simp only at h` beta-reduces it if you want to read it.

**R21 · `T.a_pos`, `NeZero.pos T.N`** change the **context**: `0 < T.a` is a field of the structure, and
`NeZero.pos n : 0 < n` holds whenever there is an instance `[NeZero n]`, which `T.N` has. Placeholders:
`(T : TightBindingChain)`.

| Before | After `have ha := T.a_pos` | After `have hN := NeZero.pos T.N` |
|---|---|---|
| `⊢ G` | `ha : 0 < T.a ⊢ G` | `hN : 0 < T.N ⊢ G` |

**R22 · `exact_mod_cast h`** **closes** a goal that is `h` up to casts `↑` (`ℕ → ℝ`, `ℕ → ℂ`, `Fin n → ℕ`, …).
It normalises the casts in both, then compares. Placeholders: `(n : ℕ) (h : 0 < n)`.

| Before | After |
|---|---|
| `h : 0 < n ⊢ 0 < ↑n` | no goals |

**R23 · `positivity`** **closes** `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built by `*`, `/`, `^`, `+` from
numerals, `Real.pi`, and variables with a `0 < x` hypothesis in the context. So first put `0 < T.a` and
`(0 : ℝ) < ↑T.N` in the context (R21, R22). Placeholders: `(a x : ℝ) (ha : 0 < a) (hx : 0 < x)`.

| Before | After |
|---|---|
| `⊢ 3 * Real.pi / (a * x ^ 2) ≠ 0` | no goals |

**R24 · `mul_left_cancel₀`** changes the **context**. `a ≠ 0 → a * b = a * c → b = c`.
Placeholders: `(a b c : ℝ) (ha : a ≠ 0) (h : a * b = a * c)` (any type without zero divisors).

| Before | After `have h' := mul_left_cancel₀ ha h` |
|---|---|
| `⊢ G` | `h' : b = c ⊢ G` |

**R25 · `sub_left_inj`** changes the **context**. `b - a = c - a ↔ b = c`; `.mp` goes left to right.
Placeholders: `(a b c : ℝ) (h : b - a = c - a)`.

| Before | After `have h' := sub_left_inj.mp h` |
|---|---|
| `⊢ G` | `h' : b = c ⊢ G` |

**R26 · `Fin.ext`** changes the **goal**: two elements of `Fin N` are equal when their values in `ℕ` are.
`Fin.ext : ↑m = ↑n → m = n`. The fact you have is about `↑↑m : ℝ`; R22 removes the outer cast.
Placeholders: `(N : ℕ) (m n : Fin N)`.

| Before | After `apply Fin.ext` |
|---|---|
| `h : ↑↑m = ↑↑n ⊢ m = n` | `⊢ ↑m = ↑n` |

In the exercise: `exact Fin.ext (by exact_mod_cast sub_left_inj.mp (mul_left_cancel₀ hc h))`.

---

## Part 3 · `span_top` (milestone)

Statement: `Submodule.span ℂ (Set.range T.energyEigenstate) = ⊤`. Uses Parts 1 and 2. The Bloch states are
nonzero (Part 1: `⟪ψ_k, ψ_k⟫ = N ≠ 0`) and pairwise orthogonal (physlib), so linearly independent;
there are `|K| = N` of them (Part 2) and `dim = N` (the site basis has `N` vectors).

**R27 · `Set.finite_of_ncard_pos`** changes the **context**. `0 < s.ncard → s.Finite` (an infinite set has
`ncard = 0`). Get `0 < K.ncard` by `rw [card_wavenumbers]` and R21. Placeholders: `{α : Type} (s : Set α)`.

| Before | After `have hfin := Set.finite_of_ncard_pos hs` |
|---|---|
| `hs : 0 < s.ncard ⊢ G` | `hfin : s.Finite ⊢ G` |

**R28 · `haveI : Fintype s := hfin.fintype`** changes the **context**: it adds an *instance* (a value Lean
finds by itself for `[Fintype ι]` brackets). R29 needs `Fintype ↑K` to talk about `Fintype.card ↑K`.
`Set.Finite.fintype : s.Finite → Fintype ↑s`. Placeholders: `{α : Type} (s : Set α) (hfin : s.Finite)`.

| Before | After |
|---|---|
| `hfin : s.Finite ⊢ ∃ n, P n` | `this : Fintype ↑s ⊢ ∃ n, P n` |

**R29 · `apply LinearIndependent.span_eq_top_of_card_eq_finrank'`** changes the **goal list**. The lemma: for a
finite family `b : ι → E` in a finite-dimensional space, `LinearIndependent ℂ b → Fintype.card ι =
Module.finrank ℂ E → Submodule.span ℂ (Set.range b) = ⊤`. Placeholders: `{ι E : Type} [Fintype ι]`, `E` an inner
product space with `[FiniteDimensional ℂ E]` (`T.HilbertSpace` has it), `(b : ι → E)`. Use `·` bullets after.

| Before | After |
|---|---|
| `⊢ Submodule.span ℂ (Set.range b) = ⊤` | `⊢ LinearIndependent ℂ b`, `⊢ Fintype.card ι = Module.finrank ℂ E` |

**R30 · `apply linearIndependent_of_ne_zero_of_inner_eq_zero _ hpair`** changes the **goal**. The lemma:
`(∀ i, v i ≠ 0) → (Pairwise fun i j => ⟪v i, v j⟫_ℂ = 0) → LinearIndependent ℂ v`. Giving `_` for the first
argument and `hpair` for the second leaves the first as the goal. Placeholders: `{ι E : Type} (v : ι → E)`.

| Before | After |
|---|---|
| `⊢ LinearIndependent ℂ v` | `⊢ ∀ (i : ι), v i ≠ 0` |

**R31 · `TightBindingChain.energyEigenstate_orthogonal`** is the fact that Bloch states with different `k` are
orthogonal; it **closes** a goal of that form. In the exercise pass `T.energyEigenstate_orthogonal` directly
as `hpair` in R30. Placeholders: `(T : TightBindingChain)`.

| Before | After `exact T.energyEigenstate_orthogonal` |
|---|---|
| `⊢ Pairwise fun k₁ k₂ => ⟪T.energyEigenstate k₁, T.energyEigenstate k₂⟫_ℂ = 0` | no goals |

**R32 · `intro hk`** on a `≠` goal changes the **goal and the context**: `a ≠ b` is `a = b → False`. For
`∀ i, v i ≠ 0` write `intro k hk`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `hk : a = b ⊢ False` |

**R33 · `inner_zero_left`** changes the **goal** (or, with `at h`, the **context**). `⟪0, x⟫_ℂ = 0`. In the
exercise: with `h := bloch_norm_sq T k : ⟪ψ_k, ψ_k⟫_ℂ = ↑T.N` and `hk : ψ_k = 0`, `rw [hk, inner_zero_left] at h`
first rewrites both copies of `ψ_k` to `0`, then turns `h` into `0 = ↑T.N`. Placeholders: `(x : E)`.

| Before | After |
|---|---|
| `⊢ P ⟪0, x⟫_ℂ` | `⊢ P 0` |

**R34 · `NeZero.ne n`** gives `n ≠ 0` from the instance `[NeZero n]`; cast it with R22. Changes the **context**.
Placeholders: `(T : TightBindingChain)`.

| Before | After `have hN : (T.N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne T.N` |
|---|---|
| `⊢ G` | `hN : ↑T.N ≠ 0 ⊢ G` |

**R35 · `exact hne h.symm`** **closes** `False`: `hne : a ≠ b` is a function from `a = b` to `False`, and
`h.symm` flips `h : b = a`. Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `hne : a ≠ b, h : b = a ⊢ False` | no goals |

**R36 · `(localizedState (T := T)).toBasis`** is a term, the site basis as a `Module.Basis`. `localizedState`
is an `OrthonormalBasis (Fin T.N) ℂ T.HilbertSpace`, and `.toBasis` forgets the orthonormality. `T` is an
implicit argument that nothing in `localizedState` alone determines, so name it: `(T := T)`. Changes the
**context** in the guide. Placeholders: `(T : TightBindingChain)`.

| Before | After `have b := (localizedState (T := T)).toBasis` |
|---|---|
| `⊢ G` | `b : Module.Basis (Fin T.N) ℂ T.HilbertSpace ⊢ G` |

**R37 · `rw [Module.finrank_eq_card_basis b]`** changes the **goal**: the dimension is the number of basis
vectors, `Module.finrank ℂ E = Fintype.card ι`. Give `b` explicitly (Lean cannot guess a basis).
Placeholders: `{ι E : Type} [Fintype ι] (b : Module.Basis ι ℂ E)`.

| Before | After |
|---|---|
| `⊢ P (Module.finrank ℂ E)` | `⊢ P (Fintype.card ι)` |

**R38 · `Nat.card_coe_set_eq`** changes the **goal**. `Nat.card ↑s = s.ncard`. Placeholders:
`{α : Type} (s : Set α)`.

| Before | After |
|---|---|
| `⊢ P (Nat.card ↑s)` | `⊢ P s.ncard` |

The `card_eq` goal `Fintype.card ↑K = Module.finrank ℂ T.HilbertSpace` is one `rw`: R37 (with R36) turns the
right side into `Fintype.card (Fin T.N)`, R19 into `T.N`; on the left R18 right to left gives `Nat.card ↑K`,
R38 gives `K.ncard`, and Part 2 gives `T.N`.

---

## Part 4 · `orth_of_ne` (milestone)

Statement: from `hE : H ψ = E • ψ` and `hk : E ≠ ↑E(k)`, `⟪ψ_k, ψ⟫_ℂ = 0`. Rewrite both sides of hermiticity
`⟪H ψ_k, ψ⟫ = ⟪ψ_k, H ψ⟫` into `↑E(k) * ⟪ψ_k, ψ⟫ = E * ⟪ψ_k, ψ⟫`, then cancel. Used in Part 5.

**R39 · `T.hamiltonian_hermitian ψ φ`** is the fact `⟪H ψ, φ⟫_ℂ = ⟪ψ, H φ⟫_ℂ`. In the guide it **closes** a goal of
that form; in the exercise `have h := T.hamiltonian_hermitian (T.energyEigenstate k) ψ` adds it to the
**context**. Placeholders: `(T : TightBindingChain) (ψ φ : T.HilbertSpace)`.

| Before | After `exact T.hamiltonian_hermitian ψ φ` |
|---|---|
| `⊢ ⟪T.hamiltonian ψ, φ⟫_ℂ = ⟪ψ, T.hamiltonian φ⟫_ℂ` | no goals |

**R40 · `hamiltonian_energyEigenstate`** changes the **goal** (use `at h` in the exercise):
`H ψ_k = E(k) • ψ_k`, where the scalar `T.energyEigenvalue k` is REAL. Placeholders:
`(T : TightBindingChain) (k : ↑T.QuantaWaveNumber)`.

| Before | After |
|---|---|
| `⊢ P (T.hamiltonian (T.energyEigenstate k))` | `⊢ P (T.energyEigenvalue k • T.energyEigenstate k)` |

**R41 · `rw [show r • v = (r : ℂ) • v from rfl]`** changes the **goal**: the real scalar becomes the complex
scalar `↑r`, so R4 applies (it is stated for `ℂ` scalars and does not match `r : ℝ`). This holds by `rfl`
because `ℝ` acts on `T.HilbertSpace` through `ℂ`; `rw [← Complex.coe_smul]` does the same. In the exercise,
write it with `r := T.energyEigenvalue k`, `v := T.energyEigenstate k`. Placeholders:
`(T : TightBindingChain) (r : ℝ) (v : T.HilbertSpace)`.

| Before | After |
|---|---|
| `⊢ P (r • v)` | `⊢ P (↑r • v)` |

Then R4 gives `conj ↑E(k) * ⟪ψ_k, ψ⟫` on the left, R9 removes the `conj`, and on the right `rw [hE]` and R5 give
`E * ⟪ψ_k, ψ⟫`. All of R40, `hE`, R5, R41, R4, R9 fit in one `rw [...] at h`.

**R42 · `sub_mul`** changes the **goal**. `(a - b) * c = a * c - b * c`. Placeholders: `(a b c : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((a - b) * c)` | `⊢ P (a * c - b * c)` |

**R43 · `sub_self`** changes the **goal**. `a - a = 0`. Placeholders: `(a : ℂ)`. In the exercise,
`rw [sub_mul, h, sub_self]` proves `(E - ↑E(k)) * ⟪ψ_k, ψ⟫_ℂ = 0` (after `rw [h]` both terms are equal).

| Before | After |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |

**R44 · `mul_eq_zero`** changes the **context**. `a * b = 0 ↔ a = 0 ∨ b = 0`. Placeholders: `(a b : ℂ)`.

| Before | After `have h' := mul_eq_zero.mp h` |
|---|---|
| `h : a * b = 0 ⊢ G` | `h' : a = 0 ∨ b = 0 ⊢ G` |

**R45 · `h.resolve_left hA`** **closes** `B` from `h : A ∨ B` and `hA : ¬A` (`Or.resolve_left`).
Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `h : A ∨ B, hA : ¬A ⊢ B` | no goals |

**R46 · `sub_ne_zero`** changes the **goal**. `a - b ≠ 0 ↔ a ≠ b`; as a term, `sub_ne_zero.mpr hk`.
Placeholders: `(a b : ℂ)`.

| Before | After |
|---|---|
| `⊢ a - b ≠ 0` | `⊢ a ≠ b` |

---

## Part 5 · `spectrum_eq_band`

Statement: from `hψ : ψ ≠ 0` and `hE : H ψ = E • ψ`, `∃ k : ↑K, E = ↑E(k)`. Uses Parts 3 and 4.

**R47 · `by_contra hne`** changes the **goal and the context**: assume the negation, prove `False`.
Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hne : ¬G ⊢ False` |

**R48 · `push Not at hne`** changes the **context** (plain `push Not` changes the **goal**): it pushes `¬` inward through `∃`, `∀`, `∧`, … (`¬ ∃ k, p k`
→ `∀ k, ¬ p k`, and `¬ a = b` → `a ≠ b`). Placeholders: `{ι : Type} (a : ℂ) (f : ι → ℂ)`.

| Before | After `push Not` (on the goal; `at hne` does the same to `hne`) |
|---|---|
| `⊢ ¬∃ k, a = f k` | `⊢ ∀ (k : ι), a ≠ f k` |

**R49 · `induction hx using Submodule.span_induction`** changes the **goal list**: to prove `p x` for every `x`
in a span, prove it on the generators and show it survives `0`, `+` and scalar multiplication.
Placeholders: `{E : Type}` a complex vector space, `(s : Set E) (p : E → Prop) (x : E)`.

| Before |
|---|
| `hx : x ∈ Submodule.span ℂ s ⊢ p x` |

After, four goals `case mem`, `case zero`, `case add`, `case smul`:

```lean-goal
⊢ p x✝
⊢ p 0
⊢ p (x✝ + y✝)
⊢ p (a✝¹ • x✝)
```

with, in `mem`, `h✝ : x✝ ∈ s`; in `add`, the induction hypotheses `a✝¹ : p x✝` and `a✝ : p y✝`; in `smul`,
the scalar `a✝¹ : ℂ` and `a✝ : p x✝`. Name them with `with`, one line per case:

```
induction hφ using Submodule.span_induction with
  | mem x hx => …
  | zero => …
  | add x y _ _ hx hy => …
  | smul c x _ hx => …
```

(`_ _` skips the membership proofs of `x` and `y`.) In the exercise `p φ` is `⟪φ, ψ⟫_ℂ = 0`; the goals are
`⟪x, ψ⟫_ℂ = 0` with `hx : x ∈ Set.range T.energyEigenstate`, `⟪0, ψ⟫_ℂ = 0`, `⟪x + y, ψ⟫_ℂ = 0`, and
`⟪c • x, ψ⟫_ℂ = 0`. The original `φ` stays in the context, unused.

**R50 · `obtain ⟨k, rfl⟩ := hx`** with `hx : x ∈ Set.range f` changes the **context**: `x ∈ Set.range f` is by
definition `∃ k, f k = x`; `rfl` substitutes `f k` for `x` everywhere. Placeholders:
`{ι E : Type} (f : ι → E) (x : E)`.

| Before | After |
|---|---|
| `hx : x ∈ Set.range f ⊢ P x` | `k : ι ⊢ P (f k)` |

Then `mem` is Part 4 applied to `hE`, `k` and `hne k`. `zero` is `simp` (it uses `inner_zero_left`, R33).

**R51 · `inner_add_left`** changes the **goal**. `⟪x + y, z⟫_ℂ = ⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ`. Placeholders:
`(x y z : E)`.

| Before | After |
|---|---|
| `⊢ P ⟪x + y, z⟫_ℂ` | `⊢ P (⟪x, z⟫_ℂ + ⟪y, z⟫_ℂ)` |

**R52 · `add_zero`, `mul_zero`** **close** the goal after the induction hypotheses are rewritten in:
`a + 0 = a`, `a * 0 = 0`; `rw` tries `rfl` at the end. `add`: `rw [inner_add_left, hx, hy, add_zero]`.
`smul`: `rw [inner_smul_left, hx, mul_zero]` (R4). Placeholders: `(a c : ℂ)`.

| Before | After `rw [mul_zero, mul_zero, add_zero]` |
|---|---|
| `⊢ a * 0 + c * 0 = 0` | no goals |

**R53 · `trivial`** **closes** `x ∈ ⊤` (`Submodule.mem_top`: the whole space contains every vector). In the
exercise, `rw [span_top]` first turns `ψ ∈ Submodule.span ℂ (Set.range T.energyEigenstate)` into `ψ ∈ ⊤`.
Placeholders: `(x : E)`.

| Before | After |
|---|---|
| `⊢ x ∈ ⊤` | no goals |

**R54 · `inner_self_eq_zero`** changes the **goal**. `⟪x, x⟫_ℂ = 0 ↔ x = 0`. In the exercise use it as a term:
with `key ψ hmem : ⟪ψ, ψ⟫_ℂ = 0`, `inner_self_eq_zero.mp (key ψ hmem) : ψ = 0`, and R35 with `hψ` closes
`False`. Placeholders: `(x : E)`.

| Before | After `rw [inner_self_eq_zero]` |
|---|---|
| `⊢ ⟪x, x⟫_ℂ = 0` | `⊢ x = 0` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: an inner product against a site state.** `⟪∑ n, c n • |n⟩, |m⟩⟫_ℂ = conj (c m)` for any coefficients
`c`. `simp only [sum_inner, inner_smul_left, localizedState_orthonormal_eq_ite]` (R2, R4, R6) leaves a delta
sum, which `simp` collapses (R7):

```lean-goal
⊢ ⟪∑ n, c n • localizedState n, localizedState m⟫_ℂ = (starRingEnd ℂ) (c m)
⊢ (∑ x, (starRingEnd ℂ) (c x) * if x = m then 1 else 0) = (starRingEnd ℂ) (c m)
```

**W2: counting a range.** `(Set.range fun n : Fin 5 => (3 : ℝ) * n).ncard = 5`: one `rw` with R17, R18, R19
leaves the injectivity goal; R20 opens it; R24 and R26 (with R22) close it:

```lean-goal
⊢ (Set.range fun n => 3 * ↑↑n).ncard = 5
⊢ Function.Injective fun n => 3 * ↑↑n
⊢ m = n
```

**W3: span induction with `with`.** A linear functional `f : E →ₗ[ℂ] ℂ` that vanishes on `s` vanishes on
`Submodule.span ℂ s`: `intro x hx`, then R49 with the four cases; `simp` closes `zero`, `add` and `smul`
using that `f` is linear (`map_zero`, `map_add`, `map_smul`).

```lean-goal
⊢ ∀ x ∈ Submodule.span ℂ s, f x = 0
⊢ f x = 0
```

---

## Traps

- `T.energyEigenvalue k` is real and `E` is complex. The goal `E = ↑(T.energyEigenvalue k)` has a cast, and
  `hamiltonian_energyEigenstate` gives a REAL scalar `E(k) • ψ_k`: `inner_smul_left` does not match it until
  R41 makes it `↑E(k) • ψ_k`.
- `⟪·, ·⟫_ℂ` is conjugate-linear on the LEFT: `⟪r • x, y⟫ = conj r * ⟪x, y⟫`. The `conj` disappears only for a
  real `r` (R9). The span induction's `smul` case still works because `conj c * 0 = 0`.
- `rw` cannot rewrite under `∑ n, …` when the pattern mentions `n`; use `simp only [...]` (Part 1).
- `simp` does not use `Complex.exp_conj` and `Complex.exp_add` in the direction you need; name them with `←`.
- `T.QuantaWaveNumber` is a `Set ℝ`, not a type. `k : ↑T.QuantaWaveNumber` is an element of the subtype, and
  `Fintype.card ↑T.QuantaWaveNumber` needs an instance `Fintype ↑T.QuantaWaveNumber`, which Lean does not find
  by itself: build it with R27 and R28 before R29.
- Three cardinalities: `Set.ncard s` (sets), `Nat.card α` (any type, `0` if infinite), `Fintype.card α` (needs
  `[Fintype α]`). Convert with R18 and R38.
- `localizedState` needs `(T := T)` when nothing else fixes `T` (R36).
- In `induction … with`, every case must appear, even one with no variables to name (`| zero => simp`), and
  each `| case … =>` starts its own line. Lean accepts the `|` lines at the indentation of `induction` or
  further in; the guide indents them (W3).
- `≠` is `→ False`: `intro hk` opens it (R32) and `hne h` closes `False` (R35).
- `T.N / 2` in `QuantaWaveNumber` is natural-number division (rounds down).
- `t1 ; t2` runs `t2` on the first goal only (TACTIC_STATES, "Structure"). After R29, use `·` bullets.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `ψ_k` | `simp only [TightBindingChain.energyEigenstate]` | R1 |
| sums out of `⟪·,·⟫` | `sum_inner`, `inner_sum` | R2, R3 |
| scalars out of `⟪·,·⟫` | `inner_smul_left` (conj), `inner_smul_right` | R4, R5 |
| `⟪\|m⟩, \|n⟩⟫` | `localizedState_orthonormal_eq_ite` | R6 |
| finish `⟪ψ_k, ψ_k⟫ = N` | `simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofReal]` | R7–R13 |
| set equality | `ext x` | R14 |
| unfold `K` | `simp [TightBindingChain.QuantaWaveNumber]` | R15, R16 |
| size of a range | `rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]` | R17–R19 |
| prove `Function.Injective f` | `intro m n h` | R20 |
| `0 < T.a`, `0 < T.N`, `T.N ≠ 0` | `T.a_pos`, `NeZero.pos T.N`, `NeZero.ne T.N` | R21, R34 |
| goal = hypothesis up to casts | `exact_mod_cast h` | R22 |
| `0 < e`, `e ≠ 0` | `positivity` | R23 |
| cancel `a * _`, `_ - a` | `mul_left_cancel₀ ha h`, `sub_left_inj.mp h` | R24, R25 |
| `m = n` in `Fin N` | `Fin.ext (by exact_mod_cast …)` | R26 |
| `s.Finite`, `Fintype ↑s` | `Set.finite_of_ncard_pos`, `haveI : Fintype s := hfin.fintype` | R27, R28 |
| span = everything | `apply LinearIndependent.span_eq_top_of_card_eq_finrank'` | R29 |
| orthogonal ⇒ independent | `apply linearIndependent_of_ne_zero_of_inner_eq_zero _ T.energyEigenstate_orthogonal` | R30, R31 |
| prove / use `a ≠ b` | `intro hk` / `hne h.symm` | R32, R35 |
| `⟪0, x⟫`, `⟪x + y, z⟫` | `inner_zero_left`, `inner_add_left` | R33, R51 |
| dimension of `T.HilbertSpace` | `Module.finrank_eq_card_basis (localizedState (T := T)).toBasis` | R36, R37 |
| `Nat.card ↑s` → `s.ncard` | `Nat.card_coe_set_eq` | R38 |
| `H` is Hermitian, `H ψ_k = E(k) • ψ_k` | `T.hamiltonian_hermitian`, `hamiltonian_energyEigenstate` | R39, R40 |
| real scalar → complex scalar | `show r • v = (r : ℂ) • v from rfl` | R41 |
| `(a - b) * c`, `a - a` | `sub_mul`, `sub_self` | R42, R43 |
| `a * b = 0` with `a ≠ 0` | `(mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hk)` | R44–R46 |
| proof by contradiction | `by_contra hne; push Not at hne` | R47, R48 |
| `∀ φ ∈ span ℂ S, p φ` | `induction hφ using Submodule.span_induction with …` | R49 |
| `x ∈ Set.range f` | `obtain ⟨k, rfl⟩ := hx` | R50 |
| `a * 0`, `a + 0` | `mul_zero`, `add_zero` | R52 |
| `x ∈ ⊤` | `trivial` | R53 |
| `⟪x, x⟫ = 0` → `x = 0` | `inner_self_eq_zero.mp` | R54 |
| see the state | infoview | |
