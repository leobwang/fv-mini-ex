# M171 · Translation symmetry and Bloch's theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's linear maps `V →ₗ[ℂ] V`, finite
sums `∑`, bases and orthonormal bases, equivalences `≃` used to reindex sums; physlib's tight-binding chain
(`TightBindingChain`), its site basis `|n⟩`, the operators `|m⟩⟨n|`, its Hamiltonian and its energy
eigenstates.

**The physics.** A ring of `N` sites with spacing `a`. The site basis `|0⟩, …, |N-1⟩` is orthonormal. The
Hamiltonian is `H = E0 ∑ₙ |n⟩⟨n| - t ∑ₙ (|n⟩⟨n+1| + |n+1⟩⟨n|)` with on-site energy `E0 : ℝ` and hopping
`t : ℝ`; indices live in `Fin N`, so `n + 1` and `n - 1` wrap mod `N` (periodic boundary). The translation
`𝒯 = ∑ₙ |n+1⟩⟨n|` sends `|n⟩ ↦ |n+1⟩`. The eigenstates are plane waves
`ψ_k = ∑ₙ e^{i k n a} |n⟩` for `k` in the set `QuantaWaveNumber` of allowed wavenumbers
(`e^{i k N a} = 1`). Bloch: `𝒯 ψ_k = e^{-i k a} ψ_k`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : V → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{V : Type}` is any type. A bracket such as `[AddCommGroup V]` is a
  requirement on `V` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that. States
  containing the character `|` (the bra-ket notation) are shown in `lean-goal` blocks instead of tables.

## Reading the goals

| You see | It means |
|---|---|
| `T : TightBindingChain` | a chain: `T.N` sites (`T.N ≠ 0`), spacing `T.a > 0`, on-site energy `T.E0`, hopping `T.t` |
| `T.HilbertSpace` | `ℂ^N`, functions `Fin T.N → ℂ` with the usual inner product |
| `Fin T.N` | site indices `0, …, N-1`; `+` and `-` on it wrap mod `N` |
| `localizedState n` | the site state `\|n⟩` (an `OrthonormalBasis (Fin T.N) ℂ T.HilbertSpace`, applied to `n`) |
| `\|m⟩⟨n\|` | `localizedComp m n`, the operator `ψ ↦ ⟪\|n⟩, ψ⟫ • \|m⟩`; Lean prints this notation for it. `⟪u, v⟫` is the inner product of `ℂ^N` (conjugate-linear in `u`) |
| `V →ₗ[ℂ] V` | ℂ-linear maps from `V` to `V`; `f x` applies `f` |
| `f ∘ₗ g` | composition of linear maps, `x ↦ f (g x)` |
| `c • v` | scalar `c : ℂ` times vector (or linear map) `v` |
| `Complex.exp z`, `Complex.I` | the complex exponential `e^z` and the imaginary unit `i` |
| `⇑b` | `b` (a basis, a linear map) used as a function; Lean inserts this coercion and usually hides it |
| `↑T.E0`, `↑T.a` | the real number cast into `ℂ` |
| `↑↑k` | `k : ↑T.QuantaWaveNumber` is a real number packed with a proof that it is allowed; `↑↑k` is that real, then cast into `ℂ` |
| `↑↑n` | the site `n : Fin T.N` as a natural number (`n.val`), then cast into `ℂ` |
| `∑ x, f x` | the sum over all `x` of a finite type (`Finset.univ`) |
| `Finset.univ` | the set of all elements of a finite type |
| `localizedState.toBasis m` | the same vector `\|m⟩`, viewed through the plain basis `.toBasis` (R6 removes it) |
| `(Equiv.subRight c) i` | the bijection `i ↦ i - c` applied to `i` (R19 turns it into `i - c`) |
| `x✝ : n ∈ Finset.univ` | an unnamed hypothesis left by `fun n _ => …` (R18); you never need it |
| `case e_a` | the goal `congr` produced for the scalar argument (R21) |

---

## Part 1 · helper `translation_apply` (yours, before `hamiltonian_comm`)

Statement (not a spec; you write it): `translation T (localizedState p) = localizedState (p + 1)`, i.e.
`𝒯 |p⟩ = |p+1⟩`. Unfold `translation` (`simp only [translation]` or name it in `simp [...]`), then R1–R4.

**R1 · `LinearMap.sum_apply`** changes the **goal**: a sum of linear maps applied to a vector becomes a sum
of the applied maps. Lemma: `(∑ d ∈ t, f d) b = ∑ d ∈ t, f d b`. Placeholders:
`{ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (f : ι → V →ₗ[ℂ] V) (x : V)`; `T.HilbertSpace` meets
the brackets, `ι = Fin T.N`.

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) x)` | `⊢ P (∑ d, (f d) x)` |

**R2 · `localizedComp_apply_localizedState`** changes the **goal**: `|m⟩⟨n|` on a site state, by
orthonormality `⟨n|p⟩ = δₙₚ`. Lemma (physlib): `|m⟩⟨n| |p⟩ = if n = p then |m⟩ else 0`. Placeholders:
`(T : TightBindingChain) (m n p : Fin T.N)`. Under a `∑` binder use `simp only [...]`, not `rw`.

```lean-goal
⊢ P (|m⟩⟨n| (localizedState p))
⊢ P (if n = p then localizedState m else 0)
```

**R3 · `Finset.sum_ite_eq'`** changes the **goal**: a sum with a Kronecker-delta `if` collapses to one term.
Lemma: `(∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0`. Mind the side: `x = a` (summation
variable on the left) is `sum_ite_eq'`; `a = x` is `Finset.sum_ite_eq`. Placeholders:
`{ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] (b : ι → V) (a : ι)` (`Fin T.N` has decidable `=`).

| Before | After |
|---|---|
| `⊢ P (∑ x, if x = a then b x else 0)` | `⊢ P (if a ∈ Finset.univ then b a else 0)` |

**R4 · `simp only [Finset.mem_univ, if_true]`** changes the **goal**: `a ∈ Finset.univ` is `True`, so the `if`
takes its `then` branch. Placeholders: `{ι V : Type} [Fintype ι] [DecidableEq ι] (x y : V) (a : ι)`.

| Before | After |
|---|---|
| `⊢ P (if a ∈ Finset.univ then x else y)` | `⊢ P x` |

**W1** chains R1 → R2 → R3 → R4 on the identity `∑ n, |n⟩⟨n|` (not the exercise's operator):

```lean-goal
⊢ ∑ d, |d⟩⟨d| (localizedState p) = localizedState p
⊢ (∑ x, if x = p then localizedState x else 0) = localizedState p
⊢ (if p ∈ Finset.univ then localizedState p else 0) = localizedState p
```

In practice one `simp [translation, localizedComp_apply_localizedState]` does R1–R4 at once.

---

## Part 2 · `hamiltonian_comm`

Statement: `T.hamiltonian ∘ₗ translation T = translation T ∘ₗ T.hamiltonian`, i.e. `H 𝒯 = 𝒯 H`. Two linear
maps are equal when they agree on a basis (R5). On `|m⟩` both sides become
`E0 • |m+1⟩ - t • (|m+2⟩ + |m⟩)`, up to index arithmetic in `Fin T.N`: the left side produces
`m + 1 - 1` (R12) and the right side `m - 1 + 1` (R20, `sub_add_cancel`, stated in Part 3).

**R5 · `apply b.toBasis.ext`** changes the **goal**. Lemma `Module.Basis.ext`:
`(∀ i, f₁ (b i) = f₂ (b i)) → f₁ = f₂` for a basis `b : Module.Basis ι ℂ V`. `localizedState` is an
*orthonormal* basis; `.toBasis` forgets orthonormality, giving the plain basis that `ext` needs. Write it
as `apply (localizedState (T := T)).toBasis.ext` (`(T := T)` names the implicit chain argument;
`apply localizedState.toBasis.ext` also works). Then `intro m`. Placeholders:
`{ι E : Type} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E)
(f g : E →ₗ[ℂ] E)`; `T.HilbertSpace` meets the brackets.

| Before | After |
|---|---|
| `⊢ f = g` | `⊢ ∀ (i : ι), f (b.toBasis i) = g (b.toBasis i)` |

**R6 · `OrthonormalBasis.coe_toBasis`** changes the **goal**: `⇑b.toBasis = ⇑b`, so `b.toBasis i` becomes
`b i` (here `localizedState m`, which the other lemmas recognise). Same placeholders as R5, plus `(i : ι)`.

| Before | After |
|---|---|
| `⊢ P (b.toBasis i)` | `⊢ P (b i)` |

**R7 · `LinearMap.comp_apply`** changes the **goal**: `(f ∘ₗ g) x = f (g x)`. Placeholders:
`{V : Type} [AddCommGroup V] [Module ℂ V] (f g : V →ₗ[ℂ] V) (x : V)`.

| Before | After |
|---|---|
| `⊢ P ((f ∘ₗ g) x)` | `⊢ P (f (g x))` |

**R8 · `hamiltonian_apply_localizedState`** changes the **goal**. Lemma (physlib):
`T.hamiltonian |n⟩ = (T.E0 : ℂ) • |n⟩ - (T.t : ℂ) • (|n + 1⟩ + |n - 1⟩)`. Placeholders:
`(T : TightBindingChain) (n : Fin T.N)`.

| Before | After |
|---|---|
| `⊢ P (T.hamiltonian (localizedState n))` | `⊢ P (↑T.E0 • localizedState n - ↑T.t • (localizedState (n + 1) + localizedState (n - 1)))` |

**R9 · `map_sub`**, **R10 · `map_add`**, **R11 · `map_smul`** change the **goal**: linearity, pushed into
the argument. Lemmas: `f (x - y) = f x - f y`, `f (x + y) = f x + f y`, `f (c • x) = c • f x`. They hold for
any linear map (any `f` of a type with `AddMonoidHomClass` / `MulActionHomClass`; `V →ₗ[ℂ] V` qualifies).
Placeholders: `{V : Type} [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) (x y : V) (c : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (f (x - y))` | `⊢ P (f x - f y)` |
| `⊢ P (f (x + y))` | `⊢ P (f x + f y)` |
| `⊢ P (f (c • x))` | `⊢ P (c • f x)` |

After R6, R7, your helper, R8, R9–R11 in one `simp only [...]`, the goal is (in `hamiltonian_comm`):
`E0 • |m+1⟩ - t • (|m+1+1⟩ + |m+1-1⟩) = E0 • |m+1⟩ - t • (|m+1+1⟩ + |m-1+1⟩)`. The right side's `m - 1 + 1`
comes from `𝒯 |m - 1⟩ = |m - 1 + 1⟩`. Add R20 (`sub_add_cancel`) to the same `simp only` to turn it into
`|m⟩`; then `rw` with R12 fixes the left side's `m + 1 - 1` and closes the goal. Keep all these lemmas in
**one** `simp only`: the helper turns `T.hamiltonian (𝒯 |m⟩)` into `T.hamiltonian |m + 1⟩`, which needs R8
again, and a separate later `simp only` without R8 leaves it unexpanded.

**R12 · `add_sub_cancel_right`** changes the **goal**: `a + b - b = a` in any additive group, so also in
`Fin T.N` (arithmetic mod `N`). Placeholders: `{G : Type} [AddGroup G] (a b : G)`; `Fin T.N`, `ℤ`, `ℂ`
qualify, `ℕ` does **not** (truncated subtraction).

| Before | After |
|---|---|
| `⊢ P (a + b - b)` | `⊢ P a` |

**W3** checks an operator identity on the basis: R5, `intro m`, R6 (plus `LinearMap.id_apply`), then W1's
chain:

```lean-goal
⊢ (∑ n, |n⟩⟨n|) (localizedState.toBasis m) = LinearMap.id (localizedState.toBasis m)
⊢ (∑ n, |n⟩⟨n|) (localizedState m) = localizedState m
```

---

## Part 3 · `bloch_theorem`

Statement: `translation T (T.energyEigenstate k) = exp (-I * k * a) • T.energyEigenstate k`. Push `𝒯`
into the sum: `𝒯 ψ_k = ∑ₙ e^{ikna} |n+1⟩`. Reindex `n ↦ n - 1` so it reads `∑ₙ e^{ik(n-1)a} |n⟩`, then
compare coefficients termwise with `∑ₙ (e^{-ika} e^{ikna}) |n⟩`.

**R13 · unfold `TightBindingChain.energyEigenstate`** changes the **goal**: by definition
`T.energyEigenstate k = ∑ n, Complex.exp (Complex.I * k * n * T.a) • |n⟩`. Use `rw` or `simp only` with
the name. Placeholders: `(T : TightBindingChain) (k : T.QuantaWaveNumber)`.

| Before | After |
|---|---|
| `⊢ P (T.energyEigenstate k)` | `⊢ P (∑ n, Complex.exp (Complex.I * ↑↑k * ↑↑n * ↑T.a) • localizedState n)` |

**R14 · `map_sum`** changes the **goal**: a linear map commutes with finite sums,
`g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x)`. Placeholders:
`{ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (f : V →ₗ[ℂ] V) (v : ι → V)`.

| Before | After |
|---|---|
| `⊢ P (f (∑ i, v i))` | `⊢ P (∑ x, f (v x))` |

Then R11 (`map_smul`) and your helper turn each term `𝒯 (c • |n⟩)` into `c • |n + 1⟩`.

**R15 · `Finset.smul_sum`** changes the **goal**: `r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x` (scalar into the
sum; used on the right side). Placeholders: `{ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] (r : ℂ)
(v : ι → V)`.

| Before | After |
|---|---|
| `⊢ P (r • ∑ i, v i)` | `⊢ P (∑ x, r • v x)` |

**R16 · `smul_smul`** changes the **goal**: `a₁ • a₂ • b = (a₁ * a₂) • b`, two scalars merge into one.
Placeholders: `{V : Type} [AddCommGroup V] [Module ℂ V] (a b : ℂ) (x : V)`.

| Before | After |
|---|---|
| `⊢ P (a • b • x)` | `⊢ P ((a * b) • x)` |

After R13, R14, R11, helper, R15, R16 the goal is
`∑ x, e^{ikxa} • |x + 1⟩ = ∑ x, (e^{-ika} * e^{ikxa}) • |x⟩`.

**R17 · `rw [← (Equiv.subRight c).sum_comp]`** changes the **goal**: reindexes a sum by the bijection
`i ↦ i - c`. Lemma `Equiv.sum_comp`: `∑ i, g (e i) = ∑ i, g i` for any `e : ι ≃ κ` (a bijection with its
inverse). Right to left it inserts `e`. `rw` rewrites the **first** sum it finds (the left side here), and
only that one. Placeholders: `{N : ℕ} [NeZero N] {V : Type} [AddCommGroup V] (g : Fin N → V) (c : Fin N)`;
`[NeZero N]` says `N ≠ 0`, which makes `Fin N` an additive group (so `i - c` and `Equiv.subRight` exist);
`Fin T.N` has it.
In the exercise `c = (1 : Fin T.N)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, g i)` | `⊢ P (∑ i, g ((Equiv.subRight c) i))` |

**R18 · `refine Finset.sum_congr rfl fun n _ => ?_`** changes the **goal and the context**: two sums over the
same set are equal if their terms are. Lemma `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) →
s₁.sum f = s₂.sum g`. Placeholders: `{ι V : Type} [Fintype ι] [AddCommGroup V] (f g : ι → V)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `n : ι, x✝ : n ∈ Finset.univ ⊢ f n = g n` |

**R19 · `Equiv.subRight_apply`** changes the **goal**: `(Equiv.subRight a) b = b - a`. Placeholders:
`{G : Type} [AddGroup G] (c x : G)`.

| Before | After |
|---|---|
| `⊢ P ((Equiv.subRight c) x)` | `⊢ P (x - c)` |

**R20 · `sub_add_cancel`** changes the **goal**: `a - b + b = a` (in `Fin T.N`: `|n - 1 + 1⟩ = |n⟩`). Used
twice: in `hamiltonian_comm` (right side's `|m - 1 + 1⟩`) and here.
Placeholders: `{G : Type} [AddGroup G] (a b : G)`; not `ℕ`.

| Before | After |
|---|---|
| `⊢ P (a - b + b)` | `⊢ P a` |

**W2** chains R17 → R18 → R19, R20 for arbitrary coefficients `g : Fin T.N → ℂ`:

```lean-goal
⊢ ∑ n, g n • localizedState (n + 1) = ∑ n, g (n - 1) • localizedState n
⊢ ∑ i, g ((Equiv.subRight 1) i) • localizedState ((Equiv.subRight 1) i + 1) = ∑ n, g (n - 1) • localizedState n
⊢ g ((Equiv.subRight 1) n) • localizedState ((Equiv.subRight 1) n + 1) = g (n - 1) • localizedState n
```

**R21 · `congr 1`** changes the **goal**: `c • v = d • v` becomes `c = d`; the second argument goal `v = v`
is closed by `rfl` on the spot. Placeholders: `{V : Type} [AddCommGroup V] [Module ℂ V] (c d : ℂ) (v : V)`.
`congr` also closes a goal by `assumption` when a hypothesis matches exactly.

| Before | After |
|---|---|
| `⊢ c • v = d • v` | `⊢ c = d` |

**R22 · `quantaWaveNumber_exp_sub_one`** changes the **goal**. Lemma (physlib), for `n : Fin T.N` and an
allowed `k`: `exp (I * k * ↑(n - 1).val * a) = exp (I * k * n * a) * exp (-I * k * a)`. It is true only because
`n - 1` wraps mod `N` *and* `e^{ikNa} = 1`. Placeholders:
`(T : TightBindingChain) (k : T.QuantaWaveNumber) (n : Fin T.N)`.

| Before | After |
|---|---|
| `⊢ P (Complex.exp (Complex.I * ↑↑k * ↑↑(n - 1) * ↑T.a))` | `⊢ P (Complex.exp (Complex.I * ↑↑k * ↑↑n * ↑T.a) * Complex.exp (-Complex.I * ↑↑k * ↑T.a))` |

What is left is `x * y = y * x`: close it with `ring` (TACTIC_STATES, "Closing").

---

## Traps

- `n + 1 : Fin T.N` wraps around mod `N`. `m + 1 - 1 = m` holds there (R12), but Lean will not do it for
  you: `simp only` with the other lemmas leaves `localizedState (m + 1 - 1)`.
- `↑↑(n - 1)` is the natural number `(n - 1).val`, which is `n - 1` only for `n ≠ 0` (it is `N - 1` at
  `n = 0`). Do not try to push the cast inside; use R22, which handles the wrap-around.
- `rw` cannot rewrite under a binder (`∑ x, …`, `fun x => …`); use `simp only [lemma]` there. R2, R11 and
  the helper are always applied inside sums.
- `hamiltonian_comm` produces both shapes: `m + 1 - 1` (left) is `a + b - b` (R12, `add_sub_cancel_right`),
  `m - 1 + 1` (right) is `a - b + b` (R20, `sub_add_cancel`). Each lemma fixes only its own shape; you need
  both, or the goal stays open after `rw`.
- `Finset.sum_ite_eq` vs `Finset.sum_ite_eq'`: the prime is for `if x = a` (bound variable on the left).
- The helper `translation_apply` is not in the spec: state and prove it yourself above `hamiltonian_comm`,
  then name it in both `simp only` calls.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `(∑ i, f i) x` → `∑ i, f i x` | `simp only [LinearMap.sum_apply]` | R1 |
| `\|m⟩⟨n\| \|p⟩` | `simp only [localizedComp_apply_localizedState]` | R2 |
| collapse `∑ x, if x = a then b x else 0` | `simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]` | R3, R4 |
| `𝒯 \|p⟩ = \|p + 1⟩` (helper) | `simp [translation, localizedComp_apply_localizedState]` | R1–R4 |
| maps equal on a basis | `apply (localizedState (T := T)).toBasis.ext; intro m` | R5 |
| `b.toBasis i` → `b i` | `OrthonormalBasis.coe_toBasis` | R6 |
| `(f ∘ₗ g) x` → `f (g x)` | `LinearMap.comp_apply` | R7 |
| `H \|n⟩` | `hamiltonian_apply_localizedState` | R8 |
| linearity | `map_sub`, `map_add`, `map_smul`, `map_sum` | R9–R11, R14 |
| `a + b - b`, `a - b + b` (mod N) | `add_sub_cancel_right`, `sub_add_cancel` | R12, R20 |
| unfold `ψ_k` | `TightBindingChain.energyEigenstate` | R13 |
| scalar into a sum / merge scalars | `Finset.smul_sum`, `smul_smul` | R15, R16 |
| reindex `n ↦ n - 1` | `rw [← (Equiv.subRight (1 : Fin T.N)).sum_comp]` | R17 |
| sums termwise | `refine Finset.sum_congr rfl fun n _ => ?_` | R18 |
| `(Equiv.subRight c) x` → `x - c` | `Equiv.subRight_apply` | R19 |
| `c • v = d • v` → `c = d` | `congr 1` | R21 |
| `exp (i k (n-1) a)` | `quantaWaveNumber_exp_sub_one` | R22 |
| commutativity of `*` | `ring` | TACTIC_STATES |
