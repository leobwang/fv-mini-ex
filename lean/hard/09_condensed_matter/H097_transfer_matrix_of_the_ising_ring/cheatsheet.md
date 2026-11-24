# H097 · Transfer matrix of the Ising ring: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `rw`, `simp`, `induction`, `cases`, `calc`, `have`).
**New here:** Mathlib's matrices indexed by `Bool` (`Matrix.of`, powers, `Matrix.trace`), finite sums
and products `∑`/`∏` over `Fin n` and over function spaces `Fin (n + 1) → Bool`, reindexing a sum
along an equivalence `≃` (`Equiv.sum_comp`, `Fin.consEquiv`, `Equiv.funUnique`), the index
operations `Fin.castSucc`, `Fin.succ`, `Fin.last`, `Fin.cons`, `Real.exp`, and the tactics
`simp_rw`, `congr 1`, `linarith`.

**The physics in one line.** A ring of `n + 1` sites `0, …, n`, spin $s_i = \mathrm{spin}(\sigma_i) = \pm 1$,
energy $E(\sigma) = -J\big(\sum_{i<n} s_i s_{i+1} + s_n s_0\big) - h\sum_i s_i$, partition function
$Z = \sum_\sigma e^{-\beta E(\sigma)}$ (sum over all $2^{n+1}$ configurations). With
$T_{ab} = \exp\big(\beta(J s_a s_b + h (s_a + s_b)/2)\big)$ the claim is $Z = \operatorname{tr} T^{n+1}$.
The proof has two independent halves:

1. **Matrix half** (any `M : Matrix Bool Bool ℝ`): $(M^n)_{ab}$ is the sum, over all paths
   $\sigma_0 \dots \sigma_n$ with $\sigma_0 = a$, $\sigma_n = b$, of $\prod_{i<n} M_{\sigma_i\sigma_{i+1}}$
   (Part 1). Taking $a = b$ and summing gives $\operatorname{tr} M^{n+1}$ as a sum over closed paths
   (Part 2).
2. **Physics half**: give each bond half of the field term of each of its two ends (Part 3); then
   $e^{-\beta E(\sigma)} = \prod_{\text{bonds}} T_{\sigma_i\sigma_{i+1}}$ (Part 4).

Part 5 glues them.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal (in particular inside a `∑` or an `if`, for `simp only`/`simp_rw`).
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it; in this
  problem the values are always in `ℝ`, which meets all of them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin (n + 1)` | the sites `{0, 1, …, n}` (natural numbers `< n + 1`) |
| `i.castSucc`, `i.succ` (for `i : Fin n`) | the sites `i` and `i + 1`, as elements of `Fin (n + 1)`. Bond `i — i+1` is `σ i.castSucc`, `σ i.succ` |
| `Fin.last n` | the last site `n : Fin (n + 1)`; the bond `σ (Fin.last n)`, `σ 0` closes the ring |
| `⟨0, ⋯⟩` | the element of `Fin k` with value `0`; `⋯` is the hidden proof `0 < k` |
| `σ : Fin (n + 1) → Bool` | a spin configuration (equivalently, a path of `n + 1` spins) |
| `Fin.cons x τ` | the function `Fin (n + 1) → β` with value `x` at `0` and `τ i` at `i.succ` (prepend `x`) |
| `Matrix Bool Bool ℝ` | real 2×2 matrices whose rows and columns are indexed by `false`, `true`; `M a b` is an entry |
| `Matrix.of f` | the matrix with entries `f a b` |
| `M ^ n`, `1` | matrix power, identity matrix |
| `M.trace`, `M.diag` | `∑ i, M i i`; the diagonal `fun i => M i i` |
| `∑ x, f x` | sum of `f x` over every `x` of a finite type (`Bool`, `Fin n`, `Fin (n + 1) → Bool`, pairs) |
| `∑ x ∈ s, f x`, `Finset.univ` | sum over a finite set `s`; `Finset.univ` is the set of all elements, and `∑ x, f x` means `∑ x ∈ Finset.univ, f x` |
| `∏ i, f i` | the product, same conventions |
| `x✝ : τ ∈ Finset.univ` | an unnamed (`✝`) hypothesis, here always true and unused |
| `n✝`, `a✝` | names Lean made up; you cannot type them (R1 shows how to name them) |
| `i_1`, `x_1`, `b_1` | a bound variable renamed to avoid a clash with an outer `i`, `x`, `b` |
| `e : ι ≃ κ`, `e.symm`, `e i` | an equivalence (a bijection with its inverse), its inverse, applying it |
| `uniqueElim b` | the constant function with value `b` on a one-element type such as `Fin 1` |
| `if p then a else b` | needs `p` decidable (`Bool` and `Fin` equalities are) |
| `Real.exp x` | $e^x$ |
| `- -x` | `-(-x)`, a double minus left by R38; `ring_nf` removes it |
| `∑ x, …` without a type | Lean does not print the binder type: in `∑ x, spin (σ x.castSucc)`, `x : Fin n` |
| `inst✝ : AddCommMonoid M` | a type-class assumption from a `[…]` binder |
| `case zero`, `case succ` | the goals made by `induction`; `case pos`/`case neg` by `by_cases`; `case h₀`/`case h₁` the side goals of R16; `case false.true` by `cases a <;> cases b` |

---

## Part 1 · `pow_apply_eq_sum` (milestone)

Statement: for `M : Matrix Bool Bool ℝ`, `(M ^ n) a b` equals the sum over `σ : Fin (n + 1) → Bool` of
`if σ 0 = a ∧ σ (Fin.last n) = b then ∏ i : Fin n, M (σ i.castSucc) (σ i.succ) else 0`. Induction on
`n`, with `a` generalized because the step needs the hypothesis at another start spin.

### Base case: induction, `M ^ 0`, paths of one spin

**R1 · `induction n generalizing a with | zero => … | succ n ih => …`** changes the **goal list and the
context**: two goals. `generalizing a` puts `∀ a` into the induction hypothesis, so in the step
`ih : ∀ (a : Bool), P n a` can be used at any start spin. Placeholders: `(P : ℕ → Bool → Prop) (n : ℕ) (a : Bool)`.
The alternatives may be indented under `induction`.

| Before | After `induction n generalizing a` | After `rename_i n ih` (what `\| succ n ih =>` shows) |
|---|---|---|
| `n : ℕ, a : Bool ⊢ P n a` | `a : Bool ⊢ P 0 a`, `n✝ : ℕ ⊢ P (n✝ + 1) a` (and `a✝ : ∀ (a : Bool), P n✝ a`) | `n : ℕ ⊢ P (n + 1) a` (and `ih : ∀ (a : Bool), P n a`) |

**R2 · `rw [pow_zero]`** changes the **goal**. The lemma is `pow_zero : x ^ 0 = 1`. Placeholders:
`{α : Type} [Monoid α] (x : α)`; a monoid has `*` and `1`, and square matrices form one.

| Before | After |
|---|---|
| `⊢ P (x ^ 0)` | `⊢ P 1` |

**R3 · `rw [Matrix.one_apply]`** changes the **goal**. The lemma is
`(1 : Matrix n n α) i j = if i = j then 1 else 0`. Placeholders: `{α : Type} [Zero α] [One α] (a b : Bool)`.

| Before | After |
|---|---|
| `⊢ P (1 a b)` | `⊢ P (if a = b then 1 else 0)` |

**R4 · `rw [← e.sum_comp]`** changes the **goal**: it reindexes a sum. The lemma is
`Equiv.sum_comp (e : ι ≃ κ) (g : κ → M) : ∑ i, g (e i) = ∑ k, g k`; right to left, a sum over `κ` becomes a
sum over `ι`. Placeholders: `{ι κ M : Type} [Fintype ι] [Fintype κ] [AddCommMonoid M]` (`Fintype`: finitely
many elements; `AddCommMonoid`: a commutative `+` with `0`, as in `ℝ`).

| Before | After |
|---|---|
| `⊢ P (∑ k, g k)` | `⊢ P (∑ i, g (e i))` |

**R5 · `Equiv.funUnique (Fin 1) β`** is the equivalence `(Fin 1 → β) ≃ β` (a function on one point is its
value). Used in R4 as `e := (Equiv.funUnique (Fin 1) Bool).symm`, it turns `∑ σ : Fin 1 → Bool` into a sum
over `Bool`. Evaluating `e.symm b` changes the **goal**: `Equiv.funUnique_symm_apply` gives `uniqueElim b`,
and `uniqueElim_const` gives `b`. `simp` does both. Placeholders: `{β : Type} (b : β)`.

| Before | After `rw [Equiv.funUnique_symm_apply]` | After `rw [uniqueElim_const]` |
|---|---|---|
| `⊢ P ((Equiv.funUnique (Fin 1) β).symm b 0)` | `⊢ P (uniqueElim b 0)` | `⊢ P b` |

**R6 · `cases a <;> cases b`** changes the **goal list**: for `a b : Bool`, four goals, one per pair of
values. Placeholders: `(P : Bool → Bool → Prop)`.

| Before | After |
|---|---|
| `a b : Bool ⊢ P a b` | `⊢ P false false`, `⊢ P false true`, `⊢ P true false`, `⊢ P true true` |

**R7 · `simp [Fin.last]`** changes the **goal**: it unfolds `Fin.last 0` to the literal index `⟨0, ⋯⟩`, which
`simp` identifies with `0`. In the base case, `simp [Fin.last]` then also applies R5 and evaluates the
`if`s and the empty product `∏ i : Fin 0, … = 1`. Placeholders: `{β : Type} (f : Fin 1 → β)`.

| Before | After `simp only [Fin.last]` |
|---|---|
| `⊢ P (f (Fin.last 0))` | `⊢ P (f ⟨0, ⋯⟩)` |

### Step, first half: a path of `n + 2` spins = its first spin + a path of `n + 1` spins

The step proves, as `have hR`, that the right-hand side for `n + 1` (paths `σ : Fin (n + 2) → Bool` from `a`
to `b`) equals `∑ τ : Fin (n + 1) → Bool, if τ (Fin.last n) = b then M a (τ 0) * ∏ i : Fin n, M (τ i.castSucc) (τ i.succ) else 0`.

**R8 · `rw [← (Fin.consEquiv fun _ => β).sum_comp]`** changes the **goal**. `Fin.consEquiv fun _ => β` is the
equivalence `β × (Fin n → β) ≃ (Fin (n + 1) → β)` sending `(x, τ)` to `Fin.cons x τ`; with R4, a sum over
paths becomes a sum over pairs (first spin, rest). Placeholders:
`{β M : Type} [Fintype β] [AddCommMonoid M] (n : ℕ) (g : (Fin (n + 1) → β) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ σ, g σ)` | `⊢ P (∑ i, g ((Fin.consEquiv fun x => β) i))` |

**R9 · `rw [Fintype.sum_prod_type]`** changes the **goal**: `∑ p : β × γ, f p = ∑ x, ∑ y, f (x, y)`.
Placeholders: `{β γ M : Type} [Fintype β] [Fintype γ] [AddCommMonoid M] (f : β × γ → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ p, f p)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R10 · `rw [Finset.sum_comm]`** changes the **goal**: swaps a double sum,
`∑ x, ∑ y, f x y = ∑ y, ∑ x, f x y`. Placeholders: as R9 with `(f : β → γ → M)`. `rw` swaps the first double
sum it finds; to swap an inner one, use it under `Finset.sum_congr` (R11) or in a `calc` step.

| Before | After |
|---|---|
| `⊢ P (∑ x, ∑ y, f x y)` | `⊢ P (∑ y, ∑ x, f x y)` |

**R11 · `refine Finset.sum_congr rfl fun i _ => ?_`** changes the **goal and the context**: to prove two sums
over the same set equal, prove the summands equal for each `i`. The lemma is
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. Placeholders:
`{ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `i : ι, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R12 · `simp only [Fin.consEquiv_apply]`** changes the **goal**: `(Fin.consEquiv _) (x, τ) i = Fin.cons x τ i`
(`rw` would leave `(x, τ).1`, `(x, τ).2`; `simp only` reduces them). Placeholders:
`{β : Type} (n : ℕ) (x : β) (τ : Fin n → β)`.

| Before | After |
|---|---|
| `⊢ P ((Fin.consEquiv fun x => β) (x, τ) 0)` | `⊢ P (Fin.cons x τ 0)` |

**R13 · `Fin.cons_zero`, `Fin.cons_succ`** change the **goal**: `Fin.cons x τ 0 = x` and
`Fin.cons x τ i.succ = τ i`. They fire only when the index is literally `0` or `_.succ` (see R14).
Placeholders: as R12 with `(i : Fin n)`.

| Before | After `rw [Fin.cons_zero]` | After `rw [Fin.cons_succ]` |
|---|---|---|
| `⊢ P (Fin.cons x τ 0) (Fin.cons x τ i.succ)` | `⊢ P x (Fin.cons x τ i.succ)` | `⊢ P x (τ i)` |

**R14 · `← Fin.succ_last`, `← Fin.succ_castSucc`, `Fin.castSucc_zero`** change the **goal**: they rewrite an
index into the form R13 needs. The lemmas are `Fin.succ_last : (Fin.last n).succ = Fin.last (n + 1)`,
`Fin.succ_castSucc : i.castSucc.succ = i.succ.castSucc`, `Fin.castSucc_zero : Fin.castSucc 0 = 0`.
Placeholders: `{β : Type} (n : ℕ) (x : β) (τ : Fin (n + 1) → β) (i : Fin n)`.

| Before | After |
|---|---|
| `⊢ P (Fin.cons x τ (Fin.last (n + 1)))` | `⊢ P (Fin.cons x τ (Fin.last n).succ)` |
| `⊢ P (Fin.cons x τ i.succ.castSucc)` | `⊢ P (Fin.cons x τ i.castSucc.succ)` |
| `⊢ P (f (Fin.castSucc 0))` | `⊢ P (f 0)` |

**R15 · `Fin.prod_univ_succ`** changes the **goal**: `∏ i : Fin (n + 1), f i = f 0 * ∏ i : Fin n, f i.succ`
(peel the first bond off the path). Placeholders: `{M : Type} [CommMonoid M] (n : ℕ) (f : Fin (n + 1) → M)`
(`CommMonoid`: a commutative `*` with `1`, as in `ℝ`).
In `hR`, one `simp only` with R12, R13, R14 (in the directions above) and R15 turns the summand into
`if x = a ∧ τ (Fin.last n) = b then M x (τ 0) * ∏ …τ… else 0`.

| Before | After |
|---|---|
| `⊢ P (∏ i, f i)` | `⊢ P (f 0 * ∏ i, f i.succ)` |

**R16 · `rw [Finset.sum_eq_single a]`** changes the **goal list**: the sum becomes its `a` term, and two side
goals appear: every other term is `0` (`case h₀`), and the term at `a` is `0` if `a` is not in the set
(`case h₁`, trivial for `Finset.univ`: `simp`). The lemma is
`Finset.sum_eq_single a : (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s → f a = 0) → ∑ x ∈ s, f x = f a`.
Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M] (f : ι → M) (a : ι)`. In `hR` the first spin `x` is
forced to be `a`, so the sum over `x` collapses at `a`; in `case h₀`, `intro c _ hc` and `simp [hc]`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (f a)`, `⊢ ∀ b ∈ Finset.univ, b ≠ a → f b = 0`, `⊢ a ∉ Finset.univ → f a = 0` |

### Step, second half: `M ^ (n + 1) = M * M ^ n` and the induction hypothesis

**R17 · `rw [pow_succ']`** changes the **goal**: `x ^ (n + 1) = x * x ^ n` (the first step of the path is
`M`). Placeholders: `{α : Type} [Monoid α] (x : α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (x ^ (n + 1))` | `⊢ P (x * x ^ n)` |

**R18 · `rw [Matrix.mul_apply]`** changes the **goal**: $(MN)_{ab} = \sum_j M_{aj} N_{jb}$. Placeholders:
`{α : Type} [Mul α] [AddCommMonoid α] (M N : Matrix Bool Bool α) (a b : Bool)`.

| Before | After |
|---|---|
| `⊢ P ((M * N) a b)` | `⊢ P (∑ j, M a j * N j b)` |

**R19 · `simp_rw [hfg]`** changes the **goal**: it rewrites with `hfg : ∀ i, f i = g i` under binders such
as `∑ j, …`, where `rw [hfg]` fails ("did not find an occurrence of the pattern") because the bound `j` is
not a term `rw` can match. In the step: `simp_rw [ih]` rewrites `(M ^ n) j b` inside `∑ j, M a j * …`.
Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ x, g x)` |

**R20 · `Finset.mul_sum`** changes the **goal**: `a * ∑ i, f i = ∑ i, a * f i` (use with `simp_rw` when it sits
under another `∑`). Placeholders: `{ι R : Type} [Fintype ι] [CommSemiring R] (a : R) (f : ι → R)`
(`CommSemiring`: commutative `+` and `*` with distributivity; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

After R20, swap the two sums (R10), go under the outer one (R11), and collapse the sum over the middle spin
`c` at `c = τ 0` (R16). The main goal then has `if τ 0 = τ 0 ∧ τ (Fin.last n) = b then …` on one side and
`if τ (Fin.last n) = b then …` on the other: split on the condition (R21) and `simp [hb]`.

**R21 · `by_cases hb : p`** changes the **goal list and the context**: one goal with `hb : p` (`case pos`),
one with `hb : ¬p` (`case neg`). Placeholders: `(p G : Prop)`. `by_cases hb : p <;> simp [hb]` handles both.

| Before | After |
|---|---|
| `⊢ G` | `hb : p ⊢ G`, `hb : ¬p ⊢ G` |

**R22 · `Ne.symm`** changes the **context** (with `have`): `Ne.symm : c ≠ d → d ≠ c`. In `case h₀` of R16 you
get `hc : c ≠ τ 0`, but the goal says `τ 0 = c`; `simp [hc]` does not rewrite that, `simp [Ne.symm hc]` does.
Placeholders: `{β : Type} (c d : β)`.

| Before | After `have hd := Ne.symm hc` |
|---|---|
| `hc : c ≠ d ⊢ G` | `hd : d ≠ c ⊢ G` |

**W1** (a path of length 2): `rw [pow_succ']`, `rw [pow_one]` (`x ^ 1 = x`), `rw [Matrix.mul_apply]`; the last
`rw` closes the goal by `rfl`:

```lean-goal
⊢ (M ^ 2) a b = ∑ j, M a j * M j b
⊢ (M * M ^ 1) a b = ∑ j, M a j * M j b
⊢ (M * M) a b = ∑ j, M a j * M j b
```

**W3** (split a sum over configurations into first spin and the rest, R8, R9, then R12 and R13 in one
`simp only`, which closes it):

```lean-goal
⊢ (∑ σ, f (σ 0) * g fun i => σ i.succ) = ∑ x, ∑ τ, f x * g τ
⊢ (∑ i, f ((Fin.consEquiv fun x => Bool) i 0) * g fun i_1 => (Fin.consEquiv fun x => Bool) i i_1.succ) = ∑ x, ∑ τ, f x * g τ
⊢ (∑ x, ∑ y, f ((Fin.consEquiv fun x => Bool) (x, y) 0) * g fun i => (Fin.consEquiv fun x => Bool) (x, y) i.succ) = ∑ x, ∑ τ, f x * g τ
```

**W4** (collapse with R16; the three goals; `simp [Ne.symm hx]` in the middle one):

```lean-goal
⊢ (∑ x, if c = x then f x else 0) = f c
⊢ (if c = c then f c else 0) = f c
⊢ ∀ b ∈ Finset.univ, b ≠ c → (if c = b then f b else 0) = 0
⊢ c ∉ Finset.univ → (if c = c then f c else 0) = 0
```

---

## Part 2 · `trace_pow_succ` (milestone)

Statement: `Matrix.trace (M ^ (n + 1)) = ∑ σ : Fin (n + 1) → Bool, (∏ i : Fin n, M (σ i.castSucc) (σ i.succ)) * M (σ (Fin.last n)) (σ 0)`:
the trace is the sum over closed paths, with the closing step `σ n → σ 0`. Write `M ^ (n + 1) = M ^ n * M`
so that the last factor is the closing step, then use Part 1 for `(M ^ n) a c`.

**R23 · `rw [Matrix.trace]`, then `simp only [Matrix.diag]`** change the **goal**: `M.trace` unfolds to
`∑ i, M.diag i`, and `M.diag i` to `M i i`. Placeholders: `{α : Type} [AddCommMonoid α] (M : Matrix Bool Bool α)`.

| Before | After `rw [Matrix.trace]` | After `simp only [Matrix.diag]` |
|---|---|---|
| `⊢ P M.trace` | `⊢ P (∑ i, M.diag i)` | `⊢ P (∑ x, M x x)` |

**R24 · `rw [pow_succ]`** changes the **goal**: `x ^ (n + 1) = x ^ n * x` (compare R17). Placeholders: as R17.

| Before | After |
|---|---|
| `⊢ P (x ^ (n + 1))` | `⊢ P (x ^ n * x)` |

**R25 · `Finset.sum_mul`** changes the **goal**: `(∑ i, f i) * a = ∑ i, f i * a`. Placeholders: as R20.

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) * a)` | `⊢ P (∑ i, f i * a)` |

After R23, R24, R18 and Part 1 (all in one `simp only [Matrix.diag, Matrix.mul_apply, pow_apply_eq_sum, Finset.sum_mul]`),
the goal is a triple sum `∑ a, ∑ c, ∑ σ, (if σ 0 = a ∧ σ (Fin.last n) = c then ∏ … else 0) * M c a`. Bring `∑ σ`
outside with a three-step `calc` (W7 below): step 1 names the middle sum `∑ a, ∑ σ, ∑ c, …` (summand written
out) and proves it by R10 under `∑ a`, written as the term `Finset.sum_congr rfl fun a _ => Finset.sum_comm`
(the term form of R11) or as `by` R11 then `rw [Finset.sum_comm]`; step 2 `_ = _ := Finset.sum_comm` swaps the
outer two; step 3 `_ = _ := by …` goes under `∑ σ` with R11 and uses R26–R28.

**R26 · `ite_mul`, then `zero_mul`** change the **goal**: `(if p then a else b) * c = if p then a * c else b * c`
and `0 * c = 0`. Placeholders: `{α : Type} [MulZeroClass α] (p : Prop) [Decidable p] (a c : α)` (`MulZeroClass`: `*` with a `0`
that absorbs it, as in `ℝ`; `Decidable p`: `p` can be tested, which `if p` needs; every `Bool` or `Fin` equality is).

| Before | After `rw [ite_mul]` | After `rw [zero_mul]` |
|---|---|---|
| `⊢ P ((if p then a else 0) * c)` | `⊢ P (if p then a * c else 0 * c)` | `⊢ P (if p then a * c else 0)` |

**R27 · `ite_and`** changes the **goal**: `(if p ∧ q then a else b) = if p then (if q then a else b) else b`.
Placeholders: `{α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if p ∧ q then a else b)` | `⊢ P (if p then if q then a else b else b)` |

**R28 · `Finset.sum_ite_eq`** changes the **goal**:
`∑ x ∈ s, (if a = x then f x else 0) = if a ∈ s then f a else 0`; with `Finset.mem_univ` the `if` is true.
After R26 and R27, plain `simp` applies it to both sums (over `a` and over `c`) and closes the summand goal.
Placeholders: `{ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (a : ι) (f : ι → M)` (`DecidableEq ι`:
equality on `ι` can be tested; `Bool` meets it).

| Before | After |
|---|---|
| `⊢ P (∑ x, if a = x then f x else 0)` | `⊢ P (if a ∈ Finset.univ then f a else 0)` |

**W2** (trace of a product, R23 then R18 under the binder with `simp_rw`, R19; the last step closes it):

```lean-goal
⊢ (M * N).trace = ∑ i, ∑ j, M i j * N j i
⊢ ∑ i, (M * N).diag i = ∑ i, ∑ j, M i j * N j i
⊢ ∑ x, (M * N) x x = ∑ i, ∑ j, M i j * N j i
```

**W7** (reorder a triple sum, `f : Bool → Bool → Fin 3 → ℝ`, with a `calc`; the whole `calc` is one tactic
and closes the goal). Its step 1 goes from `∑ a, ∑ b, ∑ k, f a b k` to the named middle expression
`∑ a, ∑ k, ∑ b, f a b k` by `Finset.sum_congr rfl fun a _ => Finset.sum_comm` (R10 under `∑ a`); step 2,
`_ = _ := Finset.sum_comm`, swaps the outer two sums, and Lean fills in the right side itself:

```lean-goal
⊢ ∑ a, ∑ b, ∑ k, f a b k = ∑ k, ∑ a, ∑ b, f a b k
```

---

## Part 3 · `field_split` (milestone)

Statement: $\sum_i s_i = \sum_{i<n} (s_i + s_{i+1})/2 + (s_n + s_0)/2$: each site's field term is shared by its
two bonds. Peel the last term (R29) and the first term (R30) off `∑ i, spin (σ i)`, split the right side into
two sums (R31, R32), and combine linearly (R33).

**R29 · `Fin.sum_univ_castSucc`** changes the **goal** with `rw`, or the **context** with `have`. The lemma is
`∑ i : Fin (n + 1), f i = ∑ i : Fin n, f i.castSucc + f (Fin.last n)` (peel the last term). Here you want it as
a fact: `have h1 := Fin.sum_univ_castSucc (fun i => spin (σ i))` adds
`h1 : ∑ i, spin (σ i) = ∑ i, spin (σ i.castSucc) + spin (σ (Fin.last n))` (W5 shows the same with `f`).
Placeholders: `{M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M)`.

| Before | After `rw [Fin.sum_univ_castSucc]` |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ i, f i.castSucc + f (Fin.last n))` |

**R30 · `Fin.sum_univ_succ`** changes the **goal** with `rw`, or the **context** with `have`. The lemma is
`∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, f i.succ` (peel the first term). Use it as `have h2 := …` like R29.
Placeholders: as R29.

| Before | After `rw [Fin.sum_univ_succ]` |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + ∑ i, f i.succ)` |

**R31 · `rw [← Finset.sum_div]`** changes the **goal**: `(∑ i, f i) / a = ∑ i, f i / a`, right to left.
Placeholders: `{ι K : Type} [Fintype ι] [DivisionSemiring K] (f : ι → K) (a : K)` (`/` exists; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i / a)` | `⊢ P ((∑ i, f i) / a)` |

**R32 · `Finset.sum_add_distrib`** changes the **goal**: `∑ i, (f i + g i) = ∑ i, f i + ∑ i, g i`.
Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M] (f g : ι → M)`. In this problem use
`simp only [← Finset.sum_div, Finset.sum_add_distrib]` so both fire under the `/ 2`.

| Before | After |
|---|---|
| `⊢ P (∑ i, (f i + g i))` | `⊢ P (∑ x, f x + ∑ x, g x)` |

**R33 · `linarith`** **closes** a goal that is a linear combination of hypotheses (`=`, `≤`, `<` over `ℝ`).
Any non-linear subterm is one unknown: here `∑ i, spin (σ i)`, `∑ x, spin (σ x.castSucc)`,
`∑ x, spin (σ x.succ)`, `spin (σ 0)`, `spin (σ (Fin.last n))` are five unknowns, and `h1`, `h2` relate them.

| Before | After |
|---|---|
| `h1 : s = x + y, h2 : s = 2 * y ⊢ s = (x + y) / 2 + y` | ∅ |

**W5** (peel both ends as facts `h1`, `h2` with R29, R30, then R33; the goal does not change until `linarith` closes it):

```lean-goal
⊢ ∑ i, f i.succ - ∑ i, f i.castSucc = f (Fin.last n) - f 0
```

---

## Part 4 · `weight_eq` (milestone)

Statement: `Real.exp (-β * ringEnergy J h σ) = (∏ i : Fin n, transfer β J h (σ i.castSucc) (σ i.succ)) * transfer β J h (σ (Fin.last n)) (σ 0)`.
Unfold `transfer` (R34) and write the right side as one exponential (R35, R36); unfold `ringEnergy` and use
Part 3; strip `Real.exp` (R37); what is left is an identity of real numbers with sums in it (R38, R39).

**R34 · `Matrix.of_apply`** changes the **goal**: `Matrix.of f a b = f a b`. Placeholders:
`{α : Type} (f : Bool → Bool → α) (a b : Bool)`.

| Before | After |
|---|---|
| `⊢ P (Matrix.of f a b)` | `⊢ P (f a b)` |

**R35 · `← Real.exp_sum`** changes the **goal**: `Real.exp (∑ x ∈ s, f x) = ∏ x ∈ s, Real.exp (f x)`, right to
left. Placeholders: `{ι : Type} [Fintype ι] (f : ι → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∏ i, Real.exp (f i))` | `⊢ P (Real.exp (∑ x, f x))` |

**R36 · `← Real.exp_add`** changes the **goal**: `Real.exp (x + y) = Real.exp x * Real.exp y`, right to left.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x * Real.exp y)` | `⊢ P (Real.exp (x + y))` |

R34–R36 together with `ringEnergy` and `field_split` go in one
`simp only [transfer, Matrix.of_apply, ← Real.exp_sum, ← Real.exp_add, ringEnergy, field_split]`: the goal is
then `Real.exp (…) = Real.exp (…)`.

**R37 · `congr 1`** changes the **goal**: `f x = f y` becomes `x = y` (it may also close easy leftovers by
`rfl` or an assumption). Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ Real.exp (x + 0) = Real.exp x` | `⊢ x + 0 = x` |

**R38 · `simp only [mul_add, mul_neg, neg_mul, sub_eq_add_neg]`** changes the **goal**: `a * (b + c) = a * b + a * c`,
`a * -b = -(a * b)`, `-a * b = -(a * b)`, `a - b = a + -b`. Together with `Finset.mul_sum` (R20) it pushes
`-β *` and `-J *` and `h *` into the sums. Placeholders: `{R : Type} [CommRing R] (a b c : R)` (`CommRing`: commutative `+`, `-`, `*`;
`ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (-a * (b - c))` | `⊢ P (-(a * b) + - -(a * c))` |

**R39 · `ring_nf`, `ring`** (TACTIC_STATES). Here the point is how they treat sums: `ring` sees `∑ i, f i` as one
unknown, so two sums are equal for `ring` only if they are syntactically equal; `ring_nf` also normalises each
summand inside a `∑`. So: `ring_nf` (summands in one normal form), then
`simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]` (R32, R25, R20: split the sums and pull
constant factors out), then `ring` closes. Placeholders: `{ι : Type} [Fintype ι] (a : ℝ) (f : ι → ℝ)`.

| Before | After `ring_nf` |
|---|---|
| `⊢ P (∑ i, 2 * (f i * a))` | `⊢ P (∑ x, f x * a * 2)` |

**W6** (R35, R36, R37, then `ring`):

```lean-goal
⊢ (∏ i, Real.exp (v i)) * Real.exp y = Real.exp (y + ∑ i, v i)
⊢ Real.exp (∑ x, v x) * Real.exp y = Real.exp (y + ∑ i, v i)
⊢ Real.exp (∑ x, v x + y) = Real.exp (y + ∑ i, v i)
⊢ ∑ x, v x + y = y + ∑ i, v i
```

---

## Part 5 · `Zring_eq_trace`

Statement: `Zring β J h n = Matrix.trace (transfer β J h ^ (n + 1))`. Rewrite the trace with Part 2 and unfold
`Zring` (`rw [trace_pow_succ, Zring]`); both sides are now sums over `σ`, and Part 4 says the summands agree.
Part 4 has to be used under the binder `∑ σ, …`, so `simp_rw [weight_eq]` (R19), not `rw`.

---

## Traps

- Without `generalizing a`, the induction hypothesis is only about the fixed start spin `a`, but the step needs it
  at every middle spin `j` (R1).
- `pow_succ'` (R17, `M * M ^ n`) for the path sum, `pow_succ` (R24, `M ^ n * M`) for the trace: the last factor
  must be the closing bond `M (σ (Fin.last n)) (σ 0)`.
- For `i : Fin n`, `i.castSucc` and `i.succ` are the sites `i` and `i + 1` of `Fin (n + 1)`, and `Fin.last n` is
  site `n`; `Fin.cons_succ` only fires on a literal `_.succ`, so rewrite `i.succ.castSucc` and `Fin.last (n + 1)`
  first (R14, right to left).
- `rw [ih]` and `rw [weight_eq]` fail under `∑`: the variable is bound. Use `simp_rw` (R19).
- `simp [hc]` with `hc : c ≠ τ 0` leaves `τ 0 = c` alone; pass `Ne.symm hc` (R22).
- `ring` treats each `∑` as one unknown: it cannot prove `∑ i, a * f i = a * ∑ i, f i`. Pull constants out of the
  sums first (R39).
- A hand-written `Fin.cons x τ` needs its type: `(Fin.cons x τ : Fin (n + 1) → β)`.
- `x✝ : τ ∈ Finset.univ` after R11 is always true; ignore it (`fun τ _ => ?_`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with a `∀`-strong hypothesis | `induction n generalizing a with \| zero => … \| succ n ih => …` | R1 |
| `M ^ 0`, `M ^ (n+1)` | `rw [pow_zero]`, `rw [pow_succ']` (`M * M ^ n`), `rw [pow_succ]` (`M ^ n * M`) | R2, R17, R24 |
| entry of `1`, of `M * N`, of `Matrix.of f` | `Matrix.one_apply`, `Matrix.mul_apply`, `Matrix.of_apply` | R3, R18, R34 |
| trace → diagonal sum | `rw [Matrix.trace]; simp only [Matrix.diag]` | R23 |
| reindex a sum along `e : ι ≃ κ` | `rw [← e.sum_comp]` | R4 |
| `Fin 1 → β` as `β` | `(Equiv.funUnique (Fin 1) β).symm` with R4 | R5 |
| path = first spin + rest | `rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]` | R8, R9 |
| evaluate `Fin.cons` | `simp only [Fin.consEquiv_apply, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ, Fin.castSucc_zero, ← Fin.succ_castSucc]` | R12–R14 |
| peel a product / sum over `Fin (n+1)` | `Fin.prod_univ_succ`, `Fin.sum_univ_succ`, `Fin.sum_univ_castSucc` | R15, R30, R29 |
| swap two sums | `rw [Finset.sum_comm]` | R10 |
| go under a sum | `refine Finset.sum_congr rfl fun i _ => ?_` | R11 |
| sum with one nonzero term | `rw [Finset.sum_eq_single a]` + three goals | R16 |
| rewrite under `∑` | `simp_rw [h]` | R19 |
| constants in/out of sums | `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_div`, `Finset.sum_add_distrib` | R20, R25, R31, R32 |
| `if` arithmetic | `ite_mul`, `zero_mul`, `ite_and`, then `simp` (`Finset.sum_ite_eq`) | R26–R28 |
| split on a condition | `by_cases hb : p <;> simp [hb]` | R21 |
| flip `≠` | `Ne.symm hc` | R22 |
| linear combination of facts | `linarith` | R33 |
| exponentials | `← Real.exp_sum`, `← Real.exp_add`, then `congr 1` | R35–R37 |
| real identity with sums | `simp only [Finset.mul_sum, mul_add, mul_neg, neg_mul, sub_eq_add_neg]`, `ring_nf`, pull sums apart, `ring` | R38, R39 |
| see the state | infoview | |
