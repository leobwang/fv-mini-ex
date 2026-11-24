# H096 · Spin correlations in the Ising chain: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). H095 (the partition function `Z`, built with
`Fin.cons`) is related but not required: its result is milestone `Z_eq` here, proved again from scratch.
**New here:** Mathlib's finite sums `∑`, the site types `Fin n` with `castSucc`, `succ`, `last`,
appending a site with `Fin.snoc` and re-indexing a sum by the bijection `Fin.snocEquiv`, `Real.exp`,
`cosh`, `sinh`, `tanh`, and induction from a lower bound (`Nat.le_induction`).

**The physics in one line.** A configuration of the open chain of `n + 1` spins is a function
`σ : Fin (n + 1) → Bool`; site `i` carries `s_i = spin (σ i) ∈ {1, -1}`, the energy is
$E(σ) = -J \sum_{i<n} s_i s_{i+1}$, the Boltzmann weight is $e^{-βE(σ)}$ and
$Z = \sum_σ e^{-βE(σ)}$. With $K = βJ$, appending a site $n+1$ multiplies the weight by
$e^{K s_n s_{n+1}}$, and summing over $s_{n+1} = ±1$ gives

$$\sum_{b} e^{K s b} = 2\cosh K, \qquad \sum_{b} b\, e^{K s b} = 2 \sinh K \cdot s \qquad (s = ±1).$$

So spins beyond site `r` multiply numerator and `Z` by the same $2\cosh K$ (`corr` does not depend on
`n`), and at `n = r` the ratio is $\frac{2(2\sinh K)^r}{2(2\cosh K)^r} = \tanh^r K$.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n` | the type `{0, 1, …, n - 1}`; sites of the chain. `Fin (n + 1)` has `n + 1` sites |
| `σ : Fin (n + 1) → Bool` | a spin configuration: `σ i = true` is up, `false` is down |
| `∑ σ, f σ` | the sum of `f σ` over **all** values of a finite type (`Finset.sum Finset.univ f`) |
| `∑ x ∈ s, f x` | the sum over the finite set `s` only |
| `Finset.univ`, `x✝ : x ∈ Finset.univ` | the finite set of all values; a membership fact that is always true |
| `i.castSucc` | `i : Fin n` seen in `Fin (n + 1)`: the same number, one more site available |
| `i.succ` | `i + 1`, as an element of `Fin (n + 1)` |
| `Fin.last n` | the last site `n` of `Fin (n + 1)` |
| `n.succ` | `n + 1` (some lemmas print it this way) |
| `⟨r, ⋯⟩` | the site `r` of `Fin (n + 1)`, with its proof `r < n + 1` hidden as `⋯` |
| `corr β J (n + 1) r ⋯` | `corr` with its proof argument `r ≤ n + 1` hidden as `⋯` |
| `Fin.snoc p x` | the configuration `p : Fin (n + 1) → α` with value `x` appended at the new last site `n + 1` |
| `A ≃ B` | an equivalence: a bijection `A → B` with its inverse |
| `Fin.snocEquiv fun x => α` | the bijection `α × (Fin (n + 1) → α) ≃ (Fin (n + 2) → α)`, `(x, p) ↦ Fin.snoc p x` |
| `(x, p)`, `α × β` | a pair; the type of pairs |
| `Fintype.card α`, `Finset.univ.card` | the number of elements of `α` |
| `k • c` | `c + … + c` (`k` copies), for `k : ℕ`; `simp` turns it into `↑k * c` (`↑k`: `k` cast to `ℝ`) |
| `Real.exp`, `Real.cosh`, `Real.sinh`, `Real.tanh` | $e^x$, $\cosh x = \frac{e^x + e^{-x}}{2}$, $\sinh x = \frac{e^x - e^{-x}}{2}$, $\tanh = \sinh / \cosh$ |
| `if b = true then … else …` | how `if b then … else …` prints after `simp` |
| `n✝`, `x✝`, `hmn✝`, `a✝` | inaccessible names: Lean made them, you cannot type them (name them with `with`, `rename_i`, `fun x _ =>`) |
| `case base`, `case succ`, `case inl` | the label of a goal produced by a case split |

---

## Part 1 · `snoc_split`

Statement: a sum over chains of `n + 2` spins, of `f (first n + 1 spins) (last spin) · e^{-βE}`, equals a
sum over chains `τ` of `n + 1` spins of `(∑ b, f τ b · e^{K s_n b}) · e^{-βE(τ)}`. It is the one place where
a configuration is split into "old chain + new spin".

**First prove a helper** (statement in hint H2): `energy_snoc`, the energy of `Fin.snoc σ b` is
`energy J σ - J * (spin (σ (Fin.last n)) * spin b)`. Unfold `energy`, split the last bond off with R1,
then evaluate every `Fin.snoc …` at a `castSucc` or `last` site with R2–R5 in **one** `simp only [...]`
(the sites sit under `∑ i`, where `rw` fails), and close with `ring`.

### Sites of a longer chain

**R1 · `rw [Fin.sum_univ_castSucc]`** changes the **goal**: a sum over `Fin (n + 1)` becomes the sum over
the first `n` sites plus the last term. Lemma: `∑ i, f i = ∑ i : Fin n, f i.castSucc + f (Fin.last n)`.
Placeholders: `{M : Type} [AddCommMonoid M]` (a commutative `+` with `0`: `ℕ`, `ℝ`, `ℂ`),
`(n : ℕ) (f : Fin (n + 1) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ i, f i.castSucc + f (Fin.last n))` |

**R2 · `simp only [Fin.succ_castSucc]`** changes the **goal**: `i.castSucc.succ = i.succ.castSucc` (both
are `i + 1`; the second form is a `castSucc`, so R3 applies to it). In `energy_snoc` these sites sit under
`∑ i`, and `rw [Fin.succ_castSucc]` fails there ("did not find an occurrence"): the instance mentions the
bound `i`. `simp only` rewrites under the binder. Placeholders: `{M : Type} [AddCommMonoid M] (n : ℕ)
(f : Fin (n + 2) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i.castSucc.succ)` | `⊢ P (∑ x, f x.succ.castSucc)` |

**R3 · `simp only [Fin.snoc_castSucc]`** changes the **goal**: the appended configuration at an old site is
the old value. Lemma: `Fin.snoc p x i.castSucc = p i`. Placeholders:
`{α : Type} (n : ℕ) (p : Fin (n + 1) → α) (x : α) (i : Fin (n + 1))`.

| Before | After |
|---|---|
| `⊢ P (Fin.snoc p x i.castSucc)` | `⊢ P (p i)` |

**R4 · `simp only [Fin.succ_last]`** changes the **goal**: `(Fin.last n).succ = Fin.last (n + 1)`, printed with
`n.succ`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fin.last n).succ` | `⊢ P (Fin.last n.succ)` |

**R5 · `simp only [Fin.snoc_last]`** changes the **goal**: the appended configuration at the new last site
is the appended value. Lemma: `Fin.snoc p x (Fin.last n) = x`. Placeholders as in R3.

| Before | After |
|---|---|
| `⊢ P (Fin.snoc p x (Fin.last (n + 1)))` | `⊢ P x` |

### Re-indexing the sum over configurations

**R6 · `rw [← (Fin.snocEquiv fun _ => α).sum_comp]`** changes the **goal**: a sum over configurations of
`n + 2` sites becomes a sum over pairs (last value, first `n + 1` values). `Equiv.sum_comp` says
`∑ i, g (e i) = ∑ i, g i` for a bijection `e`; right to left it inserts `e`. Placeholders:
`{α M : Type} [Fintype α] [AddCommMonoid M]` (`α` finite, as `Bool`),
`(n : ℕ) (F : (Fin (n + 2) → α) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ σ, F σ)` | `⊢ P (∑ i, F ((Fin.snocEquiv fun x => α) i))` |

**R7 · `rw [Fintype.sum_prod_type]`** changes the **goal**: a sum over pairs becomes a double sum,
first component outside. Placeholders: `{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M]`,
`(F : α × β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ p, F p)` | `⊢ P (∑ x, ∑ y, F (x, y))` |

**R8 · `rw [Finset.sum_comm]`** changes the **goal**: the two sums swap. After R6, R7 the outer sum is over
the new spin; R8 puts the old chain `τ` outside, as the right-hand side wants. Placeholders:
`(F : α → β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, ∑ b, F a b)` | `⊢ P (∑ y, ∑ x, F x y)` |

**R9 · `refine Finset.sum_congr rfl fun x _ => ?_`** changes the **goal and the context**: an equation
of two sums over the same set becomes an equation of their terms, for an arbitrary `x`. Lemma:
`s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`. Placeholders: `(f g : α → M)`.

| Before | After |
|---|---|
| `⊢ ∑ a, f a = ∑ a, g a` | `x : α, x✝ : x ∈ Finset.univ ⊢ f x = g x` |

**R10 · `rw [Finset.sum_mul]`** changes the **goal**: a sum times a factor becomes a sum of products.
Lemma: `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`. Placeholders: `{R : Type} [Semiring R]` (`+`, `*`
with distributivity: `ℕ`, `ℝ`, `ℂ`), `(f : α → R) (a : R)`. Use it on the right-hand side before the
second R9, so that both sides are sums over `b`.

| Before | After |
|---|---|
| `⊢ P ((∑ i, f i) * a)` | `⊢ P (∑ i, f i * a)` |

**R11 · `show`** changes the **goal** to a definitionally equal form you write out.
`(Fin.snocEquiv _) (x, p)` *is* `Fin.snoc p x`, but R3 and R5 only match the second spelling. Write the
type ascription `(Fin.snoc p x : Fin (n + 2) → α)`, or Lean cannot infer the family of `Fin.snoc`.
(`simp only [Fin.snocEquiv_apply]` is no substitute here: in `snoc_split` it rewrites the arguments of
`f` but leaves `energy J ((Fin.snocEquiv fun x => Bool) (b, τ))`, so `energy_snoc` never matches.) Placeholders:
`{α : Type} (n : ℕ) (x : α) (p : Fin (n + 1) → α)`.

| Before | After |
|---|---|
| `⊢ Q ((Fin.snocEquiv fun x => α) (x, p))` | `⊢ Q (Fin.snoc p x)` |

**R12 · `rw [mul_assoc]`** changes the **goal**: `a * b * c = a * (b * c)` (`*` groups to the left).
Placeholders: `{α : Type} [Semigroup α]` (an associative `*`: `ℕ`, `ℝ`, `ℂ`), `(a b c : α)`. With an
argument, `mul_assoc a` moves only products that start with `a`.

| Before | After |
|---|---|
| `⊢ P (a * b * c)` | `⊢ P (a * (b * c))` |

**R13 · `rw [← Real.exp_add]`** changes the **goal**: two exponentials merge. Lemma:
`Real.exp (x + y) = Real.exp x * Real.exp y`. Placeholders: `(x y : ℝ)`. R12 first, so that the two
`exp` factors are adjacent.

| Before | After |
|---|---|
| `⊢ P (Real.exp x * Real.exp y)` | `⊢ P (Real.exp (x + y))` |

**R14 · `ring_nf`** **closes** an equation that is a ring identity once the arguments of `Real.exp` are
normalized too. `ring` treats `Real.exp (a - b)` and `Real.exp (-b + a)` as two unrelated unknowns and
fails ("Try this: ring_nf"); `ring_nf` rewrites inside them first. Example:
`c * Real.exp (a - b) = Real.exp (-b + a) * c`. At the end of `snoc_split` the term is
`f (fun i => τ i) b * exp (-β * (E - J * (s * b)))` against `f τ b * exp (β * J * (s * b) + -β * E)`.

### Worked combination (W1)

**W1** sums out the last site of an observable `g` that ignores it, `∑ σ, g (σ ∘ castSucc) = 2 * ∑ τ, g τ`:
R6, R7, R8, R21, R9, R17, R11, R3, `ring`. The goals:

```lean-goal
⊢ (∑ σ, g fun i => σ i.castSucc) = 2 * ∑ τ, g τ
⊢ (∑ y, ∑ x, g fun i => (Fin.snocEquiv fun x => Bool) (x, y) i.castSucc) = ∑ i, 2 * g i
⊢ (∑ x, g fun i => (Fin.snocEquiv fun x => Bool) (x, τ) i.castSucc) = 2 * g τ
⊢ ((g fun i => Fin.snoc τ true i.castSucc) + g fun i => Fin.snoc τ false i.castSucc) = 2 * g τ
⊢ ((g fun i => τ i) + g fun i => τ i) = 2 * g τ
```

`fun i => τ i` is `τ` (eta), and `ring` sees that.

---

## Part 2 · `sum_snoc`

Statement: for an observable `g` of the first `n + 1` spins,
`∑ σ, g (σ ∘ castSucc) · e^{-βE(σ)} = 2 cosh(βJ) · ∑ τ, g τ · e^{-βE(τ)}`.
Specialize `snoc_split` with `f := fun τ _ => g τ` (R20), push the factor `2 cosh` inside the sum (R21),
compare term by term (R9), pull `g τ` out of the `Bool` sum (R21 right to left), and use the helper
`sum_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) : ∑ b : Bool, Real.exp (K * (s * spin b)) = 2 * Real.cosh K`,
applied with `s := spin (τ (Fin.last n))` and the helper `spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1`.

**R15 · `cases b`** (for `b : Bool`) changes the **goal list and the context**: `b` leaves, one goal per
value. Proves `spin_pm` with `cases b <;> simp [spin]`. Placeholders: `(P : Bool → Prop) (b : Bool)`.

| Before | After |
|---|---|
| `b : Bool ⊢ P b` | `⊢ P false`, `⊢ P true` |

**R16 · `rcases hs with rfl | rfl`** changes the **goal list and the context**: `hs : s = 1 ∨ s = -1`
splits, and `rfl` substitutes the value for `s` everywhere (so `s` and `hs` leave). Placeholders:
`(s : ℝ) (P : ℝ → Prop)`. Proves the `Bool`-sum helpers with `rcases hs with rfl | rfl <;> simp [spin, R18] <;> ring`.

| Before | After |
|---|---|
| `hs : s = 1 ∨ s = -1 ⊢ P s` | `⊢ P 1`, `⊢ P (-1)` |

**R17 · `rw [Fintype.sum_bool]`** changes the **goal**: a sum over `Bool` has two terms. Lemma:
`∑ b, f b = f true + f false`. `simp` applies it by itself. Placeholders:
`{M : Type} [AddCommMonoid M] (f : Bool → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ b, f b)` | `⊢ P (f true + f false)` |

**R18 · `Real.cosh_eq`** changes the **goal**: `cosh x = (exp x + exp (-x)) / 2`. Give it to `simp`, so that
both sides are in terms of `exp`, then `ring`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.cosh x)` | `⊢ P ((Real.exp x + Real.exp (-x)) / 2)` |

**R19 · `Real.sinh_eq`** changes the **goal**: `sinh x = (exp x - exp (-x)) / 2`. Used for the
`sum_spin_exp_bond` helper of Part 4. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.sinh x)` | `⊢ P ((Real.exp x - Real.exp (-x)) / 2)` |

**R20 · `rw [L (fun a _ => g a)]`** changes the **goal**: a lemma `L` about every function `f` is used after
choosing `f`. Lean beta-reduces `(fun a _ => g a) a true` to `g a`, so the instantiated left side matches
your goal. Placeholders: `{α : Type} [Fintype α] (g : α → ℝ)` and a lemma
`L : ∀ f : α → Bool → ℝ, ∑ a, f a true = ∑ a, ∑ b, f a b`. The same move: `rw [snoc_split β J n (fun τ _ => g τ)]`.

| Before | After |
|---|---|
| `⊢ P (∑ a, g a)` | `⊢ P (∑ a, ∑ b, g a)` |

**R21 · `rw [Finset.mul_sum]`** changes the **goal**: a factor in front of a sum goes inside. Lemma:
`a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`; `rw [← Finset.mul_sum]` pulls a common left factor back out.
Placeholders: `{R : Type} [Semiring R] (f : α → R) (a : R)`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**W2** (guide) has the `±1` pattern on other statements: `s * s = 1` by `rcases hs with rfl | rfl <;> norm_num`,
and `∑ b : Bool, exp (if b then K else -K) = 2 cosh K`, where `simp [Real.cosh_eq]` leaves

```lean-goal
⊢ Real.exp K + Real.exp (-K) = 2 * ((Real.exp K + Real.exp (-K)) / 2)
```

and `ring` closes it.

---

## Part 3 · `Z_eq`

Statement: `Z β J n = 2 * (2 * cosh (βJ)) ^ n`. Induction on `n`. Base: `simp [Z, energy]` (a chain of one
spin has no bonds, R22, and two configurations, R23). Step: `have h := sum_snoc β J n (fun _ => 1)`, clean
`h` with R24, then `rw [Z, h, ← Z, ih]` (R25) and `ring`.

**R22 · `Fin.sum_univ_zero`** changes the **goal**: a sum over `Fin 0` is `0`. In `energy` of a one-spin
chain the bond sum is over `Fin 0`. `simp` applies it by itself. Placeholders: `(f : Fin 0 → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P 0` |

**R23 · `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fun`, then `simp`** change the **goal**: a
constant sum is (number of terms) • value, and there are `2 ^ 1` functions `Fin 1 → Bool`. `simp` does all
of it by itself. Placeholders: `(c : ℝ)`.

| Before | After `rw [Finset.sum_const]` | After `rw [Finset.card_univ]` | After `rw [Fintype.card_fun]` | After `simp` |
|---|---|---|---|---|
| `⊢ P (∑ _σ, c)` | `⊢ P (Finset.univ.card • c)` | `⊢ P (Fintype.card (Fin 1 → Bool) • c)` | `⊢ P (Fintype.card Bool ^ Fintype.card (Fin 1) • c)` | `⊢ P (2 * c)` |

**R24 · `simp only [one_mul] at h`** changes the **context**: `h` is rewritten, the goal is not.
`sum_snoc` with `g := fun _ => 1` has `1 * exp …` terms inside its sums; `Z` has none, and `simp only`
rewrites under the `∑` binder. Placeholders: `(a : ℝ) (P : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : P (1 * a) ⊢ P a` | `h : P a ⊢ P a` |

**R25 · `rw [D]`, `rw [← D]`** change the **goal**: `rw [D]` replaces the defined name `D` by its body;
`rw [← D]` turns a copy of the body back into the name, so that a hypothesis about the name (`ih`) applies.
Placeholders: `def T (n : ℕ) : ℕ := 2 ^ n` and `e : 2 ^ (n + 1) = 2 ^ n * 2`.

| Before | After `rw [T]` | After `rw [e]` | After `rw [← T]` |
|---|---|---|---|
| `⊢ P (T (n + 1))` | `⊢ P (2 ^ (n + 1))` | `⊢ P (2 ^ n * 2)` | `⊢ P (T n * 2)` |

---

## Part 4 · `G_eq`

Statement: `∑ σ, s₀ s_n e^{-βE(σ)} = 2 * (2 * sinh (βJ)) ^ n`, the end-to-end numerator. Induction on `n`.
Base: `simp [energy, spin_mul_self]` with the helper `spin_mul_self (b : Bool) : spin b * spin b = 1`.
Step: `have h := snoc_split β J n (fun τ b => spin (τ 0) * spin b)`, fix `Fin.castSucc 0` in `h` (R26),
then `rw [h, pow_succ, ← mul_assoc, ← ih, Finset.sum_mul]` (R27, R12 backwards, R10), R9, and inside the term
`simp_rw` (R28) with `mul_assoc (spin (τ 0))`, `← Finset.mul_sum` and the helper
`sum_spin_exp_bond (K s : ℝ) (hs : s = 1 ∨ s = -1) : ∑ b : Bool, spin b * Real.exp (K * (s * spin b)) = 2 * Real.sinh K * s`;
`ring` closes.

**R26 · `simp only [Fin.castSucc_zero] at h`** changes the **context**: site `0` of the short chain, seen in
the long chain, is site `0`. Lemma: `Fin.castSucc 0 = 0`. Placeholders: `(n : ℕ) (P : Fin (n + 2) → Prop)`.

| Before | After |
|---|---|
| `h : P (Fin.castSucc 0) ⊢ P 0` | `h : P 0 ⊢ P 0` |

**R27 · `rw [pow_succ]`** changes the **goal**: `a ^ (n + 1) = a ^ n * a`. Placeholders:
`{M : Type} [Monoid M] (a : M) (n : ℕ)` (an associative `*` with `1`: `ℕ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (a ^ (n + 1))` | `⊢ P (a ^ n * a)` |

**R28 · `simp_rw [mul_assoc c]`, `simp_rw [← Finset.mul_sum]`** change the **goal** under a binder.
`rw` cannot rewrite `c * f b * g b` inside `∑ b, …`, because the instance mentions the bound `b`;
`simp_rw` can. Placeholders: `(c : ℝ) (f g : Bool → ℝ)`.

| Before | After `simp_rw [mul_assoc c]` | After `simp_rw [← Finset.mul_sum]` |
|---|---|---|
| `⊢ P (∑ b, c * f b * g b)` | `⊢ P (∑ x, c * (f x * g x))` | `⊢ P (c * ∑ i, f i * g i)` |

---

## Part 5 · `corr_succ`

Statement: `corr β J (n + 1) r _ = corr β J n r hr`: one more spin beyond `r` changes nothing. State the
numerator fact with its type written out, `have h1 : ∑ σ : Fin (n + 2) → Bool, … = 2 * Real.cosh (β * J) * ∑ σ : Fin (n + 1) → Bool, … := sum_snoc β J n (fun τ => spin (τ 0) * spin (τ ⟨r, by omega⟩))`,
get the `Z` fact as in Part 3 (`h2`, R24), prove `hc : 2 * Real.cosh (β * J) ≠ 0` (R29), then
`rw [corr, corr, h1, Z, h2, ← Z]` and cancel with R30.

**R29 · `positivity`** **closes** a goal `0 < e`, `0 ≤ e` or `e ≠ 0` when `e` is built by `*`, `+`, `^` from
pieces Mathlib knows are positive (numerals, `Real.exp`, `Real.cosh`, squares). Example:
`0 < 3 * Real.cosh x * Real.exp x`.

**R30 · `rw [mul_div_mul_left _ _ hc]`** changes the **goal**: a common left factor of numerator and
denominator cancels. Lemma: `c ≠ 0 → c * a / (c * b) = a / b`. Placeholders: `(a b c : ℝ) (hc : c ≠ 0)`
(any field: `ℝ`, `ℂ`, `ℚ`).

| Before | After |
|---|---|
| `hc : c ≠ 0 ⊢ P (c * a / (c * b))` | `⊢ P (a / b)` |

---

## Part 6 · `corr_eq`

Statement: `corr β J n r hr = tanh (βJ) ^ r` for every `r ≤ n`. Induction on `n` starting at `r` (R31).
Base `n = r`: `rw [corr]`, turn the site `⟨r, _⟩` into `Fin.last r` (R32) so `G_eq` applies, then
`rw [G_eq, Z_eq, Real.tanh_eq_sinh_div_cosh, div_pow]` (R33, R34), `have hc` (R35), `field_simp` (R36),
`ring`. Step: `rw [corr_succ β J n r hrn, ih]`.

**R31 · `induction n, hr using Nat.le_induction`** changes the **goal list and the context**: a goal about
every `n ≥ r` becomes the base case `n = r` and the step `n → n + 1` (with `hrn : r ≤ n` and the induction
hypothesis `ih`). Lemma: `Nat.le_induction : P m _ → (∀ n (h : m ≤ n), P n h → P (n + 1) _) → ∀ n (h : m ≤ n), P n h`.
Placeholders: `(r n : ℕ) (hr : r ≤ n) (Q : ℕ → Prop)`. The guide names the step's variables with
`rename_i n hrn ih`; in your proof write
`induction n, hr using Nat.le_induction with | base => … | succ n hrn ih => …` (W3).

| Before | After |
|---|---|
| `hr : r ≤ n ⊢ Q n` | `⊢ Q r`, `hrn : r ≤ n, ih : Q n ⊢ Q (n + 1)` |

**R32 · `rw [show (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r from rfl]`** changes the **goal**: it replaces
a term by a definitionally equal one, here the site `⟨r, _⟩` by `Fin.last r`, so that a lemma stated with
`Fin.last` (`G_eq`) matches. Placeholders: `(r : ℕ) (P : Fin (r + 1) → Prop)`.

| Before | After |
|---|---|
| `⊢ P ⟨r, ⋯⟩` | `⊢ P (Fin.last r)` |

**R33 · `rw [Real.tanh_eq_sinh_div_cosh]`** changes the **goal**: `tanh x = sinh x / cosh x`. Placeholders:
`(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.tanh x)` | `⊢ P (Real.sinh x / Real.cosh x)` |

**R34 · `rw [div_pow]`** changes the **goal**: `(a / b) ^ k = a ^ k / b ^ k`. Placeholders:
`{α : Type} [DivisionCommMonoid α] (a b : α) (k : ℕ)` (commutative `*` with `⁻¹`: `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P ((a / b) ^ k)` | `⊢ P (a ^ k / b ^ k)` |

**R35 · `have hc := Real.cosh_pos x`** changes the **context**: `Real.cosh_pos x : 0 < Real.cosh x`.
Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `hc : 0 < Real.cosh x ⊢ G` |

**R36 · `field_simp`** changes the **goal**: it multiplies out every denominator it can show is nonzero,
leaving an equation without `/` for `ring`. It uses `c ≠ 0` or `0 < c` from the context (it also knows
`cosh x ≠ 0` by itself, but `hc` is the safe habit). Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `hc : 0 < c ⊢ a = b / c` | `⊢ a * c = b` |

**W4** (guide) runs R33, R34, R35, R36 on `sinh x ^ 3 * 5 / (5 * cosh x ^ 3) = tanh x ^ 3`. After R33, R34:

```lean-goal
⊢ Real.sinh x ^ 3 * 5 / (5 * Real.cosh x ^ 3) = Real.sinh x ^ 3 / Real.cosh x ^ 3
```

and `field_simp` closes it. In `corr_eq` it leaves a polynomial identity in `sinh` and `cosh` for `ring`.

**W3** (guide) is the shape of the whole argument on a simpler object: if `f (n + 1) = f n` for all `n`,
then `f n = f r` for `n ≥ r`, by `induction n, hr using Nat.le_induction with` and the alternatives
`| base => rfl`, `| succ n hrn ih => rw [hf, ih]`.

---

## Traps

- `Fin.snoc σ b` appends spin `b` after site `n`. Write it as `(Fin.snoc σ b : Fin (n + 2) → Bool)` so Lean
  knows the family of types (R11).
- After R6, the goal shows `(Fin.snocEquiv fun x => Bool) (b, τ)`, not `Fin.snoc τ b`. `simp only
  [Fin.snoc_castSucc, Fin.snoc_last]` does nothing until you `show` the `Fin.snoc` form (R11).
- `Fin.succ_last` prints its result as `Fin.last n.succ`; `simp only [Fin.snoc_last]` still matches it.
- `rw [G_eq]` fails on `σ ⟨r, ⋯⟩`: the lemma says `σ (Fin.last n)`. Rewrite the site first (R32).
- `rw` does not rewrite under `∑ b, …` when the pattern mentions `b`: use `simp_rw` (R28).
- `ring` fails when two `Real.exp` arguments are equal only after algebra; use `ring_nf` (R14).
- In `corr_succ`, write the type of `h1` out. `have h1 := sum_snoc … (fun τ => …)` alone gives
  `spin ((fun i => σ i.castSucc) ⟨r, ⋯⟩)` inside `h1`, which `rw [h1]` does not find in `corr`; the written
  type `spin (σ ⟨r, by omega⟩)` is accepted because it is definitionally equal.
- After `induction n, hr using Nat.le_induction with … | succ n hrn ih`, the context also shows a stale
  `n✝ : ℕ` (the old `n`); ignore it.
- `t1 ; t2` runs `t2` on the first goal only. After `cases` / `rcases … with rfl | rfl`, use `<;>`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split off the last term of `∑ i : Fin (n + 1)` | `rw [Fin.sum_univ_castSucc]` | R1 |
| evaluate `Fin.snoc p x` at old / new site | `simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]` | R2–R5 |
| sum over `Fin (n + 2) → α` → pairs | `rw [← (Fin.snocEquiv fun _ => α).sum_comp]` | R6 |
| pairs → double sum, swap | `rw [Fintype.sum_prod_type, Finset.sum_comm]` | R7, R8 |
| compare two sums term by term | `refine Finset.sum_congr rfl fun x _ => ?_` | R9 |
| factor into / out of a sum | `rw [Finset.sum_mul]`, `rw [Finset.mul_sum]`, `rw [← Finset.mul_sum]` | R10, R21 |
| `snocEquiv (b, τ)` → `Fin.snoc τ b` | `show … (Fin.snoc τ b : Fin (n + 2) → Bool) …` | R11 |
| regroup, merge exponentials | `rw [mul_assoc, ← Real.exp_add]` | R12, R13 |
| close up to algebra inside `exp` | `ring_nf` | R14 |
| `b : Bool` / `s = ±1` cases | `cases b <;> simp [spin]` / `rcases hs with rfl \| rfl <;> simp [spin, Real.cosh_eq] <;> ring` | R15–R18 |
| `cosh`, `sinh`, `tanh` in `exp` / ratio form | `Real.cosh_eq`, `Real.sinh_eq`, `Real.tanh_eq_sinh_div_cosh` | R18, R19, R33 |
| use a milestone for a chosen `f` | `rw [snoc_split β J n (fun τ _ => g τ)]`, `have h := …` | R20 |
| base case of a chain | `simp [Z, energy]` | R22, R23 |
| clean a hypothesis | `simp only [one_mul] at h` | R24 |
| unfold / fold a definition | `rw [Z, h, ← Z, ih]` | R25 |
| `Fin.castSucc 0` → `0` | `simp only [Fin.castSucc_zero] at h` | R26 |
| `a ^ (n + 1)` → `a ^ n * a` | `rw [pow_succ]` | R27 |
| rewrite under `∑ b, …` | `simp_rw [mul_assoc c, ← Finset.mul_sum]` | R28 |
| `2 * Real.cosh x ≠ 0` | `by positivity` | R29 |
| cancel a common factor | `rw [mul_div_mul_left _ _ hc]` | R30 |
| induction from `n = r` | `induction n, hr using Nat.le_induction with \| base => … \| succ n hrn ih => …` | R31 |
| `⟨r, _⟩` → `Fin.last r` | `rw [show (⟨r, by omega⟩ : Fin (r + 1)) = Fin.last r from rfl]` | R32 |
| `(a / b) ^ k` | `rw [div_pow]` | R34 |
| clear denominators | `have hc := Real.cosh_pos _`, `field_simp`, `ring` | R35, R36 |
| see the state | infoview | |
