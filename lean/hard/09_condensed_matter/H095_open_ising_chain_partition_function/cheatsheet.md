# H095 · Open Ising chain partition function: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's finite sums `∑`, the index
types `Fin n` and the maps `Fin.succ`, `Fin.castSucc`, `Fin.cons`; re-indexing a sum along an
equivalence `≃`; `simp_rw` (rewriting under a binder); `Real.exp`, `Real.cosh`.

The physics: spins `s_i = spin (σ i) ∈ {1, -1}` on sites `0 … n`, energy
`E(σ) = -J ∑_{i<n} s_i s_{i+1}`, partition function `Z = ∑_σ exp(-β E(σ))` over all `2^(n+1)`
configurations `σ : Fin (n + 1) → Bool`. Claim: `Z = 2 (2 cosh βJ)^n`. Proof idea: spin 0 touches only
the bond `(0, 1)`, so summing it out multiplies by `∑_{a = ±1} exp(βJ a s_1) = 2 cosh βJ` whatever
`s_1` is, and the rest is the partition function of the shorter chain.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on `M` (a *type class*): here, a commutative `+` with a `0`, which `ℝ` and `ℕ` meet.
  `[Fintype α]` says `α` is finite, so `∑ a : α` makes sense; `Bool`, `Fin n`, `Fin n → Bool` and
  pairs of finite types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin n` | the type of indices `{0, …, n - 1}`; a site of the chain is `i : Fin (n + 1)` |
| `σ : Fin (n + 1) → Bool` | a configuration: `true` = spin up, `false` = spin down at each site |
| `∑ i, f i` | `Finset.sum Finset.univ f`, the sum over all `i` of a finite type (the type is inferred) |
| `∑ _x, c` | a sum whose terms do not use the index |
| `i.succ` | for `i : Fin n`, the site `i + 1` of `Fin (n + 1)` |
| `i.castSucc`, `Fin.castSucc i` | for `i : Fin n`, the same number `i`, seen as a site of `Fin (n + 1)` |
| `Fin.succ 0`, `Fin.castSucc 0` | sites `1` and `0` (printed this way when `0 : Fin n` is written explicitly) |
| `Fin.cons x p` | the function on `Fin (n + 1)` with value `x` at `0` and `p i` at `i.succ`: prepend a site |
| `Fin.tail σ` | `fun i => σ i.succ`: drop site 0 (the inverse of `Fin.cons`) |
| `e : α ≃ β` | an *equivalence*: a bijection `α → β` with its inverse; `e a` applies it |
| `Fin.consEquiv fun x => α` | the bijection `α × (Fin n → α) ≃ (Fin (n + 1) → α)`, `(x, p) ↦ Fin.cons x p` |
| `(x, y)`, `α × β` | a pair, and the type of pairs |
| `Fintype.card α` | the number of elements of a finite type `α` |
| `Finset.univ.card` | the same number, as the size of the set of all elements |
| `k • c` | `k : ℕ` times `c`, written as repeated addition (`nsmul`) |
| `x✝ : x ∈ Finset.univ` | an unnamed (inaccessible) hypothesis "`x` is in the index set"; always true, ignore it |
| `Real.exp`, `Real.cosh` | `exp`, and `cosh x = (exp x + exp (-x)) / 2` |
| `if b then 1 else -1` (`b : Bool`) | `if b = true then 1 else -1`: a `Bool` used as a condition is compared with `true`; after `simp [spin]` you may meet `false = true`, which `Bool.false_eq_true` turns into `False` (R2) |
| `-J * x`, `-β * energy J σ` | `(-J) * x`: unary minus binds tighter than `*` |
| `noncomputable def` | a definition Lean cannot run as a program (real-number arithmetic is not executable); you can still unfold it and prove things about it |
| `(Fin.cons a σ : Fin (n + 2) → Bool)` | a type ascription: the same term, with its type stated so Lean knows which chain length is meant |
| `case false`, `case true` | the two goals after `cases b` for `b : Bool` (R1) |
| `case inl`, `case inr` | the goals for the left and right alternatives of an `∨` |
| `case zero`, `case succ` | the base case and the step of an induction |

---

## Part 1 · `spin_pm` (milestone)

Statement: `spin b = 1 ∨ spin b = -1`. Two cases of `b`, each decided by unfolding `spin`.

**R1 · `cases b`** changes the **goal list**: for `b : Bool`, one goal per value. Placeholders:
`(P : Bool → Prop) (b : Bool)`.

| Before | After |
|---|---|
| `b : Bool ⊢ P b` | `⊢ P false`, `⊢ P true` |

**R2 · `simp only [D, Bool.false_eq_true, ↓reduceIte]`** changes the **goal**: unfold `D`, decide the
condition `false = true` (`Bool.false_eq_true : (false = true) = False`), and drop the `if`
(`↓reduceIte` reduces `if True then a else b` to `a`, `if False …` to `b`). Plain `simp [D]` does all of
this and also closes `2 = 2 ∨ 2 = 0` (`true_or`). Placeholders: `def D (b : Bool) : ℝ := if b then 2 else 0`.

| Before | After |
|---|---|
| `⊢ P (D false)` | `⊢ P 0` |

**W1** chains them: `cases b <;> simp [D]` proves `D b = 2 ∨ D b = 0`.

---

## Part 2 · `energy_cons` (milestone)

Statement: the energy of `Fin.cons a σ` (spin `a` prepended to `σ`) is the new bond
`-J * (spin a * spin (σ 0))` plus `energy J σ`. Unfold `energy`, split the first bond off the sum
(R3), then evaluate every `Fin.cons` (R4–R7) and close with `ring`.

**R3 · `Fin.sum_univ_succ`** changes the **goal**: `∑ i : Fin (n + 1), f i = f 0 + ∑ i : Fin n, f i.succ`.
Placeholders: `{M : Type} [AddCommMonoid M] (n : ℕ) (f : Fin (n + 1) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + ∑ i, f i.succ)` |

**R4 · `Fin.castSucc_zero`** changes the **goal**: `Fin.castSucc 0 = 0` (site 0 stays site 0; needs
`0` to exist in `Fin n`, true for `Fin (n + 1)`). Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fin.castSucc 0)` | `⊢ P 0` |

**R5 · `Fin.cons_zero`** changes the **goal**: `Fin.cons x p 0 = x`. Placeholders:
`{α : Type} (n : ℕ) (x : α) (p : Fin n → α)`. `rw` works on a lone term, but in `energy_cons` the
sites sit under `∑ i`, where only `simp only` reaches (Traps).

| Before | After |
|---|---|
| `⊢ P (Fin.cons x p 0)` | `⊢ P x` |

**R6 · `← Fin.succ_castSucc`** changes the **goal**. The lemma is `i.castSucc.succ = i.succ.castSucc`
(both are site `i + 1` of `Fin (n + 2)`); right to left it rewrites the site into a `succ`, which is the
form R7 needs. After R3 the bonds of the longer chain read `Fin.cons a σ i.succ.castSucc`. Placeholders:
`(n : ℕ) (i : Fin n)`.

| Before | After |
|---|---|
| `⊢ P i.succ.castSucc` | `⊢ P i.castSucc.succ` |

**R7 · `Fin.cons_succ`** changes the **goal**: `Fin.cons x p i.succ = p i`. Placeholders:
`{α : Type} (n : ℕ) (x : α) (p : Fin n → α) (i : Fin n)`. With `simp only` it also evaluates
`Fin.cons x p (Fin.succ 0)` to `p 0`.

| Before | After |
|---|---|
| `⊢ P (Fin.cons x p i.succ)` | `⊢ P (p i)` |

**W2: the chain R3 → R4–R7 on a sum of `x_i + x_{i+1}`.** After `simp only [Fin.sum_univ_succ]`:

```lean-goal
⊢ Fin.cons x p (Fin.castSucc 0) + Fin.cons x p (Fin.succ 0) + ∑ i, (Fin.cons x p i.succ.castSucc + Fin.cons x p i.succ.succ) = x + p 0 + ∑ i, (p i.castSucc + p i.succ)
```

and `simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]` closes it. In
`energy_cons` the same `simp only` leaves an identity that `ring` closes.

---

## Part 3 · `sum_exp_bond` (milestone)

Statement: for `s = ±1`, `∑ a : Bool, exp (K * (spin a * s)) = 2 * cosh K`. Split on `s` (R8), write
the sum over `Bool` as two terms (R9, `simp` does it), expand `cosh` (R10), close with `ring`.

**R8 · `rcases hs with rfl | rfl`** changes the **context and the goal list**: `hs : s = 1 ∨ s = -1` is
split into its two cases, and `rfl` substitutes `s` away in each. Placeholders: `(s : ℝ)`.

| Before | After |
|---|---|
| `hs : s = 1 ∨ s = -1 ⊢ P s` | `⊢ P 1`, `⊢ P (-1)` |

**R9 · `Fintype.sum_bool`** changes the **goal**: `∑ b : Bool, f b = f true + f false`. Placeholders:
`{M : Type} [AddCommMonoid M] (f : Bool → M)`. `simp` uses its own route (`Fintype.univ_bool`,
`Finset.sum_insert`), with the same result.

| Before | After |
|---|---|
| `⊢ P (∑ b, f b)` | `⊢ P (f true + f false)` |

**R10 · `Real.cosh_eq`** changes the **goal**: `cosh x = (exp x + exp (-x)) / 2`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.cosh x)` | `⊢ P ((Real.exp x + Real.exp (-x)) / 2)` |

After `simp [spin, Real.cosh_eq]` each case is `exp K + exp (-K) = 2 * ((exp K + exp (-K)) / 2)` (or
with the two terms swapped): `ring` closes it, since `/ 2` is multiplication by the number `2⁻¹`.

---

## Part 4 · `Z_eq`

Statement: `Z β J n = 2 * (2 * Real.cosh (β * J)) ^ n`. Induction on `n` (R11).

### Base case: one spin, no bonds

**R11 · `induction n with | zero => ?_ | succ n ih => ?_`** changes the **goal list and the context**: the
base case `n = 0`, and the step with `ih : P n`. Placeholders: `(P : ℕ → Prop) (n : ℕ)`. You can also
write the proofs right after `=>`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `ih : P n ⊢ P (n + 1)` |

`simp [Z, energy]` closes the base case. It applies R12–R15: no bonds, so the energy is `-J * 0 = 0`;
every term is `exp 0 = 1`; the sum of `1` over `Fin 1 → Bool` counts its `2` configurations.

**R12 · `Fin.sum_univ_zero`** changes the **goal**: a sum over `Fin 0` is `0`. Placeholders:
`{M : Type} [AddCommMonoid M] (f : Fin 0 → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P 0` |

**R13 · `Real.exp_zero`** changes the **goal**: `exp 0 = 1`.

| Before | After |
|---|---|
| `⊢ P (Real.exp 0)` | `⊢ P 1` |

**R14 · `Finset.sum_const`, then `Finset.card_univ`** change the **goal**: a sum of a constant is the
number of terms `•` the constant. Placeholders: `{α : Type} [Fintype α] (c : ℝ)`.

| Before | After `rw [Finset.sum_const]` | After `rw [Finset.card_univ]` |
|---|---|---|
| `⊢ P (∑ _x, c)` | `⊢ P (Finset.univ.card • c)` | `⊢ P (Fintype.card α • c)` |

**R15 · `simp`** changes the **goal**: it counts configurations, `Fintype.card (Fin m → Bool) = 2 ^ m`
(via `Fintype.card_pi`, `Fintype.card_bool`, `Finset.prod_const`), and turns `k • c` into `↑k * c`
(`nsmul_eq_mul`). Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Fintype.card (Fin m → Bool))` | `⊢ P (2 ^ m)` |

### Step: summing out spin 0

The step first proves, as a `have`, that `Z β J (n + 1)` equals
`∑ σ, ∑ a, exp (β * J * (spin a * spin (σ 0))) * exp (-β * energy J σ)` (R16–R23 with `energy_cons`),
then factors it (R24–R27) and uses `ih`.

**R16 · `rw [S]`** changes the **goal**: a name defined by `def` is replaced by its body (Lean generated
the equation `S n w = ∑ σ, w σ`). `rw [Z]` does this to the left side only, because the right side has
no `Z`. Placeholders: `noncomputable def S (n : ℕ) (w : (Fin n → Bool) → ℝ) : ℝ := ∑ σ, w σ`.

| Before | After |
|---|---|
| `⊢ P (S n w)` | `⊢ P (∑ σ, w σ)` |

**R17 · `rw [← (Fin.consEquiv fun _ => α).sum_comp]`** changes the **goal**. `Equiv.sum_comp` says that
for a bijection `e : ι ≃ κ`, `∑ i, g (e i) = ∑ i, g i` (re-indexing a sum). Right to left, with
`e = Fin.consEquiv`, a sum over configurations of `n + 1` sites becomes a sum over pairs
(value at site 0, values at the other `n` sites). Placeholders:
`{α M : Type} [Fintype α] [AddCommMonoid M] (n : ℕ) (F : (Fin (n + 1) → α) → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ σ, F σ)` | `⊢ P (∑ i, F ((Fin.consEquiv fun x => α) i))` |

**R18 · `Fintype.sum_prod_type`** changes the **goal**: `∑ x : α × β, F x = ∑ a, ∑ b, F (a, b)`.
Placeholders: `{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α × β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ p, F p)` | `⊢ P (∑ x, ∑ y, F (x, y))` |

**R19 · `Finset.sum_comm`** changes the **goal**: swaps the two sums, so the spin-0 sum `∑ a : Bool` is
inside. Placeholders: `{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (F : α → β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, ∑ b, F a b)` | `⊢ P (∑ y, ∑ x, F x y)` |

**R20 · `refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_`** changes the
**goal and the context**: two double sums over the same index sets are equal when their terms are.
`Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`; `rfl` proves the index sets
equal. Placeholders: `{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f g : α → β → M)`.

| Before | After |
|---|---|
| `⊢ ∑ a, ∑ b, f a b = ∑ a, ∑ b, g a b` | `x : α, x✝¹ : x ∈ Finset.univ, y : β, x✝ : y ∈ Finset.univ ⊢ f x y = g x y` |

**R21 · `show`** changes the **goal** to a definitionally equal one you type. `(Fin.consEquiv _) (x, p)`
*is* `Fin.cons x p`, but the lemmas `Fin.cons_zero`, `Fin.cons_succ` and the milestone `energy_cons`
only match the `Fin.cons` form. Write the type: `(Fin.cons x p : Fin (n + 1) → α)`. Placeholders:
`{α : Type} (n : ℕ) (x : α) (p : Fin n → α) (Q : (Fin (n + 1) → α) → Prop)`.

| Before | After |
|---|---|
| `⊢ Q ((Fin.consEquiv fun x => α) (x, p))` | `⊢ Q (Fin.cons x p)` |

**R22 · `rw [← Real.exp_add]`** changes the **goal**. The lemma is `exp (x + y) = exp x * exp y`; right to
left it merges a product of exponentials. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.exp x * Real.exp y)` | `⊢ P (Real.exp (x + y))` |

**R23 · `ring_nf`** **closes** `exp A = exp B` when `A = B` is a ring identity: it normalizes both
arguments to the same text. `ring` fails here, because it treats `exp A` and `exp B` as two unrelated
unknowns. Example: `exp (-a * (-b * c + d)) = exp (a * b * c + -a * d)`.

### Step: factoring

**R24 · `simp_rw [← Finset.sum_mul]`** changes the **goal**. `Finset.sum_mul : (∑ i, f i) * a = ∑ i, f i * a`;
right to left it pulls a factor that does not depend on the inner index out of the inner sum. The
pattern sits under the outer `∑ a`, which `rw` cannot reach ("Did not find an occurrence of the
pattern"); `simp_rw` can. Placeholders: `{α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) (g : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ a, ∑ b, f a b * g a)` | `⊢ P (∑ x, (∑ i, f x i) * g x)` |

**R25 · `simp_rw [L _ _ (hq _)]`** changes the **goal**: under a binder, rewrite with a lemma
`L : ∀ k x, Q x → f k x = c k` whose hypothesis `Q x` is supplied by `hq : ∀ x, Q x`. Each `_` is filled
anew at every occurrence. In the exercise: `L = sum_exp_bond`, `hq = spin_pm`, so every inner sum
`∑ a, exp (β * J * (spin a * spin (x 0)))` becomes `2 * cosh (β * J)`. Placeholders:
`{α : Type} [Fintype α] (Q : α → Prop) (f : ℝ → α → ℝ) (c : ℝ → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f 2 x)` | `⊢ P (∑ x, c 2)` |

**R26 · `simp_rw [← Finset.mul_sum]`** changes the **goal**. `Finset.mul_sum : a * ∑ i, f i = ∑ i, a * f i`;
right to left it pulls a constant factor out of a sum. Placeholders: `{α : Type} [Fintype α] (f : α → ℝ) (a : ℝ)`.
Plain `rw` works too when the sum is not under a binder.

| Before | After |
|---|---|
| `⊢ P (∑ i, a * f i)` | `⊢ P (a * ∑ i, f i)` |

**R27 · `rw [← S]`** changes the **goal**: the body of a definition is folded back into its name, so a
hypothesis about the name (here `ih : Z β J n = …`) can be used with `rw [ih]`. The body must appear
literally (bound-variable names do not matter). Placeholders: as in R16.

| Before | After |
|---|---|
| `⊢ P (∑ σ, w σ)` | `⊢ P (S n w)` |

Then `rw [ih]` and `ring` (`2c · 2(2c)^n = 2(2c)^(n+1)`).

### Worked combinations (W3, W4, on objects that are not the exercise's)

**W3: summing out the first variable, R17 then R18.** For `∑ σ : Fin (n + 1) → Bool, w (σ 0) * v (Fin.tail σ)`:

```lean-goal
⊢ ∑ σ, w (σ 0) * v (Fin.tail σ) = ∑ a, ∑ τ, w a * v τ
⊢ ∑ x, ∑ y, w ((Fin.consEquiv fun x => Bool) (x, y) 0) * v (Fin.tail ((Fin.consEquiv fun x => Bool) (x, y))) = ∑ a, ∑ τ, w a * v τ
```

The second line is closed by `rfl`: `Fin.consEquiv … (x, y) 0` is `x` and its `Fin.tail` is `y` by
definition.

**W4: factoring a product weight, R19 → R24 → R26.** `∑ a, ∑ τ, w a * v τ = (∑ a, w a) * ∑ τ, v τ` by
`rw [Finset.sum_comm]`, `simp_rw [← Finset.sum_mul]`, `simp_rw [← Finset.mul_sum]`.

---

## Traps

- `i.castSucc` and `i.succ` are different sites: for `i : Fin n`, `i.castSucc` is site `i` and `i.succ` is
  site `i + 1` of `Fin (n + 1)`. In the longer chain, after R3, a site such as `i.succ.castSucc` is not of
  the form `_.succ`, so `Fin.cons_succ` does not fire until R6 rewrites it to `i.castSucc.succ`.
- R4–R7 are needed inside `∑ i, …` with sites that mention `i`: write them in one `simp only [...]`; `rw`
  cannot rewrite there.
- After R17–R19 the term contains `(Fin.consEquiv fun x => Bool) (a, σ)`, not `Fin.cons a σ`; `rw [energy_cons]`
  fails until R21 (`show …`) restates it.
- In `show`, writing the type `(Fin.cons a σ : Fin (n + 2) → Bool)` documents which chain length is meant; the
  `_` on the right side of `show … = _` keeps the rest of the goal as it is.
- `rw` does not rewrite under `∑ x, …` when the pattern mentions `x`: use `simp_rw` (R24–R26).
- `ring` treats `exp A` as an opaque unknown: to compare two exponentials use `ring_nf` (R23), or merge them
  first with R22.
- `rw [← Z]` folds only a sum that is literally the body of `Z` with the same arguments; do it after R26 has
  pulled `2 * cosh (β * J)` out.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| case split on `b : Bool` | `cases b` | R1 |
| evaluate an `if` on `true`/`false` | `simp [D]` | R2 |
| split off the first term of `∑ i : Fin (n + 1)` | `simp only [Fin.sum_univ_succ]` | R3 |
| evaluate `Fin.cons` at sites `0`, `i.succ` | `simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]` | R4–R7 |
| split `s = 1 ∨ s = -1` and substitute | `rcases hs with rfl \| rfl` | R8 |
| sum over `Bool` | `Fintype.sum_bool` (or `simp`) | R9 |
| expand `cosh` | `Real.cosh_eq` | R10 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R11 |
| base case: no bonds, `2` configurations | `simp [Z, energy]` | R12–R15 |
| unfold / fold a `def` | `rw [S]` / `rw [← S]` | R16, R27 |
| sum over `Fin (n + 1) → α` → over (site 0, rest) | `rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]` | R17, R18 |
| swap two sums | `rw [Finset.sum_comm]` | R19 |
| compare double sums term by term | `refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_` | R20 |
| restate a goal in a defeq form | `show …` | R21 |
| `exp x * exp y → exp (x + y)` | `rw [← Real.exp_add]` | R22 |
| `exp A = exp B` with `A = B` by ring | `ring_nf` | R23 |
| pull a factor out of an inner sum | `simp_rw [← Finset.sum_mul]` / `simp_rw [← Finset.mul_sum]` | R24, R26 |
| rewrite under `∑` with a lemma needing a hypothesis | `simp_rw [L _ _ (hq _)]` | R25 |
| see the state | infoview | |
