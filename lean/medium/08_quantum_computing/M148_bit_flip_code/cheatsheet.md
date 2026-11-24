# M148 · Three-qubit bit-flip code: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's finite sums `∑` (over a
`Fintype`, over a `Finset`, and of functions), scalar multiplication `•` on functions, `Option`
case splits, `fin_cases` on `Fin 3`, `simp_rw`, `split_ifs`, and the physics of syndrome decoding.

**The physics in one paragraph.** A 3-qubit state is a vector of 8 complex amplitudes, one per basis
label `|abc⟩` with bits `a b c ∈ {0, 1}`. The code state is `enc α β = α|000⟩ + β|111⟩`. A bit flip
`X_k` on qubit `k` permutes the labels (`|abc⟩ ↦` the label with bit `k` negated); `err e v` applies it
(`e = none`: no error). The **syndrome** of a label is the pair of parities
`synd(abc) = (a ⊕ b, b ⊕ c)`, where `⊕` is XOR. `proj σ` is the **projector** onto the labels with
syndrome `σ` (it zeroes every other amplitude). `guess σ` names the flip that produced syndrome `σ`,
and `decode = ∑_σ C_σ P_σ` (with `P_σ = proj σ` and `C_σ = err (guess σ)`) measures and corrects.
Theorem 1: `decode (X_e (enc α β)) = enc α β` for each of the 4 errors. Theorem 2: `decode` is linear,
so it also corrects any superposition `∑_e c_e X_e`, returning `(∑_e c_e) · enc α β`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[AddCommMonoid M]`
  is a requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℂ` | Mathlib's complex numbers (`Complex`) |
| `Q3` | `Fin 2 × Fin 2 × Fin 2`, the 8 basis labels. `abbrev` makes it unfold silently |
| `(a, b, c)` | a label; `×` nests to the right, so it is `(a, (b, c))` |
| `p.1`, `p.2.1`, `p.2.2` | the three bits of `p`: first, second, third |
| `Q3 → ℂ` | a state vector: one complex amplitude per label |
| `a + b` on `Fin 2` | addition mod 2, i.e. XOR: `1 + 1 = 0` |
| `Option (Fin 3)` | either `none` (no error) or `some k` with `k ∈ {0, 1, 2}` |
| `∑ x, f x` | `∑ x ∈ Finset.univ, f x`: the sum over every element of a finite type (`Fintype`). `Finset.univ` is the finite set of all elements, so `σ ∈ Finset.univ` (from R17) is always true |
| `∑ c ∈ s, f c` | the sum over a finite set `s : Finset ι` |
| `∑ σ, F σ` with `F σ : Q3 → ℂ` | a sum of **functions**, computed pointwise: `(∑ σ, F σ) p = ∑ σ, F σ p` (R7) |
| `c • v` with `v : Q3 → ℂ` | the scalar `c` times every amplitude of `v` (R10) |
| `(fun i => i) ⟨0, ⋯⟩` | the index `0`, printed this way after `fin_cases` |
| `match … with \| none, p => p \| …` | `flip` unfolded before its argument is known; `simp` evaluates it once the labels are concrete |
| `inst✝ : Fintype ι` | an unnamed type-class hypothesis (here: `ι` is finite) |
| `x✝`, `h✝` | hypotheses with no name you can type; name them (`fun σ hσ => ?_`, `split_ifs with h`) to use them |
| `c_1`, `x_1` | a bound variable renamed because the name `c` (or `x`) is already taken; only printing |
| `case some.«1»` | the goal for `e = some 1` |
| `case pos`, `case neg` | after `split_ifs` (R18): the goal where the `if` condition holds, and the one where it fails |
| `synd (flip (guess x) p) = x` | the `if` condition of `proj` after unfolding: the label `flip (guess x) p` has syndrome `x` |

---

## Part 1 · `corrects`

Statement: `decode (err e (enc α β)) = enc α β` for every `e : Option (Fin 3)`. Both sides are
functions `Q3 → ℂ`. It is a finite check: 4 errors × 8 labels = 32 equations of complex numbers, each
closed by evaluating everything with `simp`.

### Splitting into finitely many cases

**R1 · `funext ⟨a, b, c⟩`** changes the **goal and the context**: two functions are equal when they agree
at every point, and the pattern `⟨a, b, c⟩` names the three components of the point at once.
Placeholders: `{α β γ δ : Type} (f g : α × β × γ → δ)`. Plain `funext p` keeps the point as one `p`.

| Before | After |
|---|---|
| `⊢ f = g` | `a : α, b : β, c : γ ⊢ f (a, b, c) = g (a, b, c)` |

**R2 · `rcases e with _ | e`** changes the **goal list and the context**: one goal per constructor of
`Option`. The `none` alternative binds nothing (`_`); the `some` alternative names its argument `e`.
Placeholders: `{α : Type} (P : Option α → Prop) (e : Option α)`.

| Before | After |
|---|---|
| `e : Option α ⊢ P e` | `⊢ P none`, `e : α ⊢ P (some e)` |

**R3 · `fin_cases e`** changes the **goal list and the context**: `e : Fin 3` leaves the context and there is
one goal per value `0, 1, 2`. Placeholders: `(P : Fin 3 → Prop) (e : Fin 3)`. On `a : Fin 2` it gives
two goals (TACTIC_STATES).

| Before | After |
|---|---|
| `e : Fin 3 ⊢ P e` | `⊢ P ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨2, ⋯⟩)` |

**R4 · `all_goals (try fin_cases e)`** changes the **goal list**: `all_goals t` runs `t` on every goal, and
`try t` turns a failure of `t` into "do nothing". After R2 the `none` goal has no `e`, so a bare
`all_goals fin_cases e` would fail there. Placeholders: `(P : Option (Fin 3) → Prop)`.

| Before | After |
|---|---|
| `⊢ P none`, `e : Fin 3 ⊢ P (some e)` | `⊢ P none`, `⊢ P (some ((fun i => i) ⟨0, ⋯⟩))`, `⊢ P (some ((fun i => i) ⟨1, ⋯⟩))`, `⊢ P (some ((fun i => i) ⟨2, ⋯⟩))` |

Then split the label: `fin_cases a <;> fin_cases b <;> fin_cases c` gives 8 goals per error
(TACTIC_STATES, "Extensionality and finite case splits").

### Evaluating one case with `simp`

`decode` is a sum over the 4 syndromes `σ : Fin 2 × Fin 2`. `simp` evaluates it only if you give it the
definitions **and** R5, R6 to expand that sum into 4 terms; R7–R9 it applies by itself. Do not step
through the intermediate goals: unfolded, one case fills pages (nested `match` and `if`). One call
`simp [defs…, R5, R6]` per case is the intended move.

**R5 · `Fintype.sum_prod_type`** changes the **goal**: a sum over pairs becomes a double sum,
$\sum_{p \in \alpha\times\beta} f(p) = \sum_x \sum_y f(x, y)$. Placeholders:
`{α β M : Type} [Fintype α] [Fintype β] [AddCommMonoid M] (f : α × β → M)`. `Fintype` means finite (every
`Fin n` and products of them); `AddCommMonoid` means a commutative `+` with `0` (`ℂ`, and also `Q3 → ℂ`).

| Before | After |
|---|---|
| `⊢ P (∑ p, f p)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R6 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`. R5 then R6 twice turn `∑ σ : Fin 2 × Fin 2` into 4 terms.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R7 · `Finset.sum_apply`** changes the **goal**: a sum of functions evaluated at a point is the sum of the
values, `(∑ c ∈ s, g c) a = ∑ c ∈ s, g c a`. This is how `decode v p` becomes a sum of numbers.
Placeholders: `{ι α β : Type} [AddCommMonoid β] (s : Finset ι) (g : ι → α → β) (a : α)`. `simp` uses it by
itself; `simp only` needs it named.

| Before | After |
|---|---|
| `⊢ P ((∑ c ∈ s, g c) a)` | `⊢ P (∑ c ∈ s, g c a)` |

**R8 · `simp` on an `if` with concrete labels** changes the **goal**: `simp` decides the equality of two
concrete tuples (componentwise, `Prod.mk.injEq`) and picks the branch. Placeholders:
`{β : Type} (x y : β)`. This is what evaluates `enc`, `proj` and `guess` once the label is fixed.

| Before | After |
|---|---|
| `⊢ P (if (1, 0) = (0, 0) then x else y)` | `⊢ P y` |

**R9 · `simp` computes in `Fin 2`** changes the **goal**: numerals in `Fin n` are added mod `n` (simprocs
`Fin.isValue`, `Fin.reduceAdd`: *simprocs* are evaluation procedures built into `simp`, applied without being named). This evaluates `flip` and `synd`. Placeholders: `(P : Fin 2 → Prop)`.

| Before | After |
|---|---|
| `⊢ P (1 + 1)` | `⊢ P 0` |

**W1: the brute-force pattern on two bits.** `fl e` flips bit `e` of a two-bit label; flipping twice is
the identity. R1, R2, R4, then `all_goals (fin_cases a <;> fin_cases b <;> simp [fl])`:

```lean-goal
⊢ (fun p => fl e (fl e p)) = fun p => p
⊢ fl e (fl e (a, b)) = (a, b)
⊢ fl none (fl none (a, b)) = (a, b)
⊢ fl (some e) (fl (some e) (a, b)) = (a, b)
```

**W2: a sum over pairs.** `∑ p : Fin 2 × Fin 2, (if p.1 + p.2 = 1 then x else 0) = x + x` closes with
`simp [Fintype.sum_prod_type, Fin.sum_univ_two]` (R5, R6, then R8, R9 on each of the 4 terms):

```lean-goal
⊢ (∑ p, if p.1 + p.2 = 1 then x else 0) = x + x
```

---

## Part 2 · `corrects_superposition`

Statement: `decode (∑ e, c e • err e (enc α β)) = (∑ e, c e) • enc α β`. Brute force is hopeless here
(the `c e` are arbitrary). The milestone is a helper you add **between** the two spec theorems:

```
theorem decode_lin {ι : Type} [Fintype ι] (c : ι → ℂ) (v : ι → Q3 → ℂ) :
    decode (∑ e, c e • v e) = ∑ e, c e • decode (v e)
```

Prove it pointwise (R1 as `funext p`), then: unfold and push the point inside (R7, R10, R11), push the
scalar into the inner sum and through the `if` (R13 with R12, R14, R15), swap the two sums (R16), compare
term by term (R17), split the `if` (R18), `simp`: in the `pos` goal both sides are the same sum, in the `neg`
goal the right side is a sum of zeros, which `simp` turns into `0` (`Finset.sum_const_zero`). Then the theorem: `rw [decode_lin]`, rewrite every
term with Part 1 (R13 with `corrects`), and fold the scalar sum (R19).

### Linearity: scalars and sums

**R10 · `Pi.smul_apply`** changes the **goal**: a scalar times a function, evaluated at `i`, is the scalar
times the value. Placeholders: `{ι M α : Type} [SMul M α] (b : M) (x : ι → α) (i : ι)`; `[SMul M α]` means
`M` acts on `α` by `•` (here `ℂ` on `ℂ`).

| Before | After |
|---|---|
| `⊢ P ((b • x) i)` | `⊢ P (b • x i)` |

**R11 · `smul_eq_mul`** changes the **goal**: `•` between two elements of the same ring is `*`.
Placeholders: `{α : Type} [Mul α] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (a • b)` | `⊢ P (a * b)` |

**R12 · `Finset.mul_sum`** changes the **goal**: multiplication distributes over a finite sum,
`a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`. Placeholders:
`{ι α : Type} [NonUnitalNonAssocSemiring α] (s : Finset ι) (a : α) (f : ι → α)`; the class asks for `+`, `0`
and a `*` that distributes over `+` (no `-`, no `1`, no associativity needed), met by `ℂ`, `ℝ`, `ℕ`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i ∈ s, f i)` | `⊢ P (∑ i ∈ s, a * f i)` |

**R13 · `simp_rw [l]`** changes the **goal**: it rewrites with `l` everywhere, also under binders (`fun x =>`,
`∑ x,`). `rw` cannot: when the matched term mentions a bound variable (`a i` below), `rw` fails with
"did not find an occurrence of the pattern". Bound variables may be renamed in the result.
Placeholders: `(s : Finset ι) (t : Finset κ) (a : ι → α) (f : ι → κ → α)`, `α` as in R12.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, a i * ∑ j ∈ t, f i j)` | `⊢ P (∑ x ∈ s, ∑ i ∈ t, a x * f x i)` |

**R14 · `mul_ite`** changes the **goal**: a factor moves into both branches of an `if`,
`a * (if c then b else d) = if c then a * b else a * d`. Placeholders:
`{α : Type} [Mul α] (c : Prop) [Decidable c] (a b d : α)`; `[Decidable c]` means `c` can be tested, as `p = σ`
on `Q3` can.

| Before | After |
|---|---|
| `⊢ P (a * if c then b else d)` | `⊢ P (if c then a * b else a * d)` |

**R15 · `mul_zero`** changes the **goal**: `a * 0 = 0`. Placeholders: `{α : Type} [MulZeroClass α] (a : α)`
(`*` with a `0` that absorbs; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a * 0)` | `⊢ P 0` |

**R16 · `Finset.sum_comm`** changes the **goal**: the two sums of a double sum swap,
`∑ i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, ∑ i ∈ s, f i j`. Placeholders:
`{ι κ M : Type} [AddCommMonoid M] (s : Finset ι) (t : Finset κ) (f : ι → κ → M)`. `rw` rewrites the first
double sum it finds; in `decode_lin` that is the right-hand side, which is what you want.

| Before | After |
|---|---|
| `⊢ P (∑ i ∈ s, ∑ j ∈ t, f i j)` | `⊢ P (∑ y ∈ t, ∑ x ∈ s, f x y)` |

**R17 · `refine Finset.sum_congr rfl fun i hi => ?_`** changes the **goal and the context**: two sums over
the same set are equal when their terms are. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g`;
`rfl` proves `s = s`, and `fun i hi => ?_` leaves the term goal with `i` and `hi : i ∈ s` in context.
Placeholders: `{ι M : Type} [AddCommMonoid M] (s : Finset ι) (f g : ι → M)`. Write `fun σ _ => ?_` if you
do not need `hi`.

| Before | After |
|---|---|
| `⊢ ∑ i ∈ s, f i = ∑ i ∈ s, g i` | `i : ι, hi : i ∈ s ⊢ f i = g i` |

**R18 · `split_ifs with hc`** changes the **goal list and the context**: for the condition `c` of an `if` in
the goal, one goal assumes `hc : c` (the `then` branch), the other `hc : ¬c`. Every `if` with the same
condition is resolved at once. Without `with`, the hypotheses are unnamed `h✝`; `simp` still uses them.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (if c then x else y)` | `hc : c ⊢ P x`, `hc : ¬c ⊢ P y` |

**R19 · `Finset.sum_smul`** changes the **goal**: a sum of scalars times a vector is the sum of the scaled
vectors, `(∑ i ∈ s, r i) • x = ∑ i ∈ s, r i • x`. Placeholders:
`{ι R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] (s : Finset ι) (r : ι → R) (x : M)`;
`Module R M` means `M` is a vector space over `R` (here `Q3 → ℂ` over `ℂ`). After this rewrite both sides
of the last goal agree and `rw` closes it with `rfl`.

| Before | After |
|---|---|
| `⊢ P ((∑ i ∈ s, r i) • x)` | `⊢ P (∑ i ∈ s, r i • x)` |

**W3: linearity of another sum-of-functions map.** `L v = ∑ σ : Fin 2, fun p => if p = σ then v (p + 1) else 0`
(project on `σ`, then shift). The chain `funext p` → `simp only [L, Finset.sum_apply, Pi.smul_apply,
smul_eq_mul]` → `simp_rw [Finset.mul_sum, mul_ite, mul_zero]` → `rw [Finset.sum_comm]` →
`refine Finset.sum_congr rfl fun σ _ => ?_` → `split_ifs <;> simp` passes through:

```lean-goal
⊢ L (∑ e, c e • v e) = ∑ e, c e • L (v e)
⊢ L (∑ e, c e • v e) p = (∑ e, c e • L (v e)) p
⊢ (∑ c_1, if p = c_1 then ∑ x, c x * v x (p + 1) else 0) = ∑ x, c x * ∑ c, if p = c then v x (p + 1) else 0
⊢ (∑ c_1, if p = c_1 then ∑ x, c x * v x (p + 1) else 0) = ∑ x, ∑ x_1, if p = x_1 then c x * v x (p + 1) else 0
⊢ (∑ c_1, if p = c_1 then ∑ x, c x * v x (p + 1) else 0) = ∑ y, ∑ x, if p = y then c x * v x (p + 1) else 0
⊢ (if p = σ then ∑ x, c x * v x (p + 1) else 0) = ∑ x, if p = σ then c x * v x (p + 1) else 0
```

---

## Traps

- `rcases e with _ | e` followed by `all_goals fin_cases e` fails: the `none` goal has no `e`. Wrap it in
  `try` (R4).
- `t1 ; t2` runs `t2` on the first goal only. After `rcases`/`fin_cases`, use `<;>` or `all_goals`.
- `simp [decode, err, flip, enc, proj, synd, guess]` **without** `Fintype.sum_prod_type, Fin.sum_univ_two`
  leaves the sum over the 4 syndromes unexpanded and fails with unsolved goals. Give it R5 and R6.
- Do not try to read the unfolded goal of a `corrects` case; it is pages of `match`/`if`. Check that one
  `simp` call closes all 32 cases instead.
- `rw [corrects]` on `∑ e, c e • decode (err e (enc α β))` fails ("did not find an occurrence"): the `e`
  is bound by the `∑`. Use `simp_rw [corrects]` (R13).
- Your helper `decode_lin` goes **outside** the spec regions, after the proof of `corrects` and above the
  `SKELETON · corrects_superposition` comment (which stays directly before that theorem's `-- BEGIN SPEC`). State it for an arbitrary finite index type `ι`, not just
  `Option (Fin 3)`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| function equation on triples → one point | `funext ⟨a, b, c⟩` (or `funext p`) | R1 |
| split `e : Option α` | `rcases e with _ \| e` | R2 |
| split `e : Fin 3` / `a : Fin 2` | `fin_cases e` / `fin_cases a <;> fin_cases b <;> fin_cases c` | R3 |
| split only where possible | `all_goals (try fin_cases e)` | R4 |
| evaluate a concrete case | `simp [defs…, Fintype.sum_prod_type, Fin.sum_univ_two]` | R5–R9 |
| sum over pairs → double sum | `Fintype.sum_prod_type` | R5 |
| sum over `Fin 2` → 2 terms | `Fin.sum_univ_two` | R6 |
| `(∑ c ∈ s, g c) a → ∑ c ∈ s, g c a` | `Finset.sum_apply` | R7 |
| `(b • x) i → b • x i`, `a • b → a * b` | `Pi.smul_apply`, `smul_eq_mul` | R10, R11 |
| `a * ∑ → ∑ a *` | `Finset.mul_sum` | R12 |
| rewrite under `∑`/`fun` | `simp_rw [l₁, l₂]` | R13 |
| `a * ite → ite (a * ·)`, `a * 0 → 0` | `mul_ite`, `mul_zero` | R14, R15 |
| swap a double sum | `rw [Finset.sum_comm]` | R16 |
| `∑ f = ∑ g` termwise | `refine Finset.sum_congr rfl fun σ _ => ?_` | R17 |
| split an `if` | `split_ifs with h` | R18 |
| `(∑ r i) • x → ∑ r i • x` | `rw [Finset.sum_smul]` | R19 |
| see the state | infoview | |
