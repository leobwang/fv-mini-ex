# M132 · Quantum teleportation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). The `1/√2` milestone is the same trick as in M126 (helpful,
not required). **New here:** states as functions `Fin 2 × … → ℂ`, arithmetic in `Fin 2`, Mathlib's finite
sums `∑`, `Complex.normSq`, `split_ifs` and `Decidable`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

**The model.** A state of qubits q₀ q₁ q₂ (Alice holds q₀ q₁, Bob holds q₂) and a reference system `R` is an amplitude
function `v : Fin 2 × Fin 2 × Fin 2 × R → ℂ`: `v (a, b, c, r)` is the amplitude of `|a b c⟩ ⊗ |r⟩`. `×` nests
to the right, so a point is `p = (a, (b, (c, r)))` and its parts are `p.1 = a` (q₀), `p.2.1 = b` (q₁),
`p.2.2.1 = c` (q₂), `p.2.2.2 = r`, and `p.2.2 = (c, r)` (Bob's part). The protocol is
`init` (χ on q₀ and `R`, Bell pair on q₁ q₂) → `cnot01` → `h0` → measure q₀ q₁ with outcomes `(m₀, m₁)`
(`bob` reads off the amplitudes with q₀ = m₀, q₁ = m₁) → Bob applies `fixX m₁`, then `fixZ m₀`. Every
gate here is written as a formula for the new amplitude at `p`, so "apply the gate" means "unfold the
definition and evaluate". `s = (√2)⁻¹` is the only irrational number in sight, and it always appears twice.

| You see | It means |
|---|---|
| `Fin 2` | the type `{0, 1}`; a qubit's basis label |
| `Fin 2 × R → ℂ` | an amplitude function on one qubit and `R` |
| `p.1`, `p.2`, `p.2.2.1` | first component; the rest of the tuple; the third component (see *The model* above) |
| `c + m₁` with `c m₁ : Fin 2` | addition mod 2, i.e. XOR: `1 + 1 = 0` |
| `(fun i => i) ⟨0, ⋯⟩` | the value `0 : Fin 2`, printed this way after `fin_cases` |
| `if c then a else b` | `a` when `c` holds, else `b`; `c` must be decidable (`[Decidable c]`) |
| `↑x` | the real number `x` cast into `ℂ` |
| `x⁻¹` | the inverse `1 / x`; `(↑√2)⁻¹` is `1/√2` (the definition of `s`) |
| `√x` | `Real.sqrt x`, a real number |
| `2⁻¹`, `4⁻¹` | `1 / 2`, `1 / 4`; `simp` writes `1 / n` this way |
| `Complex.normSq z` | $\lvert z\rvert^2 = (\operatorname{Re} z)^2 + (\operatorname{Im} z)^2$, a **real** number |
| `∑ q, f q` | the sum of `f q` over all `q` of a finite type (Mathlib's `Finset.univ`) |
| `∑ x, ∑ y, f (x, y)` | a double sum; Lean names the bound variables `x`, `y`, `x_1`, … itself |
| `Finset.univ` | the finite set of all elements of a finite type |
| `R : Type` | the reference system: any type (from `variable {R : Type}`); finite in `teleport_prob` |
| `∀ (P : Prop) [inst : Decidable P], …` | for every proposition `P` that can be decided (so `if P` makes sense), … |
| `inst✝ : Fintype R` | an anonymous instance: `R` is finite, so `∑` over it makes sense |
| `x✝ : r ∈ Finset.univ` | an anonymous hypothesis (here: always true, never needed) |
| `h✝ : Q` | an anonymous hypothesis made by `split_ifs` |
| `case «0».«1»` | the goal for the values `0`, `1` of the variables split by `fin_cases` |

---

## Part 1 · `teleport`

Statement: for all outcomes `m₀ m₁`, Bob's corrected state is the input state times `1/2`:
`fixZ m₀ (fixX m₁ (bob … m₀ m₁)) = fun q => (1 / 2 : ℂ) * χ q`. The `1/2` is the amplitude
of the outcome (probability ¼). Plan: prove the milestone `s * s = 1 / 2` once, reduce the function
equation to its values at `(c, r)`, split the three bits `m₀ m₁ c`, and evaluate.

### Milestone: `s * s = 1 / 2`

**R1 · `rw [D]`** changes the **goal**: a defined constant is replaced by its body (Lean generated the
equation `D = body` when you defined `D`). Placeholders: `t` defined by
`noncomputable def t : ℂ := (Real.sqrt 3 : ℂ)⁻¹` (`noncomputable` because `Real.sqrt` cannot be run).

| Before | After |
|---|---|
| `⊢ P t` | `⊢ P (↑√3)⁻¹` |

**R2 · `rw [← mul_inv]`** changes the **goal**. The lemma is `mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹`, and `←` uses
it right to left. Placeholders: `{α : Type} [DivisionCommMonoid α] (a b : α)`: `α` has a commutative `*` and
an inverse `⁻¹`; `ℂ` and `ℝ` qualify.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ * b⁻¹)` | `⊢ P (a * b)⁻¹` |

**R3 · `rw [← Complex.ofReal_mul]`** changes the **goal**. The lemma is `↑(x * y) = ↑x * ↑y`; right to left it
moves `*` inside the cast, so a lemma about real numbers can apply. Placeholders: `(x y : ℝ)`, goal in `ℂ`.

| Before | After |
|---|---|
| `⊢ P (↑x * ↑y)` | `⊢ P ↑(x * y)` |

**R4 · `rw [Real.mul_self_sqrt]`** changes the **goal list**. The lemma is `0 ≤ x → √x * √x = x`, so the goal
is rewritten and a side goal `0 ≤ x` is added. Write `rw [Real.mul_self_sqrt (by norm_num)]` to prove it on
the spot. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (√x * √x)` | `⊢ P x`, `⊢ 0 ≤ x` |

**R5 · `norm_num`** **closes** a goal made of numerals, including `⁻¹`, `/` and casts of numerals such as
`(↑3)⁻¹ = 1 / 3`.

### Function equation → number equations

**R6 · `funext ⟨a, b⟩`** changes the **goal and the context**: two functions are equal when they agree at every
point, and the pattern `⟨a, b⟩` names the two components of the point. A right side `fun q => …` is applied
to `(a, b)` and reduced. Placeholders: `{α β : Type} (f g : α × β → ℂ) (k : ℂ)`.

| Before | After |
|---|---|
| `⊢ f = fun q => k * g q` | `a : α, b : β ⊢ f (a, b) = k * g (a, b)` |

**R7 · `have h := lemma`** changes the **context**: it adds the lemma's statement under the name `h` (here
`Real.sqrt_nonneg 3 : 0 ≤ √3`). Use it to bring your milestone into a proof: `have h := s_mul_s`.
Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : 0 ≤ √3 ⊢ G` |

**R8 · `fin_cases a <;> fin_cases b`** changes the **goal list and the context**: each `Fin 2` variable leaves
the context, and there is one goal per combination of values (2 variables: 4 goals; `m₀ m₁ c`: 8 goals).
Placeholders: `(P : Fin 2 → Fin 2 → Prop) (a b : Fin 2)`.

| Before | After |
|---|---|
| `a b : Fin 2 ⊢ P a b` | `⊢ P ((fun i => i) ⟨0, ⋯⟩) ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨0, ⋯⟩) ((fun i => i) ⟨1, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩) ((fun i => i) ⟨0, ⋯⟩)`, `⊢ P ((fun i => i) ⟨1, ⋯⟩) ((fun i => i) ⟨1, ⋯⟩)` |

### Evaluating an amplitude

One call `simp [fixZ, fixX, bob, h0, cnot01, init]` does R9–R12 everywhere in the goal, plus the arithmetic
cleanup (`0 * a = 0`, `a + 0 = a`, `1 * a = a`, `-1 * a = -a`, …). Pass every gate name the goal mentions.

**R9 · `simp only [D]`** changes the **goal**: a defined function applied to its arguments is replaced by its
body with the arguments substituted. Placeholders: `dbl` defined by
`def dbl (w : Fin 2 × ℕ → ℂ) : Fin 2 × ℕ → ℂ := fun q => 2 * w q`, `(w : Fin 2 × ℕ → ℂ) (c : Fin 2) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (dbl w (c, n))` | `⊢ P (2 * w (c, n))` |

**R10 · projections of a tuple** change the **goal**: `(a, b, c).1 = a`, `(a, b, c).2.1 = b`, … `simp`
does this by itself (`simp only []` does only this). Placeholders: `{α β γ : Type} (a : α) (b : β) (c : γ)`.

| Before | After |
|---|---|
| `⊢ P (a, b, c).2.1` | `⊢ P b` |

**R11 · arithmetic in `Fin 2`** changes the **goal**: `simp` computes sums of numerals mod 2
(`Fin.reduceAdd`), and it also turns `(fun i => i) ⟨1, ⋯⟩` back into `1`. Placeholders: `(P : Fin 2 → Prop)`.

| Before | After |
|---|---|
| `⊢ P (1 + 1)` | `⊢ P 0` |

**R12 · `if` with a numeral condition** changes the **goal**: `simp` decides equalities of `Fin 2` numerals
(and `∧`, `¬` of them) and keeps the right branch. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if 1 = 1 ∧ 0 = 1 then a else b)` | `⊢ P b` |

After `simp`, each of the 8 goals is a number equation in which `s` appears twice, separated by an amplitude:
`s * (χ (0, r) * s) = 2⁻¹ * χ (0, r)` in the first case. W3 is the same shape with `t`.

### Closing the number equations

**R13 · `ring_nf`** changes the **goal**: it puts both sides in a normal form for ring expressions. Here it
collects the two copies of `s` into `s ^ 2`. Placeholders: `(a x : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (a * (x * a))` | `⊢ P (a ^ 2 * x)` |

**R14 · `sq`** changes the **goal**. The lemma is `sq : a ^ 2 = a * a`. After R13 the goal says `s ^ 2`, but your
milestone says `s * s`; `simp [sq, h]` turns `s ^ 2` into `s * s` and then rewrites with `h : s * s = 1 / 2`.
Placeholders: `{α : Type} [Monoid α] (a : α)` (any type with an associative `*` and a `1`; `ℂ` qualifies).

| Before | After |
|---|---|
| `⊢ P (a ^ 2)` | `⊢ P (a * a)` |

**R15 · `ring`** **closes** an equation that holds in every commutative ring, such as `2⁻¹ * x = x * 2⁻¹`. It
treats `χ (0, r)`, `s` and `x⁻¹` as unknowns and uses no hypotheses, so it cannot use `s * s = 1 / 2` itself.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a bit flip done twice is the identity.** `flip1 w = fun q => w (q.1 + 1, q.2)`. R6 and R8 give:

```lean-goal
⊢ flip1 (flip1 w) (c, n) = w (c, n)
⊢ flip1 (flip1 w) ((fun i => i) ⟨0, ⋯⟩, n) = w ((fun i => i) ⟨0, ⋯⟩, n)
```

and `simp [flip1]` closes both goals (R9–R11: `0 + 1 + 1 = 0`).

**W2: the milestone for `t = (√3)⁻¹`.** R1, R2, R3, R4 with `(by norm_num)`, then R5:

```lean-goal
⊢ t * t = 1 / 3
⊢ (↑√3)⁻¹ * (↑√3)⁻¹ = 1 / 3
⊢ (↑√3 * ↑√3)⁻¹ = 1 / 3
⊢ (↑(√3 * √3))⁻¹ = 1 / 3
⊢ (↑3)⁻¹ = 1 / 3
```

**W3: `t` twice with a factor in between.** With `h : t * t = 1 / 3`: R13, then `simp [sq, h]` (R14), then R15:

```lean-goal
⊢ t * (w (0, n) * t) = 3⁻¹ * w (0, n)
⊢ t ^ 2 * w (0, n) = w (0, n) * (1 / 3)
⊢ 3⁻¹ * w (0, n) = w (0, n) * 3⁻¹
```

---

## Part 2 · `teleport_prob`

Statement: `∑ q, Complex.normSq (bob … m₀ m₁ q) = (1 / 4) * ∑ q, Complex.normSq (χ q)`: the probability of
outcome `(m₀, m₁)` (Bob's unnormalised state's squared norm) is ¼ of the input's squared norm. Both sides are
**real** numbers, and the sums run over `q : Fin 2 × R`, which needs `[Fintype R]`.

Plan: first the milestone `key`, a closed form of each amplitude:
`bob (h0 (cnot01 (init χ))) m₀ m₁ (c, r) = ±(1/2) · χ (c + m₁, r)`, with the sign `-1` exactly when
`m₀ = 1 ∧ c + m₁ = 1`. It is proved exactly like Part 1 (R7, R8, `simp` with R9–R12, R13, R14, R15). Then the
sum is bookkeeping: split it, take `normSq` of each factor, the sign has `normSq = 1`, `normSq (1/2) = 1/4`,
and finally the reindexing `c ↦ c + m₁` (swap the two terms when `m₁ = 1`).

### Splitting the sum and `normSq`

**R16 · `rw [Fintype.sum_prod_type]`** changes the **goal**: a sum over pairs becomes a double sum,
$\sum_{q \in \alpha\times\beta} f(q) = \sum_a \sum_b f(a, b)$. Placeholders:
`{α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ)`. `Fintype α` means `α` is finite; `Fin 2` qualifies,
and `R` does because of the theorem's `[Fintype R]`.

| Before | After |
|---|---|
| `⊢ P (∑ q, f q)` | `⊢ P (∑ x, ∑ y, f (x, y))` |

**R17 · `simp only [hk]`** with `hk : ∀ i, f i = g i` changes the **goal**: it rewrites `f i` into `g i` even
inside `∑ i, …`, where `i` is a bound variable. `rw [hk]` fails there (it cannot rewrite a term containing a
bound variable). This is how your milestone `key` enters: `simp only [Fintype.sum_prod_type, key, …]`.
Placeholders: `{α : Type} [Fintype α] (f g : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ x, g x)` |

**R18 · `Complex.normSq_mul`** changes the **goal**: the squared norm of a product is the product of the
squared norms, `normSq (z * w) = normSq z * normSq w`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (Complex.normSq (z * w))` | `⊢ P (Complex.normSq z * Complex.normSq w)` |

### The sign has `normSq = 1`

The sign `if m₀ = 1 ∧ x + m₁ = 1 then -1 else 1` has a condition with variables in it, so `simp` cannot
decide it. Prove once a fact for every condition, `∀ P : Prop, [Decidable P] → Complex.normSq (if P then -1
else 1) = 1`, and hand it to `simp only`.

**R19 · `intro Q _`** changes the **context**: on a goal `∀ Q : Prop, [Decidable Q] → …` it introduces `Q` and
an anonymous instance `inst✝ : Decidable Q` (a proof that `Q` can be decided, which `if Q` needs). `_` leaves
it unnamed; `simp` and `split_ifs` find it by themselves. Placeholders: `(G : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (Q : Prop) [Decidable Q], G Q` | `Q : Prop, inst✝ : Decidable Q ⊢ G Q` |

**R20 · `split_ifs`** changes the **goal list and the context**: a goal containing `if Q then a else b` becomes
two goals, one with `h✝ : Q` and `a`, one with `h✝ : ¬Q` and `b`. Placeholders:
`(Q : Prop) [Decidable Q] (a b : ℂ)`.

| Before | After |
|---|---|
| `Q : Prop ⊢ P (if Q then a else b)` | `h✝ : Q ⊢ P a`, `h✝ : ¬Q ⊢ P b` |

**R21 · `Complex.normSq_neg`, `map_one`** change the **goal**: `normSq (-z) = normSq z`, and `normSq 1 = 1`.
`Complex.normSq` is a bundled map `ℂ →*₀ ℝ` (it preserves `*`, `1` and `0`), so `normSq 1 = 1` is the generic
lemma `map_one`, not a `Complex.` lemma. `simp` applies both by itself. Placeholders: none.

| Before | After `rw [Complex.normSq_neg]` | After `rw [map_one]` |
|---|---|---|
| `⊢ P (Complex.normSq (-1))` | `⊢ P (Complex.normSq 1)` | `⊢ P 1` |

**R22 · `norm_num`** **closes** `normSq` of a numeral fraction, such as `Complex.normSq (1 / 3) = 1 / 9`. Use it
for the fact `Complex.normSq (1 / 2) = 1 / 4`, then hand that fact to `simp only`.

### Bookkeeping

Feed the facts and R23–R26 to one `simp only [hs, one_mul, h4, Fin.sum_univ_two, Finset.mul_sum,
← Finset.sum_add_distrib]`; both sides become a single sum over `r : R` (W4).

**R23 · `one_mul`** changes the **goal**: `1 * a = a` (the sign's `normSq` became `1`). Placeholders:
`{α : Type} [MulOneClass α] (a : α)` (`*` with a unit `1`; `ℝ` qualifies).

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

**R24 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms (Bob's bit `c = 0, 1`).
Placeholders: `{β : Type} [AddCommMonoid β] (f : Fin 2 → β)` (`β` has a commutative `+` with `0`; `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R25 · `Finset.mul_sum`** changes the **goal**: a constant factor moves into a sum,
`a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i` (for `s = Finset.univ` Lean prints `∑ i, …`). Placeholders:
`{α : Type} [Fintype α] (a : ℝ) (f : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**R26 · `rw [← Finset.sum_add_distrib]`** changes the **goal**. The lemma is
`∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`; right to left it merges two sums over the same set.
Placeholders: `{α : Type} [Fintype α] (f g : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i + ∑ i, g i)` | `⊢ P (∑ x, (f x + g x))` |

**R27 · `refine Finset.sum_congr rfl fun r _ => ?_`** changes the **goal and the context**: two sums over the
same set are equal when the terms are, one `r` at a time. `Finset.sum_congr : s₁ = s₂ → (∀ x ∈ s₂, f x = g x) →
s₁.sum f = s₂.sum g`; `rfl` proves `s₁ = s₂`, and `fun r _ => ?_` leaves the term equation as the goal.
Placeholders: `{α : Type} [Fintype α] (f g : α → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i = ∑ i, g i` | `r : α, x✝ : r ∈ Finset.univ ⊢ f r = g r` |

The last goal still contains `0 + m₁` and `1 + m₁`: split `m₁` (R8), let `simp` compute (R11), and finish with
`ring` (R15). When `m₁ = 1` the two terms come out swapped, which `ring` does not mind.

**W4: sum bookkeeping on `∑ q, normSq (3 * w q) = 9 * ∑ q, normSq (w q)`.** With `h9 : Complex.normSq 3 = 9`
(R22), one `simp only [Fintype.sum_prod_type, Complex.normSq_mul, h9, Fin.sum_univ_two, Finset.mul_sum,
← Finset.sum_add_distrib]` (R16, R18, R24, R25, R26), then R27, then `ring`:

```lean-goal
⊢ ∑ q, Complex.normSq (3 * w q) = 9 * ∑ q, Complex.normSq (w q)
⊢ ∑ x, (9 * Complex.normSq (w (0, x)) + 9 * Complex.normSq (w (1, x))) = ∑ i, 9 * (Complex.normSq (w (0, i)) + Complex.normSq (w (1, i)))
⊢ 9 * Complex.normSq (w (0, r)) + 9 * Complex.normSq (w (1, r)) = 9 * (Complex.normSq (w (0, r)) + Complex.normSq (w (1, r)))
```

---

## Traps

- `funext ⟨c, r⟩` comes **before** `fin_cases c`: Bob's bit `c` does not exist until `funext` names it.
- `t1 ; t2` runs `t2` on the first goal only. After `fin_cases`, chain with `<;>` or use `all_goals`.
- `simp [sq, h]` right after the gate `simp` does nothing useful: `s * (χ (0, r) * s)` contains no literal
  `s * s`. Run `ring_nf` first (R13), which makes it `s ^ 2 * …`, then `simp [sq, h]` (R14).
- `ring` alone cannot finish: it treats `s` as an unknown and ignores `h : s * s = 1 / 2` (R15).
- `rw [key]` fails under `∑ x, …`; use `simp only [key]` (R17).
- `p.2.2` is Bob's **pair** `(c, r)`, not his bit; his bit is `p.2.2.1`.
- `c + m₁` is addition mod 2 (`1 + 1 = 0`), which is why the `X^m₁` correction undoes the flip.
- `Complex.normSq` lands in `ℝ`: the `1 / 4` in `teleport_prob` is a real number, and the facts you prove
  about it must be stated in `ℝ` (`Complex.normSq (1 / 2) = 1 / 4` is, automatically).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold a defined constant | `rw [s]` | R1 |
| `a⁻¹ * b⁻¹ → (a * b)⁻¹` | `rw [← mul_inv]` | R2 |
| move `*` inside a real cast | `rw [← Complex.ofReal_mul]` | R3 |
| `√x * √x → x` | `rw [Real.mul_self_sqrt (by norm_num)]` | R4 |
| numeric goal | `norm_num` | R5, R22 |
| function equation on pairs | `funext ⟨c, r⟩` | R6 |
| use a proved lemma | `have h := name` | R7 |
| split `Fin 2` variables | `fin_cases a <;> fin_cases b` | R8 |
| evaluate gates, tuples, `Fin 2` sums, `if`s | `simp [gate names]` | R9–R12 |
| `s * (x * s) → s ^ 2 * x` | `ring_nf` | R13 |
| use `h : s * s = …` on `s ^ 2` | `simp [sq, h]` | R14 |
| ring identity | `ring` | R15 |
| sum over pairs → double sum | `Fintype.sum_prod_type` | R16 |
| rewrite under `∑` | `simp only [key]` | R17 |
| `normSq` of a product | `Complex.normSq_mul` | R18 |
| introduce `[Decidable Q]` | `intro Q _` | R19 |
| case on an `if` | `split_ifs` | R20 |
| `normSq (-1)`, `normSq 1` | `simp` (`Complex.normSq_neg`, `map_one`) | R21 |
| `1 * a → a` | `one_mul` | R23 |
| sum over `Fin 2` → two terms | `Fin.sum_univ_two` | R24 |
| factor into a sum | `Finset.mul_sum` | R25 |
| merge two sums | `← Finset.sum_add_distrib` | R26 |
| equal sums termwise | `refine Finset.sum_congr rfl fun r _ => ?_` | R27 |
| see the state | infoview | |
