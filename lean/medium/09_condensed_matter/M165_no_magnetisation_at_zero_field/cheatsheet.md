# M165 · No magnetisation at zero field: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `cases`, `have`, `rw`, `simp`, anonymous
constructors `⟨…⟩`. **New here:** Mathlib's bijections (`Equiv`, written `α ≃ β`), finite sums `∑` over a
whole finite type, `Fin` index arithmetic (`castSucc`, `succ`), real numbers `ℝ` with `Real.exp`, and
`linarith`.

**The physics in one line.** A configuration `σ : Fin (n + 1) → Bool` assigns an up (`true`) or down
(`false`) spin to each of the sites `0, …, n`. The global flip `F(σ) = (i ↦ ¬σ i)` is a bijection of the
`2^(n+1)` configurations with `F ∘ F = id`. With no field, `E(F σ) = E(σ)` (each bond term
`s(σ i) s(σ (i+1))` gets two minus signs), while `s(F σ k) = -s(σ k)`. Summing over `F σ` instead of `σ`
reorders the same terms, so the sum `S` satisfies `S = -S`, i.e. `S = 0`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` with `hG : G` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Fintype ι]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin (n + 1)` | the sites `{0, 1, …, n}`: naturals `< n + 1` |
| `σ : Fin (n + 1) → Bool` | a spin configuration; `σ i = true` is spin up at site `i` |
| `!b` | Boolean not (`¬`); `!!b` is `!(!b)`. Lean prints `spin (!b)` as `(spin !b)` |
| `!σ i`, `(spin !σ x.castSucc)` | `!` binds weaker than function application: `!(σ i)`, and `spin (!(σ x.castSucc))` |
| `if b then x else y` | shown as `if b = true then x else y`: a `Bool` used as a condition becomes the `Prop` `b = true` |
| `i.castSucc`, `i.succ` (for `i : Fin n`) | the sites `i` and `i + 1`, as elements of `Fin (n + 1)`; bond `i` joins them |
| `∑ i : Fin n, f i`, `∑ σ, f σ` | the sum of `f` over every element of a finite type (Mathlib: `Finset.sum Finset.univ f`). The bound name is cosmetic: after a rewrite Lean may print `∑ x, f x` for `∑ i, f i` |
| `[Fintype ι]`, `inst✝ : Fintype ι` | "`ι` is finite", needed for `∑ i : ι`. `Fin m`, `Bool`, and `Fin m → Bool` all are |
| `α ≃ β` | `Equiv α β`: a bijection given as `toFun`, `invFun` and two proofs that they are mutually inverse |
| `e x` for `e : α ≃ β` | `e` used as a function, through the coercion `⇑e = e.toFun` |
| `{ toFun := f, invFun := g, left_inv := ⋯, right_inv := ⋯ }` | how Lean prints `⟨f, g, l, r⟩ : α ≃ β`; `⋯` hides the proofs |
| `e : α ≃ α := …` in the context | a `let`: `e` is a name **and** its definition, which `simp only [e]` can unfold |
| `Real.exp x` | the real exponential `eˣ` |
| `-β * energy J σ` | `(-β) * energy J σ`; `energy J σ` is `E(σ)`, its chain length `n` is implicit (read off `σ`) |
| `(-J * ∑ x, f x) = …` | the parentheses only end the sum: `∑ x, …` extends as far right as possible |
| `flip σ k` | site `k` of the flipped configuration `flip σ` (an `Equiv` applied to `σ`, then the result applied to `k`) |
| `case false`, `case true` | the two goals made by `cases b` for `b : Bool` |

---

## Part 1 · `no_magnetization`

Statement: for all real `β J`, every `n : ℕ` and every site `k : Fin (n + 1)`,
`∑ σ : Fin (n + 1) → Bool, spin (σ k) * Real.exp (-β * energy J σ) = 0`, where `spin b` is `1` or `-1` and
`energy J σ = -J * ∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)`.

### Building the flip

**R1 · `let e : α ≃ α := ⟨f, g, l, r⟩`** changes the **context**: it adds `e` together with its definition;
the goal is unchanged. The four components are `toFun f`, `invFun g`, `left_inv : ∀ x, g (f x) = x` and
`right_inv : ∀ y, f (g y) = y`. In the example `f = g = (x ↦ -x)` and both laws are
`neg_neg : - -x = x`. Placeholders: `{α : Type} [InvolutiveNeg α]` (α has a `-` with `- -x = x`: `ℤ`, `ℝ`,
and functions into them), `(G : Prop)`. The new context line is

```lean
e : α ≃ α := { toFun := fun x => -x, invFun := fun x => -x, left_inv := ⋯, right_inv := ⋯ }
```

Use `let`, not `have`: `have` keeps only `e : α ≃ α` and forgets what `e` does, so R6 cannot evaluate it.

**R2 · `funext i`** changes the **goal and the context**: an equation of functions becomes an equation of
their values at a new variable `i`. A law of an `Equiv` between *function* types has exactly this shape:
`invFun (toFun v) = v`. Write each law as `fun v => by funext i; simp`. Placeholders:
`{ι : Type} (v : ι → ℤ)`.

| Before | After |
|---|---|
| `⊢ (fun v i => -v i) ((fun v i => -v i) v) = v` | `i : ι ⊢ (fun v i => -v i) ((fun v i => -v i) v) i = v i` |

`simp` then closes it (it β-reduces the `fun`s and uses `neg_neg`). For `!` instead of `-`, `simp` uses R3.

**R3 · `Bool.not_not`** changes the **goal**. The lemma is `Bool.not_not : (!!b) = b`; `simp` applies it by
itself. Placeholders: `(b : Bool)`.

| Before | After |
|---|---|
| `⊢ P !!b` | `⊢ P b` |

### The sign of a flipped spin

**R4 · `cases b`** for `b : Bool` changes the **goal list and the context**: `b` leaves the context and there
is one goal for `false` and one for `true`. Placeholders: `(x y : ℝ) (b : Bool)`.

| Before | After |
|---|---|
| `b : Bool ⊢ P (if b = true then x else y)` | `⊢ P (if false = true then x else y)`, `⊢ P (if true = true then x else y)` |

**R5 · `simp`** on an `if` with a literal condition changes the **goal**: it picks the branch. Pass the name of
a definition to unfold it first (`simp [d]`), and `simp` also evaluates `!false` to `true`. Placeholders:
`(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (if false = true then x else y)` | `⊢ P y` |

In `hs`, after `intro b; cases b` the goals are `(spin !false) = -spin false` and `(spin !true) = -spin true`:
the `if` is still hidden inside `spin`. `simp [spin]` (on both goals: `cases b <;> simp [spin]`) unfolds it,
turns `!false` into `true`, picks the branches and closes `1 = -(-1)` by itself.

### Evaluating the flip and moving signs

**R6 · `simp only [e]`, then `simp only [Equiv.coe_fn_mk]`** change the **goal**: `e x` for a `let`-bound
`e` becomes the body of its `toFun` at `x`. The lemma is `Equiv.coe_fn_mk : ⇑⟨f, g, l, r⟩ = f`. Both names
can go in one call: `simp only [e, Equiv.coe_fn_mk, …]`. Placeholders: `{α : Type} [InvolutiveNeg α] (x : α)`
and `e` from R1.

| Before | After `simp only [e]` | After `simp only [Equiv.coe_fn_mk]` |
|---|---|---|
| `⊢ P (e x)` | `⊢ P ({ toFun := fun x => -x, invFun := fun x => -x, left_inv := ⋯, right_inv := ⋯ } x)` | `⊢ P (-x)` |

**R7 · `simp only [hf]` under a `∑`** changes the **goal**: it rewrites with `hf` inside the summand. `rw [hf]`
fails here ("did not find an occurrence of the pattern"): the subterm `f (g (u i))` contains the bound
variable `i`, and `rw` cannot rewrite such subterms. `simp` can. Placeholders:
`{ι α : Type} [Fintype ι] (f : α → ℝ) (g : α → α) (u : ι → α) (hf : ∀ a, f (g a) = -f a)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f (g (u i)))` | `⊢ P (∑ x, -f (u x))` |

**R8 · `neg_mul_neg`** changes the **goal**. The lemma is `neg_mul_neg : -a * -b = a * b`. Placeholders:
`{α : Type} [Mul α] [HasDistribNeg α] (a b : α)` (α has `*` and a `-` that moves through `*`: `ℤ`, `ℝ`, `ℂ`).

| Before | After |
|---|---|
| `⊢ P (-a * -b)` | `⊢ P (a * b)` |

**R9 · `neg_mul`** changes the **goal**. The lemma is `neg_mul : -a * b = -(a * b)`. Placeholders as R8.

| Before | After |
|---|---|
| `⊢ P (-a * b)` | `⊢ P (-(a * b))` |

### Reindexing the sum and finishing

**R10 · `have h := Equiv.sum_comp e g`** changes the **context**: it adds the reindexing identity. The lemma
is `Equiv.sum_comp (e : ι ≃ κ) (g : κ → M) : ∑ i, g (e i) = ∑ i, g i`: a bijection only permutes the
summands. Give `g` as a `fun` (`fun σ => …`); Lean β-reduces `g (e i)` in `h`. Placeholders:
`{ι M : Type} [Fintype ι] [AddCommMonoid M] (e : ι ≃ ι) (g : ι → M)` (`M` has a commutative `+` with `0`:
`ℕ`, `ℤ`, `ℝ`).

The goal `⊢ G` is unchanged; the context gains the line

```lean
h : ∑ i, g (e i) = ∑ i, g i
```

**R11 · `simp only [hg] at h`** changes the **context**: `h` is rewritten, inside its sums too (R7); the goal
is unchanged. Placeholders: `{ι : Type} [Fintype ι] (e : ι ≃ ι) (g : ι → ℝ) (hg : ∀ i, g (e i) = -g i)`.

The goal `⊢ ∑ i, -g i = ∑ i, g i` is unchanged; the hypothesis line changes:

| Before | After |
|---|---|
| `h : ∑ i, g (e i) = ∑ i, g i` | `h : ∑ x, -g x = ∑ i, g i` |

**R12 · `Finset.sum_neg_distrib`** changes the **goal** (or, with `at h`, the context). The lemma is
`Finset.sum_neg_distrib : ∑ i ∈ s, -f i = -∑ i ∈ s, f i`; for a sum over a whole type, `s` is all of it.
Placeholders: `{ι M : Type} [Fintype ι] [AddCommGroup M] (f : ι → M)` (`M` also has subtraction: `ℤ`, `ℝ`).

| Before | After |
|---|---|
| `⊢ P (∑ i, -f i)` | `⊢ P (-∑ x, f x)` |

**R13 · `linarith`** **closes** a goal that follows linearly from hypotheses over an ordered field such as `ℝ`.
It treats any non-linear subterm, a whole sum `∑ σ, …` included, as one unknown. Placeholders: `(S : ℝ)`.

| Before | After |
|---|---|
| `h : -S = S ⊢ S = 0` | no goals |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** Pointwise negation of vectors as an `Equiv` of `ι → ℤ`: R1 with both laws written
`fun v => by funext i; simp` (R2).

**W2: an odd function sums to zero.** `f : α → ℝ` with `f (-x) = -f x`. Steps: `let e` (R1); `hg : ∀ x,
f (e x) = -f x` by `simp only [e, Equiv.coe_fn_mk]` (R6); `have h := Equiv.sum_comp e f` (R10);
`simp only [hg] at h` (R11); `simp only [Finset.sum_neg_distrib] at h` (R12); `linarith` (R13). The goal
stays the same throughout while `h` becomes `-∑ x, f x = ∑ x, f x`:

```lean-goal
⊢ ∑ x, f x = 0
```

**W3.** `∑ i, -a i * -b i = ∑ i, a i * b i` is one `simp only [neg_mul_neg]`: R8 applied under the `∑` (R7).

---

## Traps

- `have flip : … ≃ … := ⟨…⟩` hides the definition; `simp only [flip]` then does nothing. Use `let` (R1).
- An `Equiv` needs all four components. Between function types the laws are equations of functions: start
  each with `funext i` (R2).
- `rw` cannot rewrite inside `∑ i, …` when the matched subterm mentions `i`; use `simp only [h]` (R7, R11).
- Both sides of `h` after R11/R12 contain the same sum with different bound names (`x` vs `σ`). That is
  cosmetic: `linarith` sees one unknown.
- State `h2` with `flip σ` in exactly the places where `Equiv.sum_comp` puts it (`spin (flip σ k)` and
  `energy J (flip σ)`), or `simp only [h2] at h` will not match.
- `t1 ; t2` runs `t2` on the first goal only. After `cases b`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a named bijection you can evaluate later | `let e : α ≃ α := ⟨f, g, l, r⟩` | R1 |
| a law between functions | `fun v => by funext i; simp` | R2, R3 |
| `(!!b) = b` | `Bool.not_not` (in `simp`) | R3 |
| a fact about every `b : Bool` | `intro b; cases b <;> simp [d]` | R4, R5 |
| evaluate `e x` | `simp only [e, Equiv.coe_fn_mk]` | R6 |
| rewrite inside `∑` | `simp only [h]` (not `rw`) | R7 |
| `-a * -b → a * b` | `neg_mul_neg` | R8 |
| `-a * b → -(a * b)` | `neg_mul` | R9 |
| `∑ i, g (e i) = ∑ i, g i` | `have h := Equiv.sum_comp e g` | R10 |
| rewrite a hypothesis | `simp only [l₁, l₂] at h` | R11 |
| `∑ -f → -∑ f` | `Finset.sum_neg_distrib` | R12 |
| `S = 0` from `-S = S` | `linarith` | R13 |
| see the state | infoview | |
