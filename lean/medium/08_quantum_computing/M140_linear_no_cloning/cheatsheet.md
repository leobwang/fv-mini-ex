# M140 · Linear no-cloning: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `have`, `obtain`, `rw`, `simp`, `¬`, `∃`, `∧`.
**New here:** Mathlib's vectors as functions `d → ℂ`, the basis vectors `Pi.single`, pointwise `+` and `•` on
functions, matrix–vector product `*ᵥ`, product index types `d × d`, and the classes `Fintype`, `DecidableEq`,
`Nontrivial`.

**The math.** Write `|k⟩` for the `k`-th basis vector of `ℂ^d` and `v ⊗ w` for the vector on index pairs
`(p₁, p₂) ↦ v p₁ · w p₂` (the tensor product, as a function). Suppose `C (v ⊗ e) = c_v · (v ⊗ v)` with
`c_v ≠ 0` for every `v ≠ 0`. Pick indices `i ≠ j`. Linearity of `C` and the cases `v = |i⟩`, `v = |j⟩` give

`C ((|i⟩ + |j⟩) ⊗ e) = C (|i⟩ ⊗ e) + C (|j⟩ ⊗ e) = cᵢ |i⟩⊗|i⟩ + cⱼ |j⟩⊗|j⟩`,

whose `(i, j)` entry is `0` (each term needs both indices equal). The case `v = |i⟩ + |j⟩` says the same vector
is `c (|i⟩ + |j⟩) ⊗ (|i⟩ + |j⟩)`, whose `(i, j)` entry is `c · 1 · 1 = c ≠ 0`. Contradiction. (With `d = 1` there
is no second index and a cloner exists: `ℂ^1 ⊗ ℂ^1` is one-dimensional.)

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal or hypothesis.
- Placeholders are written as Lean binders. `{ι α : Type}` are any types (`ι` an index type such as `d` or
  `d × d`, `α` a number type such as `ℂ`). A bracket such as `[Zero α]` is a requirement on `α` (a *type
  class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `d → ℂ` | a vector of `ℂ^d`: a function from the index type `d` to `ℂ`. `v k` is its `k`-th coordinate |
| `[Fintype d]` | `d` is finite (needed to sum over it in a matrix product) |
| `[DecidableEq d]` | equality of indices can be decided (needed by `Pi.single` and by `if k = i then …`) |
| `[Nontrivial d]` | `d` has two different elements, i.e. dimension `≥ 2` (R2) |
| `inst✝ : Nontrivial d` | how the infoview shows such a bracket hypothesis; it has no usable name |
| `d × d`, `p : d × d` | the type of index pairs; `p.1`, `p.2` are its components, `(i, j)` is a pair |
| `Matrix (d × d) (d × d) ℂ` | a square matrix on `ℂ^d ⊗ ℂ^d`, rows and columns indexed by pairs |
| `C *ᵥ v` | `Matrix.mulVec C v`, the matrix `C` times the column vector `v` (needs `open Matrix`) |
| `fun p => v p.1 * e p.2` | the product vector `v ⊗ e`, written entrywise: `(v ⊗ e)(p₁, p₂) = v p₁ · e p₂` |
| `(C *ᵥ fun p => …)` | the parentheses Lean prints around `C *ᵥ (fun p => …)` |
| `Pi.single i 1` | the basis vector `\|i⟩`: `1` at index `i`, `0` elsewhere (R5, R10, R17) |
| `Pi.single i 1 p.1` | that vector evaluated at the index `p.1` |
| `c • fun p => …` | `c • (fun p => …)`: the scalar `c` times the whole vector. A `fun` extends as far right as possible, so Lean drops the parentheses |
| `f + g`, `c • f` | vectors added / scaled pointwise: `(f + g) x = f x + g x`, `(c • f) x = c • f x` (R9, R16) |
| `0 k` | the zero vector evaluated at `k` (R6) |
| `a ≠ b` | `a = b → False` (R3) |
| `¬A` | `A → False` (R1) |
| `if i' = i then x else 0` | what `Pi.single i x i'` unfolds to (R17) |
| `this` | the name `have :=` gives a fact when you do not name it |

---

## Part 1 · `no_linear_cloner`

Statement: for a matrix `C` on `ℂ^d ⊗ ℂ^d` and a blank vector `e : d → ℂ`, it is not the case that every
nonzero `v` satisfies `C *ᵥ (v ⊗ e) = c • (v ⊗ v)` for some `c ≠ 0`.

### Proof by contradiction and two distinct indices

**R1 · `intro h` on `¬ A`** changes the **goal and the context**. `¬ A` is `A → False`, so `intro` moves `A` into
the context and leaves `False` to prove. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `h : A ⊢ False` |

**R2 · `obtain ⟨i, j, hij⟩ := exists_pair_ne α`** changes the **context**. The lemma is
`exists_pair_ne (α : Type) [Nontrivial α] : ∃ x y, x ≠ y`; the type is an explicit argument. Placeholders:
`(α : Type) [Nontrivial α]` (α has two different elements; `Fin 2`, `ℕ`, `ℂ` qualify, and so does `d` here).

| Before | After |
|---|---|
| `⊢ G` | `i j : α, hij : i ≠ j ⊢ G` |

### Showing a vector is nonzero

To use the cloner on `v` you must give `v ≠ 0`. A vector is nonzero when one coordinate is: assume `v = 0`,
evaluate at that coordinate, and let `simp` see `1 = 0`.

**R3 · `intro hk` on `a ≠ b`** changes the **goal and the context**: `a ≠ b` is `a = b → False`. As a term you
can write `fun hk => by …` instead (as in `have ne : ∀ k, … ≠ 0 := fun k hk => by …`). Placeholders:
`{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `hk : a = b ⊢ False` |

**R4 · `have := congrFun hk x`** changes the **context**. The lemma is `congrFun : f = g → ∀ x, f x = g x`: an
equation of functions (here: vectors) gives the equation of their values at `x`. Placeholders:
`{ι β : Type} (f g : ι → β) (hk : f = g) (x : ι)`. For a vector on pairs, `x` is a pair such as `(i, j)`.

| Before | After |
|---|---|
| `hk : f = g ⊢ G` | `this : f x = g x ⊢ G` |

**R5 · `Pi.single_eq_same`** changes the **goal**: `Pi.single i x i = x`, a basis vector at its own index.
Placeholders: `{ι α : Type} [DecidableEq ι] [Zero α] (i : ι) (x : α)` (`ℂ`, `ℝ` have a `0`). `simp` applies it by
itself.

| Before | After |
|---|---|
| `⊢ P (Pi.single i x i)` | `⊢ P x` |

**R6 · `Pi.zero_apply`** changes the **goal**: `(0 : ι → α) k = 0`, the zero vector at any index is the number
`0`. Placeholders: `{ι α : Type} [Zero α] (k : ι)`. `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P (0 k)` | `⊢ P 0` |

**R7 · `simp at h` turning `h` into `False`** changes the **goal list**: when the simplified hypothesis is `False`,
the goal is closed, whatever it was. `simp` knows `one_ne_zero : 1 ≠ 0`, so `h : 1 = 0` becomes `False`. With
R4–R6, `this : Pi.single k 1 k = 0 k` simplifies to `1 = 0`, then to `False`.

| Before | After |
|---|---|
| `h : 1 = 0 ⊢ G` | no goals |

### Using the cloner

**R8 · `obtain ⟨c, -, hc⟩ := h a ha`** changes the **context**. With
`h : ∀ x, Q x → ∃ y, R x y ∧ S x y`, the term `h a ha` is `∃ y, R a y ∧ S a y`; `obtain` unpacks the `∃` and
the `∧`, and `-` throws away a part you do not need (here `R a b`). `h _ hs0` lets Lean infer the `_` from the
type of `hs0`. Placeholders: `{α β : Type} (Q : α → Prop) (R S : α → β → Prop) (a : α) (ha : Q a)`.

| Before | After |
|---|---|
| `⊢ G` | `b : β, hb : S a b ⊢ G` |

In the exercise the cloner gives `hi : (C *ᵥ fun p => Pi.single i 1 p.1 * e p.2) = ci • fun p => …` and
the same for `j`. Keep `hc : c ≠ 0` only for the superposition: it is the fact that ends the proof.

### A superposition is nonzero

**R9 · `Pi.add_apply`** changes the **goal**: `(f + g) x = f x + g x`, vector addition is pointwise.
Placeholders: `{ι α : Type} [Add α] (f g : ι → α) (x : ι)`. `simp` applies it by itself.

| Before | After |
|---|---|
| `⊢ P ((f + g) x)` | `⊢ P (f x + g x)` |

**R10 · `rw [Pi.single_eq_of_ne hne]`** changes the **goal**. The lemma is
`Pi.single_eq_of_ne : i' ≠ i → Pi.single i x i' = 0`: a basis vector off its own index. Note the order: the
hypothesis is `i' ≠ i`, the evaluation index first. Placeholders:
`{ι α : Type} [DecidableEq ι] [Zero α] (i i' : ι) (hne : i' ≠ i) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (Pi.single i x i')` | `⊢ P 0` |

**R11 · `hab.symm`** (`Ne.symm : a ≠ b → b ≠ a`) changes the **context** when you name it with `have`, or is
passed directly: `simp [hij.symm]`. Placeholders: `{α : Type} (a b : α) (hab : a ≠ b)`.

| Before | After |
|---|---|
| `hab : a ≠ b ⊢ G` | `hba : b ≠ a ⊢ G` |

With R9, R5, R10 the fact `(Pi.single i 1 + Pi.single j 1) i = 0 i` becomes `1 + 0 = 0`. Plain `simp at this`
stops at `this : 1 + Pi.single j 1 i = 0`: to evaluate `Pi.single j 1 i` it must know the indices differ, so pass
the fact, `simp [hij] at this` (R10 wants `i ≠ j` here, the evaluation index first, which is `hij` itself) or
`simp [hij.symm] at this` (R11; the twin lemma `Pi.single_eq_of_ne' : i ≠ i' → Pi.single i x i' = 0` uses it).
Either way `simp` then closes the goal as in R7.

### Splitting the superposition

**R12 · `funext p`** changes the **goal and the context**: two functions are equal when they agree at every
point. Placeholders: `{ι β : Type} (f g : ι → β)`. For the `lin` fact, `ι` is `d × d` and `p` is an index pair.

| Before | After |
|---|---|
| `⊢ f = g` | `p : ι ⊢ f p = g p` |

**R13 · `add_mul`** changes the **goal**: `(a + b) * c = a * c + b * c`. Placeholders:
`{α : Type} [Semiring α] (a b c : α)` (α has `+`, `*` and distributivity; `ℂ`, `ℝ`, `ℕ` qualify). `mul_add` is the
left-hand version `a * (b + c) = a * b + a * c` (W2).

| Before | After |
|---|---|
| `⊢ P ((a + b) * c)` | `⊢ P (a * c + b * c)` |

**R14 · `rw [e] at h`** changes the **context**: it rewrites the hypothesis `h` instead of the goal. With a list,
`rw [e₁, e₂, e₃] at h` applies them in order, each to the result of the previous. Placeholders:
`{α : Type} (a b : α) (e : a = b)`.

| Before | After |
|---|---|
| `h : P a ⊢ P b` | `h : P b ⊢ P b` |

**R15 · `Matrix.mulVec_add`** changes the **goal** (or, with `at`, a hypothesis): `A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y`,
a matrix acts linearly. Placeholders: `{m n α : Type} [Fintype n] [Semiring α] (A : Matrix m n α) (x y : n → α)`
(`m` rows, `n` columns; in the exercise both are `d × d` and `α = ℂ`).

| Before | After |
|---|---|
| `⊢ P (A *ᵥ (x + y))` | `⊢ P (A *ᵥ x + A *ᵥ y)` |

`rw [Matrix.mulVec_add] at hs` only fires once the input of `C` is literally a sum `f + g`. That is why the
`lin` fact comes first: `fun p => (|i⟩ + |j⟩) p.1 * e p.2` is a single `fun`, not a sum of two vectors.

### Evaluating at one index pair

After R14, R15 and `congrFun hs (i, j)` (R4), the hypothesis is an equation of numbers built from `+`, `•` and
`Pi.single … p.1` at `p = (i, j)`. `simp` evaluates it with R9, R16, R17, R18.

**R16 · `Pi.smul_apply`, then `smul_eq_mul`** change the **goal**: scaling is pointwise, and a number scaling a
number is multiplication. Placeholders: `{ι α : Type} [Mul α] (c : α) (f : ι → α) (x : ι)`.

| Before | After `rw [Pi.smul_apply]` | After `rw [smul_eq_mul]` |
|---|---|---|
| `⊢ P ((c • f) x)` | `⊢ P (c • f x)` | `⊢ P (c * f x)` |

**R17 · `Pi.single_apply`** changes the **goal**: `Pi.single i x i' = if i' = i then x else 0`. Use it when you do
not know in advance whether the index equals `i`, then let R18 decide. Placeholders:
`{ι α : Type} [DecidableEq ι] [Zero α] (i i' : ι) (x : α)`.

| Before | After |
|---|---|
| `⊢ P (Pi.single i x i')` | `⊢ P (if i' = i then x else 0)` |

**R18 · `simp [hne]`** with `hne : a ≠ b` changes the **goal**: it rewrites `a = b` to `False` and `a = a` to
`True`, and then picks the matching branch of each `if`. It does **not** flip: `b = a` needs `hne.symm`
(R11). Placeholders: `{ι α : Type} [DecidableEq ι] (a b : ι) (hne : a ≠ b) (x y : α)`.

| Before | After |
|---|---|
| `⊢ P (if a = b then x else y) ∧ P (if a = a then x else y)` | `⊢ P y ∧ P x` |

**R19 · `exact hc h.symm`** **closes** `False`. `h.symm : a = b` (`Eq.symm`), and `hc : a ≠ b` is a function
from `a = b` to `False`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `hc : a ≠ b, h : b = a ⊢ False` | no goals |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: a basis vector of `ℝ^3` is nonzero** (R3, R4, then `simp` with R5, R6, R7):

| Before | After `intro hk` | After `have := congrFun hk 2` |
|---|---|---|
| `⊢ Pi.single 2 5 ≠ 0` | `hk : Pi.single 2 5 = 0 ⊢ False` | `this : Pi.single 2 5 2 = 0 2 ⊢ False` |

and `simp at this` closes it (`5 = 0` is `False`).

**W2: splitting the second slot** `e ⊗ (u + w) = e ⊗ u + e ⊗ w` on `Fin 2 × Fin 2`: `funext p` (R12), then
`simp [mul_add]` (R9 on both sides, then `mul_add`):

```lean-goal
⊢ (fun p => e p.1 * (u + w) p.2) = (fun p => e p.1 * u p.2) + fun p => e p.1 * w p.2
⊢ e p.1 * (u + w) p.2 = ((fun p => e p.1 * u p.2) + fun p => e p.1 * w p.2) p
```

**W3: linearity at a hypothesis.** A matrix `A` on `ℝ^2` with `A |0⟩ = |0⟩` and `A |1⟩ = |1⟩` cannot send
`|0⟩ + |1⟩` to `0`. `rw [Matrix.mulVec_add, hx, hy] at h` (R14, R15), then R4 at index `0`, then `simp at this`:

| Before | After `rw [Matrix.mulVec_add, hx, hy] at h` | After `have := congrFun h 0` |
|---|---|---|
| `h : A *ᵥ (Pi.single 0 1 + Pi.single 1 1) = 0 ⊢ False` | `h : Pi.single 0 1 + Pi.single 1 1 = 0 ⊢ False` | `this : (Pi.single 0 1 + Pi.single 1 1) 0 = 0 0 ⊢ False` |

**W4: a scaled product vector vanishes off the diagonal.** On `Fin 3 × Fin 3`, the hypothesis

```lean
h : (a • fun p => Pi.single 0 1 p.1 * Pi.single 0 1 p.2) (0, 2) = c
```

is `a · (|0⟩ ⊗ |0⟩)` at the pair `(0, 2)`. `simp [Pi.single_apply] at h` (R16, R17, R18; `0 = 2` is decided for
numerals) turns it into `0 = c`, and `exact h.symm` closes the goal:

| Before | After `simp [Pi.single_apply] at h` |
|---|---|
| `⊢ c = 0` | `h : 0 = c ⊢ c = 0` |

This is the last step of the exercise in miniature: there the same `simp` needs `hij` and `hij.symm` to decide
`i = j` and `j = i`, and ends with `this : 0 = c` next to `hc : c ≠ 0` (R19).

---

## Traps

- `simp [hij]` with `hij : i ≠ j` rewrites `i = j` to `False` but not `j = i`, so an `if j = i then … else …` (from
  R17) stays. In the last step pass both: `simp [Pi.single_apply, hij, hij.symm]` (R18).
- Plain `simp at this` with no index fact leaves `this : 1 + Pi.single j 1 i = 0` in the nonzero proof for
  `|i⟩ + |j⟩`: `simp` cannot evaluate `Pi.single j 1 i` without `hij` (or `hij.symm`) in its list.
- `rw [Matrix.mulVec_add] at hs` fails on `C *ᵥ fun p => (Pi.single i 1 + Pi.single j 1) p.1 * e p.2`: the
  input is one `fun`, not a sum. Prove the splitting `lin` first (R12, R13) and `rw [lin]` before R15.
- `Pi.single i 1` alone does not know its type; write `(Pi.single i 1 : d → ℂ)` in a `have`, or Lean cannot
  elaborate it (`Type mismatch … ?m`).
- In `obtain ⟨c, hc, hs⟩ := h _ hs0`, keep `hc`: the basis cases may drop theirs with `-`, the superposition
  case may not.
- `Pi.single_eq_of_ne` wants `i' ≠ i` (evaluation index first). If you hold `i ≠ i'`, pass `hne.symm`.
- `exists_pair_ne` takes the type explicitly: `exists_pair_ne d`, not `exists_pair_ne`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `¬ A` | `intro h` (goal becomes `False`) | R1 |
| two different indices | `obtain ⟨i, j, hij⟩ := exists_pair_ne d` | R2 |
| prove `v ≠ 0` | `intro hk` or `fun hk => by …` | R3 |
| vector equation → coordinate equation | `have := congrFun hk x` | R4 |
| `\|i⟩` at `i` / at `i' ≠ i` / at unknown `i'` | `Pi.single_eq_same` / `Pi.single_eq_of_ne` / `Pi.single_apply` | R5, R10, R17 |
| zero vector at an index | `Pi.zero_apply` | R6 |
| a hypothesis simplifies to `1 = 0` | `simp at this` closes the goal | R7 |
| use the cloner on `v` | `obtain ⟨c, -, hv⟩ := h v hv0` | R8 |
| `(f + g) x`, `(c • f) x` | `Pi.add_apply`; `Pi.smul_apply`, `smul_eq_mul` | R9, R16 |
| flip `i ≠ j` | `hij.symm` | R11 |
| equation of functions | `funext p` | R12 |
| `(a + b) * c` | `add_mul` (`mul_add` for `a * (b + c)`) | R13 |
| rewrite a hypothesis | `rw [e₁, e₂] at h` | R14 |
| `A *ᵥ (x + y)` | `Matrix.mulVec_add` | R15 |
| decide `if i = j` | `simp [hij, hij.symm]` | R18 |
| `hc : c ≠ 0` and `this : 0 = c` | `exact hc this.symm` | R19 |
| see the state | infoview | |
