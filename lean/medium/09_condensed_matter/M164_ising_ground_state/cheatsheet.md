# M164 · Ising ground state: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ` and the cast
`ℕ → ℝ`, finite sums `∑` over `Fin n`, `Set.range`, `lowerBounds` and `IsLeast`, case splits on `Bool`,
`calc` chains, and the automation tactics `norm_num` and `nlinarith`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Preorder β]`
  is a requirement on `β` (a *type class*): here, that `β` has a `≤` that is reflexive and transitive.
  `ℝ`, `ℕ`, `ℤ` all qualify.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ`, `ℕ` | Mathlib's real numbers; Lean's natural numbers |
| `↑n` | the natural number `n` cast into `ℝ` (the spec writes `-J * n`, Lean inserts the cast) |
| `Fin n` | the type `{0, 1, …, n-1}`; a bond index. Sites are `Fin (n + 1)` |
| `i.castSucc`, `i.succ` | for `i : Fin n`, the sites `i` and `i + 1` as elements of `Fin (n + 1)`: the two ends of bond `i`. No wrap-around |
| `σ : Fin (n + 1) → Bool` | a spin configuration; `true` = up (`+1`), `false` = down (`-1`) |
| `∑ i, f i` | `∑ i ∈ Finset.univ, f i`: the sum over every `i` of a finite type (here `Fin n`) |
| `∑ _i, c` | a sum whose terms do not depend on the index |
| `Finset.univ` | the finite set of *all* elements of a finite type (here all of `Fin n`) |
| `∀ i ∈ s, P i` | `∀ i, i ∈ s → P i` |
| `Set.range f` | the set `{f x \| x}` of all values of `f`; `a ∈ Set.range f` means `∃ x, f x = a` |
| `lowerBounds s` | the set of all `a` with `a ≤ y` for every `y ∈ s` |
| `IsLeast s a` | `a ∈ s ∧ a ∈ lowerBounds s`: `a` is the minimum of `s` (attained) |
| `energy J (n := n)` | `energy` with its implicit argument `n` filled by name; Lean prints it as `energy J` |
| `energy J fun x => true` | `energy J` applied to the all-up configuration `fun x => true` |
| `if b = true then x else y` | how Lean prints `if b then x else y` for `b : Bool` |
| `if True then x else y` | the same after `simp` evaluated `true = true` to the proposition `True` |
| `a✝` | a hypothesis with no usable name (you wrote `_`) |
| `case refine_1`, `case false.true` | names of the goals produced by `refine` and `cases` (`false.true`: `a = false`, `b = true` after `cases a <;> cases b`) |

---

## Part 1 · `ground_state`

Statement: for `J ≥ 0`, `IsLeast (Set.range (energy J (n := n))) (-J * n)`. In words: the energy
`E(σ) = -J ∑ᵢ s(σᵢ) s(σᵢ₊₁)` of an open chain of `n + 1` Ising spins, `s(true) = 1`, `s(false) = -1`,
takes the value `-J n` for some configuration `σ`, and never goes below it.

### Least element of a range: attained

**R1 · `refine ⟨?_, ?_⟩` on `IsLeast s a`** changes the **goal list**: `IsLeast s a` is by definition
the conjunction `a ∈ s ∧ a ∈ lowerBounds s`, so the anonymous constructor splits it into "attained" and
"lower bound". Placeholders: `{α : Type} [Preorder α] (s : Set α) (a : α)`.

| Before | After |
|---|---|
| `⊢ IsLeast s a` | `⊢ a ∈ s`, `⊢ a ∈ lowerBounds s` |

**R2 · `refine ⟨x, ?_⟩` on `a ∈ Set.range f`** changes the **goal**: membership in a range is
`∃ x, f x = a`, so you name the witness `x` and are left with the equation. Placeholders:
`{α β : Type} (f : α → β) (a : β) (x : α)`. Nested form: `refine ⟨⟨x, by …⟩, ?_⟩` does R1 and R2 at once.

| Before | After |
|---|---|
| `⊢ a ∈ Set.range f` | `⊢ f x = a` |

### Evaluating one configuration (`simp [names]` does R3–R5 together)

**R3 · `simp only [D]`** changes the **goal**: it replaces the defined name `D` by its body.
Placeholders: `D` defined by `def w (b : Bool) : ℝ := if b then 3 else -2`, `(b : Bool)`.

| Before | After |
|---|---|
| `⊢ P (w b)` | `⊢ P (if b = true then 3 else -2)` |

**R4 · `simp` on an `if` with a literal Boolean** changes the **goal**: it picks the branch
(lemmas `if_pos : c → (if c then x else y) = x`, `if_neg : ¬c → (if c then x else y) = y`, and
`Bool.false_eq_true : (false = true) = False`). Placeholders: `(x y : ℝ)`. If you unfold step by step with
`simp only [energy, spin]`, the condition already shows as `True` (`if True then 1 else -1`, see *Reading the goals*);
a plain `simp` then picks the branch and finishes.

| Before | After |
|---|---|
| `⊢ P (if true = true then x else y) ∧ P (if false = true then x else y)` | `⊢ P x ∧ P y` |

**R5 · `simp` on a constant sum** changes the **goal**: `∑ _i : Fin n, c` becomes `↑n * c`. The lemmas
are `Finset.sum_const : ∑ _i ∈ s, c = s.card • c` (`s.card` is the number of elements of the finite set `s`),
`Finset.card_univ : Finset.univ.card = Fintype.card α` (`Fintype.card α` counts the elements of a finite type `α`),
`Fintype.card_fin : Fintype.card (Fin n) = n` and `nsmul_eq_mul : n • c = ↑n * c` (`•` is repeated addition). With `c = 1`, `simp` also removes `* 1`.
Placeholders: `(n : ℕ) (c : ℝ)`. Write the type of a constant sum: `∑ _i : Fin n, (1 : ℝ)`, else it is in `ℕ`.

| Before | After |
|---|---|
| `⊢ P (∑ _i, c)` | `⊢ P (↑n * c)` |

### Least element of a range: lower bound

**R6 · `rintro _ ⟨x, rfl⟩` on `a ∈ lowerBounds (Set.range f)`** changes the **context and the goal**.
`a ∈ lowerBounds s` unfolds to `∀ ⦃y⦄, y ∈ s → a ≤ y` (`⦃y⦄` is a *strict-implicit* binder: `y` is filled in
only once the membership proof is supplied; `intro`/`rintro` introduce it like an ordinary `∀`). `rintro` introduces `y` (unnamed, `_`) and
`y ∈ Set.range f`, splits that `∃` into `x` and `f x = y`, and `rfl` substitutes `y := f x`.
Placeholders: `{α β : Type} [Preorder β] (f : α → β) (a : β)`.

| Before | After |
|---|---|
| `⊢ a ∈ lowerBounds (Set.range f)` | `x : α ⊢ a ≤ f x` |

**R7 · `cases b` with `b : Bool`** changes the **goal list and the context**: `b` leaves the context and
there is one goal per value. Placeholders: `(P : Bool → Prop) (b : Bool)`. `cases a <;> cases b` gives all
four pairs.

| Before | After |
|---|---|
| `b : Bool ⊢ P b` | `⊢ P false`, `⊢ P true` |

**R8 · `norm_num [D]`** **closes** a numeric goal after unfolding `D`: it does R3, R4 and the
arithmetic (`3 * -2 ≤ 1`) in one call. Example: `w true * w false ≤ 1`.

**R9 · `calc`** **closes** `a ≤ c` from a chain of steps, each with its own proof after `:=`. Steps may mix
`≤`, `<` and `=`; the relation of the chain is the weakest one used. Placeholders: `(a b c : ℝ)`.
Lines after the first start with `_`, indented under the first term.

| Before | After |
|---|---|
| `⊢ a ≤ c` | proofs of `a ≤ b` and `b = c` |

**R10 · `Finset.sum_le_sum`** changes the **goal**: a sum inequality becomes a termwise one. The lemma is
`(∀ i ∈ s, f i ≤ g i) → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`; for `∑ i : Fin n`, `s` is `Finset.univ`.
Placeholders: `(n : ℕ) (f g : Fin n → ℝ)`. As a term inside a `calc` step: `Finset.sum_le_sum fun i _ => h i`.

| Before | After `apply Finset.sum_le_sum` | After `intro i _` |
|---|---|---|
| `⊢ ∑ i, f i ≤ ∑ i, g i` | `⊢ ∀ i ∈ Finset.univ, f i ≤ g i` | `i : Fin n, a✝ : i ∈ Finset.univ ⊢ f i ≤ g i` |

### Finishing

**R11 · `unfold D`** changes the **goal**: the name `D`, applied to its arguments, becomes its body.
Needed because `nlinarith` does not look inside definitions. Placeholders: `def lin (k x : ℝ) : ℝ := -k * x`,
`(k x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (lin k x)` | `⊢ P (-k * x)` |

**R12 · `nlinarith`** **closes** a linear or polynomial inequality over `ℝ` from the hypotheses in the
context. Beyond `linarith` (linear combinations of hypotheses), it multiplies pairs of them first: from
`hk : 0 ≤ k` and `h : S ≤ m` it uses `k * (m - S) ≥ 0`, which gives `-k * m ≤ -k * S`. Every fact it
needs (here `hJ` and your sum bound) must be in the context; `S` may be any term, such as a whole sum.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: a least element of a range over `Bool`** (R1, R2, R4, R6, R7). `w true = 3`, `w false = -2`:

```lean-goal
⊢ IsLeast (Set.range w) (-2)
⊢ -2 ∈ lowerBounds (Set.range w)
⊢ -2 ≤ w b
```

The first line is the start; after `refine ⟨⟨false, by simp [w]⟩, ?_⟩` only the lower bound is left;
after `rintro _ ⟨b, rfl⟩` it is one inequality, closed by `cases b <;> norm_num [w]`.

**W2: a sum of bounded terms is bounded** (R9, R10, R5): from `hf : ∀ i, f i ≤ 3`,

```lean-goal
⊢ ∑ i, f i ≤ ↑n * 3
```

is a `calc` through `∑ _i : Fin n, (3 : ℝ)`: the first step by `Finset.sum_le_sum fun i _ => hf i`, the
second by `simp`.

**W3: scaling by a nonpositive factor** (R11, R12):

```lean-goal
⊢ lin k m ≤ lin k x
⊢ -k * m ≤ -k * x
```

`unfold lin`, then `nlinarith` with `hk : 0 ≤ k` and `hx : x ≤ m` in the context.

---

## Traps

- `nlinarith` and `linarith` do not unfold `energy`: `unfold energy` (R11) first, or the goal is an
  opaque `-J * ↑n ≤ energy J σ`.
- They also do not prove the sum bound for you: state it as a `have` whose left side is the sum **exactly**
  as it appears after `unfold energy` (`∑ i : Fin n, spin (σ i.castSucc) * spin (σ i.succ)`).
- `∑ _i : Fin n, 1` without `(1 : ℝ)` is a sum in `ℕ`, and the `calc` step no longer type-checks.
- `cases a <;> cases b`: with `;` instead of `<;>` the second split runs on the first goal only.
- `hb _ _` inside `Finset.sum_le_sum fun i _ => hb _ _`: each `_` is a `Bool` that Lean reads off the goal
  `spin (σ i.castSucc) * spin (σ i.succ) ≤ 1` (here `σ i.castSucc` and `σ i.succ`). The second `_` in
  `fun i _ =>` is the unused proof of `i ∈ Finset.univ`.
- `spin` is a `def` with an `if`: `norm_num` alone does not see inside it; write `norm_num [spin]`.
- Bonds are indexed by `Fin n`, sites by `Fin (n + 1)`; `i.castSucc` is not `i` (different types).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `IsLeast s a` | `refine ⟨?_, ?_⟩` | R1 |
| show `a ∈ Set.range f` | `refine ⟨x, ?_⟩` or `⟨x, proof⟩` | R2 |
| evaluate a definition with an `if` on a literal | `simp [D]` | R3, R4 |
| `∑ _i : Fin n, c` → `↑n * c` | `simp` | R5 |
| take an arbitrary element of a range | `rintro _ ⟨x, rfl⟩` | R6 |
| all values of a `Bool` | `cases b` (`cases a <;> cases b` for pairs) | R7 |
| numeric goal after unfolding `D` | `norm_num [D]` | R8 |
| chain `≤` and `=` | `calc a ≤ b := … ` / `_ = c := …` | R9 |
| sum ≤ sum, termwise | `Finset.sum_le_sum fun i _ => h i` | R10 |
| expose a definition for arithmetic | `unfold D` | R11 |
| inequality needing a product of hypotheses | `nlinarith` | R12 |
| add a fact | `have h : T := by …` | TACTIC_STATES |
| see the state | infoview | |
