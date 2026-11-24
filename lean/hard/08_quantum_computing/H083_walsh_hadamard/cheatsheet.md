# H083 · Walsh–Hadamard: Bernstein–Vazirani and Deutsch–Jozsa: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `constructor`, `exact`, `rw`, `simp`,
`have`, `funext`, `fin_cases`, `ring`, `norm_num`.
**New here:** Mathlib's finite sums and products `∑`, `∏` over a finite type (`Finset`, `Fintype`), the
bit type `Fin 2` and its arithmetic, bit strings `Fin n → Fin 2` with pointwise `+`, complex numbers with
real numbers cast into them, `Real.sqrt`, `Pi.single` (basis vectors), and `Finset.filter` (a sub-Finset
cut out by a predicate).

**The maths.** A bit string is `x : Fin n → Fin 2`, i.e. `x = (x₀, …, x_{n−1})` with `xᵢ ∈ {0, 1}`.
`dot x y = ∑ᵢ xᵢ yᵢ ∈ ℕ`; only its parity matters, through the *character* `χ_x(y) = (−1)^{x·y}`.
`W v` is `H^{⊗n} v`: `(W v)(y) = 2^{−n/2} ∑ₓ χ_x(y) v(x)`. The two facts that carry everything:

- **character sum** (MILESTONE `char_sum`): `∑_y (−1)^{x·y} = 2ⁿ` if `x = 0`, else `0`. Proof: `(−1)^{∑ᵢ xᵢyᵢ} = ∏ᵢ (−1)^{xᵢyᵢ}`,
  so `∑_y ∏ᵢ = ∏ᵢ ∑_{b ∈ {0,1}} (−1)^{xᵢ b} = ∏ᵢ (1 + (−1)^{xᵢ})`, and a factor with `xᵢ = 1` is `0`.
- **characters multiply** (MILESTONE `neg_one_pow_dot_add`): `(−1)^{x·y} (−1)^{x·z} = (−1)^{x·(y+z)}`, where `y + z`
  is bitwise XOR. Coordinatewise, it is an identity of three bits: check all 8 cases.

Then `W (W v) = v` and Bernstein–Vazirani are "regroup, then apply the character sum to `y + z`", and
`y + z = 0 ↔ z = y` (MILESTONE `bits_add_eq_zero`). Deutsch–Jozsa needs neither: `dot x 0 = 0`, so the `|0…0⟩`
amplitude is `2^{−n} ∑ₓ (−1)^{f(x)}`, and a balanced `f` has as many `+1` as `−1` terms.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[CommMonoid M]` is a
  requirement on `M` (a *type class*). Each entry says which familiar types meet it; `ℂ` meets every one
  used here (`CommMonoid`, `CommSemiring`, `AddCommMonoid`, `DivisionMonoid`, `CommMonoidWithZero`).
  `[Fintype ι]` says `ι` is finite, so `∑ i, f i` makes sense; `Fin n` and `Fin n → Fin 2` are.
  `[DecidableEq ι]` says `=` on `ι` can be tested, so `if x = a then … else …` makes sense.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Fin 2` | the bits `{0, 1}`; `+` is addition mod 2 (XOR), so `1 + 1 = 0` |
| `Fin n → Fin 2` | a bit string of length `n` (function from positions to bits) |
| `x + y`, `0` on bit strings | pointwise XOR; the all-zero string `0…0` (R17) |
| `0 x_1` | the zero bit string applied to position `x_1`: the bit `0` |
| `↑(x i)`, `↑a` | the bit `x i : Fin 2` (or `a`) as a natural number `0` or `1` (`Fin.val`) |
| `∑ x, f x`, `∏ i, f i` | sum / product over every element of a finite type (`Finset.univ`) |
| `∑ x ∈ s, f x` | sum over the elements of a `Finset s` (a finite set) |
| `x_1`, `y_1` | bound variables Lean renamed to avoid a clash; the name does not matter |
| `(fun i => i) ⟨0, ⋯⟩`, `⟨1, ⋯⟩` | the bit `0` (resp. `1`), printed this way after `fin_cases` |
| `case «0».«1».«0»` | after `fin_cases a <;> fin_cases b <;> fin_cases c`: the goal for `a = 0, b = 1, c = 0` |
| `x✝`, `h✝` | inaccessible names (made by a tactic); you cannot type them |
| `↑√(2 ^ n)` | the real number `Real.sqrt (2 ^ n)` cast into `ℂ` |
| `(↑√(2 ^ n))⁻¹` | `2^{−n/2}` as a complex number |
| `dot x y` | the exercise's `∑ i, (x i).val * (y i).val` (unfold with `simp_rw [dot]`, R1) |
| `Pi.single s 1 y` | the basis vector `\|s⟩` at `y`: `1` if `y = s`, else `0` (R38) |
| `{x \| f x = 0}` | the **Finset** `Finset.univ.filter (fun x => f x = 0)`: all `x` with `f x = 0` (not a `Set`) |
| `Finset.filter p Finset.univ` | the same, printed this way when `p` is a variable |
| `s.card` | the number of elements of the Finset `s` |
| `∑ x with p x, f x` | sum over `{x \| p x}` (R40) |
| `k • c` with `k : ℕ` | `c + ⋯ + c`, `k` copies (R43) |
| `case pos`, `case neg` | the two branches after `split_ifs` (R7) |
| `case mp`, `case mpr` | the two directions `→`, `←` after `constructor` on `↔` |

---

## Part 1 · `char_sum` (MILESTONE 1)

Statement: `∑ y : Fin n → Fin 2, (-1 : ℂ) ^ dot x y = if x = 0 then 2 ^ n else 0`. Used in Parts 5 and 6,
always at `x = y + z`.

**R1 · `simp_rw [h]`** changes the **goal**: it rewrites under binders such as `∑ i, …` or `fun i => …`,
where `rw` fails (`rw` cannot see the bound `i`). With a definition name, `simp_rw [D]` unfolds `D` there.
`simp only [h]` does the same in one pass. Placeholders: `{ι β : Type} [Fintype ι] [AddCommMonoid β]`
(`β` has `+` and `0`, as `ℂ` and `ℕ` do), `(f g : ι → β) (hfg : ∀ i, f i = g i)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (∑ x, g x)` |

**R2 · `rw [← Finset.prod_pow_eq_pow_sum]`** changes the **goal**. The lemma is
`∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i` (exponent sum = product of powers); right to left it splits
`(−1)^{∑ᵢ xᵢyᵢ}` into `∏ᵢ (−1)^{xᵢyᵢ}`. Placeholders: `{ι M : Type} [Fintype ι] [CommMonoid M]`
(commutative `*`; `ℂ`), `(f : ι → ℕ) (a : M)`. Under `∑ y` use it inside `simp_rw` (R1).

| Before | After |
|---|---|
| `⊢ P (a ^ ∑ i, f i)` | `⊢ P (∏ i, a ^ f i)` |

**R3 · `rw [← Fintype.prod_sum f]`** changes the **goal**. The lemma is
`Fintype.prod_sum f : ∏ i, ∑ j, f i j = ∑ x, ∏ i, f i (x i)`, where `x` ranges over all functions
`ι → κ`: expanding a product of sums gives one term per choice function. Right to left, a sum over bit
strings of a product becomes a product of two-term sums. **Give `f` explicitly**; here
`f = fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val)`. Placeholders: `{ι κ R : Type} [Fintype ι]
[DecidableEq ι] [Fintype κ] [CommSemiring R]` (`+` and commutative `*`; `ℂ`), `(f : ι → κ → R)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, ∏ i, f i (x i))` | `⊢ P (∏ i, ∑ j, f i j)` |

**R4 · `Fin.sum_univ_two`** changes the **goal**: a sum over `Fin 2` becomes two terms. Placeholders:
`{β : Type} [AddCommMonoid β] (f : Fin 2 → β)`.

| Before | After |
|---|---|
| `⊢ P (∑ i, f i)` | `⊢ P (f 0 + f 1)` |

**R5 · `Fin.val_zero`, `Fin.val_one`** change the **goal**: the bits `0`, `1` read as natural numbers are
`0`, `1`. In the infoview `↑0` is `(0 : Fin 2).val`.

| Before | After |
|---|---|
| `⊢ P ↑0 ↑1` | `⊢ P 0 1` |

**R6 · `mul_zero`, `mul_one`, `one_mul`, `pow_zero`** change the **goal**: `a * 0 = 0`, `a * 1 = a`,
`1 * a = a`, `a ^ 0 = 1`. Put them in one `simp only [...]` with R4 and R5. Placeholders:
`{M : Type} [CommSemiring M] (c : M) (a : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (c ^ (a * 0) + 1 * c ^ (a * 1))` | `⊢ P (1 + c ^ a)` |

After R1–R6 the character sum reads `∏ x_1, (1 + (-1) ^ ↑(x x_1)) = if x = 0 then 2 ^ n else 0`.

**R7 · `split_ifs with h`** changes the **goal list**: a goal containing `if c then a else b` becomes one goal
per branch, with `h : c` or `h : ¬c` in the context. Placeholders: `{α : Type} (c : Prop) [Decidable c]
(a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h : c ⊢ P a`, `h : ¬c ⊢ P b` |

**R8 · `subst hx`** changes the **context and the goal**: with `hx : x = e` and `x` a local variable, every
`x` becomes `e` and `hx` disappears. (If both sides are variables, the right-hand one is eliminated.)

| Before | After |
|---|---|
| `hx : x = 0 ⊢ P x` | `⊢ P 0` |

**R9 · `Finset.prod_const`, `Finset.card_univ`, `Fintype.card_fin`** change the **goal**: a product of a
constant over `Fin n` is a power, `∏ _i : Fin n, c = c ^ n`. `norm_num` and `simp` use them by themselves,
together with `Pi.zero_apply` (R17), R5 and R6, which is how `norm_num` closes the `x = 0` branch.
Placeholders: `{M : Type} [CommMonoid M] (n : ℕ) (c : M)`.

| Before | After |
|---|---|
| `⊢ P (∏ _i, c)` | `⊢ P (c ^ n)` |

**R10 · `obtain ⟨i, hi⟩ : ∃ i, Q i := proof`** changes the **context**: it proves the existential and unpacks
it into a witness `i` and `hi : Q i`. Here: `∃ i, x i ≠ 0` from `hx : ¬x = 0`. Write `:= by …` with the
proof indented further.

| Before | After |
|---|---|
| `⊢ G` | `i : ι, hi : Q i ⊢ G` |

**R11 · `by_contra hc`** changes the **goal and the context**: to prove `G`, assume `hc : ¬G` and prove `False`.

| Before | After |
|---|---|
| `⊢ G` | `hc : ¬G ⊢ False` |

**R12 · `push Not at hc`** changes the **context**: it pushes `¬` inward, `¬∃ i, a i ≠ b` becomes
`∀ i, a i = b` (also `¬∀ → ∃ ¬`, `¬(p ∧ q) → (p → ¬q)`). `push_neg at hc` is the older spelling.
Placeholders: `{ι β : Type} (a : ι → β) (b : β)`.

| Before | After |
|---|---|
| `hc : ¬∃ i, a i ≠ b` | `hc : ∀ (i : ι), a i = b` |

**R13 · `funext hc`** as a **term**: from `hc : ∀ i, f i = g i` it builds `f = g`. So `exact hx (funext hc)`
**closes** `False` when `hx : ¬f = g`. (The tactic `funext i` goes the other way: goal `f = g` → `f i = g i`.)

| Before | After |
|---|---|
| `hne : ¬f = g ⊢ False` | closed by `exact hne (funext hc)` |

**R14 · `apply Finset.prod_eq_zero (Finset.mem_univ i)`** changes the **goal**: a product is `0` if one factor
is. The lemma is `Finset.prod_eq_zero : i ∈ s → f i = 0 → ∏ j ∈ s, f j = 0`; `Finset.mem_univ i : i ∈
Finset.univ` supplies the first argument. Placeholders: `{ι M₀ : Type} [Fintype ι] [CommMonoidWithZero M₀]`
(`*` with `0 * a = 0`; `ℂ`), `(f : ι → M₀) (i : ι)`.

| Before | After |
|---|---|
| `⊢ ∏ j, f j = 0` | `⊢ f i = 0` |

**R15 · `have h1 : a = 1 := by omega`** changes the **context**: `omega` knows a bit is `0` or `1`, so
`a ≠ 0` gives `a = 1`. It also proves `¬a = 0 ↔ a = 1` (Part 7). Placeholders: `(a : Fin 2)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ G` | `h1 : a = 1 ⊢ G` |

Then `simp [h1]` evaluates `1 + (-1) ^ ↑1 = 0`.

**W1** (another product of sums: `∑_x ∏ᵢ 2^{xᵢ} = ∏ᵢ (2⁰ + 2¹) = 3ⁿ`): R3 with an explicit `f`, then R4–R6,
then `norm_num` (R9):

```lean-goal
⊢ ∑ x, ∏ i, 2 ^ ↑(x i) = 3 ^ n
⊢ ∏ i, ∑ j, 2 ^ ↑j = 3 ^ n
⊢ ∏ x, (1 + 2) = 3 ^ n
```

---

## Part 2 · `neg_one_pow_dot_add` (MILESTONE 2)

Statement: `(-1 : ℂ) ^ dot x y * (-1) ^ dot x z = (-1) ^ dot x (y + z)`. Used in Parts 5 and 6 to merge two
characters into one.

**R16 · `rw [← Finset.prod_mul_distrib]`** changes the **goal**. The lemma is
`∏ i, f i * g i = (∏ i, f i) * ∏ i, g i`; right to left it merges two products over the same index.
Placeholders: `{ι M : Type} [Fintype ι] [CommMonoid M] (f g : ι → M)`.

| Before | After |
|---|---|
| `⊢ P ((∏ i, f i) * ∏ i, g i)` | `⊢ P (∏ x, f x * g x)` |

**R17 · `Pi.add_apply`, `Pi.zero_apply`** change the **goal**: `(f + g) i = f i + g i` and `(0 : ι → β) i = 0`.
On bit strings this is how `(y + z) i` becomes `y i + z i`. Placeholders: `{ι β : Type} [AddZeroClass β]`
(`+` and `0`; `Fin 2`), `(f g : ι → β) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P ((f + g) i) (0 i)` | `⊢ P (f i + g i) 0` |

After step 1 of the skeleton the goal is a product equation
`∏ x_1, (-1) ^ (↑(x x_1) * ↑(y x_1)) * (-1) ^ (↑(x x_1) * ↑(z x_1)) = ∏ i, (-1) ^ (↑(x i) * ↑(y i + z i))`.

**R18 · `refine Finset.prod_congr rfl fun i _ => ?_`** changes the **goal and the context**: two products over
the same Finset are equal if their factors are. The lemma is `Finset.prod_congr : s₁ = s₂ → (∀ x ∈ s₂,
f x = g x) → s₁.prod f = s₂.prod g`. Placeholders: `{ι M : Type} [Fintype ι] [CommMonoid M] (f g : ι → M)`.
(`Finset.sum_congr` is the same for sums, R42.)

| Before | After |
|---|---|
| `⊢ ∏ i, f i = ∏ i, g i` | `i : ι, x✝ : i ∈ Finset.univ ⊢ f i = g i` |

**R19 · `generalize e = a`** changes the **goal and the context**: every occurrence of the term `e` in the goal
becomes a new variable `a`. `fin_cases` needs a variable, not `x i`. It does not touch hypotheses, so
`revert` them first (R24). Placeholders: `{ι α : Type} (x : ι → α) (i : ι)`.

| Before | After |
|---|---|
| `⊢ P (x i)` | `a : α ⊢ P a` |

**R20 · `show (1 + 1 : Fin 2) = 0 from rfl`** is a **term**: a fact stated and proved on the spot, to hand to
`rw` or `simp`. `Fin 2` arithmetic computes, so `rfl` (or `decide`) proves it.

| Before | After |
|---|---|
| `⊢ P (1 + 1)` | `⊢ P 0` |

With three bits `a b c` generalized, `fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [R20]` checks the
8 cases. **W2** does the same for `(-1) ^ ↑a * (-1) ^ ↑b = (-1) ^ ↑(a + b)`:

```lean-goal
⊢ (-1) ^ ↑a * (-1) ^ ↑b = (-1) ^ ↑(a + b)
```

---

## Part 3 · `dot_comm` (MILESTONE 3)

Statement: `dot x y = dot y x`. Used in Parts 5 and 6 to put the summed-over string on the right of `dot`
(`char_sum` sums over the second argument).

**R21 · `simp [mul_comm]`** **closes** a goal that holds after commuting products. `simp` uses `mul_comm` only
in the direction that sorts the factors, so it does not loop. Add `dot` to unfold it. Placeholders:
`{ι R : Type} [Fintype ι] [CommSemiring R] (f g : ι → R)`.

| Before | After |
|---|---|
| `⊢ ∑ i, f i * g i = ∑ i, g i * f i` | closed |

---

## Part 4 · `bits_add_eq_zero` (MILESTONE 4)

Statement: `y + z = 0 ↔ z = y`. Used in Parts 5 and 6: `char_sum` at `x = y + z` tests `y + z = 0`, and this
turns the test into `z = y`.

`constructor` splits the `↔` into `case mp` (`y + z = 0 → z = y`) and `case mpr` (`z = y → y + z = 0`).

**R22 · `have := congrFun h i`** changes the **context**: `congrFun : f = g → ∀ a, f a = g a`. Evaluate an
equation of functions at one point. Placeholders: `{ι β : Type} (f g : ι → β) (i : ι)`.

| Before | After |
|---|---|
| `h : f = g ⊢ G` | `this : f i = g i ⊢ G` |

**R23 · `simp only [l] at h`** changes the **context**: it rewrites the hypothesis `h`, not the goal. Here with
R17's lemmas. Placeholders as in R17.

| Before | After |
|---|---|
| `hi : (f + g) i = 0 i ⊢ G` | `hi : f i + g i = 0 ⊢ G` |

**R24 · `revert h`** changes the **context and the goal**: `h : T` leaves the context and the goal becomes
`T → G`. Do this before `generalize` (R19), so the bits inside `h` are generalized too.

| Before | After |
|---|---|
| `h : T ⊢ G` | `⊢ T → G` |

**R25 · `rintro rfl`** changes the **goal**: it introduces `a = b` and substitutes at once (R8 in one step).
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a = b → P a b` | `⊢ P a a` |

---

## Part 5 · `W_W`

Statement: `W (W v) = v`, i.e. `H^{⊗n}` is an involution. Uses all four milestones.

### The normalisation `hsq : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹`

**R26 · `rw [inv_pow]`** changes the **goal**: `a⁻¹ ^ n = (a ^ n)⁻¹`. Placeholders: `{α : Type}
[DivisionMonoid α]` (`*` and `⁻¹`; `ℂ`, `ℝ`), `(a : α) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a⁻¹ ^ n)` | `⊢ P (a ^ n)⁻¹` |

**R27 · `rw [← Complex.ofReal_pow]`** changes the **goal**. The lemma is `↑(r ^ n) = ↑r ^ n` (`↑` the cast
`ℝ → ℂ`); right to left it moves `^` inside the cast, so a real lemma can apply. Placeholders: `(r : ℝ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (↑r ^ n)` | `⊢ P ↑(r ^ n)` |

**R28 · `rw [Real.sq_sqrt (by positivity)]`** changes the **goal**. The lemma is `0 ≤ r → √r ^ 2 = r`; the
argument proves `0 ≤ 2 ^ n`. Placeholders: `(r : ℝ) (hr : 0 ≤ r)`.

| Before | After |
|---|---|
| `⊢ P (√r ^ 2)` | `⊢ P r` |

**R29 · `positivity`** **closes** goals `0 ≤ e` and `0 < e` when `e` is built from visibly positive pieces
(numerals, `^`, `√`, `exp`, sums and products of such).

**R30 · `push_cast`** changes the **goal**: it moves casts inward, `↑((3 : ℝ) ^ n) = (3 : ℂ) ^ n`. In `hsq` it
may leave `(2 ^ n)⁻¹ = (2 ^ n)⁻¹` open (the two sides differ in hidden instance arguments); `rfl` closes it.

| Before | After |
|---|---|
| `⊢ P ↑(3 ^ n)` | `⊢ P (3 ^ n)` |

### Pushing scalars in, swapping sums

After `funext y` and unfolding `W`, the goal is `(c * ∑ x, χ * (c * ∑ x_1, χ' * v x_1)) = v y` with
`c = (↑√(2 ^ n))⁻¹`.

**R31 · `Finset.mul_sum`** changes the **goal**: `a * ∑ i, f i = ∑ i, a * f i`. Forward it pushes a scalar into
a sum; `← Finset.mul_sum` pulls a common factor out. Placeholders: `{ι R : Type} [Fintype ι] [CommSemiring R]
(a : R) (f : ι → R)`.

| Before | After |
|---|---|
| `⊢ P (a * ∑ i, f i)` | `⊢ P (∑ i, a * f i)` |

**R32 · `← mul_assoc`** changes the **goal**: `mul_assoc : a * b * c = a * (b * c)`; right to left it flattens
to the left-nested form `a * b * c` (`*` groups to the left). Placeholders: `{M : Type} [Semigroup M] (a b c : M)`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

With `simp only [W, Finset.mul_sum, ← mul_assoc]` the goal becomes
`∑ x, ∑ x_1, (↑√(2 ^ n))⁻¹ * (-1) ^ dot x y * (↑√(2 ^ n))⁻¹ * (-1) ^ dot x_1 x * v x_1 = v y`.

**R33 · `rw [Finset.sum_comm]`** changes the **goal**: `∑ x, ∑ y, f x y = ∑ y, ∑ x, f x y`. Now the outer sum
runs over the input `z` of `v`, the inner over `x`. Placeholders: `{α β M : Type} [Fintype α] [Fintype β]
[AddCommMonoid M] (f : α → β → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, ∑ y, f x y)` | `⊢ P (∑ y, ∑ x, f x y)` |

**W3** (R31 then R33 on a double sum):

```lean-goal
⊢ c * ∑ i, ∑ j, f i j = ∑ j, ∑ i, c * f i j
⊢ ∑ x, ∑ i, c * f x i = ∑ j, ∑ i, c * f i j
```

### The inner sum and the final sum

The `key` fact: for each `z`, the inner sum is `if z = y then v y else 0`. Regroup each term to
`((↑√(2 ^ n))⁻¹ ^ 2 * v z) * (-1) ^ dot (y + z) x` (with `dot_comm z x`, `dot_comm (y + z) x`,
`← neg_one_pow_dot_add`, then `ring`), rewrite
with it under `∑ x` (R1), pull the constant out (`← Finset.mul_sum`, R31), then `char_sum`, `bits_add_eq_zero`,
`hsq`. The goal becomes `((2 ^ n)⁻¹ * v z * if z = y then 2 ^ n else 0) = if z = y then v y else 0`; split it
with R7.

**R34 · `field_simp`** **closes** (or clears the denominators of) an equation with `⁻¹` and `/`. It needs every
denominator `≠ 0` and proves `2 ^ n ≠ 0` in `ℂ` by itself. Placeholders: `(b : ℂ) (n : ℕ)`.

| Before | After |
|---|---|
| `⊢ (3 ^ n)⁻¹ * b * 3 ^ n = b` | closed |

**R35 · `Finset.sum_ite_eq'`** changes the **goal**: `(∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a
else 0`: only the `x = a` term survives. `Finset.sum_ite_eq` is the twin with the test written `a = x`.
Placeholders: `{ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (a : ι) (b : ι → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, if x = a then b x else 0)` | `⊢ P (if a ∈ Finset.univ then b a else 0)` |

**R36 · `Finset.mem_univ`, `if_true`** change the **goal**: `a ∈ Finset.univ` is `True`, and
`if True then u else v = u`.

| Before | After |
|---|---|
| `⊢ P (if a ∈ Finset.univ then u else v)` | `⊢ P u` |

---

## Part 6 · `bernstein_vazirani`

Statement: `W (fun x => (↑√(2 ^ n))⁻¹ * (-1) ^ dot s x) = Pi.single s 1`: the phase state of `s` is mapped to the
basis state `|s⟩`. Uses all four milestones, the same `hsq` as Part 5 (re-prove it: a `have` belongs to one
proof), R31 and R32, plus:

**R37 · `← sq`** changes the **goal**: `sq a : a ^ 2 = a * a`; right to left it folds `a * a` so `hsq` can match.
Placeholders: `{M : Type} [Monoid M] (a : M)`.

| Before | After |
|---|---|
| `⊢ P (a * a)` | `⊢ P (a ^ 2)` |

**R38 · `Pi.single_apply`** changes the **goal**: `Pi.single i x i' = if i' = i then x else 0`.
`Pi.single s 1` is the function `1` at `s` and `0` elsewhere, i.e. `|s⟩`. Placeholders: `{ι M : Type}
[DecidableEq ι] [Zero M] (s y : ι) (u : M)`.

| Before | After |
|---|---|
| `⊢ P (Pi.single s u y)` | `⊢ P (if y = s then u else 0)` |

**R39 · `eq_comm (a := s)`** changes the **goal**: `eq_comm : a = b ↔ b = a`, with its argument `a` fixed to `s`,
so it flips only equations whose left side is `s`. Without `(a := s)` `simp` would flip every equation back and
forth. Here it makes `char_sum`'s test `s = y` match `Pi.single`'s `y = s`.

| Before | After |
|---|---|
| `⊢ P (if s = y then u else v)` | `⊢ P (if y = s then u else v)` |

After one `simp only [...]` with all of these the goal is
`((2 ^ n)⁻¹ * if y = s then 2 ^ n else 0) = if y = s then 1 else 0`; split it with R7, close with R34 and `simp`.

---

## Part 7 · `deutsch_jozsa`

Statement: for `f` balanced (`hbal`: as many `x` with `f x = 0` as with `f x = 1`), the amplitude of `|0…0⟩`
after `W` is `0`. First `hdot : ∀ x, dot x 0 = 0` (`simp [dot]`: R17, R5, R6), then
`hsum : ∑ x, (-1 : ℂ) ^ (f x).val = 0`, then unfold `W`, rewrite with `hdot`, R6, pull the scalar out (R31) and
use `hsum`.

**R40 · `rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]`** changes the **goal**: it splits a sum by
a predicate `p`. The lemma is `∑ x ∈ s with p x, f x + ∑ x ∈ s with ¬p x, f x = ∑ x ∈ s, f x`. Give `s` and
`p` explicitly (here `p = fun x => f x = 0`). Placeholders: `{ι M : Type} [Fintype ι] [AddCommMonoid M]
(p : ι → Prop) [DecidablePred p] (f : ι → M)`.

| Before | After |
|---|---|
| `⊢ P (∑ x, f x)` | `⊢ P (∑ x with p x, f x + ∑ x with ¬p x, f x)` |

**R41 · `simp at hx`** changes the **context**: a membership in a filter becomes the predicate
(`Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a`, plus `Finset.mem_univ`). Use it after `intro x hx` when
proving `h0`, which the infoview shows as `h0 : ∀ x ∈ {x | f x = 0}, (-1) ^ ↑(f x) = 1` (type it with
`Finset.univ.filter (fun x => f x = 0)`, see Traps). Placeholders: `{ι : Type} [Fintype ι] (p : ι → Prop)
[DecidablePred p] (x : ι)`.

| Before | After |
|---|---|
| `hx : x ∈ Finset.filter p Finset.univ ⊢ p x` | `hx : p x ⊢ p x` |

**R42 · `rw [Finset.sum_congr rfl h0]`** changes the **goal**: with `h0 : ∀ x ∈ s, f x = g x` it rewrites every
term of `∑ x ∈ s, f x`. Placeholders: `(f : ι → M) (c : M) (h0 : ∀ x ∈ Finset.univ.filter p, f x = c)`.

| Before | After |
|---|---|
| `⊢ Q (∑ x with p x, f x)` | `⊢ Q (∑ x with p x, c)` |

**R43 · `rw [Finset.sum_const]`** changes the **goal**: `∑ _x ∈ s, c = s.card • c`. Placeholders: `(c : M)`.
Before, then after:

```lean-goal
⊢ Q (∑ _x with p _x, c)
⊢ Q ({_x | p _x}.card • c)
```

**R44 · `ext x`** on Finsets (`Finset.ext`) changes the **goal and the context**: two Finsets are equal when they
have the same members. Use it for `hset : {x | ¬f x = 0} = {x | f x = 1}` (as shown in the infoview; typed with `Finset.univ.filter`); then `simp` and `omega` (R15).
Placeholders: `(p q : ι → Prop) [DecidablePred p] [DecidablePred q]`.

| Before | After |
|---|---|
| `⊢ Finset.filter p Finset.univ = Finset.filter q Finset.univ` | `x : ι ⊢ x ∈ Finset.filter p Finset.univ ↔ x ∈ Finset.filter q Finset.univ` |

**W4** (split, rewrite each piece, count: R40 → R42 → R43):

```lean-goal
⊢ ∑ x, f x = (Finset.filter p Finset.univ).card • 2
⊢ ∑ x with p x, f x + ∑ x with ¬p x, f x = (Finset.filter p Finset.univ).card • 2
⊢ ∑ x with p x, 2 + ∑ x with ¬p x, 0 = (Finset.filter p Finset.univ).card • 2
```

In the exercise, after R42 twice, R43 twice, `hbal` and `hset`, the goal is
`{x | f x = 1}.card • 1 + {x | f x = 1}.card • -1 = 0`, which `simp` closes.

---

## Traps

- `rw` does not rewrite under `∑ x, …` or `fun x => …` when the term mentions the bound variable: use
  `simp_rw` or `simp only` (R1). `rw [h]` with `h : ∀ x, …` works only for a term free of bound variables.
- `rw [← Fintype.prod_sum]` without an explicit function fails to find the pattern `f i (x i)` (R3).
- Older Mathlib `simp` did not know `(1 + 1 : Fin 2) = 0`; the reference solution passes it as
  `show (1 + 1 : Fin 2) = 0 from rfl` (R20). Harmless if `simp` already knows it.
- `generalize` changes only the goal; `revert` the hypotheses that mention the term first (R24, R19).
- `char_sum` sums over the **second** argument of `dot`; flip with `dot_comm` before using it.
- Give `dot_comm` its arguments (`dot_comm z x`). `rw [dot_comm, dot_comm]` flips the first `dot` in the goal
  and then flips the same one back, leaving the goal unchanged.
- `char_sum`'s test is `y + z = 0` (`s = y`-style after `bits_add_eq_zero`); match `Pi.single`'s `y = s` with
  `eq_comm (a := s)`, never bare `eq_comm` (R39).
- After `push_cast`, a goal whose two sides print the same may still be open: `rfl` (R30).
- Write casts out in a `have`: `(Real.sqrt (2 ^ n) : ℂ)`. A bare `√(2 ^ n)` stays in `ℝ`, and `rw [hsq]` will
  not find it in a complex goal. Likewise `(-1 : ℂ) ^ …`.
- `hsq` from Part 5 is not visible in Part 6: re-prove it, or state it once as your own helper lemma.
- `rw [hsq]` needs `(…)⁻¹ ^ 2` literally; `simp` leaves `(…)⁻¹ * (…)⁻¹`: fold it with `← sq` (R37).
- `{x | f x = 0}` in the infoview is a `Finset` (a filter of `Finset.univ`), not a `Set`; prove equalities of
  them with `ext` (R44), memberships with `simp` (R41). Do not type `{x | f x = 0}` in your own `have`: there it
  means a `Set`, and `rw [Finset.sum_congr rfl h0]` (R42) fails with a type mismatch. Type
  `Finset.univ.filter (fun x => f x = 0)` instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| rewrite or unfold under `∑` | `simp_rw [dot, h]` | R1 |
| `a ^ ∑ i, f i` → `∏ i, a ^ f i` | `← Finset.prod_pow_eq_pow_sum` | R2 |
| `∑ x, ∏ i, f i (x i)` → `∏ i, ∑ j, f i j` | `rw [← Fintype.prod_sum (fun i (b : Fin 2) => …)]` | R3 |
| sum over `Fin 2`, bit values, clean-up | `simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, mul_zero, mul_one, pow_zero]` | R4–R6 |
| case on `if` | `split_ifs with h` | R7 |
| replace a variable by its value | `subst h` / `rintro rfl` | R8, R25 |
| product of a constant | `norm_num` / `simp` | R9 |
| a witness for `∃` | `obtain ⟨i, hi⟩ : ∃ i, … := by by_contra hc; push Not at hc; exact hx (funext hc)` | R10–R13 |
| product with a zero factor | `apply Finset.prod_eq_zero (Finset.mem_univ i)` | R14 |
| a bit `≠ 0` is `1` | `omega` | R15 |
| merge two products | `← Finset.prod_mul_distrib` | R16 |
| `(y + z) i`, `0 i` | `Pi.add_apply`, `Pi.zero_apply` | R17 |
| product equation → factor equation | `refine Finset.prod_congr rfl fun i _ => ?_` | R18 |
| case-split a bit `x i` | `generalize x i = a; fin_cases a` | R19 |
| `1 + 1 = 0` in `Fin 2` | `show (1 + 1 : Fin 2) = 0 from rfl` | R20 |
| commute every product | `simp [dot, mul_comm]` | R21 |
| `f = g` → `f i = g i` | `have := congrFun h i` | R22 |
| rewrite a hypothesis | `simp only [l] at h` | R23 |
| hypothesis back into the goal | `revert h` | R24 |
| `(√(2^n))⁻¹ ^ 2 = (2^n)⁻¹` | `rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl` | R26–R30 |
| scalar into / out of a sum | `Finset.mul_sum` / `← Finset.mul_sum` | R31 |
| flatten products | `← mul_assoc` | R32 |
| swap two sums | `rw [Finset.sum_comm]` | R33 |
| `(2^n)⁻¹ * … * 2^n = …` | `field_simp` | R34 |
| `∑ x, if x = a then b x else 0` | `simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]` | R35, R36 |
| `a * a` → `a ^ 2` | `← sq` | R37 |
| basis vector `\|s⟩` at `y` | `Pi.single_apply` | R38 |
| flip only `s = _` | `eq_comm (a := s)` | R39 |
| split a sum by `p` | `rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p]` | R40 |
| filter membership → predicate | `simp at hx` | R41 |
| rewrite terms of a filtered sum | `rw [Finset.sum_congr rfl h0]` | R42 |
| sum of a constant | `Finset.sum_const` | R43 |
| equal Finsets | `ext x; simp; omega` | R44 |
| see the state | infoview | |
