# M167 · Edges of the tight-binding band: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** physlib's `TightBindingChain` (its fields,
`QuantaWaveNumber`, `energyEigenvalue`); Mathlib's `IsLeast` / `IsGreatest`, `lowerBounds` /
`upperBounds`, `Set.range`, subtypes, `Even`, casts `ℕ → ℝ`, `Real.cos` and `Real.pi`; the tactics
`omega`, `nlinarith`, `exact_mod_cast`, `push_cast`, `field_simp`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is an arbitrary goal that a context step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket such as `[Ring α]` is a
  requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The physics and the objects

A `T : TightBindingChain` is a structure (a record) with fields `T.N : ℕ` (number of sites), `T.a : ℝ`
(lattice spacing), `T.a_pos : 0 < T.a` (a proof, stored as a field), `T.E0 : ℝ` (on-site energy) and
`T.t : ℝ` (hopping amplitude). physlib also provides the instance `NeZero T.N`, i.e. `T.N ≠ 0`.

- `T.QuantaWaveNumber : Set ℝ` is, by definition,
  `{x | ∃ n : Fin T.N, 2 * Real.pi / (T.a * T.N) * ((n : ℝ) - (T.N / 2 : ℕ)) = x}`:
  the allowed wavenumbers $k_n = \frac{2\pi}{aN}\,(n - \lfloor N/2 \rfloor)$ for $n = 0, \dots, N-1$.
  `T.N / 2` is division in `ℕ`, which rounds down ($\lfloor N/2 \rfloor$).
- `T.energyEigenvalue : ↑T.QuantaWaveNumber → ℝ` is `fun k => T.E0 - 2 * T.t * Real.cos (k * T.a)`, i.e.
  $E(k) = E_0 - 2t\cos(ka)$. Its argument is an element of the *subtype* `↑T.QuantaWaveNumber`: a pair
  `⟨x, hx⟩` of a real `x` and a proof `hx : x ∈ T.QuantaWaveNumber`.
- The band is `Set.range T.energyEigenvalue`, the set of all values $E(k)$. Its bottom is
  $E_0 - 2t$ (at $k = 0$, where $\cos = 1$); for even $N = 2m$ its top is $E_0 + 2t$ (at
  $k = -\pi/a$, index $n = 0$, where $\cos(-\pi) = -1$). Both need $t \ge 0$.

## Reading the goals

| You see | It means |
|---|---|
| `T.N`, `T.a`, `T.E0`, `T.t` | the fields of the chain `T` |
| `↑T.QuantaWaveNumber` | the subtype of reals in the set `T.QuantaWaveNumber` (a set used as a type) |
| `⟨x, hx⟩` | an element of a subtype (value `x`, proof `hx : x ∈ S`), or of `Fin N` (value, proof `x < N`) |
| `↑k` (for `k : ↑S`) | the real number underlying `k` |
| `↑↑n` (for `n : Fin N`) | `n` cast to `ℕ`, then to `ℝ` |
| `↑m` (for `m : ℕ`) | `m` cast to `ℝ` |
| `↑(N / 2)` | `⌊N/2⌋` computed in `ℕ`, then cast to `ℝ` |
| `⟨0, ⋯⟩` | an element of `Fin N` whose proof is hidden |
| `⟨T.N / 2, ?refine_1⟩` | the proof slot is still an open goal (`case refine_1`), from writing `?_` there |
| `this : …` | a fact added by `have := e` without a name |
| `Set.range f` | `{y \| ∃ k, f k = y}`, the image of `f` |
| `IsLeast s a` / `IsGreatest s a` | `a ∈ s ∧ a ∈ lowerBounds s` / `a ∈ s ∧ a ∈ upperBounds s` |
| `a ∈ lowerBounds s` | `∀ ⦃y⦄, y ∈ s → a ≤ y` (dually `upperBounds`: `y ≤ a`); `⦃y⦄` is a strict-implicit binder, introduced by `intro`/`rintro` like any other |
| `Even N` | `∃ r, N = r + r` |
| `Real.pi`, `Real.cos` | $\pi$ and $\cos$ on `ℝ` |
| `inst✝ : NeZero N` | an anonymous type-class hypothesis `N ≠ 0` |
| `case refine_1` | the first goal created by a `refine` |

---

## Part 1 · `band_bottom`

Statement: for `0 ≤ T.t`, `IsLeast (Set.range T.energyEigenvalue) (T.E0 - 2 * T.t)`: the value $E_0 - 2t$
is an energy, and every energy is at least $E_0 - 2t$. The witness is $k = 0$, given by the index
$n = \lfloor N/2 \rfloor$, so first prove `h0 : (0 : ℝ) ∈ T.QuantaWaveNumber`.

### The allowed wavenumber `0`

**R1 · `refine ⟨⟨v, hv⟩, ?_⟩`** changes the **goal**. Membership in a set-builder set is the `∃` itself,
also behind a definition such as `T.QuantaWaveNumber` (the guide's stand-in is
`Q N g = {x | ∃ n : Fin N, g n = x}`). The inner `⟨v, hv⟩` is the index: a natural `v` and a proof
`hv : v < N`; write `by …` in place of `hv` to prove it on the spot. Placeholders:
`(N : ℕ) (g : Fin N → ℝ) (x : ℝ) (v : ℕ) (hv : v < N)`.

| Before | After |
|---|---|
| `⊢ x ∈ Q N g` | `⊢ g ⟨v, hv⟩ = x` |

**R2 · `have h := NeZero.pos N`** changes the **context**. The lemma is `NeZero.pos (n : ℕ) [NeZero n] : 0 < n`.
Placeholders: `(N : ℕ) [NeZero N]`; `T.N` qualifies (physlib's instance).

| Before | After |
|---|---|
| `⊢ G` | `h : 0 < N ⊢ G` |

**R3 · `omega`** **closes** a goal of linear arithmetic over `ℕ` or `ℤ` from the hypotheses; it understands
`/` and `%` by numerals (so `⌊N/2⌋` and `N = m + m`). It does not work over `ℝ`. Placeholders: `(N m : ℕ)`.

| Before | After |
|---|---|
| `h : 0 < N ⊢ N / 3 < N` | no goals |
| `hm : N = m + m ⊢ N / 2 = m` | no goals |

**R4 · `simp only [sub_self, mul_zero]`** changes the **goal**. `sub_self : a - a = 0`, `mul_zero : a * 0 = 0`.
The index cast `↑↑⟨v, hv⟩` is `↑v` by definition, and `simp` sees through that. Placeholders:
`(N v : ℕ) (hv : v < N) (c : ℝ)`. Plain `simp` does the same.

| Before | After |
|---|---|
| `⊢ P (c * (↑↑⟨v, hv⟩ - ↑v))` | `⊢ P 0` |

### Least element of the range

**R5 · `refine ⟨?_, ?_⟩` on `IsLeast`** changes the **goal list**. `IsLeast s a` is defined as
`a ∈ s ∧ a ∈ lowerBounds s`, so it splits like an `∧`. Placeholders: `(s : Set ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ IsLeast s a` | `⊢ a ∈ s`, `⊢ a ∈ lowerBounds s` |

**R6 · `refine ⟨⟨x, hx⟩, ?_⟩` on `Set.range`** changes the **goal**. `b ∈ Set.range f` is `∃ k, f k = b`
(`Set.mem_range`). With `f` defined on a subtype `↑S`, the witness is a pair `⟨x, hx⟩`. Placeholders:
`(S : Set ℝ) (f : ↑S → ℝ) (x b : ℝ) (hx : x ∈ S)`. R5 and R6 nest: `refine ⟨⟨⟨x, hx⟩, ?_⟩, ?_⟩`
leaves the value equation and the bound.

| Before | After |
|---|---|
| `⊢ b ∈ Set.range f` | `⊢ f ⟨x, hx⟩ = b` |

**R7 · `unfold TightBindingChain.energyEigenvalue`** changes the **goal**: the name is replaced by its
formula. `simp only [TightBindingChain.energyEigenvalue]` does the same. Placeholders:
`(T : TightBindingChain) (k : ↑T.QuantaWaveNumber)`.

| Before | After |
|---|---|
| `⊢ P (T.energyEigenvalue k)` | `⊢ P (T.E0 - 2 * T.t * Real.cos (↑k * T.a))` |

**R8 · `zero_mul`, then `Real.cos_zero`** change the **goal**. `zero_mul : 0 * a = 0`, `Real.cos_zero : cos 0 = 1`.
`↑⟨0, h0⟩` is `0` by definition, so `zero_mul` applies. In the problem, R7 then R8 leaves
`⊢ T.E0 - 2 * T.t * 1 = T.E0 - 2 * T.t`; finish with `rw [mul_one]` (`mul_one : a * 1 = a`).
`simp [TightBindingChain.energyEigenvalue]` does R7, R8 and `mul_one` at once; plain `simp` without the
definition makes no progress. Placeholders: `(S : Set ℝ) (h0 : 0 ∈ S) (a : ℝ)`.

| Before | After `simp only [zero_mul]` | After `rw [Real.cos_zero]` |
|---|---|---|
| `⊢ P (Real.cos (↑⟨0, h0⟩ * a))` | `⊢ P (Real.cos 0)` | `⊢ P 1` |

### Every energy is at least the bottom

**R9 · `rintro _ ⟨k, rfl⟩`** changes the **goal and the context**. `a ∈ lowerBounds s` is
`∀ ⦃y⦄, y ∈ s → a ≤ y`; `rintro` introduces `y` (named `_`), destructs `y ∈ Set.range f` into `k` and
`f k = y`, and `rfl` substitutes `y := f k`. Placeholders: `(S : Set ℝ) (f : ↑S → ℝ) (a : ℝ)`.

| Before | After |
|---|---|
| `⊢ a ∈ lowerBounds (Set.range f)` | `k : ↑S ⊢ a ≤ f k` |

**R10 · `have h := Real.cos_le_one x`** changes the **context**. The lemma is `Real.cos_le_one (x : ℝ) : cos x ≤ 1`.
Placeholders: `(x : ℝ)`; in the problem `x` is `↑k * T.a`.

| Before | After |
|---|---|
| `⊢ G` | `h : Real.cos x ≤ 1 ⊢ G` |

**R11 · `nlinarith`** **closes** a goal of (in)equalities over an ordered field such as `ℝ` that follows by
multiplying pairs of hypotheses and then linear arithmetic. Here it multiplies `0 ≤ x` by `0 ≤ 1 - y`.
`linarith` alone fails: the product `t · cos` is not linear. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x, hy : y ≤ 1 ⊢ x * y ≤ x` | no goals |

---

## Part 2 · `band_top`

Statement: for `0 ≤ T.t` and `Even T.N`, `IsGreatest (Set.range T.energyEigenvalue) (T.E0 + 2 * T.t)`.
Write $N = m + m$. The index $n = 0$ gives $k = \frac{2\pi}{a \cdot 2m}(0 - m) = -\pi/a$, and
$E(-\pi/a) = E_0 - 2t\cos(-\pi) = E_0 + 2t$. So: get `m`, prove `hk : -(Real.pi / T.a) ∈ T.QuantaWaveNumber`
(with R1), then split as in Part 1.

### Even `N`, casts and fractions

**R12 · `obtain ⟨m, hm⟩ := hN`** changes the **context**: `hN : Even N` is `∃ r, N = r + r`, and `obtain`
replaces it by the witness and the equation. Placeholders: `(N : ℕ) (hN : Even N)`.

| Before | After |
|---|---|
| `hN : Even N ⊢ G` | `m : ℕ, hm : N = m + m ⊢ G` |

**R13 · `have ha := T.a_pos`** changes the **context**. `a_pos` is a field of the structure, a proof
`0 < T.a` stored with the chain. Placeholders: `(T : TightBindingChain)`.

| Before | After |
|---|---|
| `⊢ G` | `ha : 0 < T.a ⊢ G` |

**R14 · `exact_mod_cast h`** **closes** a goal that is `h` up to casts: here the real inequality `0 < ↑m` from the
natural one `h : 0 < m`. Use it to get the fact `(0 : ℝ) < m` that `field_simp` needs (R17). Write
`exact_mod_cast (show 0 < m by omega)` when `h` is not yet in the context. Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `h : 0 < m ⊢ 0 < ↑m` | no goals |

**R15 · `push_cast`** changes the **goal**: it moves casts inward (`Nat.cast_add`: `↑(a + b) = ↑a + ↑b`, and
likewise for `*`, numerals). Use it to prove `(T.N : ℝ) = 2 * m` after `rw [hm]`, then `ring`.
Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ↑(m + m)` | `⊢ P (↑m + ↑m)` |

Order matters: rewrite the ℕ division `T.N / 2` to `m` with an `omega` fact **before** rewriting the cast
`↑T.N`; `rw [hNr]` with `hNr : ↑T.N = 2 * ↑m` cannot reach the `T.N` inside `↑(T.N / 2)`.

**R16 · `simp` on the index `0`** changes the **goal**: `↑↑⟨0, hN⟩` becomes `0`, then `zero_sub`
(`0 - a = -a`), `mul_neg` (`a * -b = -(a * b)`) and `neg_inj` (`-a = -b ↔ a = b`) remove the signs.
Placeholders: `(N m : ℕ) (hN : 0 < N) (c d : ℝ)`.

| Before | After |
|---|---|
| `⊢ c * (↑↑⟨0, hN⟩ - ↑m) = -d` | `⊢ c * ↑m = d` |

**R17 · `field_simp`** changes or **closes** the goal: it multiplies out denominators and normalises the
result, then often finishes by `ring_nf`. It must know every denominator is nonzero: put `0 < a` or `a ≠ 0`
facts in the context first (here `ha : 0 < T.a` from R13 and `(0 : ℝ) < m` from R14). Placeholders:
`(a b : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ 3 / (a * (3 * b)) * b = 1 / a` | no goals |

### Greatest element of the range

**R18 · `refine ⟨?_, ?_⟩` on `IsGreatest`** changes the **goal list**, exactly like R5 with `upperBounds`.

| Before | After |
|---|---|
| `⊢ IsGreatest s a` | `⊢ a ∈ s`, `⊢ a ∈ upperBounds s` |

### The energy at `k = -π/a`

After R7 the value goal is `T.E0 - 2 * T.t * Real.cos (-(Real.pi / T.a) * T.a) = T.E0 + 2 * T.t`. Clear
the cosine with R19 → R21 (using R20) → R22 → R23 in one `rw [...]`, then `ring`.

**R19 · `rw [neg_mul]`** changes the **goal**. `neg_mul : -a * b = -(a * b)`. Placeholders:
`{α : Type} [Ring α] (a b : α)`; `ℝ` qualifies.

| Before | After |
|---|---|
| `⊢ P (-a * b)` | `⊢ P (-(a * b))` |

**R20 · `ha.ne'`** is the term `LT.lt.ne' : 0 < a → a ≠ 0` applied to `ha` (dot notation: `ha : 0 < a` has
type `LT.lt 0 a`). It changes the **context** when used with `have`; usually you pass it directly as a
lemma argument (R21). Placeholders: `(a : ℝ) (ha : 0 < a)`.

| Before | After |
|---|---|
| `⊢ G` | `h : a ≠ 0 ⊢ G` |

**R21 · `rw [div_mul_cancel₀ _ hb]`** changes the **goal**. `div_mul_cancel₀ (a : α) (h : b ≠ 0) : a / b * b = a`.
The `_` lets `rw` find `a`. Placeholders: `{α : Type} [GroupWithZero α] (a b : α) (hb : b ≠ 0)`; `ℝ`
qualifies. In the problem: `div_mul_cancel₀ _ ha.ne'`.

| Before | After |
|---|---|
| `⊢ P (a / b * b)` | `⊢ P a` |

**R22 · `rw [Real.cos_neg]`** changes the **goal**. `Real.cos_neg (x : ℝ) : cos (-x) = cos x`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (Real.cos (-x))` | `⊢ P (Real.cos x)` |

**R23 · `rw [Real.cos_pi]`** changes the **goal**. `Real.cos_pi : cos π = -1`.

| Before | After |
|---|---|
| `⊢ P (Real.cos Real.pi)` | `⊢ P (-1)` |

### Every energy is at most the top

**R24 · `rintro _ ⟨k, rfl⟩`** on `upperBounds`: as R9 with the inequality reversed.

| Before | After |
|---|---|
| `⊢ a ∈ upperBounds (Set.range f)` | `k : ↑S ⊢ f k ≤ a` |

**R25 · `have h := Real.neg_one_le_cos x`** changes the **context**. `Real.neg_one_le_cos (x : ℝ) : -1 ≤ cos x`.
Then R11 (`nlinarith`) with `0 ≤ T.t` closes the bound.

| Before | After |
|---|---|
| `⊢ G` | `h : -1 ≤ Real.cos x ⊢ G` |

### Worked combinations (guide Part W, on objects that are not the exercise's)

**W1: a least element of a range on `ℝ`** (R5, R6, R9, R10). `IsLeast (Set.range fun x : ℝ => 3 - Real.cos x) 2`:
the witness `0` is plain (no subtype), and after `rintro` the function is still a `fun`:

```lean-goal
⊢ 2 ∈ lowerBounds (Set.range fun x => 3 - Real.cos x)
⊢ 2 ≤ (fun x => 3 - Real.cos x) x
```

`simp only` (no lemmas) beta-reduces it to `2 ≤ 3 - Real.cos x`; then `linarith` (no product needed).

**W2: an index with ℕ division** (R12, R1, R3, R15, R16). For even `N` and the set
`Q N (fun n => ↑↑n - ↑(N / 2))`, the index `0` hits `-(N/2)`. After `rw [h2, hNr]` (ℕ division first):

```lean-goal
⊢ (fun n => ↑↑n - ↑(N / 2)) ⟨0, ⋯⟩ = -(↑N / 2)
⊢ (fun n => ↑↑n - ↑m) ⟨0, ⋯⟩ = -(2 * ↑m / 2)
```

and `simp` closes it.

**W3: a cosine at `-π/b · b`** (R19, R21 with R20, R22, R23):

```lean-goal
⊢ 2 * Real.cos (-(Real.pi / b) * b) + 2 = 0
⊢ 2 * -1 + 2 = 0
```

---

## Traps

- `field_simp` needs nonzero facts in the context: `0 < T.a` (R13) and, after `obtain ⟨m, hm⟩ := hN`,
  `(0 : ℝ) < m` (R14, with `omega` and `NeZero.pos T.N` to get `0 < m` in `ℕ`). Without them it leaves the
  denominators in place.
- `T.N / 2` is ℕ division. `omega` handles it; `ring`, `field_simp` and `push_cast` do not. Turn it into `m`
  (`h2 : T.N / 2 = m := by omega`) before casting.
- `rw [hNr]` with `hNr : ↑T.N = 2 * ↑m` rewrites only the cast `↑T.N`, not the `T.N` inside `↑(T.N / 2)`;
  so do `rw [h2, hNr]` in that order.
- `simp` does not unfold `T.energyEigenvalue` on its own: name it (`simp [TightBindingChain.energyEigenvalue]`)
  or `unfold` it first (R7).
- `have hNr : (T.N : ℝ) = 2 * m` needs `rw [hm]` before `push_cast` (R15): there is no cast of a sum to
  push until `T.N` has become `m + m`.
- The witness of `Set.range` on a subtype is a pair: `⟨⟨0, h0⟩, _⟩`, not `⟨0, _⟩`.
- `linarith` cannot use `cos x ≤ 1` against `0 ≤ t` to bound `t * cos x`: that is a product, use `nlinarith`
  (R11) after adding the cosine bound with `have`.
- `have h : T` with no `:= …` makes `T` your next goal instead of adding `h` (TACTIC_STATES, "Adding facts").

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| show `x ∈ T.QuantaWaveNumber` | `refine ⟨⟨n, by …⟩, ?_⟩` | R1 |
| `0 < T.N` | `NeZero.pos T.N` | R2 |
| ℕ facts with `/ 2` | `omega` | R3 |
| index term vanishes | `simp` (`sub_self`, `mul_zero`) | R4 |
| split `IsLeast` / `IsGreatest` | `refine ⟨?_, ?_⟩` | R5, R18 |
| value is in the range | `refine ⟨⟨x, hx⟩, ?_⟩` | R6 |
| expose the energy formula | `unfold TightBindingChain.energyEigenvalue` | R7 |
| energy at `k = 0` | `simp [TightBindingChain.energyEigenvalue]` (`zero_mul`, `Real.cos_zero`, `mul_one`) | R7, R8 |
| bound every element of the range | `rintro _ ⟨k, rfl⟩` | R9, R24 |
| cosine bounds | `Real.cos_le_one x`, `Real.neg_one_le_cos x` | R10, R25 |
| `t ≥ 0`, `cos ≤ 1` ⇒ bound | `nlinarith` | R11 |
| `Even N` → `N = m + m` | `obtain ⟨m, hm⟩ := hN` | R12 |
| `0 < T.a` | `T.a_pos` | R13 |
| ℕ fact → ℝ fact | `exact_mod_cast` | R14 |
| `↑(m + m) = ↑m + ↑m` | `push_cast` | R15 |
| signs around the index `0` | `simp` | R16 |
| clear denominators | `field_simp` | R17 |
| `cos (-(π / a) * a) = -1` | `rw [neg_mul, div_mul_cancel₀ _ ha.ne', Real.cos_neg, Real.cos_pi]` | R19–R23 |
| see the state | infoview | |
