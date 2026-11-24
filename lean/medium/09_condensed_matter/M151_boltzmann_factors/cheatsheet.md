# M151 · Boltzmann factors: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `have`, `exact`, `rw`, `simp only`, `unfold`, `ring`,
dot notation `h.foo`. **New here:** physlib's `CanonicalEnsemble` (its energy, partition function and
Boltzmann probabilities in terms of the inverse temperature), Mathlib's real exponential `rexp`, division
lemmas for a nonzero / positive denominator, and the tactics `ring_nf` (as a closer) and `nlinarith`.

**The physics, in symbols.** Units `k_B = 1`. A finite system has microstates `i ∈ ι` with energies
`E i`. At inverse temperature `b = 1/T`: $Z(b) = \sum_i e^{-b E_i}$ (partition function) and
$p_b(i) = e^{-b E_i}/Z(b)$ (Boltzmann probability). Then
$p_b(j)/p_b(i) = e^{-b E_j}/e^{-b E_i} = e^{-b(E_j - E_i)}$: the ratio does not involve $Z$. Since
$Z > 0$ and $e^x$ is increasing, $p_b(j) \le p_b(i) \iff -b E_j \le -b E_i$, which holds when $b \ge 0$
and $E_i \le E_j$.

## How to read an entry

Each entry is one tactic or one lemma used with `have`/`rw`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal. `G : Prop` is a goal that the step leaves alone.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[GroupWithZero α]`
  is a requirement on `α` (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `𝓒 : CanonicalEnsemble ι` | a physlib system with microstates of type `ι`; `𝓒.energy : ι → ℝ` is the energy `E` |
| `[Fintype ι]` | finitely many microstates, so sums `∑ i` over all of `ι` make sense |
| `[Nonempty ι]` | at least one microstate; needed for `Z > 0` (R1) |
| `[MeasurableSpace ι]` | required by the `CanonicalEnsemble` structure; plays no role here |
| `inst✝² : Fintype ι` | an unnamed instance hypothesis: one of the `[…]` brackets of the theorem, shown in the context |
| `𝓒.mathematicalPartitionFunctionBetaReal b` | `Z(b) = ∑ i, rexp (-b * 𝓒.energy i)`, a real number |
| `𝓒.probabilityBetaReal b i` | `p_b(i) = rexp (-b * 𝓒.energy i) / Z(b)` (R3) |
| `rexp x` | `Real.exp x`, the real exponential $e^x$ |
| `-b * E` | `(-b) * E`: unary minus binds tighter than `*` |
| `a / c / (b / c)` | `(a / c) / (b / c)`: `/` groups to the left |
| `hZ.ne'` | `LT.lt.ne' hZ` (dot notation): from `hZ : 0 < Z` it is `Z ≠ 0` (R2) |

---

## Part 1 · `boltzmann_ratio`

Statement: `p_b(j) / p_b(i) = rexp (-b * (E j - E i))` for any real `b`. Get `Z(b) ≠ 0` (R1, R2), unfold both
probabilities (R3), cancel the common `Z(b)` (R4), merge the two exponentials (R5), and match the exponents
(R6).

**R1 · `mathematicalPartitionFunctionBetaReal_pos`** changes the **context**. The lemma is
`[Nonempty ι] → 0 < 𝓒.mathematicalPartitionFunctionBetaReal b`; write `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b`.
Placeholders: `{ι : Type} [Fintype ι] [MeasurableSpace ι] [Nonempty ι] (𝓒 : CanonicalEnsemble ι) (t : ℝ) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hZ : 0 < 𝓒.mathematicalPartitionFunctionBetaReal t ⊢ G` |

**R2 · `hab.ne'`** (`LT.lt.ne'`) changes the **context**. The lemma is `a < b → b ≠ a`; the primed version
flips the sides, so from `0 < Z` you get `Z ≠ 0`, which is what R4 needs. Placeholders:
`{α : Type} [Preorder α] (a b : α) (hab : a < b)` (α has `≤` and `<`; `ℝ` qualifies). You can also write it
inline: `div_div_div_cancel_right₀ hZ.ne'`.

| Before | After |
|---|---|
| `hab : a < b ⊢ G` | `h : b ≠ a ⊢ G` |

**R3 · `unfold probabilityBetaReal`** changes the **goal**: every `𝓒.probabilityBetaReal t k` becomes its body.
`simp only [probabilityBetaReal]` does the same. Placeholders: `(𝓒 : CanonicalEnsemble ι) (t : ℝ) (k : ι)`.

| Before | After |
|---|---|
| `⊢ P (𝓒.probabilityBetaReal t k)` | `⊢ P (rexp (-t * 𝓒.energy k) / 𝓒.mathematicalPartitionFunctionBetaReal t)` |

**R4 · `rw [div_div_div_cancel_right₀ hc]`** changes the **goal**. The lemma is
`c ≠ 0 → a / c / (b / c) = a / b`: a common divisor cancels from a quotient of quotients. Placeholders:
`{α : Type} [GroupWithZero α] (a b c : α) (hc : c ≠ 0)` (α has `*`, `0`, and an inverse for every nonzero
element; `ℝ` and `ℂ` qualify).

| Before | After |
|---|---|
| `⊢ P (a / c / (b / c))` | `⊢ P (a / b)` |

**R5 · `rw [← Real.exp_sub]`** changes the **goal**. The lemma is `Real.exp_sub : rexp (x - y) = rexp x / rexp y`,
and `←` uses it right to left, folding a quotient of exponentials into one. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (rexp x / rexp y)` | `⊢ P (rexp (x - y))` |

**R6 · `ring_nf`** **closes** a goal `f A = f B` in which `A` and `B` are equal as ring expressions. It puts
every ring subterm into normal form, also those inside a function such as `rexp`, and then both sides are
the same. Placeholders: `(f : ℝ → ℝ) (a x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ f (-a * x - -a * y) = f (-a * (x - y))` | closed |

**W1 (R2 → R4 → R5 → R6), with `rexp (2 * x) / c` in place of a probability:**

```lean-goal
⊢ rexp (2 * x) / c / (rexp (2 * y) / c) = rexp (2 * (x - y))
⊢ rexp (2 * x) / rexp (2 * y) = rexp (2 * (x - y))
⊢ rexp (2 * x - 2 * y) = rexp (2 * (x - y))
```

The last goal is closed by `ring_nf`.

---

## Part 2 · `lower_energy_more_likely`

Statement: with `hb : 0 ≤ b` and `hE : E i ≤ E j`, `p_b(j) ≤ p_b(i)`. Get `0 < Z(b)` (R1), unfold (R3),
drop the common positive denominator (R7), compare exponents instead of exponentials (R8), and close the
product inequality (R9).

**R7 · `rw [div_le_div_iff_of_pos_right hc]`** changes the **goal**. The lemma is
`0 < c → (a / c ≤ b / c ↔ a ≤ b)`; `rw` with an `↔` replaces the left statement by the right one.
Placeholders: `(a b c : ℝ) (hc : 0 < c)`. (Stated for any ordered group with zero; `ℝ` qualifies.)

| Before | After |
|---|---|
| `⊢ a / c ≤ b / c` | `⊢ a ≤ b` |

**R8 · `rw [Real.exp_le_exp]`** changes the **goal**. The lemma is `rexp x ≤ rexp y ↔ x ≤ y` ($e^x$ is strictly
increasing). Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ rexp x ≤ rexp y` | `⊢ x ≤ y` |

**R9 · `nlinarith`** **closes** an inequality that follows from the hypotheses after multiplying pairs of them.
`-t * y ≤ -t * x` is `0 ≤ t * (y - x)`, the product of `0 ≤ t` and `0 ≤ y - x`. `linarith` treats `t * x` as an
opaque atom and fails. Placeholders: `(t x y : ℝ) (ht : 0 ≤ t) (hxy : x ≤ y)`.

| Before | After |
|---|---|
| `ht : 0 ≤ t, hxy : x ≤ y ⊢ -t * y ≤ -t * x` | closed |

**W2 (R7 → R8 → R9), with exponent `-(3 * s) * y` and denominator `c`:**

```lean-goal
⊢ rexp (-(3 * s) * y) / c ≤ rexp (-(3 * s) * x) / c
⊢ rexp (-(3 * s) * y) ≤ rexp (-(3 * s) * x)
⊢ -(3 * s) * y ≤ -(3 * s) * x
```

The last goal is closed by `nlinarith`.

---

## Traps

- `gcongr` on `rexp (-b * E j) / Z ≤ rexp (-b * E i) / Z` matches the pattern `rexp (-b * _)` and asks for
  `0 ≤ -b` and `E j ≤ E i`: both false in general. Compare numerators with R7 and exponents with R8 instead.
- R4 wants `c ≠ 0`, R7 wants `0 < c`. R1 gives `0 < Z`; add `.ne'` (R2) for R4.
- `rw [Real.exp_sub]` (left to right) looks for `rexp (x - y)`, which is not in the goal after R4. Use `←`.
- After R5 the goal is `rexp (-b * E j - -b * E i) = rexp (-b * (E j - E i))`; `rfl` fails because the
  exponents are equal only as ring expressions. `ring_nf` (R6) closes it; so does `congr 1` then `ring`.
- R1 needs `[Nonempty ι]`: over no microstates `Z` is the empty sum `0`. The spec theorems carry that
  instance, so `𝓒.mathematicalPartitionFunctionBetaReal_pos b` finds it by itself.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `0 < Z(b)` | `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` | R1 |
| `0 < Z → Z ≠ 0` | `hZ.ne'` | R2 |
| unfold `p_b(i)` | `unfold probabilityBetaReal` / `simp only [probabilityBetaReal]` | R3 |
| `a / c / (b / c) → a / b` | `rw [div_div_div_cancel_right₀ hZ.ne']` | R4 |
| `rexp x / rexp y → rexp (x - y)` | `rw [← Real.exp_sub]` | R5 |
| exponents equal up to ring algebra | `ring_nf` | R6 |
| `a / c ≤ b / c → a ≤ b` | `rw [div_le_div_iff_of_pos_right hZ]` | R7 |
| `rexp x ≤ rexp y → x ≤ y` | `rw [Real.exp_le_exp]` | R8 |
| `-t * y ≤ -t * x` from `0 ≤ t`, `x ≤ y` | `nlinarith` | R9 |
| see the state | infoview | |
