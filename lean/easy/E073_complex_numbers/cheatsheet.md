# E073 · Complex numbers: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's complex numbers `ℂ`: the
real and imaginary parts `re`, `im`, the imaginary unit `I`, the conjugate `conj`, the cast `ℝ → ℂ`,
the squared modulus `Complex.normSq`, and proving an equation in `ℂ` by comparing parts.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal". Here it often takes two arguments, `P : ℝ → ℝ → Prop`, so one entry can
  show the `re` and the `im` lemma side by side. The step changes only the parts inside `P (…)`.
- Placeholders are written as Lean binders: `(z w : ℂ)` are arbitrary complex numbers, `(x : ℝ)` a real one.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

In Mathlib a complex number is a structure with two real fields: `z = z.re + z.im · i`. Everything below
reduces to facts about those two real numbers.

| You see | It means |
|---|---|
| `ℂ` | Mathlib's complex numbers, `Complex` (typed `\C`) |
| `z.re`, `z.im` | the real part and the imaginary part of `z`, both in `ℝ` |
| `re 2`, `im 2` | `(2 : ℂ).re`, `(2 : ℂ).im`; with `open Complex` Lean prints `Complex.re 2` this way |
| `I` | `Complex.I`, the imaginary unit `i` (`I.re = 0`, `I.im = 1`); `open Complex` lets you write `I` |
| `conj z` | the complex conjugate `z.re - z.im · i`. Notation from `open ComplexConjugate` |
| `(starRingEnd ℂ) z` | how the infoview prints `conj z` (the conjugate is Mathlib's `star` operation on `ℂ`) |
| `↑x` with `x : ℝ` | the real number `x` cast into `ℂ` (`Complex.ofReal x`, i.e. `x + 0 · i`) |
| `2 * ↑z.re` | the right side of `add_conj'`: `z.re` is real, so Lean casts it to multiply it by the complex `2` |
| `normSq z` | `Complex.normSq z = z.re² + z.im²`, the squared modulus `|z|²`, a real number |
| `case a` | the name `apply Complex.ext` gives both of its goals (the lemma's hypotheses are unnamed) |

---

## Part 1 · `mul_conj_lit`

Statement: `(1 + I) * (1 - I) = 2`. Split the equation into its real and imaginary parts, then compute each
part with the formulas for `+`, `-`, `*` and the parts of `I` and numerals.

**R1 · `apply Complex.ext`** changes the **goal list**: one goal becomes two. The lemma is
`Complex.ext : z.re = w.re → z.im = w.im → z = w`; `apply` leaves its two hypotheses as goals, both named
`case a`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ z = w` | `⊢ z.re = w.re`, `⊢ z.im = w.im` |

`apply Complex.ext <;> tac` runs `tac` on both goals (TACTIC_STATES, "Structure").

**R2 · `Complex.add_re`, `Complex.add_im`** change the **goal**: `(z + w).re = z.re + w.re` and
`(z + w).im = z.im + w.im`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z + w).re (z + w).im` | `⊢ P (z.re + w.re) (z.im + w.im)` |

**R3 · `Complex.sub_re`, `Complex.sub_im`** change the **goal**: `(z - w).re = z.re - w.re` and
`(z - w).im = z.im - w.im`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z - w).re (z - w).im` | `⊢ P (z.re - w.re) (z.im - w.im)` |

**R4 · `Complex.mul_re`, `Complex.mul_im`** change the **goal**: the product formula
$(a + bi)(c + di) = (ac - bd) + (ad + bc)i$, i.e. `(z * w).re = z.re * w.re - z.im * w.im` and
`(z * w).im = z.re * w.im + z.im * w.re`. Placeholders: `(z w : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (z * w).re (z * w).im` | `⊢ P (z.re * w.re - z.im * w.im) (z.re * w.im + z.im * w.re)` |

**R5 · `Complex.I_re`, `Complex.I_im`, `Complex.re_ofNat`, `Complex.im_ofNat`** change the **goal**: the
parts of `I` are `0` and `1`; a numeral `n : ℂ` has parts `n` and `0`. `Complex.one_re`, `one_im`,
`zero_re`, `zero_im` do the same for `1` and `0`. `simp` applies all of them (and R2–R4) by itself.

| Before | After |
|---|---|
| `⊢ P I.re I.im (re 2) (im 2)` | `⊢ P 0 1 2 0` |

**R6 · `norm_num`** **closes** a goal of numerals in `ℝ`. It first runs `simp`'s lemma set, so it also does
R2–R5: on a `re` or `im` goal of literals you do not need a separate `simp` before it.

| Before | After |
|---|---|
| `⊢ 1 * 2 - 3 * -1 = 5` | no goals |

**W1.** `(2 + I) * (2 - I) = 5`. `apply Complex.ext <;> simp` closes the `im` goal and leaves the `re` goal
as numerals, which `norm_num` closes:

```lean-goal
⊢ (2 + I) * (2 - I) = 5
⊢ 2 * 2 + 1 = 5
```

---

## Part 2 · `sq_one_add_I`

Statement: `(1 + I) ^ 2 = 2 * I`. Here you do not need parts: expand the square as a polynomial in the
unknown `I`, replace `I ^ 2` by `-1`, and finish with ring algebra.

**R7 · `ring_nf`** changes the **goal**: it rewrites every ring expression into a normal form (expanded,
sorted, `x * x` as `x ^ 2`) and does not need to close the goal. It treats `I` as an unknown, so it does not
know `I ^ 2 = -1`. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((1 + a) ^ 2)` | `⊢ P (1 + a * 2 + a ^ 2)` |

**R8 · `rw [Complex.I_sq]`** changes the **goal**. The lemma is `Complex.I_sq : I ^ 2 = -1`. `rw` needs
`I ^ 2` to appear literally, which is why R7 comes first.

| Before | After |
|---|---|
| `⊢ P (I ^ 2)` | `⊢ P (-1)` |

**R9 · `ring`** **closes** an equation that holds in every commutative ring (`ℝ`, `ℂ`), unknowns such as
`a`, `I` or `z.re` included. It does not use hypotheses or `I ^ 2 = -1`. Placeholders: `(a : ℂ)`.

| Before | After |
|---|---|
| `⊢ 1 + a * 2 + -1 = a * 2` | no goals |

**W2.** `(1 - I) ^ 2 = -2 * I`: `ring_nf` (R7), `rw [Complex.I_sq]` (R8), `ring` (R9):

```lean-goal
⊢ (1 - I) ^ 2 = -2 * I
⊢ 1 - I * 2 + I ^ 2 = -(I * 2)
⊢ 1 - I * 2 + -1 = -(I * 2)
```

---

## Part 3 · `add_conj'`

Statement: for every `z : ℂ`, `z + conj z = 2 * z.re` (the right side is `2 * ↑z.re`, the real `z.re`
cast into `ℂ`). Split into parts (R1); `simp` computes both sides with R2, R4, R5 and the two entries below.
The `im` goal closes (`z.im + -z.im = 0`), the `re` goal is left as `z.re + z.re = 2 * z.re`, which is ring
algebra (R9).

**R10 · `Complex.conj_re`, `Complex.conj_im`** change the **goal**: `(conj z).re = z.re` and
`(conj z).im = -z.im`. The infoview prints `conj z` as `(starRingEnd ℂ) z`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P ((starRingEnd ℂ) z).re ((starRingEnd ℂ) z).im` | `⊢ P z.re (-z.im)` |

**R11 · `Complex.ofReal_re`, `Complex.ofReal_im`** change the **goal**: a real `x` cast into `ℂ` has
`(↑x).re = x` and `(↑x).im = 0`. Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (↑x).re (↑x).im` | `⊢ P x 0` |

**W3.** `z - conj z = 2 * z.im * I`. `apply Complex.ext <;> simp` closes the `re` goal and leaves the `im`
goal, which `ring` closes:

```lean-goal
⊢ z - (starRingEnd ℂ) z = 2 * ↑z.im * I
⊢ z.im + z.im = 2 * z.im
```

---

## Part 4 · `normSq_lit`

Statement: `Complex.normSq (3 + 4 * I) = 25`, i.e. $|3 + 4i|^2 = 3^2 + 4^2$. Unfold `normSq` into parts,
compute the parts with `simp` (R2, R4, R5), finish the numerals with `norm_num` (R6).

**R12 · `rw [Complex.normSq_apply]`** changes the **goal**. The lemma is
`Complex.normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im`. Placeholders: `(z : ℂ)`.

| Before | After |
|---|---|
| `⊢ P (normSq z)` | `⊢ P (z.re * z.re + z.im * z.im)` |

**W4.** `normSq (1 + 2 * I) = 5`: R12, then `simp`, then `norm_num`:

```lean-goal
⊢ normSq (1 + 2 * I) = 5
⊢ (1 + 2 * I).re * (1 + 2 * I).re + (1 + 2 * I).im * (1 + 2 * I).im = 5
⊢ 1 + 2 * 2 = 5
```

---

## Traps

- `add_conj` (the library lemma `z + conj z = ↑(2 * z.re)`) is on the `BANNED:` line: Part 3 is there so you
  prove it with `Complex.ext`. Its primed name `add_conj'` is the exercise's own theorem.
- `conj` is notation that only exists after `open ComplexConjugate`; `I` needs `open Complex` (or write
  `Complex.I`). The problem opens both inside its spec region.
- `ring` and `ring_nf` do not know `I ^ 2 = -1`: they treat `I` as an unknown. Rewrite with `Complex.I_sq`
  (R8) between them. `rw [Complex.I_sq]` before `ring_nf` fails: `(1 + I) ^ 2` contains no `I ^ 2` yet.
- After `apply Complex.ext <;> simp`, `simp` may already have closed one of the two goals. A finishing tactic
  on the next line then runs on the remaining goal only; use `<;>` if both might be left.
- `norm_num` does not prove `z.re + z.re = 2 * z.re`: it computes with numerals, not with letters. That is
  `ring`'s job (R9).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `z = w` in `ℂ` → `re` and `im` goals | `apply Complex.ext` | R1 |
| parts of `+`, `-`, `*` | `simp` (`Complex.add_re`, `sub_re`, `mul_re`, … `_im`) | R2–R4 |
| parts of `I`, numerals | `simp` (`Complex.I_re`, `I_im`, `re_ofNat`, `im_ofNat`) | R5 |
| numerals in `ℝ` | `norm_num` (also runs `simp`) | R6 |
| expand a power | `ring_nf` | R7 |
| `I ^ 2 = -1` | `rw [Complex.I_sq]` | R8 |
| ring identity, letters allowed | `ring` | R9 |
| parts of `conj z` | `simp` (`Complex.conj_re`, `conj_im`) | R10 |
| parts of a real cast `↑x` | `simp` (`Complex.ofReal_re`, `ofReal_im`) | R11 |
| unfold `normSq` | `rw [Complex.normSq_apply]` | R12 |
| run on both goals | `<;>` | TACTIC_STATES |
| see the state | infoview | |
