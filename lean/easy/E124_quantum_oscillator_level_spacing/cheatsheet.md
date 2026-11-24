# E124 · Quantum oscillator level spacing: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular unfolding a `def` with `simp only [f]` (E010);
`ring` (E034) is recalled in R3. **New here:** physlib's 1D quantum harmonic oscillator (`HarmonicOscillator`, `eigenValue`), the
constant `ℏ` as a positive-real subtype, the cast `ℕ → ℝ`, and the tactic `push_cast`.

## How to read an entry

Each entry is one tactic. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  "no goals" means the tactic closed the goal.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `HarmonicOscillator` | `QuantumMechanics.OneDimension.HarmonicOscillator` (namespaces opened by `open QuantumMechanics OneDimension`): a structure with fields `m : ℝ` (mass), `ω : ℝ` (angular frequency), `hω : 0 < ω`, `hm : 0 < m` |
| `Q.ω` | the field `ω` of `Q`: the angular frequency, a real number |
| `Q.eigenValue n` | `HarmonicOscillator.eigenValue Q n`, defined as `(↑n + 1 / 2) * ↑ℏ * Q.ω`: the energy $E_n = (n + \tfrac12)\hbar\omega$ of level `n` |
| `ℏ` | `Constants.ℏ : {x : ℝ // 0 < x}` (namespace opened by `open Constants`): reduced Planck's constant together with a proof that it is positive. `{x : ℝ // 0 < x}` is a *subtype*: pairs of a real `x` and a proof of `0 < x` |
| `↑ℏ` | the real number inside `ℏ` (`Subtype.val ℏ`). The statement writes `ℏ * Q.ω`; Lean inserts the coercion to `ℝ` |
| `↑n`, `↑(n + 1)` | the natural number `n` (resp. `n + 1`, added in `ℕ`) cast to `ℝ` (`Nat.cast`) |
| `1 / 2` | the real number one half (division in `ℝ`, not `ℕ`) |

---

## Part 1 · `eigenValue_gap`

Statement: for an oscillator `Q` and `n : ℕ`, `Q.eigenValue (n + 1) - Q.eigenValue n = ↑ℏ * Q.ω`, i.e.
$E_{n+1} - E_n = \hbar\omega$: the spectrum is evenly spaced. After unfolding, the left side is
$(\uparrow(n+1) + \tfrac12)\hbar\omega - (\uparrow n + \tfrac12)\hbar\omega$. The only obstacle is the cast
`↑(n + 1)`, which must become `↑n + 1` before the algebra closes.

**R1 · `unfold HarmonicOscillator.eigenValue`** changes the **goal**: every `Q.eigenValue k` is replaced by
the definition's body. Write the full name: `Q.eigenValue` is dot notation for
`HarmonicOscillator.eigenValue Q`. `simp only [HarmonicOscillator.eigenValue]` does the same.
Placeholders: `(Q : HarmonicOscillator) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (Q.eigenValue k)` | `⊢ P ((↑k + 1 / 2) * ↑ℏ * Q.ω)` |

**R2 · `push_cast`** changes the **goal**: it moves casts inward, using `Nat.cast_add : ↑(a + b) = ↑a + ↑b`,
`Nat.cast_one : ↑1 = 1` (and the analogues for `*`, `^`, numerals) everywhere in the goal. Placeholders:
`(a b k : ℕ)`, with the cast into `ℝ`.

| Before | After |
|---|---|
| `⊢ P ↑(a + b)` | `⊢ P (↑a + ↑b)` |
| `⊢ P ↑(k + 1)` | `⊢ P (↑k + 1)` |

**R3 · `ring`** **closes** an identity of commutative rings (E034). It treats `↑n`, `↑ℏ` and `Q.ω` as
unknowns (atoms). It also treats `↑(n + 1)` as an atom unrelated to `↑n`, which is why R2 comes first.
Placeholders: `(x c : ℝ)`.

| Before | After |
|---|---|
| `⊢ (x + 1 / 2) * c + (x + 1 / 2) * c = (2 * x + 1) * c` | no goals |

**W1: the chain on another spectrum.** Rigid-rotor levels `rot B l = B * ↑l * (↑l + 1)`; show
`rot B (l + 1) - rot B l = 2 * B * (↑l + 1)`. R1 (`unfold rot`), R2, R3:

```lean-goal
⊢ rot B (l + 1) - rot B l = 2 * B * (↑l + 1)
⊢ B * ↑(l + 1) * (↑(l + 1) + 1) - B * ↑l * (↑l + 1) = 2 * B * (↑l + 1)
⊢ B * (↑l + 1) * (↑l + 1 + 1) - B * ↑l * (↑l + 1) = 2 * B * (↑l + 1)
```

**W2: what happens without R2.** After `unfold rot`, `ring_nf` normalizes but cannot use `↑(1 + l) = 1 + ↑l`,
so `ring` would fail here. `push_cast` afterwards fixes it, and `ring` closes the goal:

```lean-goal
⊢ B * ↑(1 + l) + B * ↑(1 + l) ^ 2 - B * ↑l - B * ↑l ^ 2 = B * 2 + B * ↑l * 2
⊢ B * (1 + ↑l) + B * (1 + ↑l) ^ 2 - B * ↑l - B * ↑l ^ 2 = B * 2 + B * ↑l * 2
```

---

## Traps

- `ring` straight after R1 fails: it rewrites `↑(n + 1)` to `↑(1 + n)` and keeps it as an atom, so the two
  levels do not cancel. Push the cast first (R2).
- `unfold eigenValue` fails: the definition's name is `HarmonicOscillator.eigenValue` (the namespaces opened
  by `open QuantumMechanics OneDimension` let you write `HarmonicOscillator`, not drop it).
- `HarmonicOscillator` here is the one-dimensional `QuantumMechanics.OneDimension.HarmonicOscillator`, whose
  `ω` is a single real. physlib also has a `d`-dimensional `QuantumMechanics.HarmonicOscillator d` with
  `ω : Fin d → ℝ`; do not confuse them when searching the library.
- `ℏ` is not a real number but a subtype element; the goal shows `↑ℏ`. You never need its numeric value or
  its positivity here: `ring` treats `↑ℏ` as an unknown.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `Q.eigenValue k` → `(↑k + 1 / 2) * ↑ℏ * Q.ω` | `unfold HarmonicOscillator.eigenValue` | R1 |
| `↑(k + 1)` → `↑k + 1`, `↑(a + b)` → `↑a + ↑b` | `push_cast` | R2 |
| close a polynomial identity in `ℝ` | `ring` | R3 |
| level gap of a spectrum `E k` | `unfold E`, `push_cast`, `ring` | W1 |
| see the state | infoview (cursor after a tactic) | |
