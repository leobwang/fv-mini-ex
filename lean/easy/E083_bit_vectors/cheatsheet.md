# E083 · Bit vectors: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `decide` (E001), `simp` (E010), `omega`
(E011), `rw … at h` and `have`. **New here:** core Lean's `BitVec w` (fixed-width machine words),
its literals `n#w`, wraparound arithmetic, bitwise operators and shifts, the bridge `.toNat` to `Nat`,
and the tactic `bv_omega`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Prop` when the step changes only the
  context). The step changes only the part inside `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{w : Nat}` is any width; `(x y : BitVec w)` are any two
  w-bit words.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `BitVec w` | w-bit words: the naturals `0 … 2 ^ w - 1`, with arithmetic mod `2 ^ w` |
| `n#w` | the literal `n` as a `BitVec w`, reduced mod `2 ^ w` (`BitVec.ofNat w n`) |
| `0xFF#8` | the same with a hex numeral; the infoview prints it in decimal, `255#8` |
| `x.toNat` | the unsigned value of `x`, a `Nat` with `x.toNat < 2 ^ w` |
| `x + y`, `x - y`, `x * y` | wraparound arithmetic: the true result mod `2 ^ w` |
| `x &&& y`, `x \|\|\| y`, `x ^^^ y` | bitwise and, or, xor |
| `x <<< k`, `x >>> k` | shift left / right by `k : Nat` bits; bits pushed out are lost, zeros come in |
| `x < y`, `x ≤ y` | **unsigned** comparison: `x.toNat < y.toNat` (signed is `x.slt y`) |
| `2 ^ 8` | a `Nat` power; `omega` treats `2 ^ 8` as the numeral `256` |

---

## Part 1 · `lit_wrap`

Statement: in 8 bits, `255 + 1 = 0`. Only literals, so it is a computation (R1, R2).

**R1 · `n#w` and `.toNat`, closed by `decide`.** `n#w` stores `n mod 2 ^ w`: `0x1F = 31` does not fit in
4 bits, so `0x1F#4` is `15`. The infoview prints the numeral in decimal and unreduced, `31#4`; its value
is still 15. `decide` evaluates both sides and **closes** the goal.

| Before | After `decide` |
|---|---|
| `⊢ (31#4).toNat = 15` | no goals |

**R2 · wraparound `+ - *`, closed by `decide`.** Every operation reduces mod `2 ^ w`. In 3 bits:
`7 + 2 = 9 ≡ 1` and `0 - 1 ≡ 7`. `decide` **closes** the goal.

| Before | After `decide` |
|---|---|
| `⊢ 7#3 + 2#3 = 1#3 ∧ 0#3 - 1#3 = 7#3` | no goals |

## Part 2 · `shift_lit`

Statement: shifting `1` left by 3 bits in an 8-bit word gives `8`. A literal computation (R3).

**R3 · shifts and bitwise ops on literals, closed by `decide`.** `<<< k` multiplies by `2 ^ k` mod
`2 ^ w` (`9#4 <<< 1 = 18 mod 16 = 2`); `^^^` is xor bit by bit (`0101 ^^^ 0011 = 0110`). `decide`
**closes** the goal.

| Before | After `decide` |
|---|---|
| `⊢ 2#4 <<< 2 = 8#4 ∧ 9#4 <<< 1 = 2#4 ∧ 5#4 ^^^ 3#4 = 6#4` | no goals |

## Part 3 · `xor_self`

Statement: any 16-bit word xor itself is zero. `x` is a free variable, so `decide` cannot evaluate it
(it fails with "Expected type must not contain free variables"). Use the library identity (R4), which `simp` knows (R5).

**R4 · `rw [BitVec.xor_self]`** changes the **goal**. The lemma is
`BitVec.xor_self (x : BitVec w) : x ^^^ x = 0#w`. Placeholders: `{w : Nat} (x : BitVec w)`,
`(P : BitVec w → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x ^^^ x)` | `⊢ P 0#w` |

**R5 · `simp`** **closes** a goal that is a known bitwise identity on variables. Its default lemma set
includes R4, `BitVec.and_self : x &&& x = x`, `BitVec.or_self`, `BitVec.xor_zero`, ….
Placeholders: `{w : Nat} (x : BitVec w)`.

| Before | After `simp` |
|---|---|
| `⊢ x &&& x = x` | no goals |

## Part 4 · `toNat_lt`

Statement: the value of an 8-bit word is below 256. `bv_omega` closes it (R11). By hand: add the
built-in bound (R6) and let `omega` read `2 ^ 8` as 256 (R10); W1 does exactly that at width 4.

**R6 · `have h := x.isLt`** changes the **context**. `BitVec.isLt (x : BitVec w) : x.toNat < 2 ^ w` is
the invariant every `BitVec` carries. Placeholders: `{w : Nat} (x : BitVec w)`, `(P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `h : x.toNat < 2 ^ w ⊢ P` |

**R10 · `omega`** **closes** a linear goal over `Nat`/`Int`, using the hypotheses. It handles `+`, `-`
(truncated on `Nat`), multiplication by numerals, `%` and `/` by numerals, and `2 ^ 8` (a power of
numerals is a numeral). It treats `x.toNat` as an unknown natural and adds the bound R6 by itself, but
it does not understand `BitVec` operations or `<` on `BitVec`: those must first become `.toNat` facts
(R7–R9), or use R11.

| Before | After `omega` |
|---|---|
| `h : a + b < 2 ^ 8 ⊢ (a + b) % 2 ^ 8 = a + b` | no goals |

**W1 (width 4, not the exercise's word).** R6 then R10, with `x : BitVec 4`:

| Before | After `have h := x.isLt` | After `omega` |
|---|---|---|
| `⊢ x.toNat < 16` | `h : x.toNat < 2 ^ 4 ⊢ x.toNat < 16` | no goals |

## Part 5 · `add_no_overflow`

Statement: if the true sum of two 8-bit values is below 256, the wrapped sum `(x + y).toNat` equals it.
`bv_omega` closes it (R11). By hand: turn the `BitVec` sum into a `Nat` sum mod `2 ^ 8` (R7), then
`omega` drops the `%` using `h` (R10).

**R7 · `rw [BitVec.toNat_add]`** changes the **goal**. The lemma is
`BitVec.toNat_add (x y : BitVec w) : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ w`. Placeholders:
`{w : Nat} (x y : BitVec w)`, `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (x + y).toNat` | `⊢ P ((x.toNat + y.toNat) % 2 ^ w)` |

**W2 (doubling, not the exercise's statement).** R7 then R10, with `h : x.toNat < 128`:

```lean-goal
⊢ (x + x).toNat = 2 * x.toNat
⊢ (x.toNat + x.toNat) % 2 ^ 8 = 2 * x.toNat
```

## Part 6 · `succ_ne_zero`

Statement: an 8-bit `x` below 10 does not wrap to 0 when incremented. Here `<` and `≠` are on `BitVec`,
and the goal has literals: exactly the translation `bv_omega` automates (R8, R7, R9, then R10), so use
R11.

**R8 · `rw [BitVec.lt_def] at h`** changes the **context**. The lemma is
`BitVec.lt_def : x < y ↔ x.toNat < y.toNat`: `<` on `BitVec` is unsigned. Placeholders:
`{w : Nat} (x y : BitVec w)`, `(P : Prop)`.

| Before | After |
|---|---|
| `h : x < y ⊢ P` | `h : x.toNat < y.toNat ⊢ P` |

**R9 · `rw [BitVec.toNat_ofNat]`** changes the **goal**. The lemma is
`BitVec.toNat_ofNat : (BitVec.ofNat w n).toNat = n % 2 ^ w`, i.e. `(n#w).toNat = n % 2 ^ w`.
Placeholders: `(P : Nat → Prop)`; the entry uses the literal `5#8`.

| Before | After |
|---|---|
| `⊢ P (5#8).toNat` | `⊢ P (5 % 2 ^ 8)` |

**R11 · `bv_omega`** **closes** a linear goal about `BitVec`s. It rewrites every `BitVec` fact into
`.toNat` form (R7–R9 and the analogues for `-`, `≤`, `=`, `≠`), adds the bounds R6, and runs `omega` (R10).
Placeholders: `(x y : BitVec 8)`.

| Before | After `bv_omega` |
|---|---|
| `h1 : x ≤ y, h2 : y < 20#8 ⊢ x ≠ 30#8` | no goals |

**W3 (wraparound ruled out by a hypothesis).** `x + 50#8 = 10#8` holds only for `x = 216`, and
`h : x < 200#8` excludes it; `bv_omega` closes the goal in one step:

```lean-goal
⊢ x + 50#8 ≠ 10#8
```

---

## Traps

- `bv_omega` handles `+ - < ≤ = ≠`, `.toNat` and literals. It does not understand `&&&`, `|||`, `^^^`
  or shifts applied to variables: for those use `simp` (R5) or a bitwise lemma (R4).
- `decide` works only on closed terms (literals). With a variable `x` in the goal it fails with
  "Expected type must not contain free variables". Do not use it on Parts 3–6.
- `n#w` reduces mod `2 ^ w` silently: `256#8 = 0#8`. The infoview prints hex literals in decimal.
- `<` on `BitVec` is unsigned (R8). `255#8 < 1#8` is false even though `255#8` is `-1` as a signed byte.
- `(x + y).toNat` is **not** `x.toNat + y.toNat`: there is a `% 2 ^ w` (R7). The equation needs a no-overflow
  hypothesis.
- `omega` alone fails on `BitVec` operations and on `<` between `BitVec`s (`h : x < 3#4` is opaque to
  it): first move to `.toNat` (R7–R9), or use `bv_omega`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a fact about literals only (`toNat`, `+ - *`, `&&& \|\|\| ^^^`, `<<< >>>`) | `decide` | R1–R3 |
| `x ^^^ x → 0#w` | `rw [BitVec.xor_self]` | R4 |
| a bitwise identity on a variable | `simp` | R5 |
| the bound `x.toNat < 2 ^ w` | `have h := x.isLt` | R6 |
| `(x + y).toNat → (x.toNat + y.toNat) % 2 ^ w` | `rw [BitVec.toNat_add]` | R7 |
| `x < y → x.toNat < y.toNat` in a hypothesis | `rw [BitVec.lt_def] at h` | R8 |
| `(n#w).toNat → n % 2 ^ w` | `rw [BitVec.toNat_ofNat]` | R9 |
| a linear `Nat` goal with `%`, `2 ^ 8` | `omega` | R10 |
| a linear `BitVec` goal (`+ - < ≤ = ≠`) | `bv_omega` | R11 |
| see the state | infoview | |
