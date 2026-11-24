# M142 · The CHSH operator identity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's type class `Ring` (rings whose
multiplication need not commute), the lemmas `mul_assoc`, `one_mul`, `mul_one`, `sq` and the four
distributivity laws, local `∀`-helpers with implicit arguments, and the tactics `simp only` with
instantiated helpers, `norm_num` on ring numerals, and `abel`.

**The math.** In a ring $R$ (think: operators on a Hilbert space, `Matrix n n ℂ`) take $A_0, A_1$
(Alice's observables) and $B_0, B_1$ (Bob's) with $A_i^2 = B_j^2 = 1$ and $A_iB_j = B_jA_i$ for all
$i, j$. The commutator is $[X, Y] = XY - YX$. The CHSH operator is
$C = A_0B_0 + A_0B_1 + A_1B_0 - A_1B_1 = \sum_{i,j} s_{ij} A_iB_j$ with $s_{11} = -1$ and $s_{ij} = 1$
otherwise. Then $C^2 = \sum s_{ij}s_{kl}\, A_iB_jA_kB_l = \sum s_{ij}s_{kl}\, A_iA_kB_jB_l$ (move $A_k$ left
past $B_j$), and:

| Words with | Contribute |
|---|---|
| $i = k$, $j = l$ | $A_i^2B_j^2 = 1$, four times: $4$ |
| $i = k$, $j \ne l$ | $B_0B_1 + B_1B_0$ for $i = 0$, minus the same for $i = 1$: $0$ |
| $i \ne k$, $j = l$ | $0$ in the same way |
| $i \ne k$, $j \ne l$ | $-A_0A_1B_0B_1 + A_0A_1B_1B_0 + A_1A_0B_0B_1 - A_1A_0B_1B_0 = -[A_0, A_1][B_0, B_1]$ |

So $C^2 = 4 - [A_0, A_1][B_0, B_1]$. The Lean proof does exactly this bookkeeping: expand, bring every
word to the normal form "`A`s first, then `B`s, squares removed", and compare the two sums.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : R → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` is an arbitrary goal that the step leaves alone.
- Placeholders are written as Lean binders. `{R : Type}` is any type. The bracket `[Ring R]` is a
  requirement on `R` (a *type class*): `R` has `+`, `-`, `*`, `0`, `1` with the ring laws, `*`
  associative and distributive but **not necessarily commutative**. `ℤ`, `ℝ`, `ℂ` and `Matrix n n ℂ`
  meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `{R : Type} [Ring R]` | `R` is any ring; `inst✝ : Ring R` in the context is that assumption |
| `a * b * c` | `(a * b) * c`: `*` groups to the left |
| `a * (b * (c * d))` | the right-nested word $abcd$; R9 brings every product to this shape |
| `a ^ 2` | `a * a` (`Monoid.npow`, rewritten by `sq`, R7) |
| `4`, `1` in `R` | numerals of the ring: `1` is the unit, `4` is `1 + 1 + 1 + 1` but not syntactically (R6) |
| `a - b * c` | `a - (b * c)`: `*` binds tighter than `+`, `-` |
| `∀ {a b : R}, …` | `a b` are implicit: Lean infers them from the next explicit argument (R1) |
| `∀ (x : R), …` | how Lean prints `∀ x, …` |
| `A₀ * A₁ - A₁ * A₀` | the commutator $[A_0, A_1]$ (no special notation is used here) |
| `n • x` (after a failed `abel`) | `n` copies of `x` added (`n` an integer, `-1 • x = -x`); `4 • 1` is `abel`'s normal form for `1 + 1 + 1 + 1` |
| `sw h₀₀`, `sq1 hA₀` | a helper applied to a hypothesis: the rewrite rule `∀ x, B₀ * (A₀ * x) = A₀ * (B₀ * x)`, resp. `∀ x, A₀ * (A₀ * x) = x` |

---

## Part 1 · `chsh_sq`

Statement: for `A₀ A₁ B₀ B₁ : R` with the four squares equal to `1` (`hA₀ … hB₁`) and the four
commutations `h₀₀ : A₀ * B₀ = B₀ * A₀`, …, `h₁₁`, the square of the CHSH operator equals
`4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)`.

### Helpers that rewrite inside a word

After R9 every word is right-nested, `x₁ * (x₂ * (x₃ * x₄))`. A hypothesis `h₀₀ : A₀ * B₀ = B₀ * A₀`
never matches there: its left side `A₀ * B₀` is a product of two letters, and inside the word the
second factor of every `*` is the whole tail. So you state helpers whose left side has a tail `x`.

**R1 · `have name : ∀ {a b : R}, … := by …`** changes the **context**: it adds a lemma you can
instantiate. The example states `one_l : ∀ {a : R}, a = 1 → ∀ x, a * x = x` (not a helper this exercise
needs; same shape). With implicit `{a}`, `one_l ha` reads `a` off `ha : a = 1` and is the equation
`∀ x, a * x = x`. Indent the proof lines further than `have`. Placeholders: `{R : Type} [Ring R]
(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `⊢ G`, plus `one_l : ∀ {a : R}, a = 1 → ∀ (x : R), a * x = x` in the context |

The two helpers this exercise needs:
`sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x)` (move `a` left past `b`) and
`sq1 : ∀ {a : R}, a * a = 1 → ∀ x, a * (a * x) = x` (cancel a square in front of a tail `x`). Prove each with R2, then R3, then the hypothesis (`rw [← h]` for `sw`, `rw [h]` for
`sq1`), then R4 (`sw`) or R5 (`sq1`).

**R2 · `intro a b h x`** changes the **goal and the context**: the binders of a `∀`/`→` goal move into
the context, implicit `{a b}` included. Placeholders: `{R : Type} [Ring R] (Q : R → R → R → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ {a b : R}, a * b = b * a → ∀ (x : R), Q a b x` | `a b : R, h : a * b = b * a, x : R ⊢ Q a b x` |

**R3 · `rw [← mul_assoc]`** changes the **goal**. The lemma is `mul_assoc : a * b * c = a * (b * c)`;
right to left it regroups the first `a * (b * c)` it finds. Placeholders: `{R : Type} [Ring R] (a b c : R)`.
In `sw`'s proof this exposes `b * a` on the left so `rw [← h]` can turn it into `a * b`.

| Before | After |
|---|---|
| `⊢ P (a * (b * c))` | `⊢ P (a * b * c)` |

**R4 · `rw [mul_assoc]`** changes the **goal**: left to right, the first `a * b * c` becomes
`a * (b * c)`. When both sides then agree, `rw` closes the goal itself (it tries `rfl`).

| Before | After |
|---|---|
| `⊢ P (a * b * c)` | `⊢ P (a * (b * c))` |

**R5 · `rw [one_mul]`** changes the **goal**. The lemma is `one_mul : 1 * a = a`. Placeholders:
`{R : Type} [Ring R] (a : R)`. In `sq1`'s proof it removes the `1` that `rw [h]` leaves.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

### Normalising both sides

**R6 · `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]`** changes the **goal**. `show T by tac` is a
proof of `T` that `rw` uses like a lemma; `norm_num` proves numeral identities in any ring. Do it
**first**: after expansion the left side is a sum of sixteen words, four of which become `1`, and
`abel` (R14) can only cancel them against `1 + 1 + 1 + 1`, not against `4`.

| Before | After |
|---|---|
| `⊢ P 4` | `⊢ P (1 + 1 + 1 + 1)` |

**R7 · `simp only [sq]`** changes the **goal**. The lemma is `sq : a ^ 2 = a * a`. Placeholders:
`{R : Type} [Ring R] (a : R)` (any monoid works).

| Before | After |
|---|---|
| `⊢ P (a ^ 2)` | `⊢ P (a * a)` |

**R8 · `simp only [add_mul, mul_add, sub_mul, mul_sub]`** changes the **goal**: every product of sums and
differences is distributed, keeping the order of the factors. `add_mul : (a + b) * c = a * c + b * c`,
`mul_add : a * (b + c) = a * b + a * c`, `sub_mul`, `mul_sub` the same with `-`. Placeholders:
`{R : Type} [Ring R] (a b c d : R)`.

| Before | After |
|---|---|
| `⊢ P ((a + b) * (c - d) - (a - b) * (c + d))` | `⊢ P (a * c + b * c - (a * d + b * d) - (a * c - b * c + (a * d - b * d)))` |

**R9 · `simp only [mul_assoc]`** changes the **goal**: every product is re-associated to the right, so
each word becomes `x₁ * (x₂ * (x₃ * x₄))` and the helpers of R10, R11 can see `b * (a * x)`.

| Before | After |
|---|---|
| `⊢ P (a * b * c * d)` | `⊢ P (a * (b * (c * d)))` |

**R10 · `simp only [sw hab]`** changes the **goal**. `sw hab : ∀ x, b * (a * x) = a * (b * x)` is a rewrite
rule with a free tail `x`, so it fires on `b * (a * _)` at any depth of a word. With `h₀₀ : A₀ * B₀ = B₀ * A₀`,
`sw h₀₀` moves `A₀` left past `B₀`. Placeholders: `{R : Type} [Ring R] (a b c x : R)`,
`hab : a * b = b * a`.

| Before | After |
|---|---|
| `⊢ P (c * (b * (a * x)))` | `⊢ P (c * (a * (b * x)))` |

**R11 · `simp only [sq1 ha]`** changes the **goal**: a square followed by a tail cancels.
`sq1 ha : ∀ x, a * (a * x) = x`. Placeholders: `{R : Type} [Ring R] (a c x : R)`, `ha : a * a = 1`.

| Before | After |
|---|---|
| `⊢ P (c * (a * (a * x)))` | `⊢ P (c * x)` |

**R12 · `simp only [ha]`** changes the **goal**: a square at the **end** of a word (no tail) is matched by the
hypothesis `ha : a * a = 1` itself. Placeholders as in R11.

| Before | After |
|---|---|
| `⊢ P (c * (a * a))` | `⊢ P (c * 1)` |

**R13 · `simp only [mul_one]`** changes the **goal**. The lemma is `mul_one : a * 1 = a`; it removes the `* 1`
that R12 leaves. Placeholders: `{R : Type} [Ring R] (c : R)`.

| Before | After |
|---|---|
| `⊢ P (c * 1)` | `⊢ P c` |

Put R7–R13 in **one** `simp only [...]`, with every instance of the helpers that can fire (`sw h₀₀`, …,
`sw h₁₁`, `sq1 hA₀`, `sq1 hA₁`) and **all four** squares `hA₀ hA₁ hB₀ hB₁` for word ends. The `A`
squares are needed too: `simp` may first turn `A₀ * (A₀ * (B₀ * B₀))` into `A₀ * (A₀ * 1)` and then, by
`mul_one`, into `A₀ * A₀`, which only `hA₀` itself matches. Leave them out and `abel` fails with
`2 • (A₀ * A₀)` in the goal. `simp` interleaves them until
nothing changes. Separate calls also work (W2 does that to show each stage), but then the swaps and
cancellations must share one call: a swap can create a new square and a cancellation can expose a new
swap.

**R14 · `abel`** **closes** an equation that holds in every additive commutative group: it reorders and
cancels `+`, `-` and treats each product such as `a * (b * c)`, and the numeral `1`, as an opaque atom. It
knows nothing about `*`, so it succeeds only when both sides are sums of the same normal-form words.
Placeholders: `{R : Type} [Ring R] (x y : R)`.

| Before | After |
|---|---|
| `⊢ 1 + x - y + (1 + y) = 1 + 1 + x` | closed |

### Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: a right-cancelling helper** `∀ {a : R}, a * a = 1 → ∀ x, x * a * a = x`, by R2, R4, `rw [h]`, R13:

```lean-goal
⊢ ∀ {a : R}, a * a = 1 → ∀ (x : R), x * a * a = x
⊢ x * a * a = x
⊢ x * (a * a) = x
⊢ x * 1 = x
```

**W2: `(ab + ba)² = 4`** for `a * a = 1`, `b * b = 1`, `a * b = b * a`, with `sw`, `sq1` given as
hypotheses (in the exercise you prove them, R1–R5): R6, R7,
R8 (here only `add_mul`, `mul_add` fire), R9, then R10–R12 in one call (`sw hab, sq1 ha, sq1 hb, ha, hb`),
then R14:

```lean-goal
⊢ (a * b + b * a) ^ 2 = 4
⊢ (a * b + b * a) ^ 2 = 1 + 1 + 1 + 1
⊢ (a * b + b * a) * (a * b + b * a) = 1 + 1 + 1 + 1
⊢ a * b * (a * b) + b * a * (a * b) + (a * b * (b * a) + b * a * (b * a)) = 1 + 1 + 1 + 1
⊢ a * (b * (a * b)) + b * (a * (a * b)) + (a * (b * (b * a)) + b * (a * (b * a))) = 1 + 1 + 1 + 1
⊢ 1 + 1 + (1 + 1) = 1 + 1 + 1 + 1
```

---

## Traps

- `ring` does not apply: `R` is not commutative. `noncomm_ring` proves identities true in **every** ring,
  but it cannot use hypotheses such as `hA₀ : A₀ * A₀ = 1`, so it cannot prove this one.
- `simp only [hA₀, h₀₀]` makes no progress on a right-nested word such as `A₀ * (B₀ * (A₀ * B₁))`: the left
  sides `A₀ * A₀`, `A₀ * B₀` never occur there. Use the helpers `sw`, `sq1` (R10, R11).
- The helpers fire only on right-nested words: run `mul_assoc` (R9) before them or in the same call.
- `sw h₀₀` moves `A₀` **left** past `B₀` (it rewrites `B₀ * (A₀ * x)`). Feeding `h₀₀.symm` instead would make
  `simp` swap the other way, and mixing both directions loops.
- Split `4` (R6) before `abel`: `abel` writes `1 + 1 + 1 + 1` as `4 • 1` and cannot match it with `4`.
- A square at the end of a word, `x * (B₀ * B₀)` or (after `mul_one` has fired) `A₀ * A₀`, has no tail
  for `sq1`: list all four `hA₀ hA₁ hB₀ hB₁` themselves (R12), and `mul_one` (R13).
- If `abel` fails, it prints its normal form (and suggests `abel_nf`; ignore that). Look in the goal for
  a word that is not in normal form (a `B` before an `A`, or a repeated letter such as `A₀ * A₀`); add
  the missing helper instance or square.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a helper with a tail | `have sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x) := by …` | R1 |
| name the binders | `intro a b h x` | R2 |
| regroup `a * (b * c)` / `a * b * c` | `rw [← mul_assoc]` / `rw [mul_assoc]` | R3, R4 |
| `1 * a` → `a`, `a * 1` → `a` | `one_mul`, `mul_one` | R5, R13 |
| numeral `4` for `abel` | `rw [show (4 : R) = 1 + 1 + 1 + 1 by norm_num]` | R6 |
| `a ^ 2` → `a * a` | `sq` | R7 |
| distribute | `add_mul, mul_add, sub_mul, mul_sub` | R8 |
| right-nest every word | `mul_assoc` | R9 |
| swap / cancel inside a word | `sw hab`, `sq1 ha` | R10, R11 |
| square at a word's end | `ha` (here all four: `hA₀, hA₁, hB₀, hB₁`) | R12 |
| all of R7–R13 at once | `simp only [sq, add_mul, …, mul_assoc, sw h₀₀, …, sq1 hA₀, …, hB₀, …, mul_one]` | R7–R13 |
| sums of the same words | `abel` | R14 |
| see the state | infoview | |
