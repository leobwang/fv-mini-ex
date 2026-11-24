# H030 · √2 is irrational: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `have`, `rw`, `simp`, anonymous
constructors `⟨_, _⟩`, `∀`/`∃`/`¬`. **New here:** Mathlib's strong induction on `ℕ`, divisibility `∣` and
primes, the tactics `linarith`, `omega`, `field_simp`, `exact_mod_cast`, the reals `ℝ` with `Real.sqrt`,
the casts `ℤ → ℝ`, `Int.natAbs`, and the predicate `Irrational`.

The proof has two halves. Part 1 is pure arithmetic in `ℕ`: no `p, q` with `q > 0` satisfy
`p² = 2q²`, by infinite descent (a solution with `q` gives one with `q/2 < q`). Part 2 moves a
hypothetical fraction `√2 = a / b` (with `a, b : ℤ`) down to `ℕ` and applies Part 1, which is the
**milestone**: prove it first.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`), or a bare proposition `P : Prop` when the entry only
  adds a hypothesis. The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as
  `[DivisionCommMonoid α]` is a requirement on `α` (a *type class*); each entry says which familiar
  types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
  A hypothesis that itself contains `, ` (such as `ih`) cannot sit in a cell; it is printed in a
  block under the table instead.

## Reading the goals

| You see | It means |
|---|---|
| `a ∣ b` (typed `\mid`, not `\|`) | `a` divides `b`: by definition `∃ c, b = a * c` |
| `Nat.Prime p` | `p` is prime (`2 ≤ p` and only `1, p` divide it); `Nat.prime_two : Nat.Prime 2` |
| `a ≠ b` | notation for `a = b → False` |
| `∀ m < q, X` | `∀ m, m < q → X` (a bounded quantifier) |
| `∃ m < n, X` | `∃ m, m < n ∧ X`; unpack it with `obtain ⟨m, hm, hX⟩` (W1) |
| `¬X` | `X → False`, so `intro` works on it as on `≠` |
| `ℝ`, `√x` | the real numbers; `√x` is `Real.sqrt x` (defined as `0` for `x < 0`) |
| `↑a` | a cast: the integer `a : ℤ` viewed as a real (`(a : ℝ)` in source) |
| `Irrational x` | by definition `x ∉ Set.range Rat.cast`: `Rat.cast : ℚ → ℝ` views a rational as a real, `Set.range f` is the set of values of `f`, `∉` is "not a member of". So: `x` is not a rational number. R9 turns it into a statement about integers, so you never unfold this |
| `a.natAbs` | `Int.natAbs a : ℕ`, the absolute value of `a : ℤ` as a natural number |
| `this` | the name `have := …` gives a fact when you give none |
| `case h` | the single case `Nat.strong_induction_on` produces |
| `m_1` | Lean renamed a bound `m` because a new `m` entered the context |
| `inst✝ : DivisionCommMonoid α` | an unnamed type-class assumption from `[…]` |

---

## Part 1 · `sq_ne_two_mul_sq`

Statement: for natural numbers `p, q` with `0 < q`, `p ^ 2 ≠ 2 * q ^ 2`. Descent: if `p² = 2q²` then
`2 ∣ p²`, so `2 ∣ p` (2 is prime), `p = 2k`, `4k² = 2q²`, `q² = 2k²`; the same argument gives `q = 2m`
and `k² = 2m²` with `0 < m < q`, which strong induction forbids.

**R1 · `induction q using Nat.strong_induction_on generalizing p with | _ q ih => ?_`** changes the
**context**: it adds the induction hypothesis `ih`, valid for every smaller `m`. The lemma is
`Nat.strong_induction_on : ∀ {p : ℕ → Prop} (n : ℕ), (∀ n, (∀ m < n, p m) → p n) → p n`. `generalizing p`
makes `ih` hold for **every** `p`, which descent needs (it calls `ih` with `k`, not `p`). Hypotheses
mentioning `q` (here `hq : 0 < q`) are generalized automatically and appear in `ih` as `0 < m →`. `?_`
turns the one case into an ordinary goal, so the next tactics go on the next lines.
Placeholders: `(P : ℕ → ℕ → Prop) (p q : ℕ)`.

| Before | After |
|---|---|
| `p q : ℕ ⊢ P p q` | `q : ℕ, p : ℕ ⊢ P p q` and `ih` below |

```text
q : ℕ
ih : ∀ m < q, ∀ (p : ℕ), P p m
p : ℕ
⊢ P p q
```

**R2 · `intro h`** on `a ≠ b` changes the **goal and the context**: `a ≠ b` unfolds to `a = b → False`.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `h : a = b ⊢ False` |

**R3 · `⟨c, h⟩ : a ∣ b`** is a proof term: `a ∣ b` is `∃ c, b = a * c`, so the witness `c` and
`h : b = a * c` prove it. Write it as `show a ∣ b from ⟨c, h⟩` when Lean has to be told the type.
Note that `h : p ^ 2 = 2 * q ^ 2` already has the shape `b = a * c` with `c = q ^ 2`.
Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `h : b = a * c ⊢ a ∣ b` | closed |

**R4 · `Nat.prime_two.dvd_of_dvd_pow`** changes the **context** (used in a `have`/`obtain`). The lemma is
`Nat.Prime.dvd_of_dvd_pow : Nat.Prime p → p ∣ m ^ n → p ∣ m` (a prime dividing a power divides the base);
`Nat.prime_two.dvd_of_dvd_pow h` is dot notation for `Nat.Prime.dvd_of_dvd_pow Nat.prime_two h`.
Placeholders: `(m n : ℕ) (P : Prop)`.

| Before | After |
|---|---|
| `h : 2 ∣ m ^ n ⊢ P` | `hm : 2 ∣ m ⊢ P` |

**R5 · `obtain ⟨k, rfl⟩ : 2 ∣ p := e`** changes the **context**: it unpacks `2 ∣ p` into a witness `k`
and the equation `p = 2 * k`, and the pattern `rfl` substitutes `2 * k` for `p` in every hypothesis and
the goal (`p` disappears). Placeholders: `(P : ℕ → Prop) (p : ℕ) (hd : 2 ∣ p)`.

| Before | After |
|---|---|
| `p : ℕ, hd : 2 ∣ p, hp : P p ⊢ False` | `k : ℕ, hp : P (2 * k) ⊢ False` |

**R6 · `linarith`** **closes** a goal `=`, `≤`, `<` that is a linear consequence of the hypotheses. It
normalizes first, so `(3 * a) ^ 2` is read as `9 * a ^ 2` and each power `a ^ 2` is one unknown. Use it
to divide an equation by a constant (`4k² = 2q²` gives `q² = 2k²`) and to reorder factors.
Placeholders: `(a b : ℕ)`.

| Before | After |
|---|---|
| `h : (3 * a) ^ 2 = 3 * b ^ 2 ⊢ b ^ 2 = 3 * a ^ 2` | closed |

**R7 · `exact ih m hm p hpos e`** **closes** `False`. A proof of `x ≠ y` is a function from `x = y` to
`False`, so feed it every argument in order: for
`ih : ∀ m < q, ∀ (p : ℕ), 0 < m → f p m ≠ g p m` that is `m`, a proof of `m < q`, `p`, a proof of
`0 < m`, and the equation. Each proof argument may be `(by omega)` or `(by linarith)`; an argument Lean
can infer may be `_`. The same move closes Part 2 with the milestone theorem in place of `ih`.
Placeholders: `(f g : ℕ → ℕ → ℕ) (q m p : ℕ)`.

| Before | After |
|---|---|
| `hm : m < q, hpos : 0 < m, e : f p m = g p m ⊢ False` (and `ih` above) | closed |

**R8 · `omega`** **closes** linear arithmetic goals over `ℕ` and `ℤ` (sums, constants times variables,
`<`, `≤`, `=`, `≠`). It cannot see through `^`: use `linarith` (R6) for the squared equations.
Placeholders: `(m : ℕ)`.

| Before | After |
|---|---|
| `h : 0 < 3 * m ⊢ m < 3 * m` | closed |

### Worked combinations (W1, W2)

**W1: abstract descent.** If every `n` with `P n` has a smaller `m` with `P m`, no `n` has `P n`. After
R1 (no `generalizing` needed), `intro hn` (R2: `¬P n` is `P n → False`), unpacking the smaller witness,
and R7:

```lean-goal
⊢ ¬P n
⊢ False
```

**W2: one divisibility step, with 3.** From `h : p ^ 2 = 3 * q ^ 2`, R3 + R4 (with `Nat.prime_three`)
+ R5 replace `p` by `3 * k`; then `⟨k, by linarith⟩` (R6) proves `∃ k, q ^ 2 = 3 * k ^ 2`:

```lean-goal
⊢ ∃ k, q ^ 2 = 3 * k ^ 2
```

with `h : (3 * k) ^ 2 = 3 * q ^ 2` in the context.

---

## Part 2 · `sqrt_two_irrational`

Statement: `Irrational (Real.sqrt 2)`. Suppose `√2 = a / b` with integers `a`, `b ≠ 0`. Squaring gives
`a² = 2b²` in `ℝ`, hence in `ℤ`, hence `|a|² = 2|b|²` in `ℕ` with `|b| > 0`, contradicting Part 1.

**R9 · `rw [irrational_iff_ne_rational]`** changes the **goal**. The lemma is
`irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ (a b : ℤ), b ≠ 0 → x ≠ ↑a / ↑b`: irrational means
"no fraction of integers equals it". Placeholders: `(x : ℝ)`.

| Before | After |
|---|---|
| `⊢ Irrational x` | `⊢ ∀ (a b : ℤ), b ≠ 0 → x ≠ ↑a / ↑b` |

**R10 · `intro a b hb h`** changes the **goal and the context**: one name per `∀` variable and per `→`,
and the last name takes the equation hidden in `≠` (R2). Placeholders: `(f g : ℤ → ℤ → ℝ)`.

| Before | After |
|---|---|
| `⊢ ∀ (a b : ℤ), b ≠ 0 → f a b ≠ g a b` | `a b : ℤ, hb : b ≠ 0, h : f a b = g a b ⊢ False` |

**R11 · `exact_mod_cast h`** **closes** a goal that is `h` up to casts `↑` (it uses lemmas such as
`Int.cast_pow`, `Int.cast_mul`, `Int.cast_inj`). It works upward (a fact in `ℤ`, a goal about `↑` in `ℝ`)
and downward (a fact about `↑` in `ℝ`, a goal in `ℤ`). Write the casts in a `have` statement explicitly,
`(b : ℝ)`. Placeholders: `(a b : ℤ)`.

| Before | After |
|---|---|
| `hb0 : b ≠ 0 ⊢ ↑b ≠ 0` | closed |
| `h : ↑a ^ 2 = 3 * ↑b ^ 2 ⊢ a ^ 2 = 3 * b ^ 2` | closed |

**R12 · `have := Real.sq_sqrt hx`** changes the **context**. The lemma is
`Real.sq_sqrt : 0 ≤ x → √x ^ 2 = x`; for a number write `Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)`.
Placeholders: `(x : ℝ) (hx : 0 ≤ x) (P : Prop)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x ⊢ P` | `this : √x ^ 2 = x ⊢ P` |

**R13 · `rw [h] at hs`** changes the **context**: it rewrites the hypothesis `hs` instead of the goal.
With `h : √2 = ↑a / ↑b` it replaces `√2` inside the fact from R12. Placeholders: `(P : ℝ → Prop) (s t : ℝ)`.

| Before | After |
|---|---|
| `hs : P s ⊢ P t` | `hs : P t ⊢ P t` |

**R14 · `div_pow`** changes a **hypothesis** (with `rw … at`) or the goal. The lemma is
`div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n`. Placeholders:
`{α : Type} [DivisionCommMonoid α] (a b : α) (n : ℕ)`; `ℝ` and `ℚ` qualify.

| Before | After |
|---|---|
| `hs : (a / b) ^ n = a ⊢ a ^ n / b ^ n = a` | `hs : a ^ n / b ^ n = a ⊢ a ^ n / b ^ n = a` |

**R15 · `field_simp at hs`** changes the **context**: it multiplies out every denominator it can prove
nonzero, using hypotheses such as `hb : b ≠ 0` (for `b ^ 2` too). The factor order of the result is its
own choice; read it in the infoview, and fix the order with `linarith` (R6). Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hb : b ≠ 0, hs : a / b = c ⊢ a = b * c` | `hs : a = b * c ⊢ a = b * c` |

**R16 · `have := congrArg f h`** changes the **context**: `congrArg f : x = y → f x = f y` applies a
function to both sides. With `f = Int.natAbs` it moves an equation from `ℤ` to `ℕ`.
Placeholders: `(x y : ℤ) (P : Prop)`.

| Before | After |
|---|---|
| `h : x = y ⊢ P` | `this : x.natAbs = y.natAbs ⊢ P` |

**R17 · `Int.natAbs_mul`** changes the **goal** (or a hypothesis). The lemma is
`Int.natAbs_mul (a b : ℤ) : (a * b).natAbs = a.natAbs * b.natAbs`. Placeholders: `(a b : ℤ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (a * b).natAbs` | `⊢ P (a.natAbs * b.natAbs)` |

**R18 · `Int.natAbs_pow`** changes the **goal** (or a hypothesis). The lemma is
`Int.natAbs_pow (n : ℤ) (k : ℕ) : (n ^ k).natAbs = n.natAbs ^ k`. Placeholders:
`(n : ℤ) (k : ℕ) (P : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (n ^ k).natAbs` | `⊢ P (n.natAbs ^ k)` |

**R19 · `simpa [l₁, l₂] using h`** **closes** the goal: it simplifies both `h` and the goal with the
lemmas `lᵢ` and `simp`'s defaults (which evaluate `(2 : ℤ).natAbs` to `2`), then closes the goal with
the simplified `h`. Placeholders: `(a b : ℤ)`.

| Before | After |
|---|---|
| `h : (a * b).natAbs = 7 ⊢ a.natAbs * b.natAbs = 7` | closed |

**R20 · `Int.natAbs_pos.mpr`** is a proof term. The lemma is `Int.natAbs_pos : 0 < a.natAbs ↔ a ≠ 0`;
for `hiff : A ↔ B`, `hiff.mp : A → B` and `hiff.mpr : B → A`. It supplies the milestone's hypothesis
`0 < q`. Placeholders: `(a : ℤ)`.

| Before | After |
|---|---|
| `ha : a ≠ 0 ⊢ 0 < a.natAbs` | closed |

Then the last step is R7 with the milestone: `sq_ne_two_mul_sq` is a theorem earlier in the file, so it
can be applied like `ih`, with `_` for `p` and `q` (Lean reads them off the equation).

### Worked combination (W3)

**W3: from real casts to `ℕ`, with 5.** From `h : ↑a ^ 2 = 5 * ↑b ^ 2`: `exact_mod_cast` (R11) gives
`h' : a ^ 2 = 5 * b ^ 2`, `congrArg Int.natAbs` (R16) gives `this`, and `simpa` with R17 and R18 (R19)
closes:

```lean-goal
⊢ a.natAbs ^ 2 = 5 * b.natAbs ^ 2
```

with `this : (a ^ 2).natAbs = (5 * b ^ 2).natAbs` in the context just before `simpa`.

---

## Traps

- Without `generalizing p`, `ih` speaks only about the original `p`; the descent needs it at `k` (R1).
- `obtain ⟨m, rfl⟩ : 2 ∣ q` also rewrites `ih`: it becomes `∀ m_1 < 2 * m, …`, so the descent call is
  `ih m _ k _ _` with side goals `m < 2 * m` and `0 < m`, both from `hq : 0 < 2 * m` by `omega` (R8).
- `omega` does not handle `k ^ 2`; use `linarith` (R6) for the equations, `omega` for the bounds.
- `field_simp` needs the **real** fact `hb : (b : ℝ) ≠ 0` in the context; `hb0 : b ≠ 0` in `ℤ` is not
  enough. Get it with `have hb : (b : ℝ) ≠ 0 := by exact_mod_cast hb0` (R11) before R15.
- After `field_simp at this`, the fact reads `this : ↑a ^ 2 = ↑b ^ 2 * 2` (factor order reversed from
  the goal `↑a ^ 2 = 2 * ↑b ^ 2`), so `exact this` fails; finish with `linarith` (R6).
- In a `have`, a bare `a ^ 2 = 2 * b ^ 2` with `a b : ℤ` is an equation in `ℤ`; write `(a : ℝ)` to get
  the real one.
- Part 2 has no descent of its own: once `h4 : a.natAbs ^ 2 = 2 * b.natAbs ^ 2` is in the context, the
  milestone closes it (R7, R20).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| strong induction, `p` kept general | `induction q using Nat.strong_induction_on generalizing p with \| _ q ih => ?_` | R1 |
| prove `a ≠ b` | `intro h` (goal becomes `False`) | R2 |
| `a ∣ b` from `b = a * c` | `show a ∣ b from ⟨c, h⟩` | R3 |
| `2 ∣ m` from `2 ∣ m ^ n` | `Nat.prime_two.dvd_of_dvd_pow h` | R4 |
| replace `p` by `2 * k` | `obtain ⟨k, rfl⟩ : 2 ∣ p := e` | R5 |
| linear consequence (powers as unknowns) | `linarith` | R6 |
| use a `≠` fact to close `False` | `exact ih m (by omega) k (by omega) (by linarith)` | R7 |
| linear bounds in `ℕ`/`ℤ` | `omega` | R8 |
| `Irrational x` → no fraction equals `x` | `rw [irrational_iff_ne_rational]` | R9 |
| introduce several binders | `intro a b hb h` | R10 |
| move a fact across casts | `exact_mod_cast h` | R11 |
| `√x ^ 2 = x` | `have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)` | R12 |
| rewrite a hypothesis | `rw [h, div_pow] at this` | R13, R14 |
| clear denominators in a hypothesis | `field_simp at this` (needs `hb : (b : ℝ) ≠ 0`) | R15 |
| apply `f` to both sides | `have := congrArg Int.natAbs h` | R16 |
| push `natAbs` through `*`, `^` and close | `simpa [Int.natAbs_mul, Int.natAbs_pow] using this` | R17–R19 |
| `0 < a.natAbs` from `a ≠ 0` | `Int.natAbs_pos.mpr hb0` | R20 |
| see the state | infoview | |
