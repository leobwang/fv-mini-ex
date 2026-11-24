# M046 · Sign analysis is sound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `omega` (E011), induction on `Nat`/lists
(E014, E015), inductive types and pattern-matching definitions (E018) and `<;>`. **New here:** *abstract
interpretation* (evaluate a program over a finite domain of abstract values that each describe a set of
concrete values), proving a finite table correct by `cases … <;> cases … <;> simp_all`, the core `Int`
lemmas for the sign of a product, opening an `if` with `unfold` and `split`, and induction on an expression
type with named alternatives. Core Lean only, no Mathlib.

The guide never uses the exercise's signs. It uses a toy domain `Nn` = `zero | nonneg | any` over `Int`
with concretisation `Nn.den` (`zero` describes `v = 0`, `nonneg` describes `0 ≤ v`, `any` describes
everything), an abstract addition `Nn.add` with overlapping patterns like `Sign.plus`, a literal
abstraction `Nn.ofInt` made of nested `if`s like `Sign.ofInt`, and toy expressions `Tm` = `lit n | add t u`
with value `Tm.ev` and abstract value `Tm.abs`.

**Soundness**, the property proved here: write γ(a) ⊆ ℤ for the set of integers sign `a` describes
(`Sign.gamma a v` is `v ∈ γ(a)`). An abstract operation `op♯` is sound for a concrete `op` when
`x ∈ γ(a)` and `y ∈ γ(b)` imply `op x y ∈ γ(op♯ a b)`. The evaluator is sound when, for every state `s`
whose variables are described by the abstract state `as`, the value of `e` is described by its abstract
value.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `(a b : Int)` are arbitrary integers; `(P : Nn → Prop)` is any statement about an abstract value.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `State` | `Nat → Int`: variable `x` has value `s x`. An `abbrev`, so it unfolds freely |
| `.neg`, `.num n` (in the spec) | leading-dot constructor: `Sign.neg`, `AExp.num n`, the type read off the context |
| `AExp` | arithmetic expressions: numerals `num n`, variables `var x`, `plus a b`, `times a b` |
| `aeval s e` | the concrete value (an `Int`) of `e` in state `s` |
| `aevalSign as e` | the abstract value (a `Sign`) of `e` when variable `x` has sign `as x` |
| `a.gamma x` | `Sign.gamma a x`, "sign `a` describes `x`", printed with dot notation `a.f` for `Sign.f a` |
| `Sign.neg.gamma x` | `Sign.gamma Sign.neg x`; `simp [Sign.gamma]` turns it into `x < 0` |
| `Sign.top.gamma y` | `Sign.gamma Sign.top y`, which is `True`; `simp_all` drops it |
| `(a.plus b).gamma (x + y)` | the abstract sum of `a, b` describes the concrete sum `x + y` |
| `(if n < 0 then Sign.neg else …).gamma n` | `Sign.ofInt n` after `unfold` (R10) |
| `case neg.pos` | the goal for `a = Sign.neg`, `b = Sign.pos` after `cases a <;> cases b` |
| `case isTrue`, `case isFalse` | the two branches of an `if` after `split` (R11); a second `split` inside `isFalse` gives `isFalse.isTrue`, `isFalse.isFalse` |
| `h✝`, `h✝¹`, `n✝`, `x✝`, `a✝ b✝` | inaccessible names: Lean made them, you cannot type them. `h✝¹` is the older of two `h✝`. Name them in a `with` pattern |
| `∀ (x : Nat), (as x).gamma (s x)` | the hypothesis `h`: every variable's sign describes its value |
| `a✝.plus b✝` with `a✝ b✝ : AExp` | `AExp.plus a✝ b✝`, the expression `a✝ + b✝`. Not `Sign.plus`: dot notation picks the function from the type of `a✝` |
| `a_ih✝`, `b_ih✝` | induction hypotheses for the arguments `a`, `b` of `plus`/`times` (R12) |
| `aevalSign as (AExp.num n✝)` | not yet reduced; `exact` unfolds it by itself (R13) |
| `‹c›` | "the hypothesis of type `c`, whatever its name": a term for an inaccessible `h✝ : c` |

---

## Part 1 · `plus_sound`

Statement: if `a` describes `x` and `b` describes `y`, then `a.plus b` describes `x + y`. With four signs
each, these are 16 small facts about integers.

**R1 · `cases a`** changes the **goal list and the context**: for a value `a` of an inductive type whose
constructors take no arguments (an enumeration), one goal per constructor, with `a` replaced by it.
Placeholders: `(P : Nn → Prop) (a : Nn)`.

| Before | After |
|---|---|
| `a : Nn ⊢ P a` | `⊢ P Nn.zero`, `⊢ P Nn.nonneg`, `⊢ P Nn.any` |

**R2 · `cases a <;> cases b`** changes the **goal list**: `cases b` runs on each of the goals of `cases a`,
so every pair of constructors gets its own goal (3 × 3 = 9 in the toy, 4 × 4 = 16 in the exercise). Their
names are `case zero.zero`, `case zero.nonneg`, …. Placeholders: `(P : Nn → Nn → Prop) (a b : Nn)`.

| Before | After |
|---|---|
| `a b : Nn ⊢ P a b` | `⊢ P Nn.zero Nn.zero`, `⊢ P Nn.zero Nn.nonneg`, …, `⊢ P Nn.any Nn.any` |

**R3 · `simp only [f]`** changes the **goal**: a pattern-matching function applied to constructors becomes
the value its table gives. Overlapping patterns are fine: the first matching line wins. In the exercise
`Sign.plus`/`Sign.times` are evaluated this way. Placeholders: `(P : Nn → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Nn.nonneg.add Nn.zero)` | `⊢ P Nn.nonneg` |

**R4 · `simp_all [f, g]`** changes the **context and the goal**: it unfolds `f`, `g` in every hypothesis
and in the goal, then simplifies each with the others. A hypothesis `x = 0` is substituted everywhere; a goal
that becomes `True` (from `Sign.top`) or matches a hypothesis is closed. Placeholders: `(x y : Int)`.

| Before | After |
|---|---|
| `ha : Nn.nonneg.den x, hb : Nn.nonneg.den y ⊢ (Nn.nonneg.add Nn.nonneg).den (x + y)` | `ha : 0 ≤ x, hb : 0 ≤ y ⊢ 0 ≤ x + y` |
| `ha : Nn.zero.den x, hb : Nn.nonneg.den y ⊢ (Nn.zero.add Nn.nonneg).den (x + y)` | no goal: `x` became `0`, the goal became `hb` |

In `plus_sound`, `cases a <;> cases b <;> simp_all [Sign.plus, Sign.gamma]` leaves exactly two of the 16
goals, `case neg.neg` (`ha : x < 0, hb : y < 0 ⊢ x + y < 0`) and `case pos.pos`.

**R5 · `omega`** **closes** a goal of linear arithmetic over `Int` or `Nat`, using the hypotheses: `+`, `-`,
`≤`, `<`, `=`, `∧`, `∨`, `¬`, and multiplication by a numeral. Placeholders: `(x y : Int)`.

| Before | After |
|---|---|
| `hx : 0 ≤ x, hy : 0 ≤ y ⊢ 0 ≤ x + y` | no goal |

---

## Part 2 · `times_sound`

Statement: if `a` describes `x` and `b` describes `y`, then `a.times b` describes `x * y`. The same R2, R4
split works, but four goals survive, and `omega` cannot close them: to `omega`, `x * y` is one opaque
unknown, so it knows nothing about its sign. Close each with one of R6–R9.

The four leftovers of `cases a <;> cases b <;> simp_all [Sign.times, Sign.gamma]`, in order:
`case neg.neg` (`x < 0`, `y < 0`, goal `0 < x * y`), `case neg.pos`, `case pos.neg`, `case pos.pos`.
The hypotheses keep the names `ha`, `hb`, so `exact Lemma ha hb` fits each one.

**R6 · `Int.mul_pos`** **closes** the goal. The lemma is `0 < a → 0 < b → 0 < a * b`. Placeholders:
`(a b : Int)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 0 < b ⊢ 0 < a * b` | no goal |

**R7 · `Int.mul_pos_of_neg_of_neg`** **closes** the goal. The lemma is `a < 0 → b < 0 → 0 < a * b`.
Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `ha : a < 0, hb : b < 0 ⊢ 0 < a * b` | no goal |

**R8 · `Int.mul_neg_of_pos_of_neg`** **closes** the goal. The lemma is `0 < a → b < 0 → a * b < 0`.
Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : b < 0 ⊢ a * b < 0` | no goal |

**R9 · `Int.mul_neg_of_neg_of_pos`** **closes** the goal. The lemma is `a < 0 → 0 < b → a * b < 0`.
Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `ha : a < 0, hb : 0 < b ⊢ a * b < 0` | no goal |

The names read left to right: `mul_neg_of_pos_of_neg` = "a product is **neg**ative **of** a **pos**itive
first factor and a **neg**ative second one". Nested, they give the sign of longer products (W4).

---

## Part 3 · `aevalSign_sound`

Statement: if every variable's abstract sign describes its value (`h : ∀ x, (as x).gamma (s x)`), then
`aevalSign as e` describes `aeval s e`, for every expression `e`.

### Milestone first: numerals

The `num n` case needs `(Sign.ofInt n).gamma n`. Prove it as your own lemma **above** `aevalSign_sound`
(a declaration can only use earlier ones), outside the spec regions:
`theorem ofInt_sound (n : Int) : (Sign.ofInt n).gamma n`.

**R10 · `unfold f`** changes the **goal**: the defined name `f` is replaced by its body, here an `if`.
Placeholders: `(n : Int) (P : Nn → Prop)`.

| Before | After |
|---|---|
| `⊢ P (Nn.ofInt n)` | `⊢ P (if n = 0 then Nn.zero else if 0 ≤ n then Nn.nonneg else Nn.any)` |

**R11 · `split`** changes the **goal list and the context**: the first `if c then t else e` in the goal gives
two goals, `case isTrue` with `h✝ : c` and `t` in place of the `if`, and `case isFalse` with `h✝ : ¬c` and
`e`. A nested `if` stays in the second goal; `split` it again. Placeholders:
`(c : Prop) [Decidable c] (t e : Nn) (P : Nn → Prop)`; `[Decidable c]` says `c` can be tested, which
`n < 0` and `n = 0` on `Int` can.

| Before | After |
|---|---|
| `⊢ P (if c then t else e)` | `h✝ : c ⊢ P t`, `h✝ : ¬c ⊢ P e` |

After `split` in the toy (W2):

```lean-goal
⊢ Nn.zero.den n
⊢ (if 0 ≤ n then Nn.nonneg else Nn.any).den n
```

Each branch is then R4 (`simp_all [Sign.gamma]` reads `h✝`). In the exercise one branch survives R4:
`case isFalse.isFalse` with `h✝¹ : 0 ≤ n, h✝ : ¬n = 0 ⊢ 0 < n` (`simp_all` rewrote `¬n < 0` to `0 ≤ n`).
It is linear, so R5 closes it.

### The induction

**R12 · `induction t`** changes the **goal list and the context**: one goal per constructor, the
constructor's arguments added as inaccessible variables, and an induction hypothesis for each argument of the
same type, named after it. Write `induction e with | num n => … | var x => … | plus a b iha ihb => … | …`
(one `|` alternative per constructor, on its own line, in any order) to give them names. Placeholders: `(P : Tm → Prop) (t : Tm)`.

| Before | After |
|---|---|
| `t : Tm ⊢ P t` | `n✝ : Int ⊢ P (Tm.lit n✝)`, `t✝ u✝ : Tm, t_ih✝ : P t✝, u_ih✝ : P u✝ ⊢ P (t✝.add u✝)` |

In the exercise the `plus` goal reads `(aevalSign as (a✝.plus b✝)).gamma (aeval s (a✝.plus b✝))` with
`a_ih✝ : (aevalSign as a✝).gamma (aeval s a✝)` and `b_ih✝` likewise: exactly the hypotheses `ha`, `hb` of
`plus_sound` with `a := aevalSign as a✝`, `x := aeval s a✝`, ….

**R13 · `exact e` up to unfolding** **closes** the goal: `exact` accepts a proof whose type equals the goal
after unfolding definitions on constructors, so `f (c x y)` and the right side of `f`'s equation for `c` are
the same to it. No `simp` is needed first. Placeholders: `(t u : Tm) (P : Int → Prop)`.

| Before | After |
|---|---|
| `h : P (t.ev + u.ev) ⊢ P (t.add u).ev` | no goal |

So in each alternative one `exact` suffices: the milestone for `num`, `h x` for `var`, and `plus_sound` /
`times_sound` applied to the two IHs (their implicit `{a b x y}` are read off the IHs' types).

### Worked combinations (toy objects)

**W1.** `cases a <;> cases b <;> simp_all [Nn.add, Nn.den] <;> omega` proves toy addition sound (R2, R4, R5).
**W2.** `unfold Nn.ofInt; split; · simp_all [Nn.den]; · split <;> simp_all [Nn.den]` proves toy literals
sound (R10, R11, R4). **W3.** `induction t with | lit n => exact ofInt_ok n | add t u iht ihu => exact add_ok
iht ihu` (R12, R13). **W4.** `Int.mul_pos (Int.mul_pos_of_neg_of_neg hx hy) hz : 0 < x * y * z` (R7 inside R6).

---

## Traps

- `omega` does not know the sign of `x * y` (it is an opaque atom), and neither does `simp_all`. The four
  product goals need R6–R9.
- `cases a <;> cases b <;> simp_all […] ; omega` runs `omega` on the first remaining goal only. Use `<;>`
  before `omega`, or `·` bullets per goal.
- The case-split goals come in constructor order (`neg`, `zero`, `pos`, `top`); after `simp_all` only the
  unsolved ones remain, in that order. Read the `case` tag before choosing R6–R9.
- `unfold Sign.ofInt` before `split`: `split` only sees an `if` that is literally in the goal.
- The numeral lemma must be declared before `aevalSign_sound`, outside the spec regions.
- In `induction e with`, every alternative must close its goal, and a missing constructor is an error.
  Bind the IHs in the pattern (`plus a b iha ihb`); without names they are the inaccessible `a_ih✝`.
- `try?` and `grind` are banned (`try?` prints `grind` one-liners for `plus_sound` and, once the operator
  lemmas exist, for `aevalSign_sound`). Do not leave `exact?` or `apply?` in the file either.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per sign | `cases a` | R1 |
| one goal per pair of signs | `cases a <;> cases b` | R2 |
| evaluate `Sign.plus`/`Sign.times` on constructors | `simp only [Sign.plus]` | R3 |
| unfold `gamma` in hypotheses and goal | `simp_all [Sign.plus, Sign.gamma]` | R4 |
| linear leftover | `omega` | R5 |
| `0 < x * y` from `0 < x`, `0 < y` | `Int.mul_pos ha hb` | R6 |
| `0 < x * y` from `x < 0`, `y < 0` | `Int.mul_pos_of_neg_of_neg ha hb` | R7 |
| `x * y < 0` from `0 < x`, `y < 0` | `Int.mul_neg_of_pos_of_neg ha hb` | R8 |
| `x * y < 0` from `x < 0`, `0 < y` | `Int.mul_neg_of_neg_of_pos ha hb` | R9 |
| open `Sign.ofInt` | `unfold Sign.ofInt` | R10 |
| case on an `if` | `split` | R11 |
| induction on `AExp` | `induction e with \| num n => … \| var x => … \| plus a b iha ihb => … \| times a b iha ihb => …` | R12 |
| close a case by a lemma | `exact lemma iha ihb` | R13 |
| see the state | infoview | |
