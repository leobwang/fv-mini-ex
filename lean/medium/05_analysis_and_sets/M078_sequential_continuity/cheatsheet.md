# M078 · ε-δ continuity ⇔ sequential continuity: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's real numbers `ℝ`, the cast
`ℕ → ℝ` (`↑n`), absolute value `|x|`, binder notation `∀ ε > 0`, `∃ δ > 0`, `∀ n ≥ N`, Archimedes
(`exists_nat_gt`), the division lemmas `div_le_iff₀` / `div_lt_iff₀`, and the tactics `obtain`,
`by_contra`, `push Not`, `choose`, `positivity`, `exact_mod_cast`, `nlinarith`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal". `G : Prop` is an arbitrary goal; in the guide a hypothesis `k : … → G`
  consumes the fact a step added.
- `Q`, `R`, `A`, `B` are arbitrary predicates (`Q : ℝ → Prop`, `R : ℝ → ℝ → Prop`, `A : ℕ → Prop`, …):
  "some property". The one exception is R8, where `B : ℝ → ℝ` is an arbitrary real function.
- Placeholders are written as Lean binders. The order lemmas (`lt_of_lt_of_le`, `not_lt`, `div_le_iff₀`)
  are stated in Mathlib for general ordered types (type-class brackets such as `[Preorder α]`,
  `[LinearOrder α]`, `[GroupWithZero α] [PartialOrder α] [PosMulStrictMono α]`); `ℝ` meets every one of them,
  so the entries use `ℝ` directly.
- A goal or hypothesis containing `|` (absolute value) or `, ` (inside a binder) cannot be checked in a
  table cell; it is written in the text or as `context has …`.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ` | the real numbers (Mathlib's `Real`) |
| `a : ℕ → ℝ`, `a n` | a real sequence and its `n`-th term |
| `↑n` | the natural number `n` cast into `ℝ` (Lean inserts the cast `Nat.cast` by itself) |
| `\|x\|` | absolute value of `x` (Mathlib's `abs x`) |
| `ε > 0`, `n ≥ N` | notation for `0 < ε`, `N ≤ n` |
| `∀ ε > 0, Q ε` | `∀ ε, ε > 0 → Q ε`: `intro ε hε` takes both (R2) |
| `∃ δ > 0, Q δ` | `∃ δ, δ > 0 ∧ Q δ`: take apart with `obtain ⟨δ, hδ, hQ⟩` (R4) |
| `∀ n ≥ N, A n` | `∀ n, n ≥ N → A n`: apply it as `hN n hn` (R17 for `n := N`) |
| `∀ (y : ℝ), …` | the same as `∀ y, …`; Lean prints the binder type |
| `(fun n => f (a n)) n` | the sequence `n ↦ f (a n)` applied to `n`; it *is* `f (a n)` (definitionally), Lean just does not simplify it |
| `ContAt f x` | the exercise's ε-δ continuity of `f` at `x`; `intro` and application see through it (R3) |
| `ConvergesTo a L` | the exercise's `a n → L`; same remark |
| `case mp`, `case mpr` | the `→` and `←` goals after `constructor` on `↔` (R1) |
| `ForallPos Q`, `Unbounded g` | toy definitions in the guide |

---

## Part 1 · `contAt_iff_seq`

Statement: `ContAt f x ↔ ∀ a : ℕ → ℝ, ConvergesTo a x → ConvergesTo (fun n => f (a n)) (f x)`, with
`ContAt f x := ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε` and
`ConvergesTo a L := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε`.

**The plan.** Write $C$ for `ContAt f x` and $S$ for "every sequence $a_n \to x$ has $f(a_n) \to f(x)$".

- **(→) a chase.** Given $ε > 0$: continuity gives $δ > 0$ with $|y - x| < δ \Rightarrow |f y - f x| < ε$;
  convergence of $a$ at tolerance $δ$ gives $N$ with $|a_n - x| < δ$ for $n \ge N$. The same $N$ works for
  $f(a_n)$.
- **(←) by contradiction.** If $C$ fails, there is a bad $ε > 0$: every $δ > 0$ has a $y$ with
  $|y - x| < δ$ but $ε \le |f y - f x|$. Take $δ = 1/(n+1)$ for each $n ∈ ℕ$ and **choose** such a $y$,
  call it $a_n$. Then $|a_n - x| < 1/(n+1) \to 0$, so $a_n \to x$ (for $η > 0$ pick $N > 1/η$ by
  Archimedes), and $S$ gives $N'$ with $|f(a_n) - f x| < ε$ for $n \ge N'$. At $n = N'$ this contradicts
  $ε \le |f(a_{N'}) - f x|$.

### Splitting `↔`, taking ε-statements apart and building them

**R1 · `constructor`** on `A ↔ B` changes the **goal list**: one goal becomes `A → B` (named `mp`) and
`B → A` (named `mpr`). Work on each with `·`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R2 · `intro ε hε`** changes the **goal and the context**. `∀ ε > 0, Q ε` is `∀ ε, ε > 0 → Q ε`, so it takes
two names: the number and the proof that it is positive. Placeholders: `(Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ ε > 0, Q ε` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

**R3 · `intro` sees through a `def`** changes the **goal and the context**. When the goal is a defined name
whose body starts with `∀` (here `ForallPos Q`; in the exercise `ConvergesTo (fun n => f (a n)) (f x)`),
`intro` unfolds it by itself. So in (→), `intro hf a ha ε hε` introduces the hypothesis, the sequence, its
convergence, and then the `ε`, `hε` of the goal `ConvergesTo …`. Placeholders: `(Q : ℝ → Prop)`,
`def ForallPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε`.

| Before | After |
|---|---|
| `⊢ ForallPos Q` | `ε : ℝ, hε : ε > 0 ⊢ Q ε` |

**R4 · `obtain ⟨δ, hδ, hR⟩ := hf ε hε`** changes the **context**. `hf ε hε` applies `hf : ∀ ε > 0, …` to
the number `ε` and the proof `hε`; a defined name such as `ContAt f x` unfolds when applied. The result is
`∃ δ > 0, R ε δ` = `∃ δ, δ > 0 ∧ R ε δ`, and the pattern has three parts: the witness, `δ > 0`, the
property. For `∃ N, …` (no `> 0`) the pattern is `⟨N, hN⟩`. Placeholders: `(R : ℝ → ℝ → Prop)`,
`(ε : ℝ) (hε : ε > 0)`, context has `hf : ∀ ε > 0, ∃ δ > 0, R ε δ`.

| Before | After |
|---|---|
| `hε : ε > 0 ⊢ G` | `δ : ℝ, hδ : δ > 0, hR : R ε δ ⊢ G` |

In the exercise, (→): `hf ε hε` gives `δ` and `∀ (y : ℝ), |y - x| < δ → |f y - f x| < ε`; then `ha δ hδ`
gives `N` and `hN : ∀ n ≥ N, |a n - x| < δ`.

**R5 · `refine ⟨N, fun n hn => ?_⟩`** changes the **goal and the context**: it gives the witness `N` for
`∃ M, …` and introduces the `n` and `hn : n ≥ N` of the `∀ n ≥ M, …` that follows; `?_` is what is left.
If you can already write the body, use `exact ⟨N, fun n hn => proof⟩` in one go. Placeholders:
`(A : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ M, ∀ n ≥ M, A n` | `n : ℕ, hn : n ≥ N ⊢ A n` |

In the exercise the body is `|(fun n => f (a n)) n - f x| < ε`; `h (a n) (hN n hn)` proves it (`exact`
accepts it although the lambda is not simplified, since the two are definitionally equal).

### Proof by contradiction

**R6 · `by_contra hf`** changes the **goal and the context**: assume the negation of the goal and prove
`False`. Placeholders: `(G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hf : ¬G ⊢ False` |

**R7 · `unfold ForallPos at h`** changes the **context**: the defined name in `h` is replaced by its body,
so that the next tactic (R8) can see the `∀`. In the exercise: `unfold ContAt at hf`. Placeholders:
`(Q : ℝ → Prop)`.

| Before | After |
|---|---|
| `h : ¬ForallPos Q ⊢ False` | context has `h : ¬∀ ε > 0, Q ε`; `⊢ False` |

**R8 · `push Not at h`** changes the **context**: it moves `¬` inward. `¬∀ x, P x` becomes `∃ x, ¬P x`,
`¬∃ x, P x` becomes `∀ x, ¬P x`, `¬(A → B)` becomes `A ∧ ¬B`, and `¬(a < b)` becomes `b ≤ a`. Bounded
binders stay bounded: `¬∀ ε > 0, …` becomes `∃ ε > 0, ¬…`. (`push Not` is Mathlib's current spelling of
`push_neg`.) Placeholders: `(A : ℝ → ℝ → Prop) (B : ℝ → ℝ)`.

Before, context has `h : ¬∀ ε > 0, ∃ δ > 0, ∀ (y : ℝ), A δ y → B y < ε`.
After, context has `h : ∃ ε > 0, ∀ δ > 0, ∃ y, A δ y ∧ ε ≤ B y`. The goal is unchanged.

In the exercise, after `obtain ⟨ε, hε, hbad⟩ := hf` (R4):
`hbad : ∀ δ > 0, ∃ y, |y - x| < δ ∧ ε ≤ |f y - f x|`.

### Building the bad sequence

**R9 · `choose a ha1 ha2 using hb`** changes the **context**. From `hb : ∀ n, ∃ y, A n y ∧ B n y` it
produces a *function* `a : ℕ → ℝ` that picks one `y` for each `n`, and one hypothesis per conjunct:
`ha1 : ∀ (n : ℕ), A n (a n)` and `ha2 : ∀ (n : ℕ), B n (a n)` (`hb` is consumed). The argument after `using`
may be any term of that shape; in the exercise it is built on the spot,
`fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)` (W3). Placeholders: `(A B : ℕ → ℝ → Prop)`.

| Before | After |
|---|---|
| context has `hb : ∀ (n : ℕ), ∃ y, A n y ∧ B n y`; `⊢ G` | `a : ℕ → ℝ ⊢ G`, plus `ha1`, `ha2` as above |

In the exercise: `ha1 : ∀ (n : ℕ), |a n - x| < 1 / (↑n + 1)` and `ha2 : ∀ (n : ℕ), ε ≤ |f (a n) - f x|`.

**R10 · `positivity`** **closes** a goal `0 < t` or `t > 0` when `t` is built from pieces it knows are
positive or nonnegative (numerals, casts `↑n ≥ 0`, hypotheses `hη : η > 0`) by `+`, `*`, `/`, … It proves
the `δ > 0` that `hbad` asks for, and the side goal `0 < ↑n + 1` of R14. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `⊢ 1 / (↑n + 1) > 0` | no goals |

### Proving `ConvergesTo a x`: Archimedes and division

`have hconv : ConvergesTo a x := by …` (TACTIC_STATES, "Adding facts"); inside, `intro η hη` (R3).

**R11 · `exists_nat_gt`** changes the **context**. The lemma is `exists_nat_gt (r : ℝ) : ∃ n : ℕ, r < ↑n`:
there is a natural number above any real (Archimedes). Use it as `obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)`.
Placeholders: `(r : ℝ)`.

| Before | After |
|---|---|
| `⊢ G` | `N : ℕ, hN : r < ↑N ⊢ G` |

**R12 · `lt_of_lt_of_le`** changes the **goal**. The lemma is `lt_of_lt_of_le : a < b → b ≤ c → a < c`.
`refine lt_of_lt_of_le hab ?_` uses `hab : a < b` and leaves `b ≤ c`. In the exercise `hab` is `ha1 n`
(`b` is `1 / (↑n + 1)`), and it combines with R5:
`refine ⟨N, fun n hn => lt_of_lt_of_le (ha1 n) ?_⟩`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `hab : a < b ⊢ a < c` | `hab : a < b ⊢ b ≤ c` |

**R13 · `exact_mod_cast hn`** **closes** a goal that is `hn` with casts added: `hn : n ≥ N` in `ℕ` proves
`(↑N : ℝ) ≤ ↑n`. Write it as `have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn`; the type ascription
`(N : ℝ)` is what makes the statement live in `ℝ`. Placeholders: `(N n : ℕ)`.

| Before | After |
|---|---|
| `hn : n ≥ N ⊢ ↑N ≤ ↑n` | no goals |

**R14 · `rw [div_le_iff₀ hc]`** changes the **goal**. The lemma is
`div_le_iff₀ (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c`: multiply out a positive denominator. `rw` with an `↔`
replaces the statement. In the exercise `c` is `↑n + 1`, so write `rw [div_le_iff₀ (by positivity)]` (R10).
Placeholders: `(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `⊢ a / c ≤ b` | `⊢ a ≤ b * c` |

**R15 · `rw [div_lt_iff₀ hc] at h`** changes the **context**: the strict version
`div_lt_iff₀ (hc : 0 < c) : a / c < b ↔ a < b * c`, used on a hypothesis. In the exercise:
`rw [div_lt_iff₀ hη] at hN` turns `hN : 1 / η < ↑N` into `hN : 1 < ↑N * η`. Placeholders:
`(a b c : ℝ) (hc : 0 < c)`.

| Before | After |
|---|---|
| `h : a / c < b ⊢ G` | `h : a < b * c ⊢ G` |

**R16 · `nlinarith`** **closes** a goal that follows from the hypotheses by linear arithmetic *after*
multiplying pairs of hypotheses together. `linarith` treats a product of two unknowns such as `a * c` as an
opaque atom and fails; `nlinarith` adds the products, here `(c - b) * a ≥ 0` from `hbc` and `ha`. In the
exercise it closes `1 ≤ η * (↑n + 1)` from `hN : 1 < ↑N * η`, `hNn : ↑N ≤ ↑n`, `hη : η > 0`.
Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `ha : 0 < a, hb : 1 < b * a, hbc : b ≤ c ⊢ 1 ≤ a * c` | no goals |

### Closing the contradiction

`obtain ⟨N, hN⟩ := h a hconv ε hε` (R4) gives `hN : ∀ n ≥ N, |(fun n => f (a n)) n - f x| < ε`.

**R17 · `le_rfl`** proves `a ≤ a`. Since `N ≥ N` is `N ≤ N`, it is the side condition when you instantiate
`hN : ∀ n ≥ N, A n` at `n := N`: `hN N le_rfl`. Changes the **context** when used in a `have`.
Placeholders: `(A : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| context has `hN : ∀ n ≥ N, A n`; `⊢ G` | `h1 : A N ⊢ G` |

**R18 · `not_lt`** changes the **context** when used in a `have`. The lemma is `not_lt : ¬a < b ↔ b ≤ a`;
`.mpr` is the `←` direction of an `↔` (`.mp` is `→`), so `not_lt.mpr h` turns `h : b ≤ a` into `¬a < b`.
In the exercise `not_lt.mpr (ha2 N) : ¬|f (a N) - f x| < ε`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : b ≤ a ⊢ G` | `h2 : ¬a < b ⊢ G` |

**R19 · `absurd`** **closes** any goal from a fact and its negation: `absurd (ha : A) (hna : ¬A) : G`.
In the exercise `A` is `|f (a N) - f x| < ε`, with `ha` from R17 and `hna` from R18. Placeholders:
`(A G : Prop)`.

| Before | After |
|---|---|
| `ha : A, hna : ¬A ⊢ G` | no goals |

### Worked combinations (W1–W4, on objects that are not the exercise's)

**W1: negating a definition.** With the toy `Unbounded g := ∀ M : ℝ, ∃ n, M < g n`, from `h : ¬Unbounded g`
R7 then R8 give `h : ∃ M, ∀ (n : ℕ), g n ≤ M`, which is the goal:

```lean-goal
⊢ ∃ M, ∀ (n : ℕ), g n ≤ M
```

**W2: the closing pattern.** From `hu : Unbounded g` and `hg : ∀ n, g n ≤ 5`: `obtain ⟨n, hn⟩ := hu 5` (R4)
gives `hn : 5 < g n`, and `absurd hn (not_lt.mpr (hg n))` (R18, R19) closes

```lean-goal
⊢ False
```

**W3: a sequence from "every `δ > 0` has a `y`".** `choose a ha1 ha2 using fun n : ℕ => hb (1 / ((n : ℝ) + 1)) (by positivity)`
(R9, R10) turns `hb : ∀ δ > 0, ∃ y, A δ y ∧ B δ y` into `a : ℕ → ℝ` with
`ha2 : ∀ (n : ℕ), B (1 / (↑n + 1)) (a n)`, which proves

```lean-goal
⊢ ∃ a, ∀ (n : ℕ), B (1 / (↑n + 1)) (a n)
```

**W4: `2 / (n + 1) ≤ η` eventually.** R11 at `2 / η`, R5, R13, R14 with R10, R15, R16. The goals, in order:

```lean-goal
⊢ ∃ N, ∀ n ≥ N, 2 / (↑n + 1) ≤ η
⊢ 2 / (↑n + 1) ≤ η
⊢ 2 ≤ η * (↑n + 1)
```

---

## Traps

- The bans keep you in ε-δ land: no bridging to Mathlib's `Continuous` / `Tendsto` / filters
  (`tendsto_nhds_iff_seq_tendsto` would be the whole problem). Work with the two definitions directly.
- `∀ ε > 0, …` needs **two** arguments: `hf ε hε`, not `hf ε`. `hbad (1 / ((n : ℝ) + 1))` alone is a function
  still waiting for a proof of `1 / (↑n + 1) > 0`: add `(by positivity)` (R10).
- State casts explicitly in a `have`: `have hNn : (N : ℝ) ≤ n`. Plain `N ≤ n` is a statement in `ℕ` (it is
  just `hn`); the real arithmetic of R16 needs the fact as `↑N ≤ ↑n` in `ℝ` (R13).
- `push Not` needs to see the quantifiers: `unfold ContAt at hf` first (R7). After it, the negated `<`
  appears as `ε ≤ …`, not `¬ … < ε`; that is why R18 is needed at the end.
- `choose` must come *after* `push Not` and `obtain ⟨ε, hε, hbad⟩`: it needs a hypothesis of the shape
  `∀ n, ∃ y, … ∧ …` (R9).
- `rw [div_le_iff₀ …]` needs the goal literally of the form `a / c ≤ b`: apply it after R12 has reduced the
  goal to `1 / (↑n + 1) ≤ η`.
- `linarith` fails on `1 ≤ η * (↑n + 1)`: `η * ↑n` is a product of two unknowns. Use `nlinarith` (R16).
- After R4 on `h a hconv ε hε`, `hN` shows `(fun n => f (a n)) n`. `exact` and `absurd` accept it as
  `f (a n)` (definitional equality); `rw` would not, it matches text (run `beta_reduce at hN` first if
  you need to rewrite).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `↔` | `constructor` | R1 |
| open `∀ ε > 0, …` (also behind `ConvergesTo`) | `intro ε hε` | R2, R3 |
| use `∀ ε > 0, ∃ δ > 0, …` at `ε` | `obtain ⟨δ, hδ, h⟩ := hf ε hε` | R4 |
| prove `∃ N, ∀ n ≥ N, …` | `refine ⟨N, fun n hn => ?_⟩` / `exact ⟨N, fun n hn => …⟩` | R5 |
| prove by contradiction | `by_contra hf` | R6 |
| unfold a definition in `hf` | `unfold ContAt at hf` | R7 |
| push `¬` inward | `push Not at hf` | R8 |
| a sequence from `∀ n, ∃ y, … ∧ …` | `choose a ha1 ha2 using …` | R9 |
| `0 < 1 / (↑n + 1)` | `positivity` | R10 |
| a natural number above `r` | `obtain ⟨N, hN⟩ := exists_nat_gt r` | R11 |
| `a < c` from `a < b` | `refine lt_of_lt_of_le hab ?_` | R12 |
| `(↑N : ℝ) ≤ ↑n` from `n ≥ N` | `exact_mod_cast hn` | R13 |
| clear `/ c` in goal / hypothesis | `rw [div_le_iff₀ hc]` / `rw [div_lt_iff₀ hc] at h` | R14, R15 |
| arithmetic with a product of unknowns | `nlinarith` | R16 |
| instantiate `∀ n ≥ N, …` at `N` | `hN N le_rfl` | R17 |
| `¬a < b` from `b ≤ a` | `not_lt.mpr h` | R18 |
| `A` and `¬A` close the goal | `exact absurd ha hna` | R19 |
| see the state | infoview | |
