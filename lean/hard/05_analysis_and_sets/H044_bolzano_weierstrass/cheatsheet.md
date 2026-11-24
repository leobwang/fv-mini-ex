# H044 · Bolzano–Weierstrass: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `theorem`, `intro`, `exact`, `apply`, `have`,
`obtain`/`rcases` patterns, `refine`, `constructor`, `induction … with`, `∃`/`∧`/`∨`/`¬`, `Or.inl`/`Or.inr`.
M075 (monotone convergence) is the first milestone; if you did it, you may copy your proof.
**New here:** Mathlib's order library on `ℝ` and `ℕ`: least upper bounds `sSup`, `BddAbove`/`BddBelow`,
`upperBounds`/`lowerBounds`, `Set.range`, `Monotone`/`Antitone`/`StrictMono`, `Set.Finite`/`Set.Infinite`,
`Nat.nth`, iterates `g^[k]`, the tactics `choose`, `linarith`, `omega`, `by_cases`.

**The maths.** A *subsequence* of `a : ℕ → ℝ` is `a ∘ φ` with `φ : ℕ → ℕ` strictly increasing. Proof route:

1. *Monotone convergence.* If `a` is monotone and bounded above, it converges to `S = sSup (range a)`, the
   least upper bound of its values: for `ε > 0`, `S - ε` is not an upper bound, so some `a N > S - ε`;
   for `n ≥ N`, `S - ε < a N ≤ a n ≤ S`.
2. *Antitone case.* If `a` is antitone and bounded below, `-a` is monotone and bounded above; its limit `S`
   gives the limit `-S` of `a`, because `|a n - (-S)| = |(-a n) - S|`.
3. *Peak lemma.* Call `n` a *peak* if `a m ≤ a n` for all `m > n`. If there are infinitely many peaks,
   list them in increasing order (`Nat.nth`); the values at successive peaks never increase (antitone).
   If there are finitely many, all are `≤ N`; every `n > N` is not a peak, so some `m > n` has
   `a n < a m`. Pick such an `m` as a function `g` (`choose`) and iterate from `N + 1`:
   `φ k = g^[k] (N + 1)` is strictly increasing and `a ∘ φ` is monotone.
4. *Bolzano–Weierstrass.* `|a n| ≤ M` gives `-M ≤ a n ≤ M`, so either subsequence is bounded on the
   side that matters.

The guide never uses the exercise's sequence `a`, its peaks or `ConvergesTo`; it uses placeholders and
toy objects (`ForallPos`, the iterate of `g` from `0`, `|x - -y|`).

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement and its placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`), or the whole goal (`P : Prop`). A hypothesis `h` in an
  entry is only there to finish the example.
- `{α : Type}` is any type. A bracket such as `[LT α]` is a requirement on `α` (a *type class*: here, `α`
  has a `<`). `ℕ` and `ℝ` meet every order bracket used here.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `\|x\|` | absolute value of `x : ℝ`; `\|(-a)\|` is `\|-a\|` printed with parentheses |
| `∀ ε > 0, P ε` | `∀ ε, ε > 0 → P ε`; likewise `∀ n ≥ N, P n` is `∀ n, n ≥ N → P n` |
| `n ≥ N`, `ε > 0` | notation for `N ≤ n`, `0 < ε` (lemmas are stated with `≤`, `<`) |
| `∃ x ∈ s, P x` | `∃ x, x ∈ s ∧ P x` |
| `∃ x, ∃ (_ : q), r` | "there is `x` with `q` and `r`": a pattern `⟨x, hq, hr⟩` takes it apart |
| `Set.range f` | the set of values `{x \| ∃ n, f n = x}` of `f : ℕ → α` |
| `{n \| p n}`, `setOf p` | the set of `n` satisfying `p` (two spellings of the same set) |
| `x ∈ {n \| p n}` | means `p x` (`Set.mem_setOf_eq`) |
| `x ∉ s` | `¬ (x ∈ s)`, a function from `x ∈ s` to `False` |
| `s.Nonempty` | `∃ x, x ∈ s` |
| `sSup s` | the least upper bound of `s : Set ℝ` (meaningful when `s` is nonempty and bounded above) |
| `upperBounds s`, `lowerBounds s` | `{c \| ∀ ⦃x⦄, x ∈ s → x ≤ c}`, `{c \| ∀ ⦃x⦄, x ∈ s → c ≤ x}` |
| `BddAbove s`, `BddBelow s` | `(upperBounds s).Nonempty`, `(lowerBounds s).Nonempty`: some bound exists |
| `Monotone f` | `∀ ⦃i j⦄, i ≤ j → f i ≤ f j` |
| `Antitone f` | `∀ ⦃i j⦄, i ≤ j → f j ≤ f i` |
| `StrictMono f` | `∀ ⦃i j⦄, i < j → f i < f j` |
| `⦃i j⦄` | strict-implicit arguments: `hm hij` fills `i j` from `hij : i ≤ j` |
| `s.Finite`, `s.Infinite` | `s` has finitely many elements; `s` does not |
| `a ∘ φ` | composition: `(a ∘ φ) k = a (φ k)` |
| `g^[k] x` | `g` applied `k` times to `x` (`g^[0] x = x`) |
| `Nat.nth p k` | the `k`-th natural number satisfying `p`, counting from `k = 0` |
| `k.succ` | `k + 1` |
| `inst✝ : LT α` | an anonymous type-class hypothesis (here: `α` has `<`) |
| `case inl`, `case inr`, `case pos`, `case neg` | the left / right side of an `∨`; the `p` / `¬p` side of `by_cases` |
| `case zero`, `case succ`, `case refine_1`, `case refine_2` | the base / step goal of `induction`; the first / second `?_` of a `refine` |
| `-a n`, `x - -y` | `-(a n)`; `x - (-y)` (in the antitone case the goal shows `a n - -sSup …`) |
| `(fun n => f n + 1) n` | a function applied to `n`, not yet simplified; `linarith` and `simp` see through it |

---

## Part 1 · `monotone_converges` (milestone)

Statement: a monotone sequence `a` whose range is bounded above converges to `sSup (Set.range a)`.

### ε–N statements and least upper bounds

**R1 · `intro ε hε`** changes the **context**: it adds `ε` and `hε : ε > 0`. It works even when the
`∀ ε > 0` hides behind a definition (here the toy `ForallPos P := ∀ ε > 0, P ε`; in the exercise,
`ConvergesTo`). Placeholders: `(P : ℝ → Prop)`.

| Before | After |
|---|---|
| `⊢ ForallPos P` | `ε : ℝ, hε : ε > 0 ⊢ P ε` |

**R2 · `Set.range_nonempty`** changes the **context** (with `have`): `Set.range_nonempty f : (Set.range f).Nonempty`.
A sequence has at least one value. Placeholders: `{α : Type} (f : ℕ → α)`.

| Before | After |
|---|---|
| `⊢ P` | `hne : (Set.range f).Nonempty ⊢ P` |

**R3 · `sub_lt_self`** changes the **context**: `sub_lt_self a hb : a - b < a` from `hb : 0 < b`.
Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `hb : 0 < b ⊢ P` | `hlt : a - b < a ⊢ P` |

**R4 · `exists_lt_of_lt_csSup`** changes the **context**. Statement: `s.Nonempty → b < sSup s → ∃ x ∈ s, b < x`
("anything below the least upper bound is beaten by an element"). The `cs` means *conditionally complete*:
the lemma holds in `ℝ`, where `sSup` only behaves for nonempty sets. Placeholders: `(s : Set ℝ) (b : ℝ)`.
In the exercise, `hs` is R2 and `hb` is R3 with `a := sSup (Set.range a)`.

| Before | After |
|---|---|
| `hs : s.Nonempty, hb : b < sSup s ⊢ P` | `hx : ∃ a ∈ s, b < a` added, goal `⊢ P` |

**R5 · `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := hx`** changes the **context**. `x ∈ Set.range f` means `∃ y, f y = x`;
the inner pattern `⟨N, rfl⟩` names the index and substitutes `x := f N`. Placeholders:
`{α : Type} [LT α] (f : ℕ → α) (b : α)` and `hx : ∃ x ∈ Set.range f, b < x`. Write it directly as
`obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup … …`.

| Before | After |
|---|---|
| `hx : ∃ x ∈ Set.range f, b < x` and `⊢ P` | `N : ℕ, hN : b < f N ⊢ P` |

**R6 · `refine ⟨N, fun n hn => ?_⟩`** changes the **goal** and the **context**: it fills the witness `N` of
`∃ N, ∀ n ≥ N, …` and introduces the `∀` in one step. Placeholders: `(P : ℕ → Prop) (N : ℕ)`.

| Before | After |
|---|---|
| `⊢ ∃ N, ∀ n ≥ N, P n` | `n : ℕ, hn : n ≥ N ⊢ P n` |

**R7 · `le_csSup hb ⟨n, rfl⟩`** changes the **context**. Statement: `BddAbove s → x ∈ s → x ≤ sSup s`.
`⟨n, rfl⟩` proves `f n ∈ Set.range f`. Placeholders: `(f : ℕ → ℝ) (n : ℕ)`, `hb : BddAbove (Set.range f)`.

| Before | After |
|---|---|
| `⊢ P` | `h1 : f n ≤ sSup (Set.range f) ⊢ P` |

**R8 · `hm hn`** with `hm : Monotone f` changes the **context**: `Monotone f` is a function taking `hn : N ≤ n`
(written `n ≥ N`) to `f N ≤ f n`. Placeholders: `(f : ℕ → ℝ) (N n : ℕ)`.

| Before | After |
|---|---|
| `hn : n ≥ N ⊢ P` | `h2 : f N ≤ f n ⊢ P` |

**R9 · `rw [abs_sub_lt_iff]`** changes the **goal**. Statement: `|a - b| < c ↔ a - b < c ∧ b - a < c`.
Placeholders: `(a b c : ℝ)`.

| Before (goal) | After (goal) |
|---|---|
| `\|a - b\| < c` | `a - b < c ∧ b - a < c` |

```lean-goal
⊢ |a - b| < c
⊢ a - b < c ∧ b - a < c
```

**R10 · `linarith`** **closes** a goal `t < u`, `t ≤ u` or `t = u` that follows from the hypotheses by adding
up linear inequalities (any `ℝ` terms such as `f n` or `sSup s` count as unknowns). `linarith [e]` also uses
the proof term `e`. After R9 use `constructor <;> linarith`.

| Before | After |
|---|---|
| `h1 : x ≤ y, h2 : y - ε < z ⊢ x - z < ε` | closed |

---

## Part 2 · `antitone_converges` (milestone)

Statement: an antitone sequence bounded below converges to some `L`. Apply Part 1 to `fun n => -a n`.

### Negation flips the order

**R11 · `obtain ⟨B, hB⟩ := hb`** changes the **context**: `BddBelow s` is `∃ B, B ∈ lowerBounds s`, and
`hB hx : B ≤ x` for `hx : x ∈ s`. With `s := Set.range a`, `hB ⟨n, rfl⟩ : B ≤ a n`.
Placeholders: `(s : Set ℝ)`.

| Before | After |
|---|---|
| `hb : BddBelow s ⊢ P` | `B : ℝ, hB : B ∈ lowerBounds s ⊢ P` |

**R12 · `neg_le_neg`** changes the **goal** (with `apply`). Statement: `a ≤ b → -b ≤ -a`. The monotonicity of
`fun n => -a n` is `fun i j hij => neg_le_neg (ha hij)`, with `ha hij` used as in R8. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `⊢ -b ≤ -a` | `⊢ a ≤ b` |

**R13 · `refine ⟨c, ?_⟩`** on `BddAbove s` changes the **goal**: `BddAbove s` is `∃ c, c ∈ upperBounds s`.
The term form `⟨c, proof⟩` is what you pass to Part 1's `hb`. Placeholders: `(s : Set ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ BddAbove s` | `⊢ c ∈ upperBounds s` |

**R14 · `rintro _ ⟨n, rfl⟩`** changes the **goal** and the **context**: `c ∈ upperBounds (Set.range f)` is
`∀ ⦃x⦄, x ∈ Set.range f → x ≤ c`; the pattern names the index and substitutes `x := f n`. The same works for
`c ∈ lowerBounds …` (goal `c ≤ f n`). Placeholders: `(f : ℕ → ℝ) (c : ℝ)`.

| Before | After |
|---|---|
| `⊢ c ∈ upperBounds (Set.range f)` | `n : ℕ ⊢ f n ≤ c` |

**R15 · `rw [show e₁ = e₂ by ring]`** changes the **goal**: it proves the identity `e₁ = e₂` with `ring` on the
spot and rewrites with it. Use it to put `a n - -S` into the form `-(-a n - S)`. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ P (x - y)` | `⊢ P (-(y - x))` |

**R16 · `rw [abs_neg]`** changes the **goal**. Statement: `|-a| = |a|`. Placeholders: `(a : ℝ)`.

| Before (goal) | After (goal) |
|---|---|
| `P \|(-a)\|` | `P \|a\|` |

```lean-goal
⊢ P |(-a)|
⊢ P |a|
```

**W4** chains R15 and R16: `rw [show -x - y = -(x - -y) by ring, abs_neg]` closes `|x - -y| = |-x - y|`.

---

## Part 3 · `monotone_subseq` (milestone: the peak lemma)

Statement: every `a : ℕ → ℝ` has a strictly increasing `φ` with `a ∘ φ` monotone or antitone. Split on the
set of peaks `{n | ∀ m > n, a m ≤ a n}`.

### Finite or infinite

**R17 · `rcases Set.finite_or_infinite s with hfin | hinf`** changes the **goal list**: one goal with
`hfin : s.Finite`, one with `hinf : s.Infinite`. Statement: `s.Finite ∨ s.Infinite`.
Placeholders: `{α : Type} (s : Set α)`.

| Before | After |
|---|---|
| `⊢ P` | `hfin : s.Finite ⊢ P`, `hinf : s.Infinite ⊢ P` |

**R18 · `obtain ⟨N, hN⟩ := hfin.bddAbove`** changes the **context**. `Set.Finite.bddAbove : s.Finite → BddAbove s`
(on `ℕ`); `hfin.bddAbove` is dot notation for it. Then `hN hx : x ≤ N` for `hx : x ∈ s`.
Placeholders: `(s : Set ℕ)`.

| Before | After |
|---|---|
| `hfin : s.Finite ⊢ P` | `N : ℕ, hN : N ∈ upperBounds s ⊢ P` |

**R19 · `by_cases hn : p`** changes the **goal list**: one goal with `hn : p`, one with `hn : ¬p`. Used to prove
`∀ n, ∃ m, n < m ∧ (N < n → a n < a m)`: if `N < n`, `n` is no peak; otherwise any `m := n + 1` works.
Placeholders: `(N n : ℕ)`.

| Before | After |
|---|---|
| `⊢ P` | `hn : N < n ⊢ P`, `hn : ¬N < n ⊢ P` |

**R20 · `absurd`** **closes** any goal from a fact and its negation: `absurd : a → ¬a → b`. A proof of `x ∉ s` is
`fun hx => absurd (…) (…)`; the example shows the `intro hx` form. Placeholders: `(s : Set ℕ) (x : ℕ)`.

| Before | After `intro hx` |
|---|---|
| `⊢ x ∉ s` | `hx : x ∈ s ⊢ False` |

then `exact absurd (hb x hx) (by omega)`: `hb x hx : x ≤ 5` against `¬x ≤ 5`.

**R21 · `omega`** **closes** linear arithmetic goals over `ℕ` and `ℤ` (`<`, `≤`, `¬`, `+`, numerals), using the
hypotheses. Not for `ℝ` (use R10 there).

| Before | After |
|---|---|
| `h : N < n ⊢ ¬n ≤ N` | closed |

**R22 · `simp only [Set.mem_setOf_eq, not_forall, not_le] at h`** changes the **context**: it pushes `¬` inside.
`Set.mem_setOf_eq : (x ∈ {y | p y}) = p x`, `not_forall : (¬∀ x, p x) ↔ ∃ x, ¬p x` (also used for the `∀` hidden
in `m > k → …`), `not_le : ¬a ≤ b ↔ b < a`. Placeholders: `(f g : ℕ → ℝ) (n : ℕ)`.

| Before (context) | After (context) |
|---|---|
| `h : n ∉ {k \| ∀ m > k, f m ≤ g k}` | `h : ∃ x, ∃ (_ : x > n), g n < f x` |
| goal `⊢ P` | goal `⊢ P` |

Then `obtain ⟨m, hm, hlt⟩ := h` gives `m : ℕ`, `hm : m > n`, `hlt : g n < f m`.

### Building the subsequence

**R23 · `choose g hg1 hg2 using h`** changes the **context**: from `h : ∀ n, ∃ m, A n m ∧ B n m` it makes a
function `g : ℕ → ℕ` picking one `m` per `n`, with its two properties. Put any condition on `n` *inside* the
`∃` (`N < n → …`), so `g` is defined on all of `ℕ`. Placeholders: `(A B : ℕ → ℕ → Prop)`.

| Before | After |
|---|---|
| `h : ∀ (n : ℕ), ∃ m, A n m ∧ B n m` and `⊢ P` | `g : ℕ → ℕ ⊢ P`, with `hg1 : ∀ (n : ℕ), A n (g n)` and `hg2 : ∀ (n : ℕ), B n (g n)` |

**R24 · `rw [Function.iterate_succ_apply']`** changes the **goal**. Statement: `g^[n.succ] x = g (g^[n] x)`
(apply the last `g` outermost). `g^[0] x` is `x`, which `simp` sees. Placeholders: `(g : ℕ → ℕ) (n x : ℕ)`.

| Before | After |
|---|---|
| `⊢ P (g^[n + 1] x)` | `⊢ P (g (g^[n] x))` |

**R25 · `lt_trans`** changes the **goal** (with `apply lt_trans h1`). Statement: `a < b → b < c → a < c`.
In the induction `∀ k, N < g^[k] (N + 1)`, the step is `lt_trans ih (hg1 _)`. Placeholders: `(a b c : ℕ)`.

| Before | After |
|---|---|
| `h1 : a < b ⊢ a < c` | `⊢ b < c` |

**R26 · `h.le`** (`LT.lt.le : a < b → a ≤ b`) **closes** `a ≤ b` from `h : a < b`. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : a < b ⊢ a ≤ b` | closed |

**R27 · `strictMono_nat_of_lt_succ`** changes the **goal**: to show `f` strictly increasing on `ℕ`, show one
step. Statement: `(∀ n, f n < f (n + 1)) → StrictMono f`. Placeholders: `(f : ℕ → ℕ)`.

| Before | After |
|---|---|
| `⊢ StrictMono f` | `⊢ ∀ (n : ℕ), f n < f (n + 1)` |

**R28 · `monotone_nat_of_le_succ`** changes the **goal**. Statement: `(∀ n, f n ≤ f (n + 1)) → Monotone f`.
Placeholders: `(f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Monotone f` | `⊢ ∀ (n : ℕ), f n ≤ f (n + 1)` |

**R29 · `antitone_nat_of_succ_le`** changes the **goal**. Statement: `(∀ n, f (n + 1) ≤ f n) → Antitone f`.
Placeholders: `(f : ℕ → ℝ)`.

| Before | After |
|---|---|
| `⊢ Antitone f` | `⊢ ∀ (n : ℕ), f (n + 1) ≤ f n` |

**R30 · `simp only [Function.comp]`** changes the **goal**: `(f ∘ φ) k` becomes `f (φ k)`. Needed before R24
can see the `g^[k + 1]` inside `(a ∘ φ) (k + 1)`. Placeholders: `(f : ℕ → ℝ) (φ : ℕ → ℕ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P ((f ∘ φ) k)` | `⊢ P (f (φ k))` |

**R31 · `Nat.nth_strictMono`** **closes** `StrictMono (Nat.nth p)`. Statement:
`(setOf p).Infinite → StrictMono (Nat.nth p)`: listing an infinite set of naturals in order is strictly
increasing. `{n | p n}` is `setOf p`, so `hinf` from R17 fits directly. Placeholders: `(p : ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ StrictMono (Nat.nth p)`, with `hinf : {n \| p n}.Infinite` | closed by `exact Nat.nth_strictMono hinf` |

**R32 · `Nat.nth_mem_of_infinite`** **closes** `p (Nat.nth p k)`. Statement:
`(setOf p).Infinite → ∀ k, p (Nat.nth p k)`: the `k`-th element satisfies `p`. When `p` is "is a peak",
`Nat.nth_mem_of_infinite hinf k : ∀ m > Nat.nth p k, a m ≤ a (Nat.nth p k)`, a function you apply to `m` and a
proof of `m > Nat.nth p k`. Placeholders: `(p : ℕ → Prop) (k : ℕ)`.

| Before | After |
|---|---|
| `k : ℕ ⊢ p (Nat.nth p k)` | closed by `exact Nat.nth_mem_of_infinite hinf k` |

**R33 · `hφ (Nat.lt_succ_self k)`** with `hφ : StrictMono φ` changes the **context**: `Nat.lt_succ_self k : k < k.succ`,
and `hφ` turns it into `φ k < φ k.succ` (`k.succ` is `k + 1`). Placeholders: `(φ : ℕ → ℕ) (k : ℕ)`.

| Before | After |
|---|---|
| `⊢ P` | `hk : φ k < φ k.succ ⊢ P` |

**Worked combinations.** W1: `choose` then `strictMono_nat_of_lt_succ` and R24 build a strictly increasing
`fun k => g^[k] 0` from `hg1 : ∀ n, n < g n`:

```lean-goal
⊢ g^[k] 0 < g^[k + 1] 0
⊢ g^[k] 0 < g (g^[k] 0)
```

W2: `induction k with | zero => simp | succ k ih => rw [Function.iterate_succ_apply']; exact lt_trans ih (hg _)`
proves a bound for every iterate (indent the `| zero`/`| succ` lines further than `induction`). W3: R31, R32, R33
on any infinite `{n | p n}`.

---

## Part 4 · `bolzano_weierstrass`

Statement: if `|a n| ≤ M` for all `n`, some strictly increasing `φ` makes `a ∘ φ` converge. Combine Part 3
with Part 1 or Part 2.

**R34 · `obtain ⟨φ, hφ, h1 | h2⟩ := h`** changes the **context** and the **goal list**: it unpacks
`∃ φ, A φ ∧ (B φ ∨ C φ)` and splits on the `∨`. Placeholders: `(A B C : (ℕ → ℕ) → Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `φ : ℕ → ℕ, hφ : A φ, h1 : B φ ⊢ P`, `φ : ℕ → ℕ, hφ : A φ, h2 : C φ ⊢ P` |

**R35 · `abs_le`** changes the **context** (with `.mp`). Statement: `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`.
`(abs_le.mp h).2 : a ≤ b` is the upper bound, `(abs_le.mp h).1 : -b ≤ a` the lower one. Placeholders: `(a b : ℝ)`.

| Before | After |
|---|---|
| `h : \|a\| ≤ b` and `⊢ P` | `h' : -b ≤ a ∧ a ≤ b ⊢ P` |

**W5** chains R13, R14, R35 and R10: `refine ⟨8, ?_⟩; rintro _ ⟨n, rfl⟩; linarith [(abs_le.mp (hb n)).2]`
bounds the range of `fun n => f n + 1` when `|f n| ≤ 7`:

```lean-goal
⊢ BddAbove (Set.range fun n => f n + 1)
⊢ 8 ∈ upperBounds (Set.range fun n => f n + 1)
⊢ (fun n => f n + 1) n ≤ 8
```

---

## Traps

- **Imports are frozen** (`BANNED: import`). You have ℝ's order and `sSup`, `Nat.nth`, finite sets and the
  tactics `linarith`, `positivity`, `ring`, `omega`. No filters, no compactness, no `Tendsto`: the proof goes
  through peaks and monotone convergence, by hand.
- The library's own monotone-subsequence lemmas are banned (`exists_increasing_or_nonincreasing_subseq`, …).
- `choose` on `∀ n, N < n → ∃ m, …` gives a `g` that needs a proof of `N < n` as an argument (a *dependent*
  function). Put the condition inside: `∀ n, ∃ m, n < m ∧ (N < n → a n < a m)`; for `n ≤ N` pick `m := n + 1`.
- A `have` proved by `induction` belongs before the `refine` that uses it; prove `∀ k, N < g^[k] (N + 1)`
  first, since `hg2` only applies above `N`.
- `induction k with` alternatives `| zero => …` must line up (or be indented further). After the `succ` case
  rewrite with `Function.iterate_succ_apply'`, not `Function.iterate_succ_apply` (that one puts `g` innermost).
- `(a ∘ φ) (k + 1)` hides `φ (k + 1)` from `rw`; unfold `Function.comp` first (R30).
- `sSup` is only meaningful for nonempty, bounded-above sets: `le_csSup` needs `BddAbove`,
  `exists_lt_of_lt_csSup` needs `Nonempty` (R2).
- In the antitone case pass `fun n => -a n`; after `rintro _ ⟨n, rfl⟩` the goal is `(fun n => -a n) n ≤ …`,
  which `linarith` still reads correctly. Likewise `hN n hn : |(fun n => -a n) n - S| < ε` closes the goal
  `|-a n - S| < ε` with `exact`: the two differ only by applying the `fun` (β-reduction), which Lean does itself.
- `omega` is for `ℕ`/`ℤ`, `linarith` for `ℝ` (it also works on `ℕ`, but does not know `n < m ↔ n + 1 ≤ m`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `∀ ε > 0` (also inside `ConvergesTo`) | `intro ε hε` | R1 |
| an element above `sSup s - ε` | `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty a) (sub_lt_self _ hε)` | R2–R5 |
| give `N`, open `∀ n ≥ N` | `refine ⟨N, fun n hn => ?_⟩` | R6 |
| `a n ≤ sSup (range a)` | `le_csSup hb ⟨n, rfl⟩` | R7 |
| use `Monotone`/`StrictMono` | `hm hij`, `hφ hlt` | R8, R33 |
| `\|x - y\| < c` → two inequalities | `rw [abs_sub_lt_iff]; constructor <;> linarith` | R9, R10 |
| bounds from `BddBelow`/`BddAbove` | `obtain ⟨B, hB⟩ := hb`; `hB ⟨n, rfl⟩` | R11 |
| flip with a minus | `neg_le_neg` | R12 |
| prove `BddAbove (Set.range f)` | `⟨c, by rintro _ ⟨n, rfl⟩; …⟩` | R13, R14 |
| reshape, then drop a minus in `\|·\|` | `rw [show e₁ = e₂ by ring, abs_neg]` | R15, R16 |
| finite or infinite peaks | `rcases Set.finite_or_infinite {n \| …} with hfin \| hinf` | R17 |
| an upper bound for a finite set | `obtain ⟨N, hN⟩ := hfin.bddAbove` | R18 |
| case on `N < n` | `by_cases hn : N < n` | R19 |
| contradiction / `ℕ` arithmetic | `absurd h (by omega)`, `omega` | R20, R21 |
| push `¬` through `∉ {k \| ∀ …}` | `simp only [Set.mem_setOf_eq, not_forall, not_le] at h` | R22 |
| a choice function | `choose g hg1 hg2 using h` | R23 |
| `g^[k+1] x` → `g (g^[k] x)` | `rw [Function.iterate_succ_apply']` | R24 |
| chain `<`; weaken `<` | `lt_trans h1 h2`, `h.le` | R25, R26 |
| `StrictMono`/`Monotone`/`Antitone` on `ℕ` from one step | `strictMono_nat_of_lt_succ`, `monotone_nat_of_le_succ`, `antitone_nat_of_succ_le` | R27–R29 |
| unfold `(f ∘ φ) k` | `simp only [Function.comp]` | R30 |
| enumerate an infinite set | `Nat.nth p`, `Nat.nth_strictMono hinf`, `Nat.nth_mem_of_infinite hinf k` | R31, R32 |
| split the milestone's `∨` | `obtain ⟨φ, hφ, hmono \| hanti⟩ := monotone_subseq a` | R34 |
| `\|a n\| ≤ M` → `a n ≤ M` / `-M ≤ a n` | `(abs_le.mp (hb _)).2` / `.1` | R35 |
