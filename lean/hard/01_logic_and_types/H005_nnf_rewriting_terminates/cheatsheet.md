# H005 · NNF rewriting terminates: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, `def` by pattern matching, `theorem`,
`intro`, `exact`, `have`, `rw`, `simp`, `cases`, `induction` on `Nat`. **New here:** induction and
case analysis on a user-defined *inductive relation* (`Rw : F → F → Prop`), well-founded relations
(`WellFounded`, `InvImage`, `Subrelation`) from core Lean, `Nat` power lemmas, `omega` with nonlinear
atoms, and `nomatch`. Core Lean only: no Mathlib.

The guide never uses the exercise's `F` and `Rw`. It uses a toy tree type and a toy step relation:

```lean
inductive T where | leaf (n : Nat) | flip (t : T) | join (s t : T)
inductive Step : T → T → Prop
  | flipFlip {t : T} : Step (.flip (.flip t)) t                     -- a rule at the root
  | flipC {t t' : T} : Step t t' → Step (.flip t) (.flip t')        -- congruence: step inside
  | joinL {s s' t : T} : Step s s' → Step (.join s t) (.join s' t)
  | joinR {s t t' : T} : Step t t' → Step (.join s t) (.join s t')
def size : T → Nat | .leaf _ => 1 | .flip t => size t + 1 | .join s t => size s + size t + 1
def IsLeaf : T → Prop | .leaf _ => True | _ => False
```

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`/`apply`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever
  it sits in a larger goal.
- Placeholders are written as Lean binders: `{α : Type}` is any type; `(n m k : Nat)` are numbers;
  `(A B : Prop)` are propositions; `(q r : α → α → Prop)` are binary relations on `α`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `a.neg`, `a.neg.neg`, `a.and b` | `F.neg a`, `F.neg (F.neg a)`, `F.and a b`: Lean prints a constructor applied to its first argument with a dot (*field notation*) |
| `F.atom n`, `(F.atom n).neg` | `.atom n` and `.neg (.atom n)`; `.c` in source means "constructor `c` of the expected type" |
| `a✝`, `a✝¹`, `t'✝`, `a_ih✝` | names Lean invented (after `induction`/`cases` without names); you cannot type them. `a✝¹` is an older `a✝` shadowed by a newer one. Name them with `with` or `case` (R2) |
| `case negNeg`, `case neg.atom`, `case atom.mp` | the goal belongs to constructor `negNeg`; `neg.atom` = the `atom` case inside the `neg` case; `.mp` / `.mpr` = the → / ← half after splitting an `↔` (R26); `.ha`, `.h` = the goal for that named argument after `apply` (R20) |
| `b_1` | a bound variable renamed because `b` is already in the context (the `and`/`or` cases of `normal_iff_nnf`) |
| `!x`, `x && y`, `x \|\| y` | `Bool` negation, and, or (functions on `Bool`, not the `Prop` connectives `¬ ∧ ∨`) |
| `¬A` | `A → False`: prove it with `intro`, use it by applying it (R30) |
| `∀ (b : F), ¬Rw a b` | "no step out of `a`": `a` is a *normal form* |
| `WellFounded r` | `r : α → α → Prop` has no infinite descending chain `… r a₂ a₁`, `r a₁ a₀` (every element is *accessible*) |
| `fun b a => Rw a b` | the converse of `Rw`: it relates `b` to `a` when `a` steps to `b`. Well-founded = no infinite chain `a₀ → a₁ → a₂ → …` of steps |
| `InvImage r f x y` | `r (f x) (f y)`: the relation `r` pulled back along `f : α → β` (R22) |
| `Subrelation q r` | `∀ {x y}, q x y → r x y`: `q ⊆ r` (R23, R24) |
| `WellFoundedRelation.rel` | how Lean prints the relation of `Nat.lt_wfRel` if you do not state it: it is `<` on `Nat` |
| `2 ^ x` | `Nat` power; `omega` sees it as an unknown number (R15) |

---

## Part 1 · `rw_sound`

Statement: `Rw a b → eval v b = eval v a` for every assignment `v : Nat → Bool`: a step preserves the truth
value. Proof by induction on the derivation of the step `h`.

**R1 · `induction h`** (with `h : Step a b`) changes the **goal list**: one goal per constructor of `Step`.
In each, `a` and `b` are replaced by that constructor's left and right side. A constructor with a premise
`Step x y` (a congruence rule) also gets the induction hypothesis `a_ih✝ : P x y`. Placeholders:
`(P : T → T → Prop) (a b : T) (h : Step a b)`. Inducting on `h`, not on a formula, is what gives you one goal
per rule.

| Before | After |
|---|---|
| `h : Step a b ⊢ P a b` | `t✝ : T ⊢ P t✝.flip.flip t✝`, `t✝ t'✝ : T, a✝ : Step t✝ t'✝, a_ih✝ : P t✝ t'✝ ⊢ P t✝.flip t'✝.flip`, `s✝ s'✝ t✝ : T, a_ih✝ : P s✝ s'✝ ⊢ P (s✝.join t✝) (s'✝.join t✝)`, `s✝ t✝ t'✝ : T, a_ih✝ : P t✝ t'✝ ⊢ P (s✝.join t✝) (s✝.join t'✝)` |

**R2 · `case c x y => tac`** changes the **goal list**: it focuses the goal of constructor `c`, gives its `✝`
variables names (in order, implicit ones included: `case flipC t t' h ih`), and `tac` must close it.
Placeholders: a constructor name `c`, fresh names `x y …`.
The block form `induction h with | c₁ => tac₁ | c₂ h ih => tac₂` does the same for all goals at once; there,
`c₂ h ih` names only the explicit premise and its hypothesis (not the implicit `{t t'}`), and
`| c₂ _ ih | c₃ _ ih => tac` runs one `tac` on several goals (W1, and the five congruence cases of `Rw`).

| Before | After `case flipFlip t => …` |
|---|---|
| `t✝ : T ⊢ P t✝.flip.flip t✝`, `t✝ t'✝ : T, a✝ : Step t✝ t'✝ ⊢ P t✝.flip t'✝.flip`, … | `t✝ t'✝ : T, a✝ : Step t✝ t'✝ ⊢ P t✝.flip t'✝.flip`, … |

**R3 · `simp only [size]`** changes the **goal**: a function defined by pattern matching, applied to a
constructor, is replaced by the right-hand side of that equation. `simp [eval]` does this and then
simplifies. Placeholders: `(s t : T)`, `size` as above.

| Before | After |
|---|---|
| `⊢ P (size (s.join t))` | `⊢ P (size s + size t + 1)` |

**R4 · `Bool.not_not`** changes the **goal**. Statement: `(!!b) = b`. `simp` applies it by itself.
Placeholders: `(b : Bool)`.

| Before | After |
|---|---|
| `⊢ P !!b` | `⊢ P b` |

**R5 · `Bool.not_and`** changes the **goal**. Statement: `(!(x && y)) = (!x || !y)` (De Morgan on `Bool`).
Give it to `simp`: `simp [eval, Bool.not_and]`. Placeholders: `(x y : Bool)`.

| Before | After |
|---|---|
| `⊢ P !(x && y)` | second line below (`\|` cannot sit in a table's code span) |

```lean-goal
⊢ P !(x && y)
⊢ P (!x || !y)
```

**R6 · `Bool.not_or`** changes the **goal**. Statement: `(!(x || y)) = (!x && !y)`. Placeholders:
`(x y : Bool)`.

| Before | After |
|---|---|
| first line below | `⊢ P (!x && !y)` |

```lean-goal
⊢ P !(x || y)
⊢ P (!x && !y)
```

**R7 · `simp [ih]`** with a hypothesis `ih : f x = f y` changes the **goal**: `simp` uses `ih` as a rewrite
rule, left to right. In a congruence case the IH says the child's value is unchanged; with `eval` unfolded,
that is exactly what is left. Placeholders: `(f : T → Bool) (x y : T)`.

| Before | After |
|---|---|
| `ih : f x = f y ⊢ P (f x)` | `ih : f x = f y ⊢ P (f y)` |

---

## Part 2 · `weight` (milestone)

A function `F → Nat` that **every** step lowers. The obvious one, size, fails: De Morgan turns
`¬(a ∧ b)` (size `|a| + |b| + 2`) into `¬a ∨ ¬b` (size `|a| + |b| + 3`). Make `neg` *multiply* weight so that
pushing it inward pays (H2, H3).

**R8 · a `def` by pattern matching** (structural recursion: each recursive call is on a direct child, so Lean
accepts it). `rfl` **closes** an equation between concrete values by computing. Use it to test your weight on
small formulas before proving anything.

| Before | After |
|---|---|
| `⊢ size (T.leaf 0).flip.flip = 3` | closed |

---

## Part 3 · `demorgan_bound` (milestone)

Statement: `1 ≤ x → 1 ≤ y → 2 ^ x + 2 ^ y + 1 < 2 ^ (x + y + 1)`. This is the inequality De Morgan needs.

**R9 · `Nat.pow_le_pow_right`** changes the **context** (used with `have`). Statement:
`n > 0 → i ≤ j → n ^ i ≤ n ^ j` with `{n i j : Nat}` implicit. `(n := 2)` sets the implicit `n` by name;
`(by omega)` proves `2 > 0`. Placeholders: `(x : Nat) (hx : 1 ≤ x)`.

| Before | After |
|---|---|
| `hx : 1 ≤ x ⊢ P` | `e : 2 ^ 1 ≤ 2 ^ x ⊢ P` |

**R10 · `simpa using e`** **closes** the goal: it simplifies both the type of `e` and the goal (`2 ^ 1` → `2`)
and then closes the goal with `e`. Placeholders: `(e : 2 ^ 1 ≤ 2 ^ x)`.

| Before | After |
|---|---|
| `e : 2 ^ 1 ≤ 2 ^ x ⊢ 2 ≤ 2 ^ x` | closed |

**R11 · `Nat.pow_succ`** changes the **goal**. Statement: `b ^ (m + 1) = b ^ m * b`. Placeholders: `(b m : Nat)`.

| Before | After |
|---|---|
| `⊢ P (b ^ (m + 1))` | `⊢ P (b ^ m * b)` |

**R12 · `Nat.pow_add`** changes the **goal**. Statement: `b ^ (m + n) = b ^ m * b ^ n`. Placeholders:
`(b m n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (b ^ (m + n))` | `⊢ P (b ^ m * b ^ n)` |

**R13 · `Nat.mul_le_mul_right k`** changes the **context** (with `have`). Statement:
`n ≤ m → n * k ≤ m * k` (the factor `k` on the right). Placeholders: `(n m k : Nat) (hnm : n ≤ m)`.

| Before | After |
|---|---|
| `hnm : n ≤ m ⊢ P` | `h1 : n * k ≤ m * k ⊢ P` |

**R14 · `Nat.mul_le_mul_left k`** changes the **context**. Statement: `n ≤ m → k * n ≤ k * m` (factor on the
left). Placeholders: as R13.

| Before | After |
|---|---|
| `hnm : n ≤ m ⊢ P` | `h2 : k * n ≤ k * m ⊢ P` |

**R15 · `omega`** **closes** a goal of linear arithmetic over `Nat`/`Int` (`+`, `-`, `*` by a numeral, `<`,
`≤`, `=`) using the hypotheses. A product of two variables (`p * q`, `2 ^ x * 2 ^ y`) or a power `2 ^ x` is
treated as one opaque number, an *atom*: `omega` knows nothing about it except what the context says. So
first `have` every fact that links the atoms (R13, R14), then call `omega`. Placeholders: `(p q : Nat)`.

| Before | After |
|---|---|
| `hq : 1 ≤ q, hpq : p ≤ p * q ⊢ p < p * q + q` | closed |

---

## Part 4 · `weight_pos` (milestone)

Statement: `1 ≤ weight a`. No induction needed: every clause of a sensible weight is visibly ≥ 1.

**R16 · `cases t`** (with `t : T`) changes the **goal list** and the **context**: `t` leaves the context and
there is one goal per constructor, with no induction hypothesis. Placeholders: `(P : T → Prop) (t : T)`.
Follow it with `<;> simp only [weight]` to unfold in every goal (R3).

| Before | After |
|---|---|
| `t : T ⊢ P t` | `n✝ : Nat ⊢ P (T.leaf n✝)`, `t✝ : T ⊢ P t✝.flip`, `s✝ t✝ : T ⊢ P (s✝.join t✝)` |

**R17 · `Nat.one_le_two_pow`** **closes** `1 ≤ 2 ^ n` (`{n : Nat}` implicit): `exact Nat.one_le_two_pow`.

| Before | After |
|---|---|
| `⊢ 1 ≤ 2 ^ n` | closed |

---

## Part 5 · `weight_decreases` (milestone)

Statement: `Rw a b → weight b < weight a`. Induction on the step (R1, R2), one argument per rule.

**R18 · `Nat.lt_two_pow_self`** **closes** `n < 2 ^ n` (`{n : Nat}` implicit). `exact` sees through the
definition of `weight`, so you may use it without unfolding first.

| Before | After |
|---|---|
| `⊢ n < 2 ^ n` | closed |

**R19 · `apply Nat.lt_trans h`** changes the **goal**. Statement: `n < m → m < k → n < k`. With the first
inequality given, the goal becomes the second. `exact Nat.lt_trans h₁ h₂` gives both at once. Placeholders:
`(n m k : Nat) (hnm : n < m)`.

| Before | After |
|---|---|
| `hnm : n < m ⊢ n < k` | `hnm : n < m ⊢ m < k` |

**R20 · `apply Nat.pow_lt_pow_right`** changes the **goal list**. Statement: `1 < a → m < n → a ^ m < a ^ n`
(`{a m n : Nat}` implicit). Two goals: the base condition (`by omega` for `1 < 2`) and the exponent
inequality (the IH under `neg`). Placeholders: `(a m n : Nat)`.

| Before | After |
|---|---|
| `⊢ a ^ m < a ^ n` | `⊢ 1 < a`, `⊢ m < n` |

---

## Part 6 · `rw_terminates`

Statement: `WellFounded (fun b a => Rw a b)`: no infinite chain of steps. Strategy: `<` on `Nat` is
well-founded (R21); pull it back along `weight` (R22); the converse step relation sits inside that pullback
by `weight_decreases` (R23, R24).

**R21 · `Nat.lt_wfRel.wf`** changes the **context** (with `have`). `Nat.lt_wfRel` is the standard
well-founded relation on `Nat` (a `WellFoundedRelation Nat`); its field `.wf` proves its relation, which is
`<`, well-founded. Placeholders: none.

| Before | After |
|---|---|
| `⊢ P` | `hlt : WellFounded fun a b => a < b ⊢ P` |

**R22 · `InvImage.wf f hr`** changes the **context**. Statement:
`WellFounded r → WellFounded (InvImage r f)` for `f : α → β`, `r : β → β → Prop`. Because `InvImage r f x y`
unfolds to `r (f x) (f y)`, you may state the result as `WellFounded (fun x y => f x < f y)`. Placeholders:
`{α : Type} (f : α → Nat)`.

| Before | After |
|---|---|
| `⊢ P` | `hw : WellFounded fun x y => f x < f y ⊢ P` |

**R23 · `refine Subrelation.wf ?_ hr`** changes the **goal**. Statement:
`Subrelation q r → WellFounded r → WellFounded q`: a relation contained in a well-founded one is
well-founded. Placeholders: `{α : Type} (q r : α → α → Prop) (hr : WellFounded r)`.

| Before | After |
|---|---|
| `hr : WellFounded r ⊢ WellFounded q` | `hr : WellFounded r ⊢ Subrelation q r` |

**R24 · `intro x y hq`** on `Subrelation q r` changes the **context** and the **goal**: `Subrelation q r`
unfolds to `∀ {x y}, q x y → r x y`. In term mode, write `fun hq => …`: Lean inserts the implicit `x y`.
For the exercise, `q x y` is `Rw y x` (the converse), so `hq` is a step from `y` to `x`. Placeholders:
`{α : Type} (q : α → α → Prop) (f : α → Nat)`.

| Before | After |
|---|---|
| `⊢ Subrelation q fun x y => f x < f y` | `x y : α, hq : q x y ⊢ f x < f y` |

---

## Part 7 · `normal_iff_nnf`

Statement: `(∀ b, ¬ Rw a b) ↔ IsNNF a`: `a` has no step out of it exactly when it is in negation normal form.
Induction on the formula `a`; in the `neg` case, a case split on what is under the `neg`.

**R25 · `induction t`** (with `t : T`) changes the **goal list**: one goal per constructor, with an induction
hypothesis for each child of type `T` (none for `leaf`). In the exercise each IH is itself an `↔`.
Placeholders: `(P : T → Prop) (t : T)`.

| Before | After |
|---|---|
| `t : T ⊢ P t` | `n✝ : Nat ⊢ P (T.leaf n✝)`, `t✝ : T, t_ih✝ : P t✝ ⊢ P t✝.flip`, `s✝ t✝ : T, s_ih✝ : P s✝, t_ih✝ : P t✝ ⊢ P (s✝.join t✝)` |

**R26 · `constructor`** on `A ↔ B` changes the **goal list**: two implications, `mp` (→) and `mpr` (←). The
term form is `⟨fun a => …, fun b => …⟩`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R27 · `trivial`** **closes** `True`, and also a predicate whose definition reduces to `True` on the given
constructor (`IsNNF (F.atom n)` is `True` by the first equation). Term form: `trivial` too. It does not
introduce: on `A → IsNNF (F.atom n)` write `intro _` first.

| Before | After |
|---|---|
| `⊢ IsLeaf (T.leaf n)` | closed |

**R28 · `nomatch h`** **closes** any goal when no constructor can have produced `h`: for
`h : Step (T.leaf n) b`, no constructor of `Step` has a leaf on its left. It also closes the goal when `h`'s
type reduces to `False` by a definition (`IsLeaf t.flip`, `IsNNF a.neg.neg`). Term form: `fun h => nomatch h`.

| Before | After |
|---|---|
| `h : Step (T.leaf n) b ⊢ G` | closed |
| `h : IsLeaf t.flip ⊢ G` | closed |

**R29 · `cases h`** (with `h : Step x b`, `x` built from constructors) changes the **goal list**: one goal per
constructor of `Step` whose left side can equal `x`; the others are discarded automatically, and `b` is
replaced by that constructor's right side. Here only the congruence rule `flipC` fits `(T.leaf n).flip`,
and its premise is a step out of a leaf, which R28 kills. Placeholders: `(n : Nat) (b : T)`.

| Before | After |
|---|---|
| `h : Step (T.leaf n).flip b ⊢ G` | `t'✝ : T, a✝ : Step (T.leaf n) t'✝ ⊢ G` |

**R30 · `intro b hb`** on `∀ b, ¬ Q b` changes the **context**: `¬ Q b` is `Q b → False`, so the second
`intro` takes the proof of `Q b`, and the goal is `False`. Placeholders: `(Q : T → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (b : T), ¬Q b` | `b : T, hb : Q b ⊢ False` |

**R31 · `absurd a hn`** with a constructor `.c` **closes** any goal. Statement: `absurd : A → ¬A → B`. `.c`
is the constructor `c` of the expected type, here `Step.flipFlip : Step t.flip.flip t`. Use it when a step
obviously exists but the hypothesis says no step exists. Placeholders: `(t : T) (hn : ¬Step t.flip.flip t)`.

| Before | After |
|---|---|
| `hn : ¬Step t.flip.flip t ⊢ G` | closed |

**R32 · `apply h.mp`** (or `h.mpr`) with `h : A ↔ B` changes the **goal**: `h.mp : A → B`, `h.mpr : B → A`.
In the `and`/`or` cases, `iha.mp` turns "no step out of `a`" into `IsNNF a`, and `iha.mpr` goes back.
Placeholders: `(A B : Prop) (h : A ↔ B)`.

| Before | After |
|---|---|
| `h : A ↔ B ⊢ B` | `h : A ↔ B ⊢ A` |

**R33 · `intro ⟨ha, hb⟩ c hc`** changes the **context**: it introduces `A ∧ B` and splits it on the spot,
then introduces the remaining binders. Placeholders: `(A B : Prop) (Q G : T → Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B → ∀ (c : T), Q c → G c` | `ha : A, hb : B, c : T, hc : Q c ⊢ G c` |

### Worked combinations (W1–W4, on the toy objects)

**W1** (R1, R2, R3, R15): every `Step` lowers `size`, by `induction h with` and one shared alternative
`| flipC _ ih | joinL _ ih | joinR _ ih => simp only [size]; omega` for the three congruence rules.

**W2** (R21–R24 in term mode): from `hd : ∀ {a b}, Step a b → size b < size a`,
`WellFounded (fun b a => Step a b)` is one term: `Subrelation.wf` applied to `fun h => hd h` and to the
`InvImage.wf` fact.

**W3** (R30, R29, R28, R31): a `flip` of a leaf has no step; a double `flip` has one.

```lean-goal
⊢ ∀ (b : T), ¬Step (T.leaf n).flip b
⊢ False
⊢ ¬∀ (b : T), ¬Step t.flip.flip b
```

**W4** (R13, R14, R15): `3 ^ x + 3 ^ y < 3 ^ x * 3 ^ y` from `3 ≤ 3 ^ x`, `3 ≤ 3 ^ y`. Plain `omega` fails: it
sees three unrelated atoms `3 ^ x`, `3 ^ y`, `3 ^ x * 3 ^ y`. After the two product bounds it succeeds:

```lean-goal
⊢ 3 ^ x + 3 ^ y < 3 ^ x * 3 ^ y
```

---

## Traps

- `fun b a => Rw a b` is the **converse** relation. `WellFounded` of it means no infinite chain
  `a₀ → a₁ → …` of steps. In `Subrelation q r`, `q x y` is then `Rw y x`, so you must show
  `weight x < weight y` from a step `y → x` — exactly `weight_decreases` (R24).
- Size does not decrease under De Morgan (Part 2). Test a candidate weight with `rfl`/`decide` on
  `¬(p ∧ q)` vs `¬p ∨ ¬q` before proving lemmas about it.
- `omega` treats `2 ^ x`, `2 ^ y` and `2 ^ x * 2 ^ y` as unrelated unknowns. State the links with `have`
  (R9–R14) first, then call it.
- `induction h with` alternatives name only the explicit premise and its IH (`| neg h ih`); `case neg a a' h ih`
  also names the implicit `{a a'}`. Writing `| neg a a' h ih` fails with "Too many variable names provided".
- After R26 on an `↔`, each goal is an implication. `trivial` and `nomatch` do not introduce its premise:
  `intro _` (or `intro _ b hb`) first.
- After `induction a` in `normal_iff_nnf`, the IH of the `neg` case is about the inner formula, not the cases
  you split it into: you will usually not need it (name it `_`).
- `cases h` with `h : Rw (F.atom n) b` leaves no goals, the same as `nomatch h`; `nomatch` also works in term
  mode (`fun h => nomatch h`), where `cases` is unavailable.
- `Rw` steps anywhere inside a formula: in the `and`/`or` cases of `normal_iff_nnf`, a step out of `a.and b`
  is `andL` or `andR` of a step out of a child, so lift a child's step with `.andL`/`.andR` (R29, R31).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per rule of a step relation | `induction h with \| c₁ => … \| c₂ _ ih => …` | R1, R2 |
| name `✝` variables of one goal | `case c x y ih => …` | R2 |
| unfold a recursive `def` on a constructor | `simp only [f]`, `simp [f]` | R3 |
| `!!b`, `!(x && y)`, `!(x \|\| y)` | `simp [Bool.not_and, Bool.not_or]` | R4–R6 |
| use an equation hypothesis | `simp [eval, ih]` | R7 |
| evaluate on a concrete term | `rfl` / `decide` | R8 |
| `1 ≤ x → 2 ≤ 2 ^ x` | `have := Nat.pow_le_pow_right (n := 2) (by omega) hx` then `simpa using this` | R9, R10 |
| `2 ^ (x + y + 1)` → product | `rw [Nat.pow_succ, Nat.pow_add]` | R11, R12 |
| multiply an inequality | `Nat.mul_le_mul_right k h`, `Nat.mul_le_mul_left k h` | R13, R14 |
| linear arithmetic with atoms | `have` the links, then `omega` | R15 |
| one goal per constructor of a value | `cases a` / `induction a` | R16, R25 |
| `1 ≤ 2 ^ n`, `n < 2 ^ n` | `Nat.one_le_two_pow`, `Nat.lt_two_pow_self` | R17, R18 |
| chain `<` | `Nat.lt_trans h₁ h₂` | R19 |
| `m < n → 2 ^ m < 2 ^ n` | `Nat.pow_lt_pow_right (by omega) h` | R20 |
| `<` on `Nat` well-founded | `Nat.lt_wfRel.wf` | R21 |
| pull back along `f` | `InvImage.wf f hr` | R22 |
| well-founded by inclusion | `Subrelation.wf (fun h => …) hr` | R23, R24 |
| split `↔` | `constructor` / `⟨…, …⟩` | R26 |
| goal `True` (after unfolding) | `trivial` | R27 |
| impossible hypothesis | `nomatch h` | R28 |
| steps out of a concrete formula | `cases h` | R29 |
| prove `∀ b, ¬ Q b` | `intro b hb` | R30 |
| a step exists, but `h` says none | `absurd .c (h _)` | R31 |
| use an `↔` | `h.mp`, `h.mpr` | R32 |
| destructure while introducing | `intro ⟨ha, hb⟩ c hc` | R33 |
| see the state | infoview | |
