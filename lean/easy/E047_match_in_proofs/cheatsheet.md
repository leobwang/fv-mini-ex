# E047 · match in proofs: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `∨` (E006), `∃` (E007), anonymous constructors
`⟨_, _⟩` and term mode (E004), `rfl`, `exact`, `refine`, `simp`, and definitions by pattern matching.
**New here:** `match` as the one way to split: on a `Nat` (`0` / `k + 1`), on an `∃` (`⟨w, hw⟩`), on an `∨`
(`.inl` / `.inr`), with nested patterns, both as a tactic inside `by` and as a term after `:=`; the
leading-dot constructor `.inl e`; computing a Boolean function after the split. No Mathlib.

`cases`, `rcases`, `obtain`, `rintro`, `induction`, `split`, `if`, the recursors (`Or.elim`, `Nat.rec`, …),
`omega` and the `comm` lemmas are banned: every split is a `match`. `let ⟨w, hw⟩ := h` is a one-branch `match`
and is allowed.

## How to read an entry

Each entry is one tactic, one term construction, or one lemma used with `simp`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Bool → Prop` or `P : Prop → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- `A B G : Prop` are arbitrary propositions; `A B : α → Prop` are predicates on an arbitrary type `{α : Type}`.
- "no goals" means the step closed the goal.
- The guide writes each `match` as `refine match … with | pat => ?_` so that the branches appear as goals. In
  the exercise you write the same patterns with a tactic block (inside `by`) or a term (after `:=`) on the
  right of each `=>`; the branch sees the same state.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## `match` in a proof

A proof of `A ∨ B` is either `Or.inl a` or `Or.inr b`; a proof of `∃ x, A x` is a pair `⟨w, hw⟩`; a `Nat` is
`0` or `k + 1`. A `match` has one branch per constructor and binds the constructor's arguments:

| Splitting | Patterns | Each branch gets |
|---|---|---|
| `n : Nat` | `\| 0 => …` `\| k + 1 => …` | `n` replaced by `0` / `k + 1` in the goal and in hypotheses |
| `h : ∃ x, A x` | `\| ⟨w, hw⟩ => …` | `w : α`, `hw : A w` |
| `h : ∃ x, A x ∧ B x` | `\| ⟨w, ha, hb⟩ => …` | `w`, `ha : A w`, `hb : B w` |
| `h : A ∨ B` | `\| .inl ha => …` `\| .inr hb => …` | `ha : A` / `hb : B` |

| Where | Write | Right of `=>` |
|---|---|---|
| inside `by` (tactic) | `match n with` then `\| 0 => tac` lines | a tactic block, e.g. `exact …`, `simp …` |
| after `:=` (term) | `match h with` then `\| ⟨w, hw⟩ => e` lines | a term of the goal's type |

## Reading the goals

| You see | It means |
|---|---|
| `n k : Nat` | in the branch `k + 1`: `n` is still listed but no longer occurs in the goal |
| `hn : 0 ≠ 7` | a hypothesis about `n`, rewritten by the `match` to the branch's pattern |
| `h : ∃ x, A x` | after `match h with`, `h` is still listed next to the new `w`, `hw` |
| `case refine_1`, `case refine_2` | labels of the goals `?_` left by `refine` (first branch, second branch) |
| `isPos n = true` | a `Bool` function compared with the `Bool` value `true`: a `Prop` |
| `false = true` | a false `Prop`; `simp` rewrites it to `False` (R11) |
| `∃ k_1, k + 1 = k_1 + 1` | the bound `k` of `∃ k, n = k + 1`, renamed `k_1` because the branch `k + 1` already uses `k` |
| `n = 0 ∨ ∃ k, n = k + 1` | `n = 0 ∨ (∃ k, n = k + 1)`: the body of `∃ k,` runs to the end |
| `isZero n = true ↔ n = 0` | `(isZero n = true) ↔ (n = 0)`: `↔` binds weaker than `=` |
| `A ∨ B`, `Or A B` | the same; `.inl`, `.inr` are `Or.inl`, `Or.inr` here (R9) |
| `(A ↔ A) ∧ 0 = 0` | `=` binds tighter than `∧`, so no parentheses around `0 = 0` |

---

## Part 1 · `zero_or_succ`

Statement: every natural number is `0` or a successor: `n = 0 ∨ ∃ k, n = k + 1`. Split `n` inside `by`; in the
branch `0` prove the left side, in the branch `k + 1` the right side with witness `k`.

**R1 · `match n with | 0 => … | k + 1 => …`** changes the **goal list**: one goal becomes one per pattern. In
each branch `n` is replaced by the pattern, in the goal and in every hypothesis mentioning `n`. Inside `by` the
tactic form is `match n with | 0 => tac₀ | k + 1 => tac₁`. Placeholders: `(P : Nat → Prop) (n : Nat)
(hn : n ≠ 7)`.

| Before | After |
|---|---|
| `n : Nat, hn : n ≠ 7 ⊢ P n` | `hn : 0 ≠ 7 ⊢ P 0`, `n k : Nat, hn : k + 1 ≠ 7 ⊢ P (k + 1)` |

**R2 · `Or.inl`** changes the **goal**: `Or.inl : A → A ∨ B` picks the left side. `exact Or.inl e` closes the
goal when `e : A`; `refine Or.inl ?_` leaves `A`. Placeholders: `(A B : Prop)`.

| Before | After `refine Or.inl ?_` |
|---|---|
| `⊢ A ∨ B` | `⊢ A` |

**R3 · `Or.inr`** changes the **goal**: `Or.inr : B → A ∨ B` picks the right side. Placeholders: `(A B : Prop)`.

| Before | After `refine Or.inr ?_` |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**R4 · `⟨w, ?_⟩`** changes the **goal**: the anonymous constructor for `∃` supplies the witness `w`; what is
left is the property at `w`. `⟨w, e⟩` closes the goal when `e : A w`; when `A w` is an equation whose sides
compute to the same thing (`k + 1 = k + 1`), `e` is `rfl`. Placeholders: `{α : Type} (A : α → Prop) (w : α)`.

| Before | After `refine ⟨w, ?_⟩` |
|---|---|
| `⊢ ∃ x, A x` | `⊢ A w` |

**W3 (on `isPos`):** the tactic form of R1, each branch closed by R2 / R3 with `rfl`. In the branch `k + 1`,
`isPos (k + 1)` computes to `true`, so `rfl : isPos (k + 1) = true`. Before the split `rfl` fails: `isPos n`
does not compute.

```lean-goal
⊢ isPos n = true ∨ n = 0
```

---

## Part 2 · `exists_swap`

Statement: from `h : ∃ n, p n ∧ q n` get `∃ n, q n ∧ p n`. In term mode, take `h` apart with one nested
pattern and put the pieces back in the other order.

**R5 · `match h with | ⟨w, hw⟩ => …`** changes the **context**: from `h : ∃ x, A x` the branch gains the
witness `w : α` and its proof `hw : A w`. `∃` has one constructor, so there is one branch. Placeholders:
`{α : Type} (A : α → Prop) (G : Prop) (h : ∃ x, A x)`.

| Before | After |
|---|---|
| `⊢ G` (with `h : ∃ x, A x` in the context) | `w : α, hw : A w ⊢ G` |

**R6 · nested pattern `⟨w, ha, hb⟩`** changes the **context**: it abbreviates `⟨w, ⟨ha, hb⟩⟩`, taking apart
the `∃` and the `∧` inside it in one step. Placeholders: `{α : Type} (A B : α → Prop) (G : Prop)
(h : ∃ x, A x ∧ B x)`.

| Before | After |
|---|---|
| `⊢ G` (with `h : ∃ x, A x ∧ B x` in the context) | `w : α, ha : A w, hb : B w ⊢ G` |

**R7 · `⟨w, ?_, ?_⟩`** changes the **goal list**: the anonymous constructor flattens the same way, so
`⟨w, e₁, e₂⟩ : ∃ x, A x ∧ B x` when `e₁ : A w` and `e₂ : B w`. As a term: write the three pieces directly.
Placeholders: `{α : Type} (A B : α → Prop) (w : α)`.

| Before | After `refine ⟨w, ?_, ?_⟩` |
|---|---|
| `⊢ ∃ x, A x ∧ B x` | `⊢ A w`, `⊢ B w` |

---

## Part 3 · `or_swap`

Statement: from `h : P ∨ Q` get `Q ∨ P`. In term mode, two branches, each putting its proof on the other side.

**R8 · `match h with | .inl ha => … | .inr hb => …`** changes the **goal list and the context**: two branches,
the first with `ha : A`, the second with `hb : B`. In term mode the right side of each `=>` is a term of the
goal's type. Placeholders: `(A B G : Prop) (h : A ∨ B)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ G` | `ha : A ⊢ G`, `hb : B ⊢ G` |

**R9 · `.inr e` / `.inl e`** (leading-dot constructor) changes the **goal**. When the expected type is `A ∨ B`,
that is `Or A B`, Lean reads `.inr` as `Or.inr`: the namespace comes from the expected type. It works in
patterns (R8) and in terms. Placeholders: `(A B : Prop)`.

| Before | After `refine .inr ?_` |
|---|---|
| `⊢ A ∨ B` | `⊢ B` |

**W1 (three predicates):** one `match` can mix R6 and R8: `| ⟨w, ha, .inl hb⟩ => … | ⟨w, ha, .inr hc⟩ => …`
takes `h : ∃ x, A x ∧ (B x ∨ C x)` apart into two branches, each answered by a term `⟨w, .inl ⟨ha, hb⟩⟩`
(R7, R9).

---

## Part 4 · `isZero_iff`

Statement: `isZero n = true ↔ n = 0`, where `isZero 0 = true` and `isZero (k + 1) = false`. Split `n` (R1). Then
in each branch `simp [isZero]` unfolds the equation (R10) and evaluates both sides of `↔` (R11, R12) until they
agree (R13).

**R10 · `simp only [f]`** changes the **goal**: it rewrites with the equations of the definition `f` (here
`isPos 0 = false`, `isPos (k + 1) = true`), only where the argument literally has the shape `0` or `_ + 1`.
That is why you split first. Placeholders: `(k : Nat) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (isPos (k + 1))` | `⊢ P true` |

**R11 · `Bool.false_eq_true`** changes the **goal**. The lemma is `(false = true) = False`. Placeholders:
`(P : Prop → Prop)`.

| Before | After `simp only [Bool.false_eq_true]` |
|---|---|
| `⊢ P (false = true)` | `⊢ P False` |

**R12 · `Nat.add_one_ne_zero`** changes the **goal**. The lemma is `n + 1 ≠ 0`; `simp` uses a lemma `a ≠ b` to
rewrite `a = b` to `False`. Placeholders: `(k : Nat) (P : Prop → Prop)`. Plain `simp [isZero]` reaches the
same `False` through other lemmas of its default set (`Nat.add_eq_zero_iff`, …); the step-by-step route
`simp only [isZero, Bool.false_eq_true, Nat.add_one_ne_zero]` (R10–R12) closes the branch `k + 1` too.

| Before | After `simp only [Nat.add_one_ne_zero]` |
|---|---|
| `⊢ P (k + 1 = 0)` | `⊢ P False` |

**R13 · `simp`** **closes** a goal once both sides of each `↔` agree (lemma `iff_self : (a ↔ a) = True`) and
each `=` has equal sides (`eq_self : (a = a) = True`). `False ↔ False` and `true = true` are of this kind.
Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ (A ↔ A) ∧ 0 = 0` | no goals |

`simp [f]` does R10–R13 in one call: you need not name R11–R13, they are `simp` lemmas already.

**W2 (on `isOne`, three patterns):** `isOne 0 = false`, `isOne 1 = true`, `isOne (k + 2) = false`. R1 with three
branches gives

```lean-goal
⊢ isOne 0 = true ↔ 0 = 1
⊢ isOne 1 = true ↔ 1 = 1
⊢ isOne (k + 2) = true ↔ k + 2 = 1
```

and `simp [isOne]` closes each one (it also knows `k + 2 = 1` is `False`).

---

## Traps

- Tactic or term? Inside `by`, the right side of `=>` is a tactic (`exact Or.inl rfl`); after `:=` with no
  `by`, it is a term (`Or.inl rfl`). Writing a tactic where a term is expected (or the reverse) is an error.
- `rfl` proves `0 = 0` and `k + 1 = k + 1`, but not `n = 0` for an unsplit `n`, and `isZero n` does not compute.
  Split first, then `rfl` or `simp [isZero]`.
- `.inl e` needs an expected type that is an `Or`. If Lean does not know the type yet (e.g. in a `have` with no
  type), write `Or.inl e`.
- A `match` must cover every constructor: `| 0 => …` alone is rejected (Lean lists the missing cases).
- Keep the `|` lines of a tactic `match` at least as far right as the `match` keyword.
- Banned: `cases`, `rcases`, `obtain`, `rintro`, `split`, `if`, `by_cases`, `Or.elim`, the recursors and
  `omega`. Use `match`, or `let ⟨w, hw⟩ := h` (a one-branch `match`).

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `n : Nat` | `match n with \| 0 => … \| k + 1 => …` | R1 |
| prove `A ∨ B` from `A` / from `B` | `Or.inl e` / `Or.inr e` | R2, R3 |
| prove `∃ x, A x` | `⟨w, e⟩` (`e : A w`, often `rfl`) | R4 |
| use `h : ∃ x, A x` | `match h with \| ⟨w, hw⟩ => …` | R5 |
| use `h : ∃ x, A x ∧ B x` | `match h with \| ⟨w, ha, hb⟩ => …` | R6 |
| prove `∃ x, A x ∧ B x` | `⟨w, e₁, e₂⟩` | R7 |
| use `h : A ∨ B` | `match h with \| .inl ha => … \| .inr hb => …` | R8 |
| constructor without the namespace | `.inl e`, `.inr e` | R9 |
| evaluate `f 0`, `f (k + 1)` | `simp only [f]`, or `simp [f]` to finish too | R10 |
| `false = true`, `k + 1 = 0` → `False` | `simp` (lemmas `Bool.false_eq_true`, `Nat.add_one_ne_zero`) | R11, R12 |
| close `A ↔ A`, `a = a` | `simp` | R13 |
| see the state | infoview | |
