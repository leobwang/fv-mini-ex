# E091 · tauto and aesop: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `Prop`, the connectives `→ ∧ ∨ ¬ ↔`, `∀`, `intro`, `rw`,
`exact`, anonymous constructors `⟨_, _⟩`, lists and `++`.
**New here:** two Mathlib search tactics, `tauto` (propositional logic) and `aesop` (logic plus `∀` and
Mathlib's simplification lemmas), the option `aesop (add norm L)`, and Mathlib's sets `Set α` with `∈`, `∩`, `⊆`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `A B : Prop` are arbitrary propositions;
  `p q : α → Prop` are predicates on `α`.
- "closes" means the tactic finishes the goal: the After cell is *no goals*. These tactics either close the goal
  or fail; they never leave a partial result for you to continue from.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `¬A` | `A → False` |
| `A ↔ B` | `(A → B) ∧ (B → A)`, as one proposition |
| `∀ (x : α), p x → q x` | for every `x` of type `α`, `p x` implies `q x`. `→` binds weaker than application, so this is `p x → q x` under the `∀` |
| `∀ x ∈ l, P x` | bounded quantifier: `∀ x, x ∈ l → P x`, for a list or a set `l` |
| `x > 0` | notation for `0 < x` |
| `Set α` | a set of elements of `α`; Mathlib defines it as a predicate `α → Prop` |
| `x ∈ s` | membership: `x` lies in the set (or list) `s`. Typed `\in` |
| `s ∩ t`, `s ∪ t` | intersection (elements of both), union (elements of either). Typed `\cap`, `\cup` |
| `s ⊆ t` | subset: `∀ x ∈ s, x ∈ t` (R6). Typed `\subseteq` (`\sub` gives strict `⊂`). Lean does not unfold it by itself |
| `@[simp]` lemma | a lemma Mathlib has tagged for automatic rewriting; `aesop` uses all of them |

---

## Part 1 · `taut_trans`, `taut_demorgan`, `taut_contra`

Statements: three laws of propositional logic over opaque propositions `P Q R : Prop`: chaining implications,
De Morgan for `¬(P ∨ Q)`, and the contrapositive `(P → Q) ↔ (¬Q → ¬P)`. Only connectives occur, so each is one
`tauto`.

**R1 · `tauto`** **closes** the goal. It proves tautologies of classical propositional logic: it introduces
`→`, splits `∧` and `↔` in goal and hypotheses, and tries each side of every `∨`. The letters `A B` are atoms to
it; it never looks inside them. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `A B : Prop ⊢ A ∧ B → B ∧ A` | no goals |

**R2 · `tauto` with `¬` and `↔`** **closes** the goal. It reads `¬A` as `A → False` and proves both directions of
an `↔`. It is *classical*: it may use excluded middle `A ∨ ¬A`, so laws such as `¬(A ∧ B) → ¬A ∨ ¬B` (not provable
without excluded middle) are in reach. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬(A ∧ B) ↔ ¬A ∨ ¬B` | no goals |

---

## Part 2 · `aesop_forall`, `aesop_list`

Statements: from `h : ∀ n, p n ∧ q n` (with `p q : ℕ → Prop`) get `(∀ n, q n) ∧ ∀ n, p n`; and from a positivity
hypothesis on every element of `xs ++ ys` get it for every element of `ys`. Both quantify, so `tauto` fails
(Traps); `aesop` closes each.

**R3 · `aesop`** **closes** the goal. It is a search: it introduces `∀` and `→`, splits `∧` in goal and
hypotheses, instantiates `∀` hypotheses at the variables in scope, and rewrites everything with Mathlib's
`@[simp]` lemmas, backtracking when a branch fails. Placeholders: `{α : Type} (p q : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (x : α), q x` (with `hpq : ∀ (x : α), p x → q x` and `hp : ∀ (x : α), p x`) | no goals |

**R4 · `rw [List.mem_append]`** changes the **goal**. The lemma is `List.mem_append : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`:
an element of an appended list lies in one of the two parts. It is `@[simp]`, so `aesop` uses it by itself; you
never name it. Placeholders: `{α : Type} (a : α) (s t : List α)`.

| Before | After |
|---|---|
| `⊢ a ∈ s ++ t` | `⊢ a ∈ s ∨ a ∈ t` |

**R5 · `aesop` on bounded quantifiers** **closes** the goal. For `∀ x ∈ l₁ ++ l₂, P x` it introduces `x` and the
membership, rewrites the membership with R4, splits the `∨` and uses `h₁` or `h₂` in each case. In the exercise
the same rewrite happens *in the hypothesis* instead. Placeholders:
`{α : Type} (P : α → Prop) (l₁ l₂ : List α)`.

| Before | After |
|---|---|
| `⊢ ∀ x ∈ l₁ ++ l₂, P x` (with `h₁ : ∀ x ∈ l₁, P x` and `h₂ : ∀ x ∈ l₂, P x`) | no goals |

---

## Part 3 · `aesop_subset`

Statement: for sets `A B C : Set α`, `A ⊆ B` implies `A ∩ C ⊆ B ∩ C`. Plain `aesop` fails here: Mathlib keeps
`⊆` folded, and `aesop` gets stuck on a leftover subset goal (Traps). Tell it to unfold `⊆` with R6 (R8); it then
finds the membership argument, using R7 by itself.

**R6 · `rw [Set.subset_def]`** changes the **goal**. The lemma is
`Set.subset_def : (s ⊆ t) = ∀ x ∈ s, x ∈ t`: an equation between propositions, so `rw` can use it. It is *not*
`@[simp]`, which is why `aesop` does not use it unless asked. Placeholders: `{α : Type} (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ s ⊆ t` | `⊢ ∀ x ∈ s, x ∈ t` |

**R7 · `rw [Set.mem_inter_iff]`** changes the **goal**. The lemma is
`Set.mem_inter_iff : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b`. It is `@[simp]`, so `aesop` uses it by itself.
Placeholders: `{α : Type} (x : α) (s t : Set α)`.

| Before | After |
|---|---|
| `⊢ x ∈ s ∩ t` | `⊢ x ∈ s ∧ x ∈ t` |

**R8 · `aesop (add norm L)`** **closes** the goal. `add norm L` adds the equation (or `↔`) `L` to `aesop`'s
normalisation step, the rewriting it does before and between search steps, for this one call. With
`L := Set.subset_def` every `⊆` in the goal and in the hypotheses becomes a bounded `∀` (R6), and R3 finishes.
Placeholders: `{α : Type} (s t u : Set α)`.

| Before | After |
|---|---|
| `hst : s ⊆ t, htu : t ⊆ u ⊢ s ⊆ u` | no goals |

Plain `aesop` on this same goal fails with `Tactic aesop failed, made no progress`.

### Worked combinations (W1–W3, on statements that are not the exercise's)

**W1: `tauto` splits an `∨` into cases.** `A ∨ B → (A → C) → (B → C) → C` (R1):

```lean-goal
⊢ A ∨ B → (A → C) → (B → C) → C
```

**W2: what R8 does, by hand, on `s ∩ t ⊆ t ∩ s`.** R6 turns `⊆` into a `∀`; `intro x hx` introduces the element
and its membership; R7 (`at hx`, then on the goal) turns both `∈ ∩` into `∧`; `exact ⟨hx.2, hx.1⟩` finishes.

```lean-goal
⊢ s ∩ t ⊆ t ∩ s
⊢ ∀ x ∈ s ∩ t, x ∈ t ∩ s
⊢ x ∈ t ∩ s
⊢ x ∈ t ∧ x ∈ s
```

**W3: the same goal in one call**, `aesop (add norm Set.subset_def)` (R8).

---

## Traps

- `tauto` does not look under a `∀` or inside `∈`, `∩`, `⊆`: on `aesop_forall` it fails with `Tactic tauto failed`
  and shows the goal unchanged (it can only split `∀`-free `∧`/`∨`/`↔`/`∃` hypotheses). Use `aesop` once a quantifier appears.
- Plain `aesop` cannot unfold `⊆` (R6 is not `@[simp]`). On subset transitivity (R8) it reports `made no
  progress`; on `aesop_subset` it reports `failed to prove the goal after exhaustive search` and leaves a subset goal
  (`A ∩ C ⊆ B`) it cannot unfold. Add `(add norm Set.subset_def)`.
- `aesop` either closes the goal or fails with an error: there is no partial state to continue from.
- The `BANNED:` line forbids the simplifier tactics by name; `aesop` uses simplification internally, and that is
  allowed.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| tautology with `→ ∧ ∨` over opaque `Prop`s | `tauto` | R1 |
| tautology with `¬`, `↔` (classical) | `tauto` | R2 |
| goal with `∀`, `∧`, `∀` hypotheses | `aesop` | R3 |
| membership in `s ++ t` | `List.mem_append` (aesop uses it) | R4 |
| bounded `∀ x ∈ l, …` over lists | `aesop` | R5 |
| unfold `s ⊆ t` | `rw [Set.subset_def]` | R6 |
| membership in `s ∩ t` | `rw [Set.mem_inter_iff]` (aesop uses it) | R7 |
| let `aesop` rewrite with an extra equation `L` | `aesop (add norm L)` | R8 |
| see the state | infoview | |
