# Tactic states: what each tactic does to the goal

Shared by every Lean problem's guide. Each row shows the proof state before and after one tactic.
Each problem folder's `cheatsheet.md` covers the moves specific to that problem and links here for
the generic ones.

Notation: `Γ ⊢ G` is context `Γ` and goal `G`. `∅` means no goal is left. `G₁ | G₂` means two
goals, worked on in order.

## Structure: splitting and combining goals

| Tactic | Before | After | Note |
|---|---|---|---|
| `constructor` | `Γ ⊢ A ∧ B` | `Γ ⊢ A \| Γ ⊢ B` | splits only the outermost `∧` |
| `refine ⟨?_, ?_⟩` | `Γ ⊢ A ∧ B` | `Γ ⊢ A \| Γ ⊢ B` | `⟨?_, ?_, ?_⟩` splits `A ∧ B ∧ C` in one go (`∧` nests to the right) |
| `refine ⟨x, ?_⟩` | `Γ ⊢ ∃ y, P y` | `Γ ⊢ P x` | fill some parts now, prove each `?_` next |
| `t <;> u` | `Γ ⊢ G` | `u` run on every goal `t` produces | |
| `all_goals u` | `G₁ \| … \| Gₙ` | `u` run on each `Gᵢ` | |
| `t ; u` | `G₁ \| … \| Gₙ` after `t` | `u` run on `G₁` only | the common mistake after `fin_cases` |
| `· tac` | `G₁ \| G₂` | proves `G₁` with `tac`, or fails | focus one goal; `.` also works |

## Adding facts

| Tactic | Before | After | Note |
|---|---|---|---|
| `have h : T := e` | `Γ ⊢ G` | `Γ, h : T ⊢ G` | `e` proves `T` |
| `have h : T := by tacs` | `Γ ⊢ G` | `Γ, h : T ⊢ G` | indent `tacs` further than `have` |
| `have h : T` | `Γ ⊢ G` | `Γ ⊢ T \| Γ, h : T ⊢ G` | Mathlib: prove `T` next |

## Extensionality and finite case splits

| Tactic | Before | After | Note |
|---|---|---|---|
| `ext i j` | `Γ ⊢ M = N` (matrices) | `Γ, i j : Fin n ⊢ M i j = N i j` | also `funext x` for functions |
| `fin_cases i` | `Γ, i : Fin 2 ⊢ P i` | `Γ ⊢ P 0 \| Γ ⊢ P 1` | indices print as `(fun i => i) ⟨0, ⋯⟩` |

## Rewriting and simplifying

| Tactic | Before | After | Note |
|---|---|---|---|
| `rw [h]` (`h : a = b`) | `Γ ⊢ P a` | `Γ ⊢ P b` | `a` must appear literally |
| `rw [← h]` | `Γ ⊢ P b` | `Γ ⊢ P a` | |
| `rw [lemma (by tac)]` | `Γ ⊢ P a` | `Γ ⊢ P b` | `(by tac)` proves the lemma's hypothesis |
| `simp [d₁, l₁]` | `Γ ⊢ G` | simplified `G`, or `∅` | unfolds definitions `dᵢ`, uses lemmas `lᵢ` |
| `simp?` | `Γ ⊢ G` | same as `simp` | also prints a `simp only [...]` you can paste in |
| `ring_nf` | `Γ ⊢ G` | `G` in ring normal form | e.g. `x * x` becomes `x ^ 2` |

## Closing

| Tactic | Closes | Note |
|---|---|---|
| `rfl` | `a = a` up to unfolding definitions | |
| `decide` | a decidable statement with concrete values | not for `ℝ` or `ℂ` |
| `norm_num` | numeric equalities and inequalities | handles `⁻¹`, `/` and casts of numerals |
| `ring` | commutative-ring identities | fails on `√`, `⁻¹` of variables, etc. |

## Seeing the state

| Command | Shows |
|---|---|
| infoview (cursor after a tactic) | goals at that point |
