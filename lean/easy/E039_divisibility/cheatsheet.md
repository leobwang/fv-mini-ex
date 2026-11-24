# E039 · Divisibility: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `obtain ⟨x, hx⟩ := h` on an `∃` and the `rfl` pattern (E007,
E030), `refine ⟨x, ?_⟩`, `exact`, `apply`, `have` (E021), anonymous constructors `⟨_, _⟩`.
**New here:** Mathlib's divisibility `a ∣ b` and the fact that it *is* an `∃`; the `ring` tactic; two library
lemmas, `dvd_mul_of_dvd_right` and `dvd_sub`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Prop`, or `P : α → Prop` when the step changes a term inside it). A
  hypothesis `g` in an example only finishes it: it shows what the goal or context became.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on `α` (a *type class*); each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ`, `ℤ` | natural numbers `0, 1, 2, …`; integers |
| `a ∣ b` | `a` divides `b`. **Definition:** `∃ c, b = a * c`. Typed `\mid`; the keyboard bar `\|` is a different symbol |
| `b = a * k` | the equation inside `a ∣ b`: the multiple `b` on the left, the cofactor `k` on the right of `a` |
| `a * k * m` | `(a * k) * m`: `*` groups to the left, so `a * (k * m)` is a different term (`ring` equates them) |
| `a ^ 2` | `a * a`: `^` with a natural-number exponent is repeated `*`; `ring` knows its laws |
| `3 * b - 2 * c` | in `ℤ`, ordinary subtraction. In `ℕ`, `-` truncates at `0`, and `dvd_sub` does not apply |
| `inst✝ : Monoid α` | an anonymous type-class hypothesis from a `[Monoid α]` binder; ignore it |
| `case h₁`, `case h₂` | the goals `apply dvd_sub` creates: the first and second hypothesis of the lemma |

---

## Part 1 · `dvd_chain`

Statement: in `ℕ`, `a ∣ b` and `b ∣ c` give `a ∣ c` (transitivity; the library's `dvd_trans` is banned). Unpack
both hypotheses into cofactors, substituting as you go (R2 twice); then give the product of the cofactors
(R3) and close the equation (R4).

**R1 · `obtain ⟨k, hk⟩ := h`** changes the **context**: `h : a ∣ b` is an `∃`, so it splits into the cofactor
`k` and the equation `hk`. Placeholders: `{α : Type} [Monoid α] (a b : α) (h : a ∣ b)`. `[Monoid α]`: α has an
associative `*` with a `1`; ℕ, ℤ, ℝ qualify.

| Before | After |
|---|---|
| `h : a ∣ b ⊢ P` | `k : α, hk : b = a * k ⊢ P` |

**R2 · `obtain ⟨k, rfl⟩ := h`** changes the **context and the goal**: the equation is used at once to replace the
local variable `b` by `a * k` everywhere, in the goal and in every other hypothesis (in Part 1, `h2 : b ∣ c`
becomes `h2 : a * k ∣ c`). `b` and `h` leave the context. Placeholders: as R1, `(P : α → Prop)`.

| Before | After |
|---|---|
| `h : a ∣ b ⊢ P b` | `k : α ⊢ P (a * k)` |

**R3 · `refine ⟨k, ?_⟩`** changes the **goal**: to prove `a ∣ b` you name the cofactor `k`, and the equation
remains. `exact ⟨k, by ring⟩` is R3 + R4 in one term. Placeholders: `{α : Type} [Monoid α] (a b k : α)`.

| Before | After |
|---|---|
| `⊢ a ∣ b` | `⊢ b = a * k` |

**R4 · `ring`** **closes** an equation that holds in every commutative (semi)ring: it reorders and regroups
products, distributes, and expands `(x * y) ^ n`. It does not use hypotheses. Placeholders:
`{α : Type} [CommSemiring α] (x y z : α)`; ℕ, ℤ, ℚ, ℝ, ℂ qualify.

| Before | After |
|---|---|
| `⊢ x * y * z = x * (z * y)` | no goals |
| `⊢ (x * y) ^ 3 = x ^ 3 * y ^ 3` | no goals |

**W1.** The Part 1 pattern on another statement, `a ∣ b → c ∣ d → a * c ∣ b * d`. R2, R2, `refine ⟨k * m, ?_⟩`,
then `ring`:

```lean-goal
⊢ a * c ∣ b * d
⊢ a * c ∣ a * k * d
⊢ a * c ∣ a * k * (c * m)
⊢ a * k * (c * m) = a * c * (k * m)
```

## Part 2 · `dvd_combo`

Statement: in `ℤ`, `a ∣ b` and `a ∣ c` give `a ∣ 3 * b - 2 * c`. No unpacking needed: build `a ∣ 3 * b` and
`a ∣ 2 * c` with R5, then subtract with R6. The whole proof can be one term.

**R5 · `dvd_mul_of_dvd_right`** changes the **context** (used with `have`). Statement:
`dvd_mul_of_dvd_right : a ∣ b → ∀ (c : α), a ∣ c * b`, with `a b` implicit and the factor `c` explicit. "Right"
says where `b` ends up: `c * b`, which matches `3 * b`. Its twin `dvd_mul_of_dvd_left : a ∣ b → ∀ c, a ∣ b * c`
gives `b * c`. Placeholders: `{α : Type} [CommSemigroup α] (a b c : α) (hb : a ∣ b)`; `[CommSemigroup α]`: α has
an associative, commutative `*`; ℕ, ℤ qualify.

| Before | After `have h := dvd_mul_of_dvd_right hb c` |
|---|---|
| `hb : a ∣ b ⊢ P` | `h : a ∣ c * b ⊢ P` |

**R6 · `dvd_sub`** changes the **goal list** (with `apply`). Statement:
`dvd_sub : a ∣ b → a ∣ c → a ∣ b - c`. As a term: `dvd_sub h₁ h₂`. Placeholders:
`{α : Type} [Ring α] (a b c : α)`; `[Ring α]`: α has `+`, `*` and negatives, so `-` is real subtraction; ℤ, ℚ, ℝ
qualify, ℕ does not. Its sibling `dvd_add : a ∣ b → a ∣ c → a ∣ b + c` also works in ℕ.

| Before | After `apply dvd_sub` |
|---|---|
| `⊢ a ∣ b - c` | `⊢ a ∣ b`, `⊢ a ∣ c` |

**W2.** Lemma terms nest: `exact dvd_add (dvd_mul_of_dvd_right h1 5) (dvd_mul_of_dvd_right h2 4)` closes

```lean-goal
⊢ a ∣ 5 * b + 4 * c
```

## Part 3 · `dvd_square`

Statement: in `ℕ`, `a ∣ b` gives `a ^ 2 ∣ b ^ 2`. Unpack `h` with R2, so the goal is about `(a * k) ^ 2`; name
the new cofactor with R3 (what must multiply `a ^ 2` to give `(a * k) ^ 2`?); close the equation with R4, which
expands powers of products.

---

## Traps

- The equation inside `a ∣ b` is `b = a * k`, not `a * k = b`. `Dvd.intro k (h : a * k = b) : a ∣ b` is the
  flipped form, if your equation is already the other way round.
- `obtain ⟨k, rfl⟩ := h` needs `b` to be a local variable. If `b` were an expression such as `n + 1`, use
  `obtain ⟨k, hk⟩ := h` (R1) and `rw [hk]`.
- After `obtain ⟨k, rfl⟩ := h1` in Part 1, `h2` reads `a * k ∣ c`. Unpack it next, the same way; do not try to
  unpack `h2` first and look for `b` afterwards.
- `dvd_mul_of_dvd_right` vs `dvd_mul_of_dvd_left`: pick by where `b` sits in the target product (`3 * b` → right).
  `rw [mul_comm]` is not needed if you pick the right one.
- `dvd_sub` needs a ring: it fails in ℕ, where `-` is truncated subtraction. Part 2 is stated in ℤ.
- `dvd_trans` and `Dvd.dvd.trans` are banned (they prove Part 1 outright); so is dot notation `h1.trans h2`.
- `∣` is `\mid`. The ASCII `|` does not parse as divisibility.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use `h : a ∣ b` as an equation | `obtain ⟨k, hk⟩ := h` (gives `hk : b = a * k`) | R1 |
| replace `b` by `a * k` everywhere | `obtain ⟨k, rfl⟩ := h` | R2 |
| prove `a ∣ b` by a cofactor | `refine ⟨k, ?_⟩` or `exact ⟨k, by ring⟩` | R3, R4 |
| close a polynomial identity | `ring` | R4 |
| `a ∣ b` ⟹ `a ∣ c * b` | `dvd_mul_of_dvd_right h c` | R5 |
| `a ∣ b` ⟹ `a ∣ b * c` | `dvd_mul_of_dvd_left h c` | R5 |
| `a ∣ b`, `a ∣ c` ⟹ `a ∣ b - c` (ring) | `dvd_sub h₁ h₂` | R6 |
| `a ∣ b`, `a ∣ c` ⟹ `a ∣ b + c` | `dvd_add h₁ h₂` | R6, W2 |
| concrete `6 ∣ 42` | `norm_num` (or `decide` in ℕ) | TACTIC_STATES |
| see the state | infoview | |
