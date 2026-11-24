# M114 · Polynomial interpolation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `have`, `rw`, `simp only`,
anonymous constructors `⟨_, _⟩`, `∃`, `∧`, `¬`. **New here:** Mathlib's polynomials `R[X]` (evaluation,
`degree`, `natDegree`), Lagrange interpolation, finite sets `Finset` and their images, unique existence
`∃!`, and the tactics `rintro`, `obtain`, `set`, `by_contra`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`apply`/`have`. It says what changes (**goal**,
**context**, or **goal list**), gives the lemma's statement, lists the placeholders with their types, then
shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. `G : Prop` with `g : T → G` is a dummy goal: the entry only adds a fact `T` to the
  context, and `g` shows that the fact is the one we wanted.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Field F]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℝ[X]` | polynomials in one variable `X` with real coefficients (`open Polynomial` enables the notation) |
| `eval x p` | `p` evaluated at the number `x`; source `p.eval x` prints as `eval x p` |
| `p.degree` | the degree of `p` in `WithBot ℕ` = `ℕ` plus a bottom element `⊥`; `degree 0 = ⊥` |
| `p.natDegree` | the degree of `p` as a natural number; `natDegree 0 = 0` |
| `↑s.card` | the number `s.card : ℕ` of elements of `s`, cast into `WithBot ℕ` to compare with a `degree` |
| `s : Finset ι` | a finite set of elements of type `ι`; `i ∈ s` is membership |
| `↑s` | the `Finset` `s` viewed as a `Set ι` (a coercion); appears inside `Set.InjOn v ↑s` |
| `Set.InjOn v ↑s` | `v` is injective on `s`: `∀ a ∈ s, ∀ b ∈ s, v a = v b → a = b` (the nodes are distinct) |
| `Finset.image f s` | the finite set `{f a ∣ a ∈ s}`; source `s.image f`. It is a `Finset` of the *values* |
| `{0, 1}` (a `Finset`) | the finite set with elements `0` and `1` |
| `∀ i ∈ t, Q i` | `∀ i, i ∈ t → Q i` |
| `∃! x, Q x` | unique existence: `∃ x, Q x ∧ ∀ y, Q y → y = x` |
| `(fun x => Q x) y` | `Q y` not yet simplified (β-reduced); `rintro` and `intro` see through it |
| `F →ₗ[F] F[X]`, `(ι → F) →ₗ[F] F[X]` | an `F`-linear map; `Lagrange.interpolate s v` is one |
| `(Lagrange.interpolate s v) r` | that linear map applied to the value function `r`: the interpolating polynomial |
| `d : ℝ[X] := e` | a local definition made by `set` (R7); `d` stands for `e` |
| `d : ℝ[X] := ⋯` | the same, with the value hidden after a split |
| `max a b` | the larger of `a` and `b` (in a linear order such as `WithBot ℕ`) |
| `case refine_1`, `refine_2`, `refine_3` | the three goals R1 leaves: degree, values, uniqueness |
| `case refine_3.heval`, `case refine_3.hcard` | the two goals R13 leaves inside the uniqueness goal: roots, then size |
| `∀ i ∈ Finset.image v s, eval i d = 0` | the roots goal of R13; this bound `i` is a *real number* (a point), not an index in `ι` |
| `{ι : Type*}`, `ι : Type u_1` | `ι` is an arbitrary type (`Type*` lets it live in any universe `u_1`; read it as `Type`) |
| `inst✝ : DecidableEq ι` | an unnamed instance hypothesis from `[DecidableEq ι]` in the statement |

Type classes met below: `Field F` (`ℚ`, `ℝ`, `ℂ`), `CommRing R` + `IsDomain R` (a commutative ring with no
zero divisors: `ℤ`, `ℚ`, `ℝ`), `Ring R`, `Semiring R` (`ℕ`, `ℤ`, `ℝ`), `AddGroup G` (`ℤ`, `ℝ`, `ℝ[X]`),
`LinearOrder α` (`ℕ`, `ℝ`, `WithBot ℕ`), `Preorder α` (any of these), `DecidableEq β` (equality can be
decided; `ℝ` gets it classically in Mathlib).

---

## Part 1 · `interpolation_exists_unique`

Statement: for a finite index set `s`, nodes `v i` that are distinct on `s`, and values `r i`, there is
exactly one real polynomial `p` with `p.degree < s.card` and `eval (v i) p = r i` for all `i ∈ s`.

Plan. Existence: the witness is the Lagrange interpolant `Lagrange.interpolate s v r` (R2), and Mathlib
knows its degree (R3) and its values (R4). Uniqueness: for another such `q`, the difference
`d = q - interpolant` has degree `< s.card` (R9–R11) and vanishes at the `s.card` distinct points
`Finset.image v s` (R14–R18, R4); a nonzero polynomial cannot have more roots than its degree (R13, R19,
R20), so `d = 0`. R20 needs `d ≠ 0`, which is why the argument runs by contradiction (R8, R12).

### Unique existence and the interpolant

**R1 · `refine ⟨w, ⟨?_, ?_⟩, ?_⟩`** changes the **goal list**. `∃! x, A x ∧ B x` unfolds to
`∃ x, (A x ∧ B x) ∧ ∀ y, (A y ∧ B y) → y = x`, so the anonymous constructor takes the witness `w`, a pair
for `A w ∧ B w`, and the uniqueness proof. Each `?_` becomes a goal; you may also put a term in place of a
`?_`. Placeholders: `{α : Type} (w : α) (A B : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃! x, A x ∧ B x` | `⊢ A w`, `⊢ B w`, `⊢ ∀ (y : α), (fun x => A x ∧ B x) y → y = w` |

**R2 · `Lagrange.interpolate s v r`** is the witness. `Lagrange.interpolate s v : (ι → F) →ₗ[F] F[X]` is a
linear map built from the finite index set `s` and the nodes `v`; applied to the values `r : ι → F` it is
the polynomial $\sum_{i \in s} r_i \prod_{j \in s, j \ne i} \frac{X - v_j}{v_i - v_j}$. It changes the
**goal** when used as a witness. Placeholders: `{F : Type} [Field F] {ι : Type} [DecidableEq ι]
(s : Finset ι) (v r : ι → F)`; `ℝ` is a field.

| Before | After `refine ⟨Lagrange.interpolate s v r, ?_⟩` |
|---|---|
| `⊢ ∃ p, Q p` | `⊢ Q ((Lagrange.interpolate s v) r)` |

**R3 · `Lagrange.degree_interpolate_lt`** changes the **context** (with `have`). Statement:
`(r : ι → F) → Set.InjOn v ↑s → ((Lagrange.interpolate s v) r).degree < ↑s.card`. Placeholders as R2,
plus `(hv : Set.InjOn v ↑s)`. Usage: `Lagrange.degree_interpolate_lt r hv`.

| Before | After `have h := Lagrange.degree_interpolate_lt r hv` |
|---|---|
| `⊢ G` | `h : ((Lagrange.interpolate s v) r).degree < ↑s.card ⊢ G` |

**R4 · `Lagrange.eval_interpolate_at_node`** changes the **context** (with `have`). Statement:
`(r : ι → F) → Set.InjOn v ↑s → i ∈ s → eval (v i) ((Lagrange.interpolate s v) r) = r i`: the interpolant
takes the prescribed value at each node. Placeholders as R3, plus `(i : ι) (hi : i ∈ s)`. Usage:
`Lagrange.eval_interpolate_at_node r hv hi`; inside `fun i hi => …` it proves the whole `∀ i ∈ s, …`.

| Before | After `have h := Lagrange.eval_interpolate_at_node r hv hi` |
|---|---|
| `⊢ G` | `h : eval (v i) ((Lagrange.interpolate s v) r) = r i ⊢ G` |

### Uniqueness: reduce to `d = 0`, argue by contradiction

**R5 · `rintro y ⟨hA, hB⟩`** changes the **context and the goal**: `intro` plus pattern matching. It
introduces `y`, then splits the hypothesis `A y ∧ B y` into `hA` and `hB` (seeing through the
`(fun x => …) y` that R1 leaves). Placeholders: `{α : Type} (w : α) (A B : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : α), (fun x => A x ∧ B x) y → y = w` | `y : α, hA : A y, hB : B y ⊢ y = w` |

**R6 · `rw [← sub_eq_zero]`** changes the **goal**. Statement: `sub_eq_zero : a - b = 0 ↔ a = b`; `←`
rewrites `a = b` into `a - b = 0`. Placeholders: `{G : Type} [AddGroup G] (a b : G)`; `ℝ[X]` is an
additive group.

| Before | After |
|---|---|
| `⊢ a = b` | `⊢ a - b = 0` |

**R7 · `set d := e`** changes the **context and the goal**: it adds the local definition `d : G := e` and
replaces every `e` in the goal by `d`. `d` is definitionally `e`, so lemmas about `e` still apply to `d`
(but see the trap on `simp`). Placeholders: `{G : Type} [AddGroup G] (a b : G)`, `e := a - b`.

| Before | After `set d := a - b` |
|---|---|
| `⊢ P (a - b)` | `d : G := a - b ⊢ P d` |

**R8 · `by_contra hd`** changes the **goal and the context**: to prove `Q`, assume `hd : ¬Q` and prove
`False` (classical logic). With `Q := d = 0` you get `hd : ¬d = 0`, which is the same as `d ≠ 0`.
Placeholders: `(Q : Prop)`.

| Before | After |
|---|---|
| `⊢ Q` | `hd : ¬Q ⊢ False` |

### Degree of a difference

**R9 · `Polynomial.degree_sub_le`** changes the **context** (with `have`). Statement:
`(p q : R[X]) → (p - q).degree ≤ max p.degree q.degree`. Placeholders: `{R : Type} [Ring R] (p q : R[X])`.

| Before | After `have h := degree_sub_le p q` |
|---|---|
| `⊢ G` | `h : (p - q).degree ≤ max p.degree q.degree ⊢ G` |

**R10 · `max_lt`** changes the **goal list**. Statement: `b < a → c < a → max b c < a`.
Placeholders: `{α : Type} [LinearOrder α] (a b c : α)`; here `α = WithBot ℕ`.

| Before | After `apply max_lt` |
|---|---|
| `⊢ max b c < a` | `⊢ b < a`, `⊢ c < a` |

**R11 · `lt_of_le_of_lt`** changes the **goal**. Statement: `a ≤ b → b < c → a < c` (chain `≤` then `<`).
Placeholders: `{α : Type} [Preorder α] (a b c : α) (hab : a ≤ b)`. As a term:
`lt_of_le_of_lt hab hbc : a < c`, which is how R9 and R10 combine into one `have` (W2).

| Before | After `apply lt_of_le_of_lt hab` |
|---|---|
| `⊢ a < c` | `⊢ b < c` |

### Root counting

**R12 · `apply hd`** with `hd : ¬Q` changes the **goal**: `¬Q` is `Q → False`, so applying it to the goal
`False` leaves `Q`. After R8 this brings back `d = 0`, now with `hd : d ≠ 0` in the context.
Placeholders: `(Q : Prop) (hd : ¬Q)`.

| Before | After |
|---|---|
| `⊢ False` | `⊢ Q` |

**R13 · `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`** changes the **goal list**. Statement:
`(p : R[X]) (t : Finset R) → (∀ i ∈ t, eval i p = 0) → p.natDegree < t.card → p = 0`: a polynomial that
vanishes on more points than its degree is zero. The points `t` are a `Finset` of *values* in `R`, not of
indices. Placeholders: `{R : Type} [CommRing R] [IsDomain R] (p : R[X]) (t : Finset R)`; `ℝ` qualifies.

| Before | After `apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p t` |
|---|---|
| `⊢ p = 0` | `⊢ ∀ i ∈ t, eval i p = 0`, `⊢ p.natDegree < t.card` |

For the first goal, `intro x hx` gives `x : R` and `hx : x ∈ t`.

**R14 · `Finset.mem_image`** changes the **goal** (with `rw`), or gives a fact (with `.mp`). Statement:
`b ∈ Finset.image f s ↔ ∃ a ∈ s, f a = b`. Placeholders: `{α β : Type} [DecidableEq β] (f : α → β)
(s : Finset α) (b : β)`. In the exercise the membership is a hypothesis `hx : b ∈ Finset.image f s`, and
`Finset.mem_image.mp hx : ∃ a ∈ s, f a = b` (`.mp` is the left-to-right direction of an `↔`).

| Before | After `rw [Finset.mem_image]` |
|---|---|
| `⊢ b ∈ Finset.image f s` | `⊢ ∃ a ∈ s, f a = b` |

**R15 · `obtain ⟨a, ha, rfl⟩ := h`** changes the **context and the goal**: it destructs
`h : ∃ a ∈ s, f a = b` into `a`, `ha : a ∈ s` and the equation `f a = b`; the pattern `rfl` substitutes that
equation, so the variable `b` disappears and becomes `f a` everywhere. Works because `b` is a local
variable. You can write `obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx` directly (R14 inside).
Placeholders: `{α β : Type} (f : α → β) (s : Finset α) (b : β)`.

| Before | After |
|---|---|
| `⊢ P b` (with `h` in the context) | `a : α, ha : a ∈ s ⊢ P (f a)` (`h` and `b` are gone) |

**R16 · `simp only [d]`** for a `set` variable changes the **goal**: `d` is replaced by its value.
`simp` does not look inside `d` by itself, so list it with the other lemmas (`simp only [d, …]`).
Placeholders: `{G : Type} [AddGroup G] (a b : G)`, `d := a - b`.

| Before | After |
|---|---|
| `d : G := a - b ⊢ P d` | `⊢ P (a - b)` |

**R17 · `Polynomial.eval_sub`** changes the **goal**. Statement: `eval x (p - q) = eval x p - eval x q`.
Placeholders: `{R : Type} [Ring R] (p q : R[X]) (x : R)`.

| Before | After `rw [eval_sub]` |
|---|---|
| `⊢ P (eval x (p - q))` | `⊢ P (eval x p - eval x q)` |

**R18 · `sub_self`** changes the **goal**. Statement: `a - a = 0`. Placeholders:
`{G : Type} [AddGroup G] (a : G)`. In the exercise it fires after R16, R17, `hval i hi` and R4 have turned
both evaluations into `r i`.

| Before | After `rw [sub_self]` |
|---|---|
| `⊢ P (a - a)` | `⊢ P 0` |

### Counting the nodes

**R19 · `Finset.card_image_of_injOn`** changes the **goal**. Statement:
`Set.InjOn f ↑s → (Finset.image f s).card = s.card`: an injective map does not merge points.
Placeholders: `{α β : Type} [DecidableEq β] (f : α → β) (s : Finset α) (hf : Set.InjOn f ↑s)`.

| Before | After `rw [Finset.card_image_of_injOn hf]` |
|---|---|
| `⊢ P (Finset.image f s).card` | `⊢ P s.card` |

**R20 · `Polynomial.natDegree_lt_iff_degree_lt`** changes the **goal**. Statement:
`p ≠ 0 → (p.natDegree < n ↔ p.degree < ↑n)`. The side condition is real: for `p = 0` and `n = 0`,
`natDegree 0 = 0 < 0` is false but `degree 0 = ⊥ < ↑0` is true. Supply `hp` (in the exercise `hd : ¬d = 0`
works, since `d ≠ 0` is notation for `¬d = 0`). Placeholders: `{R : Type} [Semiring R] (p : R[X]) (n : ℕ) (hp : p ≠ 0)`.

| Before | After `rw [natDegree_lt_iff_degree_lt hp]` |
|---|---|
| `⊢ p.natDegree < n` | `⊢ p.degree < ↑n` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: `∃!` on `ℕ`.** `refine ⟨3, rfl, ?_⟩` fills the witness and its proof (R1 with terms in place of
`?_`), leaving the uniqueness goal; `intro m hm` then `omega` finish it.

```lean-goal
⊢ ∃! n, n + 2 = 5
⊢ ∀ (y : ℕ), (fun n => n + 2 = 5) y → y = 3
⊢ m = 3
```

**W2: degree of a difference.** For `p q : ℚ[X]` with degrees `< 3`: `apply lt_of_le_of_lt (degree_sub_le p q)`
(R11 with R9 as its first argument), then `apply max_lt` (R10):

```lean-goal
⊢ (p - q).degree < 3
⊢ max p.degree q.degree < 3
⊢ p.degree < 3
⊢ q.degree < 3
```

**W3: root counting on `{0, 1}`.** For `p : ℚ[X]` with `p.natDegree < 2` vanishing at `0` and `1`,
`apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p {0, 1}` (R13) leaves the roots and the size. The
roots: `intro x hx`, `simp only [Finset.mem_insert, Finset.mem_singleton] at hx` turns `hx` into
`x = 0 ∨ x = 1`, and `rcases hx with rfl | rfl` gives one goal per root. The size: `Finset.card_pair h`
(`a ≠ b → {a, b}.card = 2`). In the exercise the points are `Finset.image v s` instead, handled by R14, R15
and R19.

```lean-goal
⊢ ∀ i ∈ {0, 1}, eval i p = 0
⊢ p.natDegree < {0, 1}.card
```

---

## Traps

- `Lagrange.interpolate s v` alone is a linear map, not a polynomial; `Lagrange.interpolate s v r` applies
  it to the values `r`, and the infoview prints that as `(Lagrange.interpolate s v) r`.
- `degree` and `natDegree` differ: the hypotheses give `degree < ↑s.card` (in `WithBot ℕ`), root counting
  (R13) wants `natDegree < card` (in `ℕ`). R20 converts, but only for a nonzero polynomial: that is why the
  proof assumes `hd : ¬d = 0` (R8) before calling R13 (via R12).
- Root counting needs a `Finset ℝ` of points, not the index set `s : Finset ι`. Use `Finset.image v s`; its
  size is `s.card` only because `v` is injective on `s` (R19 with `hv`).
- `simp only [eval_sub, …]` makes no progress on `eval x d` when `d` comes from `set`: include `d` itself in
  the list (R16). (`rw` does see through `d`, `simp` does not.)
- Prove the degree fact `d.degree < ↑s.card` with `have` *before* `apply hd`/R13: afterwards it is still in
  the context of both goals and you need it in the second one.
- `obtain ⟨i, hi, rfl⟩` keeps `hx`, now as `hx : v i ∈ Finset.image v s`; it is harmless.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∃! x, A x ∧ B x` | `refine ⟨w, ⟨?_, ?_⟩, ?_⟩` | R1 |
| the interpolating polynomial | `Lagrange.interpolate s v r` | R2 |
| its degree `< ↑s.card` | `Lagrange.degree_interpolate_lt r hv` | R3 |
| its value at node `v i` | `Lagrange.eval_interpolate_at_node r hv hi` | R4 |
| take `y` and split `A y ∧ B y` | `rintro y ⟨hA, hB⟩` | R5 |
| `a = b` → `a - b = 0` | `rw [← sub_eq_zero]` | R6 |
| name a subterm | `set d := e` | R7 |
| argue by contradiction | `by_contra hd` | R8 |
| `(p - q).degree ≤ max …` | `degree_sub_le p q` | R9 |
| `max b c < a` | `max_lt hb hc` | R10 |
| chain `≤` then `<` | `lt_of_le_of_lt hab hbc` | R11 |
| `False` from `hd : ¬Q` | `apply hd` | R12 |
| `p = 0` by counting roots | `apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p t` | R13 |
| `x ∈ Finset.image f s` → `∃ a ∈ s, f a = x` | `Finset.mem_image.mp hx` | R14 |
| destruct and substitute | `obtain ⟨a, ha, rfl⟩ := h` | R15 |
| unfold a `set` variable in `simp` | `simp only [d, …]` | R16 |
| `eval x (p - q)` | `eval_sub` | R17 |
| `a - a` → `0` | `sub_self` | R18 |
| `(Finset.image f s).card` → `s.card` | `rw [Finset.card_image_of_injOn hf]` | R19 |
| `natDegree <` ↔ `degree <` | `rw [natDegree_lt_iff_degree_lt hp]` | R20 |
| see the state | infoview | |
