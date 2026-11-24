# E021 · have, show, suffices: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E020, in particular `intro`/`exact` (E003), `¬`/`False` (E008), `rw` (E009), `simp`
(E010) and `omega` (E011).
**New here:** three ways to shape a proof. `have` works **forward**: it proves an intermediate fact and adds
it to the context. `suffices` works **backward**: it replaces the goal by a statement that implies it.
`show` **restates** the goal in an equivalent (definitionally equal) form. Also: rewriting and simplifying
a **hypothesis** (`rw … at h`, `simp at h`) and the definition of `≠`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter or change, separated by `, `.
- `T G : Prop` are arbitrary propositions; `s g : Nat → Nat` arbitrary functions on natural numbers;
  `{α : Type}` any type; `P : List α → Prop` "the rest of the statement".
- A hypothesis `k` only finishes the example. "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `f : Nat → Nat` | an arbitrary function from naturals to naturals (nothing is known about it but the hypotheses) |
| `h : ∀ (n : Nat), f n < f (n + 1)` | `f` is strictly increasing step by step; `h 0 : f 0 < f (0 + 1)` |
| `mono : ∀ (a b : Nat), a ≤ b → f a ≤ f b` | `f` is monotone; `mono x y hxy : f x ≤ f y` |
| `s (0 + 1)` | Lean does not simplify `0 + 1` after instantiating `n := 0`; it is not printed as `s 1` |
| `xs ≠ []` | `Ne xs []`, defined as `xs = [] → False`: `xs` is not the empty list |
| `xs.length`, `[].length` | `List.length xs`, `List.length []` (dot notation) |
| `False` | the proposition with no proof; a hypothesis `h : False` proves any goal |
| `n * 2` | multiplication by a numeral: still linear, `omega` handles it |

---

## Part 1 · `have_chain`

Statement: if `f n < f (n + 1)` for every `n`, then `f 0 + 3 ≤ f 3`. Instantiate `h` at `0`, `1`, `2`, each
time **writing the type out** (R1, not R2), then the goal is linear arithmetic in the atoms
`f 0, f 1, f 2, f 3` (R3).

**R1 · `have k : T := e`** changes the **context**: it adds `k : T`, where `e` is a term of type `T`. The goal
is unchanged. Lean accepts the written `T` when it *computes* to the type of `e`: `h 0 : s 0 ≤ s (0 + 1)`
and `0 + 1` computes to `1`, so `have k0 : s 0 ≤ s 1 := h 0` is fine. Placeholders: `(s : Nat → Nat)
(h : ∀ n, s n ≤ s (n + 1)) (G : Prop)`.

| Before | After |
|---|---|
| `k : s 0 ≤ s 1 → G ⊢ G` | `k0 : s 0 ≤ s 1 ⊢ G` |

**R2 · `have k := e`** (no type) changes the **context**: `k` gets the type of `e` exactly as Lean computes
it by substitution, unsimplified. Placeholders as in R1.

| Before | After |
|---|---|
| `k : s 0 ≤ s (0 + 1) → G ⊢ G` | `k0 : s 0 ≤ s (0 + 1) ⊢ G` |

**R3 · `omega`** **closes** a goal of linear arithmetic (`+`, `-`, `*` by a numeral, `<`, `≤`, `=`) over
`Nat` or `Int`, using the hypotheses of that shape. On `Nat`, `x < y` means `x + 1 ≤ y`. Anything else,
such as a function value `s 1`, is an *atom*: an unknown number. Atoms are compared as written, so `s 1`
and `s (0 + 1)` are two unrelated unknowns to `omega`, and facts made with R2 do not chain.
Placeholders: `(x y z : Nat)`.

| Before | After |
|---|---|
| `h1 : x < y, h2 : y < z ⊢ x + 2 ≤ z` | no goals |

**W1** (R1 twice, then R3) on `h : ∀ n, s n + 2 ≤ s (n + 1)`, goal `s 0 + 4 ≤ s 2`:

| Step | State |
|---|---|
| start | `⊢ s 0 + 4 ≤ s 2` |
| `have k0 : s 0 + 2 ≤ s 1 := h 0` | `k0 : s 0 + 2 ≤ s 1 ⊢ s 0 + 4 ≤ s 2` |
| `have k1 : s 1 + 2 ≤ s 2 := h 1` | `k0 : s 0 + 2 ≤ s 1, k1 : s 1 + 2 ≤ s 2 ⊢ s 0 + 4 ≤ s 2` |
| `omega` | no goals |

## Part 2 · `suffices_mono`

Statement: if `f` is monotone, then `f n ≤ f (n * 2)`. The goal is the conclusion of `mono`, so it suffices
to prove the premise `n ≤ n * 2` (R4, closing the old goal with R5), and that premise is linear arithmetic
(R3).

**R4 · `suffices hs : T by e`** changes the **goal**: `G` becomes `T`. The term or tactic block `e` must prove
the **old** goal `G`, and inside it `hs : T` is available. After the line, you prove `T`. Core Lean needs the
`by …` (or `from e`) part; Mathlib also allows a bare `suffices hs : T`. Placeholders: `(T G : Prop)
(g : T → G)`.

| Before | After |
|---|---|
| `g : T → G ⊢ G` | `g : T → G ⊢ T` |

**R5 · `exact m x y hxy`** **closes** `g x < g y`. `m : ∀ a b, a < b → g a < g b` is a function: give it two
numbers and a proof, in that order. `m x y : x < y → g x < g y`, so `m x y hxy : g x < g y`. An argument that
is an expression needs parentheses: `m x (y + 1) h`. Placeholders: `(g : Nat → Nat) (x y : Nat)
(hxy : x < y)`.

| Before | After |
|---|---|
| `hxy : x < y ⊢ g x < g y` | no goals |

**W2** (R4 with R5 inside, then R3) on `m : ∀ a b, a < b → g a < g b`, goal `g n < g (n + 3)`:

| Step | State |
|---|---|
| start | `⊢ g n < g (n + 3)` |
| `suffices hs : n < n + 3 by exact m n (n + 3) hs` | `⊢ n < n + 3` |
| `omega` | no goals |

## Part 3 · `show_ne`

Statement: a list of length 3 is not empty. `xs ≠ []` is `xs = [] → False`: introduce `hx : xs = []` (R7),
optionally restate the goal as `False` (R6), substitute `[]` for `xs` in `h` (R8), and simplify `h` to
`False` (R9, R10).

**R6 · `show T`** changes the **goal** to `T`, which must be *definitionally equal* to the goal (equal after
unfolding definitions and computing). `a ≠ b` unfolds to `a = b → False`, so `show a = b → False` is
accepted. It documents what the goal is, or picks a form a later tactic needs. Placeholders:
`{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `⊢ a ≠ b` | `⊢ a = b → False` |

**R7 · `intro hx`** on a goal `a ≠ b` changes the **goal and the context**: `intro` unfolds `≠` by itself
(no `show` needed), the goal becomes `False`, and `hx : a = b` enters the context. Placeholders as in R6.

| Before | After |
|---|---|
| `k : a = b → False ⊢ a ≠ b` | `hx : a = b ⊢ False` |

**R8 · `rw [hx] at h`** with `hx : a = b` changes the **context**: every `a` in the hypothesis `h` becomes `b`.
The goal is unchanged. Placeholders: `{α : Type} (xs : List α) (P : List α → Prop) (hx : xs = [])`.

| Before | After |
|---|---|
| `hx : xs = [], h : P xs ⊢ P []` | `hx : xs = [], h : P [] ⊢ P []` |

**R9 · `List.length_nil`** (statement: `([] : List α).length = 0`) changes the **context** when used as
`rw [List.length_nil] at h`. `simp` applies it by itself. Placeholders: `{α : Type} (G : Prop)`.

| Before | After |
|---|---|
| `h : [].length = 2 ⊢ G` | `h : 0 = 2 ⊢ G` |

**R10 · `simp at h`** simplifies the hypothesis `h`. If `h` becomes `False`, the goal is **closed**, whatever
it is: `simp` computes `[].length` to `0` (R9) and decides `0 = 2` is `False`. Placeholders as in R9.

| Before | After |
|---|---|
| `h : [].length = 2 ⊢ G` | no goals |

**W3** (R7, R6, R8, R10) on a number: `h : 2 * n = 6`, goal `n ≠ 0`:

| Step | State |
|---|---|
| start | `h : 2 * n = 6 ⊢ n ≠ 0` |
| `intro hx` | `h : 2 * n = 6, hx : n = 0 ⊢ False` |
| `show False` | `h : 2 * n = 6, hx : n = 0 ⊢ False` (unchanged: the goal already is `False`) |
| `rw [hx] at h` | `h : 2 * 0 = 6, hx : n = 0 ⊢ False` |
| `simp at h` | no goals |

---

## Traps

- `have k := h 0` (no type) gives `k : f 0 < f (0 + 1)`, and `omega` treats `f (0 + 1)` and `f 1` as
  different unknowns: write the type out (R1 vs R2).
- `suffices hs : T by e`: `e` proves the **old** goal from `hs`, not `T`. After the line the goal is `T`.
- In core Lean, `suffices hs : T` without `by …`/`from …` is a parse error ("expected 'by' or 'from'").
- `show T` fails when `T` is not definitionally equal to the goal: `show a = b` on `⊢ a ≠ b` fails.
- `rw [hx] at h` rewrites `h` only; the goal keeps its `xs`. Use `rw [hx] at h ⊢` for both.
- `mono n n * 2 hs` parses as `(mono n n) * (2 hs)`, because application binds tighter than `*`: write
  `mono n (n * 2) hs`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| add a fact `T`, proved by a term `e` | `have k : T := e` | R1 |
| instance of `h : ∀ n, …` with a clean type | `have k : f 1 < f 2 := h 1` | R1, R2 |
| linear arithmetic from hypotheses | `omega` | R3 |
| replace the goal by a premise `T` that implies it | `suffices hs : T by exact …` | R4 |
| apply a `∀ a b, a < b → …` hypothesis | `exact m x y hxy` | R5 |
| restate the goal in an equal form | `show T` | R6 |
| goal `a ≠ b` | `intro hx` (goal becomes `False`) | R7 |
| substitute in a hypothesis | `rw [hx] at h` | R8 |
| `[].length` → `0` | `rw [List.length_nil] at h` (or `simp`) | R9 |
| hypothesis that is false after simplifying | `simp at h` | R10 |
| see the state | infoview (cursor after a tactic) | |
