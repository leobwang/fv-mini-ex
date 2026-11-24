# E062 · Bool vs Prop: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular the `decide` tactic (E001), `∧`, `↔`,
`⟨_, _⟩`, `.1`/`.2`, `.mp`/`.mpr` (E005), `rw` and `rw … at h` (E009), `Bool` and case analysis on it (E016),
bounded quantifiers `∀ x ∈ l` (E025), `unfold` (E030), `refine` with `?_` (E031). **New here:** the two
worlds `Bool` (values computed by running code) and `Prop` (statements proved by proofs), and the core
lemmas that move between them: `decide`, `List.all`, `&&`, `==`, and the coercion `b ↦ (b = true)`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw` or `exact`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Prop → Prop` or `P : Bool → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- "no goals" means the step closed the goal.
- The guide never writes the banned word `decide`. It writes `((p : Prop) : Bool)`, the coercion from a
  decidable Prop to `Bool`, which elaborates to `decide p` and prints as `decide p`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Bool and Prop in one paragraph

`Bool` is an ordinary two-element data type, `true | false`; `&&`, `||`, `==` are functions that compute a
`Bool`. `Prop` is the type of statements; `∧`, `∨`, `=`, `∀` build statements, and a statement is
established by a proof, not computed. Lean bridges the two in both directions. **Bool → Prop:** a `b : Bool`
used where a Prop is expected becomes the statement `b = true` (a coercion Lean inserts by itself; R9).
**Prop → Bool:** a Prop `p` with an instance `[Decidable p]` (an algorithm that decides `p`; `Nat` `<`, `≤`, `=`
have one) can be evaluated as `decide p : Bool`. The lemmas `decide_eq_true` / `of_decide_eq_true` (R5, R4)
say that `decide p = true` and `p` are interchangeable. Each Bool operation has a matching lemma that turns
`… = true` into the Prop connective: `List.all` → `∀` (R2), `&&` → `∧` (R7), `==` → `=` (R8).

## Reading the goals

| You see | It means |
|---|---|
| `decide p` | `Decidable.decide p : Bool`, the result of running `p`'s decision procedure |
| `inst✝ : Decidable p` | an anonymous instance in the context: "`p` has a decision procedure" |
| `b = true` | the Prop "the Bool `b` is `true`"; also what a bare `b` means where a Prop is expected |
| `a && b` | `and a b : Bool`, Bool conjunction (computed) |
| `a = true ∧ b = true` | Prop conjunction (proved) of two Bool facts |
| `a == b` | `BEq.beq a b : Bool`, Bool equality test (computed); `a = b` is the Prop |
| `inst✝¹ : BEq α`, `inst✝ : LawfulBEq α` | `α` has a `==`, and that `==` agrees with `=` (true for `Nat`, `Bool`, …) |
| `xs.all f` | `List.all xs f : Bool`, `true` iff `f x = true` for every element `x` of `xs` |
| `xs.all fun x => …` | the same, with `f` written as a lambda |
| `∀ (x : α), x ∈ l → Q x` | how core Lean prints the bounded quantifier `∀ x ∈ l, Q x` |
| `(a && b && c)` | `((a && b) && c)`: `&&` groups to the left |
| `case refine_1`, `case refine_2` | the two goals `refine ⟨…?_…, …?_…⟩` left (R3): the `→` half, then the `←` half |

---

## Part 1 · `allPos_iff`

Statement: `allPos xs = true ↔ ∀ x ∈ xs, 0 < x`, where `allPos xs := xs.all (fun x => decide (0 < x))`.
"The Bool test returns `true`" iff "every element is positive". Unfold the test (R1), turn `all` into a
bounded `∀` (R2), split the `↔` into two functions (R3); each then converts one `decide (0 < x) = true` into
`0 < x` (R4) or back (R5).

**R1 · `unfold allEven`** changes the **goal**: the defined name is replaced by its body. In the exercise:
`unfold allPos`. Placeholders: `(xs : List Nat) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (allEven xs)` | `⊢ P (xs.all fun x => x % 2 == 0)` |

**R2 · `rw [List.all_eq_true]`** changes the **goal**. The lemma is
`List.all_eq_true {α} {p : α → Bool} {l : List α} : l.all p = true ↔ ∀ x, x ∈ l → p x = true`; `rw` can use an
`↔` like an `=` between Props. Placeholders: `{α : Type} (l : List α) (f : α → Bool) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (l.all f = true)` | `⊢ P (∀ (x : α), x ∈ l → f x = true)` |

**R3 · `refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩`** changes the **goal list and the context**. An `↔` is a
pair (`→`, `←`); each half of a bounded `∀` statement is a function taking the hypothesis `h`, an element `x`
and its membership proof `hx`. Afterwards the first goal has `h : ∀ (x : α), x ∈ l → A x` in its context, the
second has `h : ∀ (x : α), x ∈ l → B x`; then `h x hx` is the fact about this `x`. Placeholders:
`{α : Type} (l : List α) (A B : α → Prop)`. Term-mode form: `⟨fun h x hx => …, fun h x hx => …⟩` as the whole
`exact`.

| Before | After |
|---|---|
| `⊢ (∀ (x : α), x ∈ l → A x) ↔ ∀ (x : α), x ∈ l → B x` | `x : α, hx : x ∈ l ⊢ B x`, `x : α, hx : x ∈ l ⊢ A x` |

**R4 · `of_decide_eq_true`** **closes** `⊢ p` from `h : decide p = true`. The lemma is
`of_decide_eq_true {p : Prop} [Decidable p] : decide p = true → p`. Placeholders:
`(p : Prop) [Decidable p] (h : decide p = true)`. Use: `exact of_decide_eq_true h`.

| Before | After |
|---|---|
| `h : decide p = true ⊢ p` | no goals |

**R5 · `decide_eq_true`** **closes** `⊢ decide p = true` from `hp : p`. The lemma is
`decide_eq_true {p : Prop} [Decidable p] : p → decide p = true`. Placeholders: `(p : Prop) [Decidable p] (hp : p)`.

| Before | After |
|---|---|
| `hp : p ⊢ decide p = true` | no goals |

**W1: the whole route on `allEven`** (whose test is `==`, so R8 replaces R4/R5). R1, R2, R3, then
`beq_iff_eq.mp (h x hx)` and `beq_iff_eq.mpr (h x hx)`:

```lean-goal
⊢ allEven xs = true ↔ ∀ (x : Nat), x ∈ xs → x % 2 = 0
⊢ (xs.all fun x => x % 2 == 0) = true ↔ ∀ (x : Nat), x ∈ xs → x % 2 = 0
⊢ (∀ (x : Nat), x ∈ xs → (x % 2 == 0) = true) ↔ ∀ (x : Nat), x ∈ xs → x % 2 = 0
⊢ x % 2 = 0
⊢ (x % 2 == 0) = true
```

## Part 2 · `decide_lt`

Statement: `decide (n < n + 1) = true`. The Bool test of a true Prop is `true`. R5 reduces it to a proof
of `n < n + 1`, which is a core lemma (R6). You may not run the test (`decide` is banned); you prove it.

**R6 · `Nat.lt_add_one`** **closes** `⊢ n < n + 1`. The lemma is `Nat.lt_add_one (n : Nat) : n < n + 1`
(`n` explicit). Placeholders: `(m : Nat)`.

| Before | After |
|---|---|
| `⊢ m < m + 1` | no goals |

**W2:** `decide (m ≤ m + 2) = true` is `decide_eq_true` applied to `Nat.le_add_right m 2 : m ≤ m + 2`:

```lean-goal
⊢ decide (m ≤ m + 2) = true
```

## Part 3 · `and_true_iff`

Statement: `(a && b) = true ↔ a = true ∧ b = true`. Bool `&&` and Prop `∧` agree. This is one `rw` (R7).

**R7 · `rw [Bool.and_eq_true]`** changes the **goal**. The lemma is
`Bool.and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true)`, an **equation between Props**,
not an `↔`. So `exact Bool.and_eq_true a b` fails on an `↔` goal (`Iff.of_eq` would convert it), while `rw`
works: it rewrites the left side, then tries `rfl`, which closes a goal that has become `X ↔ X`.
Placeholders: `(a b : Bool) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((a && b) = true)` | `⊢ P (a = true ∧ b = true)` |

## Part 4 · `beq_true_iff`

Statement: `(m == n) = true ↔ m = n` for `m n : Nat`. Bool `==` and Prop `=` agree, because `Nat`'s `==` is
lawful. This is exactly the library lemma R8 at `α := Nat`, used as a term.

**R8 · `beq_iff_eq`** changes the **goal** with `rw`, or proves the `↔` as a term. The lemma is
`beq_iff_eq {α} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = true ↔ a = b`. Placeholders:
`{α : Type} [BEq α] [LawfulBEq α] (a b : α) (P : Prop → Prop)`: `[BEq α]` means `α` has an operation `==`,
`[LawfulBEq α]` that `a == b = true` exactly when `a = b`; `Nat`, `Int`, `Bool`, `Char`, `String` meet both.
`.mp : (a == b) = true → a = b`, `.mpr` the converse.

| Before | After |
|---|---|
| `⊢ P ((a == b) = true)` | `⊢ P (a = b)` |

## Part 5 · `coe_bool`

Statement: `(h : b && c) : c = true`. The hypothesis is a Bool used as a Prop, so it is really
`h : (b && c) = true` (R9). Rewrite it into a `∧` (R10) and take the right half (R11).

**R9 · a Bool where a Prop is expected** changes the **context** as it is built: writing `(h : b)` with
`b : Bool` gives `h : b = true`. Lean inserts the coercion `b ↦ (b = true)`, and the infoview shows the
result. Placeholders: `(b : Bool)`.

| Before | After |
|---|---|
| `h : b = true ⊢ b = true` | no goals |

**R10 · `rw [Bool.and_eq_true] at h`** changes the **context**: the same lemma as R7, applied to the
hypothesis `h` instead of the goal. Placeholders: `(a b : Bool) (G : Prop)`.

| Before | After |
|---|---|
| `h : (a && b) = true ⊢ G` | `h : a = true ∧ b = true ⊢ G` |

**R11 · `h.1`, `h.2`** **close** a goal that is one side of `h : A ∧ B` (`And.left h`, `And.right h`).
Placeholders: `(A B : Prop) (h : A ∧ B)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ B` | no goals |

**W3: a nested `&&`.** `(h : a && b && c) : b = true`. The outer `&&` is rewritten first, then the inner one;
`h.1.2` takes the left half, then its right half:

| Step | State |
|---|---|
| start (R9) | `h : (a && b && c) = true ⊢ b = true` |
| R10 | `h : (a && b) = true ∧ c = true ⊢ b = true` |
| R10 again | `h : (a = true ∧ b = true) ∧ c = true ⊢ b = true` |

---

## Traps

- `decide` is banned, as a tactic **and** as a term (the checker matches the word). The lemmas
  `decide_eq_true` and `of_decide_eq_true` are allowed: their names are different words. Do not try to run
  the test; prove the Prop and convert.
- `Bool.and_eq_true` is an `=` between Props, not an `↔`: `exact` it against an `↔` goal fails; use `rw`
  (R7) or `Iff.of_eq`.
- `simp` is banned, so nothing evaluates `xs.all …` or `&&` for you: every Bool → Prop step is a named lemma.
- `(h : b && c)` reads like a Prop, but its type is `(b && c) = true`; `h.2` does not work until R10 turns
  it into an `∧`.
- `==` (Bool) and `=` (Prop) are different: `(m == n) = true` is a statement about a Bool, `m = n` about
  numbers. R8 converts.
- `rw` needs the left side literally: `Bool.and_eq_true` rewrites `(a && b) = true`, not a bare `a && b`
  that is not compared with `true`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see a definition's body | `unfold allPos` | R1 |
| `l.all f = true` → `∀ x, x ∈ l → f x = true` | `rw [List.all_eq_true]` | R2 |
| prove `(∀ x ∈ l, A x) ↔ (∀ x ∈ l, B x)` | `⟨fun h x hx => …, fun h x hx => …⟩` | R3 |
| `p` from `h : decide p = true` | `of_decide_eq_true h` | R4 |
| `decide p = true` from `hp : p` | `decide_eq_true hp` | R5 |
| `n < n + 1` | `Nat.lt_add_one n` | R6 |
| `(a && b) = true` ↔ `a = true ∧ b = true` | `rw [Bool.and_eq_true]` | R7 |
| `(a == b) = true ↔ a = b` | `beq_iff_eq` (`.mp`, `.mpr`) | R8 |
| what `(h : b)` means for `b : Bool` | `h : b = true` | R9 |
| `&&` in a hypothesis → `∧` | `rw [Bool.and_eq_true] at h` | R10 |
| one side of `h : A ∧ B` | `h.1`, `h.2` | R11 |
| see the state | infoview | |
