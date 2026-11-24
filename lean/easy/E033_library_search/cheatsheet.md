# E033 · Library search: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E032, in particular `exact` and `apply` (E003), term-mode proofs (E004), `rw`
(E009), `have` (E021), implicit arguments `{…}` and `#check @L` (E023), and how list-library names follow the
shape of a statement (E024). **New here:** finding a lemma instead of proving the fact yourself. `exact?`
searches the library for a lemma that closes the goal; `apply?` searches for one that at least matches the
goal's conclusion; `#check` prints a lemma's statement so you can see which arguments to pass and in which
order. Four core lemmas: `List.length_reverse`, `Nat.le_of_dvd`, `List.reverse_append`, `Nat.mod_lt`. No
Mathlib. `simp`, `simp_all`, `omega`, `grind` and `decide` are banned: each goal must be closed by naming the
lemma.

## How to read an entry

Each entry is one tactic, one command or one lemma. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : List α → Prop`). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal. `G : Prop` is any goal the step does not look at.
- `{α : Type}` is any type of list elements (`Nat`, `Bool`, …). `#check` prints it as `{α : Type u_1}`: `u_1`
  is a *universe* variable, which only says the lemma works for types of every size; ignore it.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `a ∣ b` | `a` divides `b`: `∃ c, b = a * c`. The symbol is `∣` (typed `\mid`), not the ASCII vertical bar |
| `a % b` | remainder of `a` divided by `b` (`Nat`); `a % 0 = a` |
| `0 < b` | `b` is positive; for `Nat` the same as `b ≠ 0` |
| `xs.reverse` | `List.reverse xs`, the list in reverse order |
| `xs.reverse.length` | `(List.reverse xs).length`: dot notation chains left to right |
| `xs ++ ys` | `List.append xs ys`: `xs` followed by `ys` |
| `(xs ++ ys).reverse` | reverse of the appended list; the parentheses matter |
| `Try this: exact L a b` | output of `exact?`/`apply?`; the line to paste in place of the search tactic |
| `[apply] exact …` | the same suggestion; `[apply]` names the search strategy that found it |
| `-- Remaining subgoals:` | below an `apply?` suggestion that does not close the goal: the goals it leaves open, one per comment line |

**Library names** describe the statement, outermost function first: `List.length_reverse` is "length of a
reverse", `List.reverse_append` "reverse of an append". `Nat.le_of_dvd` reads "`≤` from `∣`": `of` separates
the conclusion (before) from the hypothesis (after). `Nat.mod_lt` is "`%` is `<`". The namespace (`List.`,
`Nat.`) is the type the statement is about.

---

## The search tools

**R1 · `exact?`** **closes** the goal and changes the **goal list**: it searches all lemmas in scope for one
whose conclusion matches the goal, fills the lemma's hypotheses from the context, and prints the proof it
found. Replace `exact?` by that line: the search is slow, and a final proof should not depend on it.
Placeholders: `(n : Nat) (h : n ≠ 0)`.

| Before | After | Infoview message |
|---|---|---|
| `h : n ≠ 0 ⊢ 0 < n` | no goals | `Try this: [apply] exact Nat.zero_lt_of_ne_zero h` |

If `exact?` finds nothing, it fails with an error and the goal stays open.

**R2 · `#check L`** changes **nothing**: it is a command, written outside any proof, and prints `L`'s statement.
Without `@` it shows the binders with their names; `#check @L` shows the fully explicit form (E023).

| Write | Infoview shows |
|---|---|
| `#check Nat.zero_lt_of_ne_zero` | `Nat.zero_lt_of_ne_zero {a : Nat} (h : a ≠ 0) : 0 < a` |

So `Nat.zero_lt_of_ne_zero h` proves `0 < n` from `h : n ≠ 0`, and `a := n` is inferred.

**R3 · `apply L`** changes the **goal list**: `L`'s conclusion is matched against the goal, and the goal is
replaced by one goal per hypothesis of `L` that the match does not fill. `apply?` prints suggestions in this form, written as `refine L ?_ ?_` (each `?_` is
one new goal) followed by the remaining subgoals as `-- ⊢ …` comments. The example uses
`Nat.mul_le_mul {n₁ m₁ n₂ m₂ : Nat} (h₁ : n₁ ≤ n₂) (h₂ : m₁ ≤ m₂) : n₁ * m₁ ≤ n₂ * m₂`. Placeholders:
`(a b c d : Nat) (h₁ : a ≤ b) (h₂ : c ≤ d)`.

| Before | After |
|---|---|
| `⊢ a * c ≤ b * d` | `⊢ a ≤ b`, `⊢ c ≤ d` |

The exercise does not need `apply?`: every goal there is closed by one lemma, which `exact?` finds directly.

---

## Part 1 · `len_rev`

Statement: `xs.reverse.length = xs.length`: reversing keeps the length. One lemma, all arguments implicit, so
its bare name is the whole proof.

**R4 · `List.length_reverse`** changes the **goal** when used with `rw`, and **closes** a goal that is
exactly its statement when used with `exact` or as a term. The lemma is
`List.length_reverse {α : Type} {as : List α} : as.reverse.length = as.length`. Placeholders:
`{α : Type} (l : List α)`.

| Before | After `rw [List.length_reverse]` |
|---|---|
| `⊢ P l.reverse.length` | `⊢ P l.length` |

**W1 (with a second rewrite):** `(l ++ l').reverse.length = l.length + l'.length` by R4 then
`rw [List.length_append]` (E024), which also closes the goal:

```lean-goal
⊢ (l ++ l').reverse.length = l.length + l'.length
⊢ (l ++ l').length = l.length + l'.length
```

---

## Part 2 · `dvd_le`

Statement: from `h : a ∣ b` and `hb : 0 < b`, conclude `a ≤ b`: a divisor of a positive number is at most
that number. (Positivity is needed: every `a` divides `0`.) One lemma with two explicit hypotheses; the
order of the arguments is the lemma's, not the theorem's.

**R5 · `Nat.le_of_dvd`** changes the **context** when used with `have`; as a term,
`Nat.le_of_dvd hn hd : m ≤ n` proves the goal directly. The lemma is
`Nat.le_of_dvd {m n : Nat} (h : 0 < n) : m ∣ n → m ≤ n`: positivity first, divisibility second. Placeholders:
`(m n : Nat) (hn : 0 < n) (hd : m ∣ n)`.

| Before | After `have h := Nat.le_of_dvd hn hd` |
|---|---|
| `⊢ G` | `h : m ≤ n ⊢ G` |

---

## Part 3 · `rev_app`

Statement: `(xs ++ ys).reverse = ys.reverse ++ xs.reverse`: reversing an append reverses each part and swaps
them. One lemma, all arguments implicit.

**R6 · `List.reverse_append`** changes the **goal** with `rw`, and **closes** a goal that is exactly its
statement with `exact` or as a term. The lemma is
`List.reverse_append {α : Type} {as bs : List α} : (as ++ bs).reverse = bs.reverse ++ as.reverse`.
Placeholders: `{α : Type} (l l' : List α)`.

| Before | After `rw [List.reverse_append]` |
|---|---|
| `⊢ P (l ++ l').reverse` | `⊢ P (l'.reverse ++ l.reverse)` |

---

## Part 4 · `mod_lt_of_pos`

Statement: from `hb : 0 < b`, conclude `a % b < b`: a remainder is smaller than a positive divisor. One lemma
with one explicit number and one explicit hypothesis.

**R7 · `Nat.mod_lt`** changes the **context** with `have`; as a term, `Nat.mod_lt x hy : x % y < y` proves the
goal directly. The lemma is `Nat.mod_lt (x : Nat) {y : Nat} (hy : 0 < y) : x % y < y`. `y` is implicit because
`hy` determines it; `x` occurs in no hypothesis, so the library makes it explicit and it comes first.
Placeholders: `(x y : Nat) (hy : 0 < y)`.

| Before | After `have h := Nat.mod_lt x hy` |
|---|---|
| `⊢ G` | `h : x % y < y ⊢ G` |

**W2 (a lemma inside a lemma, term mode):** `x % y < z` from `hy : 0 < y` and `hz : y ≤ z` is
`Nat.lt_of_lt_of_le (Nat.mod_lt x hy) hz`, where
`Nat.lt_of_lt_of_le {n m k : Nat} : n < m → m ≤ k → n < k` and R7 supplies its first argument.

**W3 (`exact?` combines hypotheses):** on `h₁ : a ≤ b, h₂ : b ≤ c ⊢ a ≤ c`, `exact?` prints
`Try this: [apply] exact Nat.le_trans h₁ h₂`.

---

## Traps

- `Nat.le_of_dvd h hb` is a type error: the lemma wants `0 < n` first. Read the order off `#check` (R2) or let
  `exact?` write the call.
- `Nat.mod_lt hb` is a type error: the first explicit argument is the number `x`, not the hypothesis. Write
  `Nat.mod_lt a hb`.
- The divides symbol is `∣` (`\mid`). Typing the ASCII vertical bar instead gives a parse error.
- Leave no `exact?` in a finished proof: replace it by its `Try this` line. It is slow and its answer can
  change when the library changes.
- `apply?` that finds no complete proof still "succeeds": it prints a long list of `refine …` suggestions and
  closes the goal with `sorry` (warning "declaration uses `sorry`"). Pick a suggestion whose remaining
  subgoals you can prove, paste it, and prove those goals.
- `exact?` only uses lemmas that are imported. In a file without `import Mathlib` it searches the core library
  only, which is enough here.
- In term mode the lemma name replaces `sorry` directly (`:= List.length_reverse` style); in tactic mode write
  `by exact List.length_reverse`. Both are the same proof.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| find a lemma that closes the goal | `exact?` | R1 |
| see a lemma's statement and argument order | `#check L`, `#check @L` | R2 |
| find a lemma that matches, leaving side goals | `apply?`; it suggests `refine L ?_ ?_` | R3 |
| use a lemma whose hypotheses become goals | `apply L` | R3 |
| `l.reverse.length = l.length` | `List.length_reverse` | R4 |
| `m ≤ n` from `0 < n` and `m ∣ n` | `Nat.le_of_dvd hn hd` | R5 |
| `(l ++ l').reverse = l'.reverse ++ l.reverse` | `List.reverse_append` | R6 |
| `x % y < y` from `0 < y` | `Nat.mod_lt x hy` | R7 |
| `n < k` from `n < m` and `m ≤ k` | `Nat.lt_of_lt_of_le` | W2 |
| see the state | infoview | |
