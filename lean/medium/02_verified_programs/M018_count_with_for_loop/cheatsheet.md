# M018 · Count with a for loop: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching on lists, `if … then … else`,
`theorem`, `induction xs with | nil => … | cons x xs ih => …` (E015), `simp`, `rw`, `omega` (E011). M015 uses
the same idea (generalise the accumulator) for a hand-written accumulator; this guide does not rely on it.
**New here:** imperative `do` notation (`Id.run`, `let mut`, `for … in … do`, `return`; see *Reading the
goals*), how a pure `for` loop unfolds into `List.foldl` (core lemma `List.forIn_pure_yield_eq_foldl`), the
two equations of `List.foldl`, and `induction … generalizing`. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : β → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- Placeholders are written as Lean binders. `{α β : Type}` are any types (`Nat` in the exercise).
- `F : List Nat → Nat → Nat` and `G : List Nat → Nat` (R4, R6) are placeholder functions: read `F xs c` as
  "the fold over `xs` started at `c`" and `G xs` as "the recursive specification of `xs`".
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Id.run do …` | a pure function written in imperative style: `Id` is the monad with no effects, `Id.run` takes its value |
| `let mut c := 0` / `c := e` | a local variable and its update; Lean compiles them away into argument passing |
| `for x in xs do body` | runs `body` once per element of `xs`, left to right, threading the `let mut` variables |
| `List.foldl f b xs` | left fold: `f (… (f (f b x₁) x₂) …) xₙ` for `xs = [x₁, …, xₙ]`; `b` is the start value. `xs.foldl f b` is the same term |
| `fun b a => b + g a` | the fold's step function: `b` is the accumulator (the loop variable), `a` the current element |
| `if a = k then 1 else 0` | a `Nat` that is `1` when `a = k` and `0` otherwise (`a = k` on `Nat` is decidable) |
| `c + if a = k then 1 else 0` | `c + (if a = k then 1 else 0)`: an `if` reaches as far right as it can, so Lean drops these parentheses. Hence `(c + if x = k then 1 else 0) + count k xs` is `(c + (if x = k then 1 else 0)) + count k xs` |
| `return c` | the value of the `do` block: the final value of the loop variable |
| `ih : ∀ (c : Nat), …` | the induction hypothesis after `generalizing c`: it holds for every start value `c` (R4) |
| `case nil`, `case cons` | the two goals made by `induction` on a list |
| `head✝`, `tail✝`, `tail_ih✝` | names `induction` made up because you gave none; `✝` means you cannot type them. Use `with \| cons x xs ih` to name them |

---

## Part 1 · `countLoop_spec`

Statement: `countLoop k xs = count k xs`: the loop and the recursive function count the occurrences of `k`
in `xs` in the same way.

The plan: R1 turns the loop into a fold from `0`. Induction on `xs` with the start value fixed at `0` fails
(the `cons` step changes the start value, R3), so first prove a helper theorem (the milestone) about the fold
from an arbitrary start value `c`, by R4. Then use it at `c := 0` (R6, R8).

### From the loop to a fold

**R1 · `simp [f]` on a `for` loop** changes the **goal**: `f` is unfolded, and the pure loop becomes a
`List.foldl`. The loop variable becomes the accumulator `b`, the loop element the argument `a`, and the
initial value (`0`) the start value. `simp?` names the lemmas: `List.forIn_pure_yield_eq_foldl` (the loop
itself), `bind_pure`, `Id.run_pure` (the `do`/`return` around it). Placeholders: `(g : Nat → Nat) (xs : List Nat)`,
the guide's loop `stepLoop g xs`, which runs `s := s + g x` from `s = 0`.

| Before | After |
|---|---|
| `⊢ P (stepLoop g xs)` | `⊢ P (List.foldl (fun b a => b + g a) 0 xs)` |

**R2 · `List.foldl_nil`** changes the **goal**: `List.foldl f b [] = b`. Placeholders:
`{α β : Type} (f : β → α → β) (b : β)`.

| Before | After |
|---|---|
| `⊢ P (List.foldl f b [])` | `⊢ P b` |

**R3 · `List.foldl_cons`** changes the **goal**: `List.foldl f b (a :: l) = List.foldl f (f b a) l`. The head is
absorbed into the accumulator, so the start value changes from `b` to `f b a`. Placeholders:
`{α β : Type} (f : β → α → β) (b : β) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P (List.foldl f b (a :: l))` | `⊢ P (List.foldl f (f b a) l)` |

### The milestone: the fold from any start value

**R4 · `induction xs generalizing c`** changes the **goal list** and the **context**: one goal per constructor
of `List`, and the induction hypothesis is quantified over the start value `c`. Placeholders:
`(F : List Nat → Nat → Nat) (G : List Nat → Nat) (xs : List Nat) (c : Nat)`.

| Before | After |
|---|---|
| `⊢ F xs c = c + G xs` | `c : Nat ⊢ F [] c = c + G []`, `head✝ : Nat, tail✝ : List Nat ⊢ F (head✝ :: tail✝) c = c + G (head✝ :: tail✝)` |

In the `cons` goal the hypothesis is `tail_ih✝ : ∀ (c : Nat), F tail✝ c = c + G tail✝`: it holds for every start
value, so it applies after R3 has changed the start value. Without `generalizing c` (second example in the
guide) it is only about the `c` you started with:

| Before `induction xs` | After, `cons` goal |
|---|---|
| `⊢ F xs c = c + G xs` | `tail_ih✝ : F tail✝ c = c + G tail✝ ⊢ F (head✝ :: tail✝) c = c + G (head✝ :: tail✝)` |

Write `induction xs generalizing c with` and the cases `| nil => …` and `| cons x xs ih => …` on the next lines
to choose the names.

**R5 · `simp only [g]` on a recursive definition** changes the **goal**: it rewrites with the equations of the
pattern-matching `def g`, one constructor at a time. `g (x :: xs)` becomes the right side of the `x :: xs` case,
which still contains `g xs`. Placeholders: the guide's `sumL : List Nat → Nat` (`sumL [] = 0`,
`sumL (x :: xs) = x + sumL xs`), `(x : Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (sumL [])` | `⊢ P 0` |
| `⊢ P (sumL (x :: xs))` | `⊢ P (x + sumL xs)` |

**R6 · `rw [ih]` with a `∀` equation** changes the **goal**: for `ih : ∀ c, F xs c = c + G xs`, Lean finds
`F xs t` in the goal and picks `c := t` itself. The same holds for `simp only [ih]` and for a theorem you
proved (the milestone, used in step 2 of the skeleton). Placeholders: `(F G)` as in R4, `(xs : List Nat) (c a : Nat)`.

| Before | After |
|---|---|
| `⊢ P (F xs (c + a))` | `⊢ P (c + a + G xs)` |
| `⊢ F xs 0 = G xs` | `⊢ 0 + G xs = G xs` |

The second row used `simp only [hF]` with `hF : ∀ ys d, F ys d = d + G ys`: the start value `0` is
substituted for `d`, leaving the `0 +` that R8 removes.

**R7 · `omega`** **closes** the goal when it is linear arithmetic over `Nat` or `Int`: `+`, `-`, numerals,
multiplication by a numeral, `=`, `<`, `≤` and the connectives. Every other subterm, such as `f x`, `count k xs`
or `if p then 1 else 0`, is an unknown number (an *atom*), so regrouping and reordering a sum of atoms is fine.
Placeholders: `(f : Nat → Nat) (x c n a b : Nat)`, `(p : Prop) [Decidable p]` (`p` can be tested, as `a = k`
on `Nat` can).

| Before | After |
|---|---|
| `⊢ c + f x + n = c + (f x + n)` | closed by `omega` |
| `⊢ (a + if p then 1 else 0) + b = (if p then 1 else 0) + (b + a)` | closed by `omega` |

**R8 · `Nat.zero_add`, `Nat.add_zero`** change the **goal**: `0 + n = n` and `n + 0 = n`. `simp` uses both by
itself. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (0 + n)` | `⊢ P n` |
| `⊢ P (n + 0)` | `⊢ P n` |

### Worked combination (W1, on a loop that is not the exercise's)

**W1.** `sumLoop` adds up a list with `s := s + x` from `s = 0`; `sumL` is the recursive sum (R5). The helper
theorem `foldl_sumL` says the fold from any `c` is `c + sumL xs` (R4; `nil`: R2, R5, R8; `cons`: R3, R6, R5,
then R7). The main statement then goes through these goals (R1, R6 with `foldl_sumL`, R8):

```lean-goal
⊢ List.foldl (fun b a => b + a) 0 xs = sumL xs
⊢ 0 + sumL xs = sumL xs
```

---

## Traps

- Induction on the goal right after R1 fails: the start value is the literal `0`, and after R3 the `cons` case
  needs the statement for the start value `0 + …`. State the milestone with a variable start value `c` and
  generalise it (R4).
- Write the milestone's right side as `c + …`, with the start value outside: then `0 + …` at the end is R8.
  With the fold body written exactly as R1 prints it (`fun b a => b + if a = k then 1 else 0`), `simp` can use
  the milestone on the goal R1 leaves.
- `simp only [count]` unfolds only one equation (R5); in the `cons` case it leaves `count k xs` for the tail,
  which is what the induction hypothesis talks about.
- `omega` does not unfold definitions: unfold first (R3, R5, R6), then close with `omega` (R7).
- `t1; t2` runs `t2` on the first goal `t1` leaves (TACTIC_STATES, "Structure"). Inside one `| cons … =>`
  case that is the case's own goal, so `simp only [...]; omega` works there.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| loop → fold | `simp [f]` (`simp?` to see the lemmas) | R1 |
| fold over `[]` | `List.foldl_nil` | R2 |
| fold over `a :: l` (start value changes) | `List.foldl_cons` | R3 |
| induction with `ih` for every start value | `induction xs generalizing c with \| nil => … \| cons x xs ih => …` | R4 |
| unfold one equation of a recursive `def` | `simp only [g]` | R5 |
| use `ih` or your own `∀` theorem | `rw [ih]`, `simp only [ih]`, `simp [f, myLemma]` | R6 |
| linear arithmetic, atoms included | `omega` | R7 |
| `0 + n`, `n + 0` | `Nat.zero_add`, `Nat.add_zero` (or `simp`) | R8 |
| see the state | infoview | |
