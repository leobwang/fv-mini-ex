# M047 · Liveness analysis for straight-line code: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular induction on lists (E015), inductive types and
pattern-matching definitions (E018), `simp`, `<;>`, anonymous functions. **New here:** *liveness analysis*
(a backward dataflow analysis), an *agreement lemma* (an expression only reads its own variables) proved as
your own milestone, induction on a program with `generalizing` so the IH works for the updated states,
splitting on `y = x` for a point update, and the core list lemmas `List.mem_append`, `List.mem_filter`.
Core Lean only, no Mathlib.

The guide never uses the exercise's objects. It uses toy environments `Env := Nat → Int`, toy expressions
`Tm` = `lit n | var x | neg t | add t u` with value `ev s t` and variable list `vars t`, a point update
`set s x v` shaped like `update`, and toy programs `List (Nat × Int)` of constant assignments run front to
back by `runAll`.

**The property.** A program `p` is a list of assignments `x := a`; `exec p s` runs it from state `s`.
`live p L` walks `p` backwards: for `x := a` it drops `x` from what is live after the assignment (its old
value is overwritten) and adds every variable of `a` (they are read). Soundness: if two initial states
`s1, s2` agree on every variable in `live p L`, the final states agree on every variable in `L`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `{α β : Type}` are arbitrary types; `(Q : Nat → Prop)` is any statement about a variable name.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `State` | `Nat → Int`: variable `x` has value `s x`. An `abbrev`, so it unfolds freely |
| `Prog` | `List (Nat × AExp)`: the assignments `x := a`, first one first |
| `aeval s a` | the value of expression `a` in state `s` |
| `fv a` | the list of variables occurring in `a` (with repeats) |
| `update s x v` | `s` with `x` now holding `v`: `fun y => if y = x then v else s y` |
| `exec ((x, a) :: p) s` | run `x := a`, then `p`; computes to `exec p (update s x (aeval s a))` |
| `live ((x, a) :: p) L` | computes to `List.filter (fun x_1 => decide (x_1 ≠ x)) (live p L) ++ fv a` |
| `∀ (y : Nat), y ∈ l → Q y` | how Lean prints the bounded `∀ y ∈ l, Q y` |
| `List.filter (fun x_1 => decide (x_1 ≠ x)) l` | `l.filter (· ≠ x)`: the elements of `l` other than `x`; `x_1` is the bound variable, renamed because `x` is taken |
| `decide c` | the `Bool` value of a decidable proposition `c`; `List.filter` needs a `Bool` test |
| `exec p s1 y` | `(exec p s1) y`: the value of variable `y` in the final state after running `p` from `s1` |
| `AExp.num n`, `.num n` | the constructor `num` of `AExp` applied to `n`; `.num n` (leading dot) is the short form Lean accepts when the expected type `AExp` is known |
| `a.plus b` | `AExp.plus a b` (dot notation) |
| `if True then v else s y` | what `simp only [update]` leaves at the updated variable (`y = y` became `True`); `if_pos` removes it (R15) |
| `(x, a) :: p` | the program whose first assignment is `x := a` |
| `case nil`, `case cons` | the two goals of an induction on a list (R8) |
| `case pos`, `case neg` | the goals with `hyx : y = x` and `hyx : ¬y = x` after `by_cases` (R13) |
| `n✝`, `head✝`, `tail_ih✝` | inaccessible names made by Lean; name them in a `with` pattern |
| `y_1` | a bound variable renamed because a hypothesis named `y` now exists (after `subst`, R14) |

---

## Part 1 · `live_sound`

Statement: for every program `p`, list `L` and states `s1 s2`, if `s1` and `s2` agree on `live p L`, then
`exec p s1` and `exec p s2` agree on `L`.

### Milestone first: `aeval_agree`

Every assignment `x := a` stores `aeval s a`, so the main proof needs: two states that agree on `fv a` give
`a` the same value. Prove it as your own lemma **above** `live_sound`, outside the spec regions:
`theorem aeval_agree (a : AExp) (s1 s2 : State) (h : ∀ y ∈ fv a, s1 y = s2 y) : aeval s1 a = aeval s2 a`.
Its proof is an induction on `a` (W1 is the same proof for the toy `Tm`).

**R1 · `induction t`** changes the **goal list and the context**: one goal per constructor of the
expression type, the constructor's arguments added as inaccessible variables, and an induction hypothesis for
every argument that is itself an expression. With `induction a with | num n => … | var x => … | plus a b iha
ihb => … | times a b iha ihb => …` (alternatives indented under `induction`) you name them. Because `h`
mentions `a`, `induction` folds it into each IH: in the exercise `iha` reads
`(∀ (y : Nat), y ∈ fv a → s1 y = s2 y) → aeval s1 a = aeval s2 a`, an implication (R7).
Placeholders: `(P : Tm → Prop) (t : Tm)`.

| Before | After |
|---|---|
| `t : Tm ⊢ P t` | `n✝ : Int ⊢ P (Tm.lit n✝)`, `x✝ : Nat ⊢ P (Tm.var x✝)`, `t✝ : Tm, t_ih✝ : P t✝ ⊢ P t✝.neg`, `t✝ u✝ : Tm, t_ih✝ : P t✝, u_ih✝ : P u✝ ⊢ P (t✝.add u✝)` |

**R2 · `rfl`** **closes** an equation whose two sides compute to the same term after unfolding definitions
on constructors. `aeval s1 (.num n)` and `aeval s2 (.num n)` are both `n`. Placeholders:
`(s1 s2 : Env) (n : Int)`.

| Before | After |
|---|---|
| `⊢ ev s1 (Tm.lit n) = ev s2 (Tm.lit n)` | no goal |

**R3 · `simp [vars]`** **closes** `x ∈ vars (.var x)`: it unfolds `vars` on the constructor to `[x]` and uses
`List.mem_singleton : a ∈ [b] ↔ a = b`. In the `var x` case the goal `aeval s1 (.var x) = aeval s2 (.var x)`
is `s1 x = s2 x` up to unfolding, so `exact h x (by simp [fv])` closes it. Placeholders: `(x : Nat)`.

| Before | After |
|---|---|
| `⊢ x ∈ vars (Tm.var x)` | no goal |

**R4 · `simp only [ev]`** changes the **goal**: a recursive function applied to a constructor becomes the
right side of its defining equation. In the exercise `simp only [aeval]` turns
`aeval s1 (a.plus b) = aeval s2 (a.plus b)` into `aeval s1 a + aeval s1 b = aeval s2 a + aeval s2 b`.
Placeholders: `(s : Env) (t u : Tm)`.

| Before | After |
|---|---|
| `⊢ P (ev s (t.add u))` | `⊢ P (ev s t + ev s u)` |

**R5 · `List.mem_append`** changes the **goal**. The lemma is `a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t`. `simp` uses it
by itself, so `simp [hy]` with `hy : y ∈ l₁` proves `y ∈ l₁ ++ l₂`. Placeholders:
`(y : Nat) (l₁ l₂ : List Nat)`.

| Before | After |
|---|---|
| `⊢ y ∈ l₁ ++ l₂` | `⊢ y ∈ l₁ ∨ y ∈ l₂` |

**R6 · `exact fun y hy => h y (by simp [hy])`** **closes** a bounded `∀` over a smaller list from one over a
larger list. A proof of `∀ y ∈ l₁, Q y` is a function taking `y` and `hy : y ∈ l₁`; feed `h` the membership
in the larger list, proved by R5. In the exercise the larger list is `fv (a.plus b)`, which is `fv a ++ fv b`
after unfolding, so write `by simp [fv, hy]`. Placeholders: `(Q : Nat → Prop) (l₁ l₂ : List Nat)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : Nat), y ∈ l₁ → Q y` (with `h : ∀ y ∈ l₁ ++ l₂, Q y`) | no goal |

**R7 · `rw [ih hq]`** changes the **goal**: an IH with a premise, `ih : Q → f s1 = f s2`, becomes an equation
once applied to a proof `hq : Q`, and `rw` uses it left to right. Build `hq` in place with R6:
`rw [iha fun y hy => h y (by simp [fv, hy])]`. After rewriting both IHs, `rw` closes the remaining
`aeval s2 a + aeval s2 b = aeval s2 a + aeval s2 b` by `rfl` itself. Placeholders:
`{σ β : Type} (f : σ → β) (s1 s2 : σ) (Q : Prop)`.

| Before | After |
|---|---|
| `ih : Q → f s1 = f s2, hq : Q ⊢ P (f s1)` | `⊢ P (f s2)` |

### The induction over the program

**R8 · `induction l generalizing b`** changes the **goal list and the context**: `b` is put back into the
goal before inducting, so the IH reads `∀ b, …` and can be used at any `b`, not just the original one. In the
exercise write `induction p generalizing s1 s2 with | nil => … | cons xa p ih => …`. The hypothesis `h`
depends on `s1 s2`, so it is generalized too, and the IH becomes
`ih : ∀ (s1 s2 : State), (∀ (y : Nat), y ∈ live p L → s1 y = s2 y) → ∀ (y : Nat), y ∈ L → exec p s1 y = exec p s2 y`.
Placeholders: `{α β : Type} (P : List α → β → Prop) (l : List α) (b : β)`.

| Before | After |
|---|---|
| `l : List α, b : β ⊢ P l b` | `b : β ⊢ P [] b`, `head✝ : α, tail✝ : List α, b : β ⊢ P (head✝ :: tail✝) b` (with `tail_ih✝ : ∀ b, P tail✝ b`) |

**R9 · `exact h`** **closes** a goal that equals the type of `h` after unfolding definitions on constructors.
In the `nil` case `live [] L` is `L` and `exec [] s` is `s`, so the goal
`∀ (y : Nat), y ∈ L → exec [] s1 y = exec [] s2 y` is `h` itself. Placeholders: `(s : Env) (P : Env → Prop)`.

| Before | After |
|---|---|
| `h : P s ⊢ P (runAll [] s)` | no goal |

**R10 · `obtain ⟨x, a⟩ := xa`** changes the **context**: a pair `xa` is replaced by its two components, and
the goal mentions `(x, a)`. Do it first in the `cons` case, so that `exec ((x, a) :: p) s1` and
`live ((x, a) :: p) L` show their unfolded forms with names you can use. Placeholders:
`{α β : Type} (P : α × β → Prop) (xa : α × β)`.

| Before | After |
|---|---|
| `xa : α × β ⊢ P xa` | `x : α, a : β ⊢ P (x, a)` |

**R11 · `apply ih`** changes the **goal**: the goal must match the conclusion of `ih` after unfolding, and it
becomes `ih`'s premise. `exec ((x, a) :: p) s1` computes to `exec p (update s1 x (aeval s1 a))`, so Lean picks
`s1 := update s1 x (aeval s1 a)` (and likewise `s2`) in the generalized IH. In the exercise the new goal is
`∀ (y : Nat), y ∈ live p L → update s1 x (aeval s1 a) y = update s2 x (aeval s2 a) y`.
Placeholders: `(q : List (Nat × Int)) (x : Nat) (v : Int) (s : Env) (P Q : Env → Prop)`.

| Before | After |
|---|---|
| `⊢ P (runAll ((x, v) :: q) s)` (with `ih : ∀ s, Q s → P (runAll q s)`) | `⊢ Q (set s x v)` |

**R12 · `intro y hy`** changes the **context and the goal**: a bounded `∀` gives a variable and its membership
hypothesis. Placeholders: `(Q : Nat → Prop) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ ∀ (y : Nat), y ∈ l → Q y` | `y : Nat, hy : y ∈ l ⊢ Q y` |

**R13 · `by_cases hyx : y = x`** changes the **goal list**: two copies of the goal, `case pos` with
`hyx : y = x` and `case neg` with `hyx : ¬y = x`. Is `y` the variable just assigned? Placeholders:
`(P : Nat → Nat → Prop) (x y : Nat)`.

| Before | After |
|---|---|
| `x y : Nat ⊢ P x y` | `hyx : y = x ⊢ P x y`, `hyx : ¬y = x ⊢ P x y` |

**R14 · `subst hyx`** changes the **context and the goal**: `hyx : y = x` is used up, `x` disappears, and
every `x` becomes `y` (in `h` too, whose bound `y` is renamed `y_1`). Placeholders:
`(P : Nat → Nat → Prop) (x y : Nat)`.

| Before | After |
|---|---|
| `x y : Nat, hyx : y = x ⊢ P x y` | `y : Nat ⊢ P y y` |

**R15 · `simp only [set, if_pos]`** changes the **goal**: at the updated variable the update returns the new
value. `set s y v y` unfolds to `if y = y then v else s y`; `simp only` rewrites `y = y` to `True` by itself,
and `if_pos : c → (if c then t else e) = t` (its premise `True` proved by `simp`) keeps the `then` branch. In
the exercise `simp only [update, if_pos]` leaves `aeval s1 a = aeval s2 a`: close it with the milestone,
`aeval_agree a s1 s2 (fun z hz => h z (by simp [live, hz]))`, since every variable of `a` is live (R5, R6).
Placeholders: `(s : Env) (y : Nat) (v : Int)`.

| Before | After |
|---|---|
| `⊢ P (set s y v y)` | `⊢ P v` |

**R16 · `simp only [set, if_neg hyx]`** changes the **goal**: away from the updated variable the update returns
the old value. The lemma is `if_neg : ¬c → (if c then t else e) = e`. In the exercise it leaves `s1 y = s2 y`,
which is `h y _` once you show `y ∈ live ((x, a) :: p) L` (R17). Placeholders:
`(s : Env) (x y : Nat) (v : Int) (hyx : ¬y = x)`.

| Before | After |
|---|---|
| `hyx : ¬y = x ⊢ P (set s x v y)` | `⊢ P (s y)` |

**R17 · `List.mem_filter`** changes the **goal**. The lemma is `a ∈ l.filter p ↔ a ∈ l ∧ p a = true`. Here
`p` is `fun x_1 => decide (x_1 ≠ x)`, so the second half is `decide (y ≠ x) = true`, which `simp` turns into
`y ≠ x` (`decide_eq_true_eq`). The membership `y ∈ live ((x, a) :: p) L` is one `simp` call that unfolds
`live` and uses R5, R17 with `hy : y ∈ live p L` and `hyx : ¬y = x` (W3). Placeholders:
`(x y : Nat) (l : List Nat)`.

| Before | After |
|---|---|
| `⊢ y ∈ List.filter (fun x_1 => decide (x_1 ≠ x)) l` | `⊢ y ∈ l ∧ decide (y ≠ x) = true` |

### Worked combinations (toy objects)

**W1.** `ev_agree` for the toy `Tm` by `induction t with`: `lit` by R2, `var` by `exact h x (by simp [vars])`
(R3), `neg` and `add` by R4 and then R7 with R6.

**W2.** Two updates of `x` with the same value agree wherever the old states agree off `x`: R12, R13, then
R14 with R15, and R16. The goal in both branches of `by_cases`:

```lean-goal
⊢ set s1 x v y = set s2 x v y
```

**W3.** Membership in `filter … ++ …` in one call, `simp [List.mem_filter, hy, hyx]` (R5, R17):

```lean-goal
⊢ y ∈ List.filter (fun x_1 => decide (x_1 ≠ x)) l ++ m
```

**W4.** `runAll q s z = s z` when no assignment of `q` writes `z`: R8 (`generalizing s`, named
alternatives), R10, R7, R16.

---

## Traps

- Without `generalizing s1 s2`, the IH talks about the original `s1 s2` only, and `apply ih` fails in the
  `cons` case: there the states are `update s1 x (aeval s1 a)` and `update s2 x (aeval s2 a)`.
- Declare the milestone `aeval_agree` above `live_sound` and outside the spec regions; a declaration can only
  use earlier ones.
- `induction … with` alternatives are indented under `induction`, and each must close its goal.
- The IHs of `aeval_agree` are implications (`(∀ y ∈ fv a, …) → …`), not equations: `rw [iha]` alone fails;
  give it the premise (R7).
- `simp only [update]` alone stops at `if True then … else …`; add `if_pos` (R15).
- After `subst hyx`, `x` is gone: write `y` for it, and `h` now reads `live ((y, a) :: p) L`.
- `live` over-approximates: it adds `fv a` even when `x` is not live. The proof never needs the case `x ∉ L`;
  it only needs "every variable of `a` is live before `x := a`".
- `simp` needs `live` (or `fv`) in its list to see the `++` and `filter` inside a membership goal.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on an expression, named | `induction a with \| num n => … \| var x => … \| plus a b iha ihb => … \| times a b iha ihb => …` | R1 |
| `num` case | `rfl` | R2 |
| `x ∈ fv (.var x)` | `by simp [fv]` | R3 |
| unfold `aeval` on a constructor | `simp only [aeval]` | R4 |
| `y ∈ l₁ ++ l₂` from `hy : y ∈ l₁` | `by simp [hy]` (`List.mem_append`) | R5 |
| shrink a bounded `∀` | `fun y hy => h y (by simp [fv, hy])` | R6 |
| rewrite with an IH that has a premise | `rw [iha (fun y hy => …)]` | R7 |
| induction on the program, IH for all states | `induction p generalizing s1 s2 with \| nil => … \| cons xa p ih => …` | R8 |
| `nil` case | `exact h` | R9 |
| split the assignment | `obtain ⟨x, a⟩ := xa` | R10 |
| use the IH on the updated states | `apply ih` | R11 |
| open the bounded `∀` | `intro y hy` | R12 |
| is `y` the assigned variable? | `by_cases hyx : y = x` | R13 |
| replace `x` by `y` | `subst hyx` | R14 |
| `update s x v x` → `v` | `simp only [update, if_pos]` | R15 |
| `update s x v y` → `s y` for `y ≠ x` | `simp only [update, if_neg hyx]` | R16 |
| membership in `filter … ++ …` | `simp [live, List.mem_filter, hy, hyx]` | R17 |
| see the state | infoview | |
