# M038 · Constant folding: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, pattern-matching definitions, `induction`,
`exact`, `rw`, `simp`, `rfl`, `<;>`, writing your own helper `theorem`. **New here:** opening a definition
whose body is a multi-argument `match` (`unfold`) and splitting it into one goal per arm (`split`), with
the "earlier arm did not match" hypotheses this produces; correctness of a *smart constructor* as a
lemma of its own, used by `simp` inside the main induction. Core Lean only, no Mathlib.

## The objects

- `Expr`: arithmetic expressions `num n`, `var i`, `plus a b`, `times a b` over `Nat`.
  `eval env : Expr → Nat` is their value when variable `i` has value `env i` (`env : Nat → Nat` is the
  *environment*).
- `mkPlus a b`, `mkTimes a b`: *smart constructors*. They build `plus a b` / `times a b` but simplify on the
  way: two numerals are added (multiplied), `num 0` is dropped from a sum, `num 0` absorbs a product,
  `num 1` is dropped from a product. Arms are tried top to bottom; the last one is the plain constructor.
- `fold`: rebuilds `plus`/`times` bottom-up with the smart constructors; `num` and `var` are left alone.
- The theorems: `fold_correct` (`eval env (fold e) = eval env e` for every `env` and `e`) and
  `fold_example` (one concrete `fold` result).

## How to read an entry

Each entry is one tactic or one proof move. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P` is "the rest of your goal" (`P : Nat → Prop` or `P : BExp → Prop`). The step changes only the part
  inside `P (…)`.
- Entries use the guide's toy objects, **not** `Expr`: `clip : Nat → Nat → Nat` (arms `0, m => m`,
  `n, 0 => n`, `n, m => n + m`); Boolean formulas `BExp` (`tt`, `ff`, `atom i`, `and p q`) with value
  `bval ρ : BExp → Bool` (`ρ : Nat → Bool` gives each atom a value; `bval ρ (and p q) = bval ρ p && bval ρ q`);
  the smart constructor `mkAnd` (`ff` absorbs, `tt` is dropped, shaped like `mkTimes`) and the simplifier
  `simpB` (shaped like `fold`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `.plus a b`, `.num 5` (source) | leading-dot constructor: `Expr.plus a b`, `Expr.num 5`, with `Expr` read off the expected type |
| `a.plus b`, `(Expr.num 0).plus b`, `((Expr.num 1).times (Expr.var 0)).plus …` | `Expr.plus a b` etc.: Lean prints `Expr.plus x y` as `x.plus y` because `x : Expr` (*dot notation*: the first explicit argument moves in front). Same for `p.and q` and `BExp.tt.and q` (= `BExp.and BExp.tt q`) in the toy |
| `Expr.num 0` | the numeral `0` as an expression (no dot form: the argument is a `Nat`) |
| `match a, b with` followed by arms | the body of `mkPlus`/`mkTimes` after `unfold` (R1); arms are tried top to bottom |
| `case h_1`, `case h_2`, … | after `split` (R2): the goal for arm 1, arm 2, … of that `match` |
| `x✝ : ∀ (b_1 : Nat), b = Expr.num b_1 → False` | an earlier arm did **not** fire: `b` is not of the form `num _`. `b_1` is a renamed bound variable |
| `x✝² : a = Expr.num 0 → False` | `a ≠ num 0` (`¬ A` is `A → False`): the arm with pattern `num 0` did not fire |
| `x✝ : ∀ (a_1 b_1 : Nat), a = Expr.num a_1 → b = Expr.num b_1 → False` | in the last arm: the first arm (`num _, num _`) did not fire, i.e. `a`, `b` are not both numerals |
| `x✝¹ x✝ : Expr` (unused) | leftover copies of the two matched values; ignore them |
| `a✝ b✝ : Nat` | *inaccessible* names: pattern variables of the arm (`num a, num b`). You cannot type them; you do not need to |
| `iha : eval env (fold a) = eval env a` | the induction hypothesis for the left argument of `plus a b` (R4) |
| `x && y` (toy) | Boolean and |

---

## Part 1 · `fold_correct`

Statement: for every environment `env` and expression `e`, `eval env (fold e) = eval env e`. `fold` does all
its work through `mkPlus`/`mkTimes`, so prove first, as your own helper theorems above `fold_correct`
(milestones), that each smart constructor keeps the value:

- `eval env (mkPlus a b) = eval env a + eval env b`
- `eval env (mkTimes a b) = eval env a * eval env b`

Then induct on `e` and use them.

### Milestones: open the smart constructor, one goal per arm

**R1 · `unfold f`** changes the **goal**: the name `f` applied to variables is replaced by its body, here a
`match` on both arguments. `simp only [f]` unfolds it the same way. A tactic that works on a `match`
(R2) cannot see inside `f` before this. Placeholders: `(P : Nat → Prop) (a b : Nat)`, `f := clip`.

```lean-goal
⊢ P (clip a b)
⊢ P (match a, b with | 0, m => m | n, 0 => n | n, m => n + m)
```

In the exercise, `unfold mkPlus` turns `⊢ eval env (mkPlus a b) = …` into
`⊢ eval env (match a, b with | Expr.num a, Expr.num b => Expr.num (a + b) | Expr.num 0, e => e | … ) = eval env a + eval env b`.

**R2 · `split`** changes the **goal list and the context**: one goal per arm of the `match` in the goal. In the
goal for arm `k` (`case h_k`) the matched variables are replaced by that arm's pattern (`a` by `0` here), and
the context gains one hypothesis per earlier arm saying that arm did not match. Placeholders:
`(P : Nat → Prop) (a b : Nat)`.

```lean-goal
⊢ P (match a, b with | 0, m => m | n, 0 => n | n, m => n + m)
```

| Before | After |
|---|---|
| the `match` goal above | `⊢ P b`, `x✝ : a = 0 → False ⊢ P a`, `x✝¹ : a = 0 → False, x✝ : b = 0 → False ⊢ P (a + b)` |

In the exercise `split` after `unfold mkPlus` gives four goals and after `unfold mkTimes` six. For example
arm 2 of `mkPlus` (`.num 0, e => e`):
`x✝ : ∀ (b_1 : Nat), b = Expr.num b_1 → False ⊢ eval env b = eval env (Expr.num 0) + eval env b`.

**R3 · `simp_all [f]`** **closes** an arm goal: it unfolds the equations of `f` where `f` is applied to a
constructor, in the goal and in every hypothesis, then applies the standard simp lemmas for `&&`, `+`, `*`
(`true && x = x`, `x && false = false`, `0 + x = x`, `x * 1 = x`, `0 * x = 0`, …). The "earlier arm did not
match" hypotheses get simplified too and do no harm. Run it on every arm at once: `split <;> simp_all [eval]`.
Placeholders: `(ρ : Nat → Bool) (q : BExp)`; `(g : Nat → Nat) (x : Nat)`.

| Before | After |
|---|---|
| `⊢ bval ρ q = (bval ρ BExp.tt && bval ρ q)` | ∅ (`simp_all [bval]`) |
| `⊢ g x = (0 + g x) * 1` | ∅ (`simp_all`) |

**W1** in the guide is the whole milestone for the toy `mkAnd`: `unfold mkAnd`, then
`split <;> simp_all [bval]`.

### The induction on `e`

**R4 · `induction e with | tt => … | ff => … | atom i => … | and p q ihp ihq => …`** changes the **goal list
and the context**: one goal per constructor of the type, one IH per argument of that same type. In the
exercise: `| num n => … | var i => … | plus a b iha ihb => … | times a b iha ihb => …`, with
`iha : eval env (fold a) = eval env a`. Placeholders: `(P : BExp → Prop) (e : BExp)`.

| Before | After |
|---|---|
| `e : BExp ⊢ P e` | `⊢ P BExp.tt`, `⊢ P BExp.ff`, `i : Nat ⊢ P (BExp.atom i)`, `ihp : P p, ihq : P q ⊢ P (p.and q)` |

**R5 · `rfl`** **closes** an equation whose two sides compute to the same term. `simpB (BExp.atom i)` falls
into the catch-all arm `p => p`, so it *is* `BExp.atom i`; likewise `fold (.num n)` is `.num n` and
`fold (.var i)` is `.var i`. A closed term (no variables) is computed all the way, which is how
`fold_example` goes. Placeholders: `(ρ : Nat → Bool) (i : Nat)`.

| Before | After |
|---|---|
| `⊢ bval ρ (simpB (BExp.atom i)) = bval ρ (BExp.atom i)` | ∅ |
| `⊢ simpB (BExp.tt.and ((BExp.atom 3).and BExp.tt)) = BExp.atom 3` | ∅ |

**R6 · `simp [f, L, g, ihp, ihq]`** changes the **goal** (and here closes it). Shown one lemma at a time with
`simp only`: `f`'s equation on the constructor `and` (`simpB (p.and q) = mkAnd (simpB p) (simpB q)`), then
your milestone `L` about the smart constructor, then `g`'s equation (`bval` on `and`), then the IHs; the
final `x = x` closes by `rfl`. One call `simp [simpB, L, bval, ihp, ihq]` does it all. In the exercise:
`f := fold`, `L := ` your `mkPlus` (or `mkTimes`) milestone, `g := eval`, IHs `iha ihb`.
Placeholders: `(ρ : Nat → Bool) (p q : BExp)`,
`(L : ∀ x y, bval ρ (mkAnd x y) = (bval ρ x && bval ρ y))`, `(ihp : bval ρ (simpB p) = bval ρ p)`,
`(ihq : bval ρ (simpB q) = bval ρ q)`.

| Before | After `simp only [simpB]` | After `simp only [L]` | After `simp only [bval]` | After `simp only [ihp, ihq]` |
|---|---|---|---|---|
| `⊢ bval ρ (simpB (p.and q)) = bval ρ (p.and q)` | `⊢ bval ρ (mkAnd (simpB p) (simpB q)) = bval ρ (p.and q)` | `⊢ (bval ρ (simpB p) && bval ρ (simpB q)) = bval ρ (p.and q)` | `⊢ (bval ρ (simpB p) && bval ρ (simpB q)) = (bval ρ p && bval ρ q)` | ∅ |

**W2** in the guide chains R4, R5 and R6 for the toy `simpB`, with W1 as `L`.

---

## Part 2 · `fold_example`

Statement: `fold` of `plus (times (num 1) (var 0)) (plus (num 2) (num 3))` is `plus (var 0) (num 5)`. The term
is closed, so both sides compute: R5, `rfl`.

---

## Traps

- **`split` before `unfold`** fails with ``Tactic `split` failed: Could not split an `if` or `match` expression in the goal``: the
  `match` is hidden inside the name `mkPlus` until R1 opens it.
- **`simp [mkPlus, eval]` alone does not finish the milestone**: it unfolds `mkPlus` to the `match` but does
  not case on `a` and `b` (they are variables). `split` does.
- **`decide` fails on `fold_example`**: `Expr` has no `DecidableEq` instance (`failed to synthesize
  Decidable …`). Use `rfl`.
- **Name the IHs in the `with` pattern** (`plus a b iha ihb`) so you can pass them to `simp`; without `with`
  they are inaccessible (`a_ih✝`).
- **Order of the arms matters.** The hypotheses `x✝ : … → False` in later arms exist because the earlier
  arms are tried first. You do not need them for this problem, but they are why `split` is sound.
- Write the milestones **before** `fold_correct` and **outside** the `BEGIN SPEC`/`END SPEC` regions.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| expose a smart constructor's `match` | `unfold mkPlus` | R1 |
| one goal per arm | `split` | R2 |
| close every arm | `split <;> simp_all [eval]` | R2, R3 |
| milestone | `theorem eval_mkPlus (env : Nat → Nat) (a b : Expr) : eval env (mkPlus a b) = eval env a + eval env b` (same for `mkTimes`, `*`) | R1–R3 |
| induction on `e` | `induction e with \| num n => … \| var i => … \| plus a b iha ihb => … \| times a b iha ihb => …` | R4 |
| `num`, `var` cases; closed example | `rfl` | R5 |
| `plus`, `times` cases | `simp [fold, <milestone>, eval, iha, ihb]` | R6 |
| see the state | infoview | |
