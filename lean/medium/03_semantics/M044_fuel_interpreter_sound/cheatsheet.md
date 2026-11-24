# M044 · A fuel-based interpreter is sound and monotone: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, `match`, `Option`, `induction`, `cases`,
`simp`, `rw`, `exact`. **New here:** reasoning about a function defined with *fuel*: unfolding it one step,
splitting on the `match`/`if` it unfolds to, and induction on the fuel with a generalized IH. Core Lean only,
no Mathlib.

## The objects

- **IMP** is a tiny imperative language. `State := Nat → Int` maps variable number `x` to its value.
  `AExp` are arithmetic expressions (`aeval s a : Int`), `BExp` boolean ones (`beval s b : Bool`), `Com`
  the commands `skip`, `assign x a`, `seq c1 c2`, `ite b c1 c2`, `while b c`. `update s x v` is `s` with
  variable `x` set to `v`.
- **`BigStep c s s'`** (big-step semantics, a relation): running `c` from `s` terminates in `s'`. One
  constructor per evaluation rule, two each for `ite` (`iteT`/`iteF`) and `while` (`whileT`/`whileF`).
- **`run n c s : Option State`** (the interpreter): the same evaluation, as a function, with *fuel* `n`.
  Each recursive call spends one unit; `run 0 c s = none` ("out of fuel"). Fuel makes `run` structurally
  recursive on `n`, so Lean accepts it although `while` may loop.
- **Soundness** (`run_sound`): if `run` answers `some s'`, the relation agrees. **Monotonicity**
  (`run_mono`): one more unit of fuel does not change a successful answer.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P`, `Q` are "the rest of your goal" (`P : α → Prop`, `Q : Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type; in the exercise it is `State`.
- The entries on unfolding use a toy fuel function from `guide.lean`, **not** the exercise's `run`:
  `tick n xs` sums the list `xs` with fuel `n` (`tick 0 _ = none`, `tick (n+1) [] = some 0`, and
  `tick (n+1) (x :: xs)` matches on `tick n xs`). `Sums xs t` is its relational version, like `BigStep`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Com.while b c`, `Com.ite b c1 c2`, `c1.seq c2` | the commands `.while b c`, `.ite b c1 c2`, `.seq c1 c2`; Lean writes `Com.seq c1 c2` as `c1.seq c2` because its first argument is a `Com` |
| `if beval s b = true then … else …` | the source's `if beval s b then …`: a `Bool` used as a condition is compared with `true` |
| `(match run n c1 s with \| some s' => … \| none => none)` | the unfolded `seq`/`while` step of `run`, still waiting for the inner run's result |
| `some s'✝`, `s'✝ : State` | a value `split at h` introduced; `✝` marks a name you cannot type (use `‹_›`, R9) |
| `heq✝ : run n c1 s = some s'✝` | the fact `split at h` learned about the `match` scrutinee |
| `h✝ : beval s b = true`, `h✝ : ¬beval s b = true` | the branch condition `split at h` learned about an `if` |
| `x✝ : Option State` | an auxiliary variable from `split`; ignore it |
| `n + 1 + 1` | the fuel `(n + 1) + 1` in `run_mono`'s successor goal; it matches the pattern `_ + 1` of `run` |
| `case succ.ite.isTrue` | the goal for: successor fuel, command `ite`, `if` condition true |
| `case h_1`, `case h_2` | the `some` resp. `none` branch after `split at h` on a `match` |
| `update s x (aeval s a)` | the state after `x := a`: `s` with variable `x` set to the value of `a` in `s` |
| `decide (p)`, `!b`, `b1 && b2` | in `beval`: the `Bool` that says whether `p` holds; Boolean not; Boolean and |
| `if beval s' b = true then match run n c s' with … else some s'` inside the goal of `run_mono`'s `while` case | the loop call `run (n + 1) (Com.while b c) s'` unfolded one more level by `simp only [run]` (see Traps) |

---

## Part 1 · `run_sound`

Statement: `run n c s = some s' → BigStep c s s'`. Whatever the interpreter returns, the big-step relation
also derives.

### Induction on the fuel

**R1 · `induction n generalizing c s s' with | zero => … | succ n ih => …`** changes the **goal list and the
context**: one goal for fuel `0`, one for `n + 1` with the IH `ih`. `generalizing x` first moves `x` (and
every hypothesis mentioning it, such as `h`) back into the goal, so `ih` is stated **for all** `x`:
`ih : ∀ (x : Nat), P n x`. That is needed because the recursive calls of `run` use other commands
(`c1`, `c2`) and other states (`s'✝`). Placeholders: `(P : Nat → Nat → Prop) (n x : Nat)`. In the exercise,
`ih : ∀ (c : Com) (s s' : State), run n c s = some s' → BigStep c s s'`.

| Before | After |
|---|---|
| `n x : Nat ⊢ P n x` | `x : Nat ⊢ P 0 x`, `n : Nat, x : Nat ⊢ P (n + 1) x` (plus `ih`) |

Without `with`, the case names are inaccessible: `⊢ P (n✝ + 1) x` with `a✝` as the IH. `with` (or
`rename_i n ih`, as in the guide) gives them names.

### Unfolding one step

**R2 · `simp only [f] at h`** changes the **context**: it rewrites `h` with the defining equation of `f`
that matches its arguments. `run (n + 1) (.seq c1 c2) s` matches the `n + 1, .seq c1 c2` line of `run`; it
does not fire on `run n c s` with an unknown command. Placeholders: `(n r : Nat)`, toy `tick`.

| Before | After `simp only [tick] at h` |
|---|---|
| `h : tick (n + 1) [] = some r ⊢ Q` | `h : some 0 = some r ⊢ Q` |

**R3 · `simp at h`** changes the **goal list**: it closes the goal when `h` says two different constructors are
equal (`none = some a` is `False`). `simp [f] at h` unfolds and closes in one step: this is the fuel-`0`
case and every "inner run returned `none`" branch. Placeholders: `{α : Type} (a : α)`.

| Before | After |
|---|---|
| `h : none = some a ⊢ Q` | ∅ |
| `h : tick 0 xs = some r ⊢ Q` | ∅ (`simp [tick] at h`) |

### Case analysis on the command

**R4 · `cases c with | skip => … | «while» b c => …`** changes the **goal list**: one goal per constructor,
its arguments named as you write them. `while` and `if` are keywords, so as constructor names write them in
guillemets `«…»`; Lean prints them plainly (`Com.while`, `Tok.if`). Placeholders: toy
`inductive Tok | «if» | num (k : Nat)`, `(P : Tok → Prop)`.

| Before | After |
|---|---|
| `t : Tok ⊢ P t` | `⊢ P Tok.if`, `k : Nat ⊢ P (Tok.num k)` |

### `skip` and `assign`: `some s = some s'`

**R5 · `Option.some.injEq`** changes the **context**. The lemma is `(some a = some b) = (a = b)`: `some` is
injective. Use it as `simp only [run, Option.some.injEq] at h`. Placeholders: `{α : Type} (a b : α)`.

| Before | After `simp only [Option.some.injEq] at h` |
|---|---|
| `h : some a = some b ⊢ Q` | `h : a = b ⊢ Q` |

**R6 · `subst h`** changes the **context and the goal**: for `h : a = b` where `b` is a local variable, it
deletes `b` and `h` and writes `a` for `b` everywhere. In the exercise `h : s = s'` turns the goal into
`BigStep .skip s s`. Placeholders: `{α : Type} (a b : α) (P : α → α → Prop)`.

| Before | After |
|---|---|
| `h : a = b ⊢ P a b` | `⊢ P a a` |

**R7 · `exact .ctor args`** **closes** the goal with a constructor. `.nil` is short for `Sums.nil`: Lean takes
the namespace from the goal's head (`Sums`, in the exercise `BigStep`). Arguments are the constructor's
explicit premises; its `{…}` arguments (states, commands) are inferred from the goal. For example
`BigStep.seq : BigStep c1 s s' → BigStep c2 s' s'' → BigStep (.seq c1 c2) s s''`.

| Before | After |
|---|---|
| `⊢ Sums [] 0` | ∅ (`exact .nil`) |
| `hxs : Sums xs t ⊢ Sums (x :: xs) (x + t)` | ∅ (`exact .cons hxs`) |

### `seq` and `while`: which branch of the `match`?

**R8 · `split at h`** on a `match` changes the **goal list and the context**: one goal per branch. In the
`some` branch, the matched value is a new variable `y✝`, `heq✝` records `f a = some y✝`, and `h` is that
branch's equation. Placeholders: `{α : Type} (f k : α → Option α) (a z : α)`. In the exercise (`seq`) you get
`heq✝ : run n c1 s = some s'✝` and `h : run n c2 s'✝ = some s'`.

| Before | After |
|---|---|
| `h : (match f a with … ) = some z`, `⊢ Q` | `heq✝ : f a = some y✝, h : k y✝ = some z ⊢ Q`, `heq✝ : f a = none, h : none = some z ⊢ Q` |

The `none` branch closes with R3.

**R9 · `‹T›`** is a **term**: "the hypothesis whose type is `T`". It is how you use `heq✝`/`h✝`, whose names
you cannot type. `‹_›` lets Lean infer `T` from the position it fills; write the type
(`‹run n c1 s = some _›`) if Lean picks the wrong one. Placeholders: `(A B : Prop) (f : A → B)`.

| Before | After `intro _` | After `exact f ‹_›` |
|---|---|---|
| `⊢ A → B` | `a✝ : A ⊢ B` | ∅ |

**R10 · `ih _ _ _ h`** is a **term**: the generalized IH applied to the hypothesis. Each `_` (command, start
state, end state) is found by unifying `ih`'s premise with `h`'s type. Placeholders:
`(R S : Nat → Nat → Prop) (ih : ∀ x y, R x y → S x y) (a b : Nat)`.

| Before | After `exact ih _ _ h` |
|---|---|
| `h : R a b ⊢ S a b` | ∅ |

### `ite` and `while`: which branch of the `if`?

**R11 · `split at h`** on an `if` changes the **goal list and the context**: two goals, with the condition
`h✝ : c` resp. `h✝ : ¬c`. The exercise's condition is `beval s b = true`. Placeholders:
`{α : Type} (b : Bool) (t e : Option α) (z : α)`.

| Before | After |
|---|---|
| `h : (if b = true then t else e) = some z ⊢ Q` | `h✝ : b = true, h : t = some z ⊢ Q`, `h✝ : ¬b = true, h : e = some z ⊢ Q` |

**R12 · `simpa using h`** (via `Bool.not_eq_true : (¬b = true) = (b = false)`) **closes** `b = false` from
`h : ¬b = true`. `split` gives `¬beval s b = true`, but `BigStep.iteF` and `BigStep.whileF` want
`beval s b = false`: pass `(by simpa using ‹¬beval s b = true›)`. Placeholders: `(b : Bool)`.

| Before | After |
|---|---|
| `h : ¬b = true ⊢ b = false` | ∅ |

---

## Part 2 · `run_mono`

Statement: `run n c s = some s' → run (n + 1) c s = some s'`. The same induction (R1, R3, R4), but now the
goal is also a `run` term: unfold both, read the branch off `h`, and steer the goal into the same branch.

**R13 · `simp only [f] at h ⊢`** changes the **context and the goal**: R2 in `h` and in the goal at once.
Placeholders: `(n r : Nat)`, toy `tick`.

| Before | After |
|---|---|
| `h : tick (n + 1) [] = some r ⊢ tick (n + 1 + 1) [] = some r` | `h : some 0 = some r ⊢ some 0 = some r` |

**R14 · `simpa [f] using h`** **closes** the goal when the goal and `h` simplify to the same statement. This
is the `skip` and `assign` case. Placeholders: as R13.

| Before | After |
|---|---|
| `h : tick (n + 1) [] = some r ⊢ tick (n + 1 + 1) [] = some r` | ∅ |

**R15 · `rw [h]` inside a `match`, then `exact`** changes the **goal**: the scrutinee `f a` becomes `some b`.
`match some b with | some y => k y | none => none` is `k b` *by definition*, so `exact` accepts a proof of
`k b = r` without further rewriting. In the exercise: `rw [ih _ _ _ ‹_›]` turns the goal's
`run (n + 1) c1 s` into `some s'✝` (R9, R10), then `exact ih _ _ _ h`. Placeholders:
`{α : Type} (f k : α → Option α) (a b : α) (r : Option α) (h : f a = some b)`.

```lean-goal
⊢ (match f a with | some y => k y | none => none) = r
⊢ (match some b with | some y => k y | none => none) = r
```

**R16 · `rw [if_pos hc]`** changes the **goal**. The lemma is `if_pos : c → (if c then t else e) = t`.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (t e : α) (hc : c)`. `[Decidable c]` means Lean can
compute whether `c` holds; `beval s b = true` qualifies. Pass `‹_›` for `hc` (the `h✝` from R11).

| Before | After |
|---|---|
| `hc : c ⊢ P (if c then t else e)` | `⊢ P t` |

**R17 · `rw [if_neg hc]`** changes the **goal**. The lemma is `if_neg : ¬c → (if c then t else e) = e`.
Placeholders: as R16, with `(hc : ¬c)`.

| Before | After |
|---|---|
| `hc : ¬c ⊢ P (if c then t else e)` | `⊢ P e` |

### Worked combinations (W1, W2 in `guide.lean`, on `tick`)

**W1** proves `tick n xs = some r → Sums xs r` by R1, R3 (fuel 0), R4 on `xs`, then R2, R5, R6, R7 (`nil`)
and R2, R8, R5, R6, R7 with R9, R10 (`cons`). **W2** proves `tick n xs = some r → tick (n + 1) xs = some r`
by R1, R3, R4, R14 (`nil`) and R13, R8, R15, R10 (`cons`). The exercise adds `ite` (R11, R12, R16, R17) and
`while`, where `split at h` runs twice: first the `if`, then the `match`.

---

## Traps

- **Generalize.** `induction n` without `generalizing c s s'` gives an IH only for the very `c s s'` of the
  statement; the recursive calls are on `c1`, `c2`, `s'✝`, so it never applies.
- **Prefer `simp only [run]` in the successor cases.** It applies exactly the matching equation of `run`,
  so the `match`/`if` that `split at h` needs is predictably there; full `simp` may also rewrite other parts
  of `h` with its whole lemma set. (`simp [run] at h` is the right call when it closes the goal: fuel `0`, R3.)
- **`split at h`, not `split`.** `h` tells you which branch ran. In `run_mono` you do not split the goal: you
  choose its branch with R16/R17 or R15, using the facts `split at h` produced.
- **`¬… = true` is not `… = false`** syntactically: `iteF`/`whileF` need R12.
- **`while` is a keyword**: the pattern is `| «while» b c =>`. Its infoview name is `Com.while`.
- **`while`, `run_mono`:** rewrite the body's run first (`rw [ih _ _ _ ‹_›]` on
  `heq✝ : run n c s = some s'✝`), then the loop's (`exact ih _ _ _ h`).
- **`simp only [run] at h ⊢` unfolds the goal's loop call too.** In the `while` case of `run_mono` the goal
  contains `run (n + 1) (Com.while b c) s'`, which also matches the `n + 1, .while b c` line of `run`, so the
  goal shows a second, nested `if beval s' b = true then match run n c s' with … else some s'` where you might
  expect `run (n + 1) (Com.while b c) s'`. Nothing is wrong: after `rw [ih _ _ _ ‹_›]` the goal is
  `match some s'✝ with | some s' => (that nested if) | none => none`, which is *by definition*
  `run (n + 1) (Com.while b c) s'✝ = some s'`, exactly the type of `ih _ _ _ h`, and `exact` checks up to
  unfolding definitions (R15). Do not try to `rw` or `split` the nested copy.
- **`‹_›` can pick the wrong hypothesis** when several have the right shape (in `seq`, both `heq✝` and `h` are
  `run n _ _ = some _`). If the step fails, write the type: `‹run n c1 s = some _›`.
- Indent the body of each `| case =>` alternative consistently; a `·` bullet must cover one goal exactly.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction with an IH for all commands/states | `induction n generalizing c s s' with \| zero => … \| succ n ih => …` | R1 |
| unfold one step of `run` in `h` | `simp only [run] at h` | R2 |
| close a goal with `h : none = some _` / fuel `0` | `simp at h` / `simp [run] at h` | R3 |
| one goal per command | `cases c with \| skip => … \| «while» b c => …` | R4 |
| `some a = some b → a = b` | `simp only [Option.some.injEq] at h` | R5 |
| eliminate a variable equal to a term | `subst h` | R6 |
| apply a `BigStep` rule | `exact .seq … …`, `exact .iteT ‹_› …` | R7 |
| which `match` branch ran | `split at h` | R8 |
| use an unnamed hypothesis | `‹_›`, `‹T›` | R9 |
| use the IH | `ih _ _ _ h` | R10 |
| which `if` branch ran | `split at h` | R11 |
| `¬b = true → b = false` | `(by simpa using ‹¬_ = true›)` | R12 |
| unfold in `h` and the goal | `simp only [run] at h` with ⊢ added to the location list | R13 |
| goal and `h` the same after unfolding | `simpa [run] using h` | R14 |
| rewrite the inner run of the goal | `rw [ih _ _ _ ‹_›]` | R15 |
| choose the goal's `if` branch | `rw [if_pos ‹_›]` / `rw [if_neg ‹_›]` | R16, R17 |
| see the state | infoview | |
