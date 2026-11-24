# M045 · Hoare rules are sound: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular term-mode proofs (E004), `omega`
(E011), induction on `Nat`/lists (E014, E015), inductive types (E018), named implicit arguments (E023)
and constructor injectivity (E029). **New here:** inductive *relations* (the big-step semantics
`BigStep`), inverting a derivation with `cases`, induction on a derivation with `generalize`, `cases`
on an equation between constructors, and `refine` with `?_` holes. Core Lean only, no Mathlib.

The guide never uses the exercise's IMP. It uses a toy language over one register `n : Nat`:
`Op` = `inc | dbl | both o1 o2 | rep o`, and `Run o n k` ("running `o` from `n` can end at `k`")
with rules `inc : Run .inc n (n+1)`, `dbl : Run .dbl n (2*n)`, `both` (run `o1` then `o2`), `stop`
(`rep o` may stop at once) and `more` (run `o` once, then `rep o` again). `rep` plays the role of
`while` without a guard. `Keeps r P := ∀ x y, P x → r x y → P y` is a definition shaped like `Hoare`,
and `ev : Tm → Int` is a pattern-matching evaluator shaped like `aeval`.

## How to read an entry

Each entry is one tactic or one term form. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- `{α : Type}` is any type. `r : α → α → Prop` is any binary relation (a step relation such as
  `BigStep c`); `P Q : α → Prop` are predicates on states (assertions, `Assn` in the exercise).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `State`, `Assn` | `Nat → Int` (variable `x` has value `s x`) and `State → Prop`; both are `abbrev`s, so they unfold freely |
| `BigStep c s s'` | a *derivation*: running `c` from `s` terminates in `s'`. One constructor per rule; a proof of it is a finite tree of rules |
| `Hoare P c Q` | the definition `∀ s s', P s → BigStep c s s' → Q s'`; `intro` sees through it (R1) |
| `.assign x a`, `.while b c` | leading-dot notation: `Com.assign x a`, `Com.while b c`, with the type `Com` taken from the expected type |
| `(AExp.var 0).plus (AExp.num (-1))` | `AExp.plus (AExp.var 0) (AExp.num (-1))`, printed with dot notation `x.f` for `T.f x` |
| `Com.while b c` | the loop; `while` is a keyword, so it never prints as `b.while c` and you must write `Com.while` in `generalize` |
| `(BExp.le (AExp.var 0) (AExp.num 0)).not` | the guard `¬ (x0 ≤ 0)` of `countdown`, as syntax; `x0` is variable `0`, whose value in `s` is `s 0` |
| `decide p` | the `Bool` truth value of a decidable proposition `p` (here `p` is `a ≤ b` on `Int`) |
| `!b`, `b && c` | Boolean not, and |
| `beval s b = true` | the guard holds in `s`; `simp` turns it into a `Prop` (R16, R17) |
| `update s x v` | `fun y => if y = x then v else s y`: `s` with `x` set to `v` |
| `s 0 + -1` | `s 0 - 1` as `aeval` produces it (`plus` with the literal `-1`) |
| `s✝`, `a✝`, `a✝¹`, `m✝` | inaccessible names: Lean made them, you cannot type them. Name them in a `with` pattern or with `rename_i` |
| `h✝` next to a newer `h` | a hypothesis hidden by a later one with the same name (Traps) |
| `a_ih✝` | an induction hypothesis that has no name yet |
| `case whileT.refl` | goal of the `whileT` rule, after `cases hw` (its one case is `Eq.refl`) |
| `case refine_1` | the first `?_` of a `refine` |

---

## Part 1 · `hoare_assign`

Statement: `Hoare (fun s => Q (update s x (aeval s a))) (.assign x a) Q`. If `Q` holds after updating `x`
to the value of `a`, then `Q` holds after running `x := a`.

**R1 · `intro x y hx hr`** changes the **goal and the context**. `intro` unfolds a definition whose body is
a `∀`/`→` by itself, so `intro s s' hp h` opens `Hoare P c Q`. Placeholders:
`{α : Type} (r : α → α → Prop) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ Keeps r P` | `x y : α, hx : P x, hr : r x y ⊢ P y` |

**R2 · `cases h`** on `h : Run .inc n m` changes the **context and the goal**. Only one rule of `Run` can
end in a derivation of `Run .inc …`, so `cases` keeps that case, deletes `h`, and replaces the end state `m`
by what the rule produces, `n + 1`. Rules whose command is not `.inc` are discarded automatically.
Placeholders: `(n m : Nat) (P : Nat → Prop)`. In the exercise the end state `s'` becomes
`update s x (aeval s a)`, and `hp` already says `Q` of exactly that.

| Before | After |
|---|---|
| `h : Run Op.inc n m ⊢ P m` | `⊢ P (n + 1)` |

## Part 2 · `hoare_seq`

Statement: from `Hoare P c1 Q` and `Hoare Q c2 R` get `Hoare P (.seq c1 c2) R`.

**R3 · `cases h with | both h1 h2 => tac`** changes the **context**: `h` is replaced by the premises of the
one rule that can produce it, named `h1 h2`. The intermediate state is an implicit argument of the rule, not
named by the pattern, so it prints as `m✝`; you never need its name, `_` (R4) finds it. The alternative must
close its goal. Placeholders: `(o1 o2 : Op) (n k : Nat) (P : Nat → Prop)`. The second example of R3 reaches
the same state with `cases h` then `rename_i h1 h2`.

| Before | After (inside the alternative) |
|---|---|
| `h : Run (o1.both o2) n k ⊢ P k` | `m✝ : Nat, h1 : Run o1 n m✝, h2 : Run o2 m✝ k ⊢ P k` |

**R4 · `exact h _ _ hx hr`** **closes** the goal. A hypothesis `h : ∀ x y, P x → r x y → Q y` (a Hoare triple
after unfolding) is a function: give it two states and two proofs and it returns `Q y`. Each `_` is inferred
from the later arguments. Chain them: the output of one triple is the `P`-argument of the next.
Placeholders: `{α : Type} (r : α → α → Prop) (P Q : α → Prop) (x y : α)`.

| Before | After |
|---|---|
| `hx : P x, hr : r x y ⊢ Q y` | no goals |

## Part 3 · `hoare_conseq`

Statement: strengthen the precondition (`P' → P`) and weaken the postcondition (`Q → Q'`).

**R5 · `fun x y hx hr => e`** **closes** the goal; it is the term form of R1 + R4. A proof of
`Keeps r P` (or `Hoare P' c Q'`) *is* a function of the four arguments. Write it directly after `:=` with no
`by`; the guide writes `by exact fun …` only so the infoview shows the goal. Placeholders as in R1.

| Before | After |
|---|---|
| `⊢ Keeps r P` | no goals |

## Part 4 · `hoare_while`

Statement: if the body `c` keeps the invariant `I` whenever the guard `b` is true, then after the loop `I`
holds and `b` is false. The derivation of a loop contains a derivation of the same loop (rule `whileT`), so
this needs induction on the derivation, and the derivation's command is not a variable.

**R6 · `generalize hw : e = w at h`** changes the **context**: every `e` in `h` becomes a fresh variable `w`,
and `hw : e = w` remembers what it was. `induction` needs this: it refuses a derivation whose indices are not
variables (Traps). Placeholders: `(o : Op) (n k : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : Run o.rep n k ⊢ P k` | `w : Op, hw : o.rep = w, h : Run w n k ⊢ P k` |

**R7 · `induction h`** changes the **goal list**: one goal per rule of `Run`, with an induction hypothesis
(IH) for each premise that is itself a `Run`. Hypotheses that mention the indices (`hw`, `h0`, in the exercise
`hI : I s`) are moved into the IHs automatically. Name the pieces with
`induction h with | more h1 h2 ih1 ih2 => tac | _ => tac`; the arguments come in the rule's order:
implicit ones are skipped, then the premises, then one IH per recursive premise. `| _ =>` covers every rule
not listed. Placeholders: `(o : Op) (n k : Nat)`.

| Before | After (5 goals; first, second and last shown) |
|---|---|
| `h : Run o n k ⊢ n ≤ k` | `⊢ n✝ ≤ n✝ + 1`, `⊢ n✝ ≤ 2 * n✝`, `a✝¹ : Run o✝ n✝ m✝, a✝ : Run o✝.rep m✝ k✝, a_ih✝¹ : n✝ ≤ m✝, a_ih✝ : m✝ ≤ k✝ ⊢ n✝ ≤ k✝` |

After `generalize` (W2) each goal also carries the equation, and each IH has the carried hypothesis and the
equation as premises, in that order:

| Before | After (rule `more`) |
|---|---|
| `hw : Op.dbl.rep = w, h : Run w n k, h0 : n = 0 ⊢ k = 0` | `h0 : n✝ = 0, hw : Op.dbl.rep = o✝.rep, a_ih✝ : m✝ = 0 → Op.dbl.rep = o✝.rep → k✝ = 0 ⊢ k✝ = 0` |

In the exercise the `whileT` IH for the second premise reads
`I s'✝ → Com.while b c = Com.while b✝ c✝ → I s''✝ ∧ beval s''✝ b = false`.

**R8 · `cases hw`** on `hw : c a = c b` (same constructor `c`) changes the **context and the goal**:
constructors are injective, so `a = b`; `cases` substitutes one for the other and removes `hw`. Placeholders:
`(o o' : Op) (P : Op → Prop)`. In the `whileF` and `whileT` goals this identifies `b✝ c✝` with your `b c`, so
the body triple `h` and the goal talk about the same guard.

| Before | After |
|---|---|
| `hw : o.rep = o'.rep ⊢ P o'` | `⊢ P o` |

**R9 · `cases hw`** on `hw : c₁ … = c₂ …` (different constructors) **closes** the goal: distinct constructors
are never equal, so there is no case to prove. This kills the `skip`, `assign`, `seq`, `iteT`, `iteF` goals in
one `| _ => cases hw`. Placeholders: `(o : Op) (G : Prop)`.

| Before | After |
|---|---|
| `hw : o.rep = Op.inc ⊢ G` | no goals |

**R10 · `exact ⟨ha, hb⟩`** **closes** `A ∧ B`. In the `whileF` goal you have the invariant and the false
guard. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `ha : A, hb : B ⊢ A ∧ B` | no goals |

**R11 · `exact ih ha rfl`** **closes** the goal with an IH whose premise is an equation. After R8 the equation
premise reads `e = e`, and `rfl` proves it. In `whileT`, `ha` is "the invariant holds after one run of the
body", which the body triple `h` gives you (R4). Placeholders: `{α : Type} (e : α) (A B : Prop)`.

| Before | After |
|---|---|
| `ih : A → e = e → B, ha : A ⊢ B` | no goals |

**W1, W2** chain R6 → R7 → R9 / R8 → R11 on the toy loop `rep dbl` (from `0`, doubling stays `0`). W1 is the
idiomatic `with` form; W2 shows every state at top level. In W2, `all_goals try (cases hw; done)` runs
`cases hw` on every goal and keeps the result only where it closes the goal (R9); `try t` undoes a failing
`t`, and `done` fails unless no goal is left. The `more` goal after `cases hw` and inverting the
`dbl` premise:

```lean-goal
⊢ k✝ = 0
```

---

## Part 5 · `countdown_correct`

Statement: `Hoare (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0)`. Invariant `I := fun s => 0 ≤ s 0`.
Build the triple from Parts 1, 3, 4 with `refine`, leaving the two arithmetic side conditions as `?_`.

**R12 · `refine f (g ?_) ?_`** changes the **goal list**: the term is checked now, and every `?_` becomes a
goal, in left-to-right order, however deep it sits. Placeholders: `(A B C D : Prop)`, `f : B → C → D`,
`g : A → B`.

| Before | After |
|---|---|
| `⊢ D` | `⊢ A`, `⊢ C` |

**R13 · `(m := e)`** sets an implicit argument by its name. `Nat.le_trans : n ≤ m → m ≤ k → n ≤ k` takes
`{n m k : Nat}`; the goal fixes `n` and `k` but not the middle `m`. Here the middle object is the invariant:
`hoare_while (I := fun s => 0 ≤ s 0) …`. Placeholders: `(n m k : Nat)`.

| Before | After |
|---|---|
| `⊢ n ≤ k` | `⊢ n ≤ m`, `⊢ m ≤ k` |

**R14 · `fun _ h => h`** **closes** `∀ x, P x → P x`. It is the trivial side of a consequence rule, when the
condition you have is already the one you need. Placeholders: `{α : Type} (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (x : α), P x → P x` | no goals |

**R15 · `simp [f] at h`** changes the **context**: it unfolds the pattern-matching function `f` along the
constructors it meets. `simp [beval, aeval, update] at *` does this in every hypothesis and in the goal.
Placeholders: `(a b : Int)`, `ev : Tm → Int`.

| Before | After |
|---|---|
| `h : ev ((Tm.lit a).add (Tm.lit b).neg) = 0 ⊢ a = b` | `h : a + -b = 0 ⊢ a = b` |

**R16 · `simp at h`** on a true Boolean test changes the **context**: `(!decide (a ≤ b)) = true` becomes the
proposition `b < a`. This is the guard `not (x0 ≤ 0)` holding: `0 < s 0`. Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `h : (!decide (a ≤ b)) = true ⊢ P` | `h : b < a ⊢ P` |

**R17 · `simp at h`** on a false Boolean test changes the **context**: `(!decide (a ≤ b)) = false` becomes
`a ≤ b`. This is the loop's exit condition: `s 0 ≤ 0`. Placeholders: `(a b : Int)`.

| Before | After |
|---|---|
| `h : (!decide (a ≤ b)) = false ⊢ P` | `h : a ≤ b ⊢ P` |

**R18 · `simp`** on a point update changes the **goal**: `(fun j => if j = i then v else f j) i` is reduced
(β-reduction, then `if i = i` is `if True`) to `v`. After `simp [update]` this is what reading variable `0`
of the updated state becomes. Placeholders: `(f : Nat → Int) (v : Int) (P : Int → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((fun j => if j = 3 then v else f j) 3)` | `⊢ P v` |

**R19 · `omega`** **closes** a goal of linear arithmetic over `Int` or `Nat`, using every hypothesis of that
shape (`∧`, `∨`, `¬`, `≤`, `<`, `=`, `+`, `-`, multiplication by numerals). It does not unfold definitions:
run `simp [defs] at *` first. Placeholders: `(x y : Int)`.

| Before | After |
|---|---|
| `h : x ≤ y ∧ y < x + 2 ⊢ y = x ∨ y = x + 1` | no goals |

**W3** chains R12 with R13 (`Int.le_trans (b := a + 1)`), then `omega` and `simp [ev] at *` on the two side
goals:

```lean-goal
⊢ a ≤ a + 1
⊢ a + 1 ≤ b
```

---

## Traps

- `induction h` on `h : BigStep (.while b c) s s'` fails with *Index in target's type is not a variable
  (consider using the `cases` tactic instead)*. Generalize first (R6), and write `Com.while b c`, not
  `.while b c`, on the left of `generalize`: there is no expected type to resolve the leading dot.
- `generalize … at h` changes only `h`. Do it after `intro`, when `h` exists.
- In `hoare_while`, `intro s s' hI h` reuses the name `h`: the body triple shows as `h✝` and cannot be
  typed. After `induction h` consumes the derivation it is `h` again, which is where you need it. To avoid
  the clash, name the derivation `hr` instead.
- `induction` moves `hI : I s` into the IHs, so the IH's first premise is the invariant at the *new* start
  state and the equation comes second: `ih (…) rfl`, not `ih rfl (…)`.
- In the `whileF`/`whileT` goals the guard is `b✝` in `hb` but `b` in the goal and in `h`. Run `cases hw` (R8)
  before using `hb` or `h`, or the types do not match.
- An alternative of `cases … with` / `induction … with` must close its goal; `skip` there is an error.
- `try?` and `grind` are banned (`try?` prints a `grind` one-liner for `hoare_conseq`). Do not leave
  `exact?` or `apply?` in the file either.
- `simp … at *` leaves the guard as `0 < s 0` and the loop exit as `s 0 ≤ 0`; `omega` reads both, together
  with `∧` in the hypothesis.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `Hoare P c Q` | `intro s s' hp h` | R1 |
| invert a derivation of a non-loop command | `cases h` | R2 |
| invert and name the premises | `cases h with \| seq h1 h2 => …` | R3 |
| use a triple | `h _ _ hp hrun` | R4 |
| prove a triple as a term | `fun s s' hp hrun => …` | R5 |
| induction on a loop derivation | `generalize hw : Com.while b c = w at h` then `induction h with …` | R6, R7 |
| `hw` between equal constructors | `cases hw` (substitutes) | R8 |
| `hw` between different constructors | `\| _ => cases hw` | R9 |
| prove `A ∧ B` | `⟨ha, hb⟩` | R10 |
| use an IH after `generalize` | `ih (…) rfl` | R11 |
| build a proof, leave holes | `refine f (g ?_) ?_` | R12 |
| fix the invariant | `hoare_while (I := fun s => …)` | R13 |
| trivial consequence | `fun _ h => h` | R14 |
| evaluate `beval`/`aeval`/`update` | `simp [beval, aeval, update] at *` | R15–R18 |
| finish integer arithmetic | `omega` | R19 |
| see the state | infoview | |
