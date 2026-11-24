# M048 · de Bruijn shifting: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `exact`, `rfl`, `have`, `·` focusing, `<;>`,
inductive types, definitions by pattern matching, `simp`. **New here:** structural induction with
`induction … with`, generalizing a parameter (and an assumption about it) so the induction hypothesis
holds at every cutoff, splitting `if … then … else` goals, `omega` for index comparisons, and
constructor injectivity. No Mathlib. M042 (`induction … with`, `by_cases`, `simp [h]` on an `if`) is
the gentler warm-up; this problem adds the generalized IH.

## How to read an entry

Each entry is one tactic or one proof move. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Tree → Prop`, `P : α → Prop`, …). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal. `Q`, `G` are arbitrary predicates/propositions.
- `{α : Type}` is any type. `n c c' d a b : Nat` are numbers (indices, cutoffs, shift amounts).
- Induction needs a concrete inductive type, so the entries use the guide's toy type, not `Tm`:
  `Tree` (constructors `leaf n`, `wrap t`, `node l r`) and `clip c t`, which caps every leaf label at
  `c`, with `c` growing by one under each `wrap`. `wrap` plays the role of `lam`, `node` of `app`, and
  the bound `c` of the cutoff.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The objects

- `Tm`: untyped λ-terms with **de Bruijn indices**: a variable is a number, `var k` refers to the
  `k`-th enclosing `lam` counting outwards from 0. `λx. λy. x y` is `lam (lam (app (var 1) (var 0)))`.
- `shift d c t`: add `d` to every variable of `t` with index `≥ c` (the **cutoff**). Indices `< c`
  point to binders inside the term being shifted and stay. Under `lam` one more binder is in scope, so
  the cutoff becomes `c + 1`. Written $\uparrow^d_c t$ in Pierce's *TAPL*.
  Example: `shift 1 0 (lam (app (var 0) (var 1))) = lam (app (var 0) (var 2))`.
- The three theorems: $\uparrow^0_c t = t$;
  $\uparrow^d_c \uparrow^{d'}_c t = \uparrow^{d+d'}_c t$; and for $c \le c'$,
  $\uparrow^1_c \uparrow^1_{c'} t = \uparrow^1_{c'+1} \uparrow^1_c t$
  (shifting at the lower cutoff first moves the higher cutoff up by one).

## Reading the goals

| You see | It means |
|---|---|
| `Tm.var n` | the constructor written `.var n` in the source |
| `t.lam`, `t.app u` | `Tm.lam t`, `Tm.app t u`: Lean prints `C.f x y` as `x.f y` when `x : C` |
| `t.wrap`, `l.node r`, `Tree.leaf n` | the same for the guide's `Tree` |
| `shift 1 c (if n < c' then Tm.var n else Tm.var (n + 1))` | the inner `shift` unfolded to an `if`; the outer one is stuck until the `if` is decided (R7, R9) |
| `ih : ∀ (c : Nat), …` | a generalized induction hypothesis: usable at any cutoff (R2) |
| `ih : ∀ (c c' : Nat), c ≤ c' → …` | generalized over both cutoffs, with the assumption as a premise (R13) |
| `h✝ : n < c` | an anonymous hypothesis (made by `split`); name it with `next h =>` (R4) |
| `case var`, `case lam`, `case app` | the goal for that constructor after `induction` |
| `case pos`, `case neg` | the `h : b` and `h : ¬b` goals after `by_cases` |
| `case isTrue`, `case isFalse` | the two goals after `split` (inside an induction case: `var.isTrue`, `var.isFalse`) |
| `¬n < c` | "not `n < c`", i.e. `n ≥ c`; `omega` turns one into the other |

---

## Part 1 · `shift_zero`

Statement: `shift 0 c t = t` for every cutoff `c`. By induction on `t`; under `lam` the goal is about
cutoff `c + 1`, so the IH must hold for every cutoff (R2).

**R1 · `induction t with | leaf n => … | wrap t ih => … | node l r ihl ihr => …`** changes the **goal
list** and the **context**. One goal per constructor, in constructor order; each case gets the
constructor's arguments under the names you write, plus one induction hypothesis per argument of the
type itself (`ih` for `t`, `ihl`/`ihr` for `l`/`r`). In the exercise:
`| var n => … | lam t ih => … | app t u iht ihu => …`. Placeholders: `(P : Tree → Prop) (t : Tree)`.

| Before | After |
|---|---|
| `t : Tree ⊢ P t` | `n : Nat ⊢ P (Tree.leaf n)`, `t : Tree, ih : P t ⊢ P t.wrap`, `l r : Tree, ihl : P l, ihr : P r ⊢ P (l.node r)` |

**R2 · `induction t generalizing c with …`** changes the **context**: `c` is taken out of the context
before the induction and re-introduced in every case, so the IH is quantified over it. Without it,
`ih : P c t` speaks about the same `c` as the goal, useless when the recursive call is at `c + 1`.
Placeholders: `(P : Nat → Tree → Prop) (c : Nat) (t : Tree)`.

| Before | After (case `wrap`) |
|---|---|
| `c : Nat, t : Tree ⊢ P c t` | `t : Tree, c : Nat ⊢ P c t.wrap`, with `ih : ∀ (c : Nat), P c t` |

**R3 · `simp only [clip]`** changes the **goal**: it applies the defining equation of `clip` wherever
`clip` meets a constructor. On a leaf that exposes the `if`; on `wrap` the recursive call at `c + 1`.
`simp only [shift]` does the same for the exercise. Placeholders: `(c n : Nat) (t : Tree) (P : Tree → Prop)`.

| Before | After |
|---|---|
| `⊢ P (clip c (Tree.leaf n))` | `⊢ P (if n < c then Tree.leaf n else Tree.leaf c)` |
| `⊢ P (clip c t.wrap)` | `⊢ P (clip (c + 1) t).wrap` |

**R4 · `split`** changes the **goal list**: a goal containing `if b then x else y` becomes two goals,
one with `h✝ : b` and `x` in place of the `if`, one with `h✝ : ¬b` and `y`. Write `next h => tac` to
name the hypothesis. In the exercise's `var` case the two goals are `Tm.var n = Tm.var n` and
`Tm.var (n + 0) = Tm.var n`, and `n + 0` reduces to `n`, so `split <;> rfl` closes both.
Placeholders: `{α : Type} (n c : Nat) (x y : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (if n < c then x else y)` | `h✝ : n < c ⊢ P x`, `h✝ : ¬n < c ⊢ P y` |

**R5 · `simp [clip, ih]`** with a generalized `ih` changes the **goal** (here closes it): `simp` unfolds
one step, then instantiates the `∀` in `ih` by itself (here `ih (c + 1)`) and rewrites. In the
exercise: `simp [shift, ih]` for `lam`, `simp [shift, iht, ihu]` for `app`. Placeholders:
`(F : Nat → Tree → Tree) (t : Tree) (c : Nat)`, `ih : ∀ (c : Nat), clip c (F c t) = F c t`.

| Before | After `simp only [clip]` | After `simp [ih]` |
|---|---|---|
| `⊢ clip c (F (c + 1) t).wrap = (F (c + 1) t).wrap` | `⊢ (clip (c + 1) (F (c + 1) t)).wrap = (F (c + 1) t).wrap` | no goals |

---

## Part 2 · `shift_shift`

Statement: `shift d c (shift d' c t) = shift (d + d') c t`. Same induction as Part 1 (R1, R2; `lam`
and `app` by R5). In the `var n` case, decide whether `n` is below the cutoff.

**R6 · `by_cases h : n < c`** changes the **goal list**: two copies of the goal, tagged `pos` with
`h : n < c` and `neg` with `h : ¬n < c`. Unlike `split` (R4) you choose the condition and the name,
which lets you decide several `if`s with one hypothesis. Placeholders: `(n c : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `h : n < c ⊢ G`, `h : ¬n < c ⊢ G` |

**R7 · `simp [h]`** with `h : b` or `h : ¬b` changes the **goal**: `simp` rewrites the condition to
`True`/`False` with `h` and then picks the branch (`if_pos`, `if_neg`). In the exercise:
`simp [shift, h]`. Placeholders: `{α : Type} (n c : Nat) (x y : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `h : n < c ⊢ P (if n < c then x else y)` | `h : n < c ⊢ P x` |
| `h : ¬n < c ⊢ P (if n < c then x else y)` | `h : ¬n < c ⊢ P y` |

**R8 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int`: `+`, `-` (truncated on
`Nat`), `<`, `≤`, `=`, `¬`, `∧`, `∨`, numerals and multiplication by numerals. It reads the
hypotheses in the context. Placeholders: `(n c d : Nat)`.

| Before | After |
|---|---|
| `h : ¬n < c ⊢ ¬n + d < c` | no goals |

**R9 · `simp [show ¬n + d < c by omega]`** changes the **goal**: after the inner `shift` moved `n` to
`n + d'`, the outer `if` asks about `n + d' < c`, which no hypothesis states literally. `show T by omega`
is a term of type `T` proved on the spot (R8), and `simp` uses it like R7. Placeholders as in R7, plus
`(d : Nat)`.

| Before | After |
|---|---|
| `h : ¬n < c ⊢ P (if n + d < c then x else y)` | `h : ¬n < c ⊢ P y` |

**R10 · constructor injectivity** changes the **goal**: `Tree.leaf a = Tree.leaf b` becomes `a = b`.
Lean generates `Tree.leaf.injEq : (Tree.leaf a = Tree.leaf b) = (a = b)` for every constructor and
`simp` uses it by itself. In the exercise: `Tm.var (n + d' + d) = Tm.var (n + (d + d'))` becomes
`n + d' + d = n + (d + d')`. A two-argument constructor gives a conjunction: `Tm.app t u = Tm.app t' u'`
becomes `t = t' ∧ u = u'` (this is what a stuck `app` case shows). Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `⊢ Tree.leaf a = Tree.leaf b` | `⊢ a = b` |

**R11 · `Nat.add_assoc`** changes the **goal**. The lemma is
`Nat.add_assoc (n m k : Nat) : n + m + k = n + (m + k)`; `+` groups to the left, so `n + a + b` is
`(n + a) + b`. Placeholders: `(n a b : Nat)`.

| Before | After |
|---|---|
| `⊢ P (n + a + b)` | `⊢ P (n + (a + b))` |

**R12 · `Nat.add_comm a b`** changes the **goal**. The lemma is `Nat.add_comm (n m : Nat) : n + m = m + n`.
Pass the arguments: `Nat.add_comm a b` rewrites only `a + b`. Bare `Nat.add_comm` in `rw` hits the
first sum it finds, and in `simp` it is used only as an ordered rewrite. The exercise passes
`Nat.add_assoc, Nat.add_comm d d'` to `simp`; `omega` would also close `n + d' + d = n + (d + d')`.
Placeholders: `(n a b : Nat)`.

| Before | After |
|---|---|
| `⊢ P (n + (a + b))` | `⊢ P (n + (b + a))` |

**W1** (`clip c (clip c t) = clip c t`) is the whole shape of Parts 1–2 on `Tree`: R2, then in the leaf
case R6 and `simp [clip, h]` (R3, R7) in both branches (`simp` decides `c < c` by itself);
`wrap` and `node` by R5.

```lean-goal
⊢ clip c (clip c t) = clip c t
```

---

## Part 3 · `shift_comm`

Statement: for `c ≤ c'`, `shift 1 c (shift 1 c' t) = shift 1 (c' + 1) (shift 1 c t)`. Now two cutoffs
grow under `lam`, and the assumption `h : c ≤ c'` must hold at the new cutoffs, so it belongs in the IH.

**R13 · `induction t generalizing c c' with …`** with `h : c ≤ c'` in the context changes the
**context**: `h` mentions `c` and `c'`, so it is generalized with them, and the IH takes it as a premise.
In each case `c c'` and `h` are re-introduced. Placeholders: `(Q : Nat → Nat → Tree → Prop) (c c' : Nat)
(t : Tree) (h : c ≤ c')`.

| Before | After (case `wrap`) |
|---|---|
| `c c' : Nat, t : Tree, h : c ≤ c' ⊢ Q c c' t` | `t : Tree, c c' : Nat, h : c ≤ c' ⊢ Q c c' t.wrap`, with `ih : ∀ (c c' : Nat), c ≤ c' → Q c c' t` |

**R14 · `ih (c + 1) (c' + 1) (by omega)`** changes the **context** when named with `have`: applying
the IH to the new cutoffs and a proof of `c + 1 ≤ c' + 1` (R8, from `h`) gives an ordinary fact, in the
exercise an equation. Pass it straight to `simp`: `simp [shift, ih (c + 1) (c' + 1) (by omega)]` for
`lam`, `simp [shift, iht c c' h, ihu c c' h]` for `app`. `simp` cannot find the premise by itself.
Placeholders: `(Q : Nat → Nat → Prop) (c c' : Nat)`, `ih : ∀ (a b : Nat), a ≤ b → Q a b`.

| Before | After |
|---|---|
| `h : c ≤ c' ⊢ G` | `h1 : Q (c + 1) (c' + 1) ⊢ G` |

The `var n` case. After `simp only [shift]` only the inner `shift`s unfold:
`shift 1 c (if n < c' then Tm.var n else Tm.var (n + 1)) = shift 1 (c' + 1) (if n < c then …)`.
Split on `n < c'` first, then (when `n < c'`) on `n < c` (R6, nested with `·`). In each of the three
branches `simp [shift, h1, h2, show … by omega]` decides the inner `if`s, unfolds the outer `shift`s
and decides their `if`s (R7, R9). Which `show` facts: whatever outer condition (`n < c' + 1`,
`n + 1 < c' + 1`, `n + 1 < c`, …) is not literally `h1` or `h2`. When `¬n < c'` there is no second
split: `c ≤ c'` forces `¬n < c`, so give `show ¬n < c by omega` instead (R9 with `h1` and `h`).

**W2** (`c ≤ c' → clip c (clip c' t) = clip c t`) chains exactly these moves on `Tree`: R13; leaf:
R3, R6 on `n < c'`, then R7 + R9 with `show ¬n < c by omega` and `show ¬c' < c by omega`; `wrap`:
R14 inside `simp`; `node`: R14 with the same `h`.

```lean-goal
⊢ clip c (clip c' t) = clip c t
```

---

## Traps

- `grind` and `try?` are banned: `try?` prints `fun_induction shift .. <;> grind` for `shift_shift`,
  which skips the lesson. Do not leave search tactics (`exact?`, `apply?`) in the file either.
- Forgetting `generalizing c` (or `c c'`) is the classic failure: the `lam` case then needs the IH at
  `c + 1` but has it only at `c`, and nothing closes the goal.
- `simp [shift, ih]` (or `simp [shift, iht, ihu]`) fails in Part 3's `lam` and `app` cases, with an
  "unused simp argument" warning: the IH has the premise `c ≤ c'`, which `simp` does not prove. Supply
  it: `ih (c + 1) (c' + 1) (by omega)`, `iht c c' h` (R14).
- `simp only [shift]` on `shift 1 c (shift 1 c' (Tm.var n))` unfolds only the inner call: the outer
  argument is an `if`, not a constructor. Decide the `if` first (R7, R9), then the outer `shift` unfolds.
- `split` names its hypothesis `h✝`, which you cannot mention; use `next h =>` or `by_cases` (R6).
- Indent `| …` alternatives at least as far as `induction`; put a case's tactics after `=>` or on
  more-indented lines below it.
- `shift_zero` is the warm-up; `shift_comm` is the real work.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a term | `induction t with \| var n => … \| lam t ih => … \| app t u iht ihu => …` | R1 |
| IH at every cutoff | `induction t generalizing c with …` | R2 |
| IH at every pair of cutoffs, with `h : c ≤ c'` | `induction t generalizing c c' with …` | R13 |
| unfold `shift` on a constructor | `simp only [shift]` | R3 |
| split an `if` in the goal | `split` (then `<;> rfl`, or `next h => …`) | R4 |
| constructor case with a ∀-IH | `simp [shift, ih]` | R5 |
| split on an index comparison | `by_cases h : n < c` | R6 |
| decide `if n < c …` | `simp [shift, h]` | R7 |
| linear facts about indices | `omega` | R8 |
| decide `if n + d < c …` from `h : ¬n < c` | `simp [shift, h, show ¬n + d < c by omega]` | R9 |
| `Tm.var a = Tm.var b` → `a = b` | `simp` (`Tm.var.injEq`) | R10 |
| regroup / swap sums | `Nat.add_assoc`, `Nat.add_comm a b` (or `omega`) | R11, R12 |
| IH with a premise at new cutoffs | `ih (c + 1) (c' + 1) (by omega)` inside `simp [...]` | R14 |
| see the state | infoview | |
