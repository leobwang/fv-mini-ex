# H001 · Hilbert calculus: deduction theorem and soundness: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `apply`, `have`, `fun`, `·`
focusing, `cases` on `Bool`, `simp`, inductive types and inductive propositions, implicit arguments.
**New here:** core Lean only (no Mathlib): building proofs of an inductive predicate from its
constructors, named implicit arguments `(b := t)`, induction on a derivation, list membership
(`List.mem_cons`), `rcases` with `rfl`, rewriting with an `↔`, `simpa … using`.

The mathematics. A *formula* (`Form`) is a variable `pₙ`, `⊥`, or an implication `a ⇒ b` (the
object-level arrow, `Form.imp a b`). `Prov Γ a` says `a` is *derivable* from the hypothesis list `Γ`:
a hypothesis in `Γ`, an instance of one of the axiom schemes

- K: `a ⇒ (b ⇒ a)` (`ax1`),
- S: `(a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))` (`ax2`),
- double negation: `((a ⇒ ⊥) ⇒ ⊥) ⇒ a` (`ax3`),

or obtained by *modus ponens* (`mp`) from `a ⇒ b` and `a`. A proof of `Prov Γ a` is a finite tree of
these rules. The *deduction theorem* says `Prov (a :: Γ) b → Prov Γ (a ⇒ b)`: a hypothesis can be
discharged into an implication. A *valuation* `v : Nat → Bool` gives each variable a truth value;
`eval v a` is the truth value of `a` (`⊥` is `false`, `a ⇒ b` is `!a || b`). *Soundness*: whatever
is derivable from `Γ` is true under every valuation making all of `Γ` true. So `⊥` is not derivable
from `[]`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  (This `⊢` is Lean's; the exercise's `Prov Γ a` is a Lean proposition, not a proof state.)
- `P` is "the rest of your goal" (`P : α → Prop`, or with more arguments). The step changes only the
  part inside `P (…)`.
- `{α : Type}` is any type. The guide's own objects are declared at the top of `guide.lean`:
  `Reach E x y` ("`y` is reachable from `x` along the edge list `E`"; rules `edge`, `refl`, `trans`)
  stands in for `Prov`, and `BExp` with its semantics `beval` stands in for `Form` and `eval`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Form.var 0`, `Form.bot` | the variable `p₀`; falsity `⊥` |
| `a.imp b` | `Form.imp a b`, the object-level `a ⇒ b`. Lean prints `C.f x y` as `x.f y` |
| `.imp a b`, `.ax1`, `.mp h₁ h₂` in your own code | `Form.imp a b`, `Prov.ax1`, `Prov.mp h₁ h₂`: the leading dot looks the name up in the type Lean expects there |
| `Prov Γ a` | `a` is derivable from the list `Γ` |
| `a :: Γ`, `[]`, `[a, b]` | list with head `a` and tail `Γ`; the empty list; `a :: b :: []` |
| `a :: b.imp c :: Γ` | `a :: ((b.imp c) :: Γ)`: `::` binds weaker than `.imp` and groups to the right |
| `g ∈ Γ` | list membership |
| `∀ (g : Form), g ∈ Γ → eval v g = true` | how Lean prints `∀ g ∈ Γ, eval v g = true` |
| `!x`, `x \|\| y`, `x && y` | Boolean not, or, and (on `Bool`, not `Prop`) |
| `eval v a = true` | the proposition "`a` is true under `v`" (a `Bool` compared with `true`) |
| `¬X` | `X → False` |
| `x✝`, `a✝¹`, `a_ih✝` | inaccessible names made by a tactic; name them with `case`/`with` |
| `hm✝` | an older hypothesis `hm`, shadowed by a newer one with the same name |
| `A ↔ B → C` | `A ↔ (B → C)`: `→` binds tighter than `↔` (the `eval_imp` goals print this way) |
| `false = true`, `true = true` | a `Bool` equation: `false = true` is equivalent to `False`, which `simp` uses |
| `?a` | a metavariable: a term Lean has not determined yet |
| `case hyp`, `case inl` | the tag of a goal: which rule, which side of an `∨` |

---

## Part 1 · `imp_intro` (milestone)

Statement: `Prov Γ b → Prov Γ (a ⇒ b)`: an already derivable formula stays derivable under an extra
premise. One `mp` with `ax1 : b ⇒ (a ⇒ b)`. Used by Part 4 for every case except `hyp`-is-`a` and
`mp`.

**R1 · `exact .c h₁ h₂`** (leading-dot constructor) **closes** the goal. `.trans` means `Reach.trans`:
Lean takes the namespace from the expected type. The constructor's implicit arguments (`{E x y z}`)
are found by unification with the goal and the arguments; a nullary constructor such as `.refl` is
filled in the same way. Placeholders: `{E : List (Nat × Nat)} {x y : Nat} (h : Reach E x y)`.

| Before | After |
|---|---|
| `h : Reach E x y ⊢ Reach E x y` | no goals (`exact .trans .refl h`) |

---

## Part 2 · `eval_imp` (milestone)

Statement: `eval v (a ⇒ b) = true ↔ (eval v a = true → eval v b = true)`: the Boolean clause of `⇒`
read as a Lean implication. Used by Part 6 (cases `ax1`, `ax2`, `mp`).

**R2 · `cases h : e`** changes the **goal list and the context**: one goal per value of the `Bool`
term `e`; in each, `e` is replaced by `false` / `true` and `h` records which. Plain `cases e` forgets
`h`. Placeholders: `(f : Nat → Bool) (x : Nat) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (f x)` | `h : f x = false ⊢ P false`, `h : f x = true ⊢ P true` |

**R3 · `simp only [D]`** changes the **goal**: a definition by pattern matching applied to a
constructor becomes that clause. The guide's `beval v (.and a b)` is defined as
`beval v a && beval v b`. Placeholders: `(v : Nat → Bool) (a b : BExp) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (beval v (a.and b))` | `⊢ P (beval v a && beval v b)` |

**R4 · `simp [h]`** with `h : e = false` **closes** the goal: it rewrites `e` to `false`, then the
Bool laws (`false && y = false`, `(false = true) ↔ False`, …) finish. Placeholders: `(x y : Bool)`.

| Before | After |
|---|---|
| `h : x = false ⊢ (x && y) = false` | no goals |

**W4** combines R2–R4: `cases h : beval v a <;> simp [beval, h]` proves

```lean-goal
⊢ beval v (a.and b) = true ↔ beval v a = true ∧ beval v b = true
```

---

## Part 3 · `prov_self`

Statement: `Prov Γ (a ⇒ a)`. This is the combinator identity `I = S K K`: one `ax2` (S) and two
`ax1` (K), joined by two `mp`. Write it as a term or with `refine`.

**R5 · `refine .c (y := t) ?_ ?_`** changes the **goal list**: each `?_` becomes a goal, one per
premise. `(y := t)` sets the implicit argument named `y`. A variable that occurs in the premises but
not in the conclusion (the cut point `y` of `trans`, the formula `a` of `Prov.mp`, the `b` of an
inner `ax1`) is not fixed by unification; without naming it Lean reports "don't know how to
synthesize implicit argument `y`". Placeholders: `{E : List (Nat × Nat)} (x y z : Nat)`.

| Before | After |
|---|---|
| `⊢ Reach E x z` | `⊢ Reach E x y`, `⊢ Reach E y z` |

In `prov_self` the outer `mp`'s cut formula is `a ⇒ (b ⇒ a)` for any `b` you like: nothing
determines `b`, so name it, e.g. `.ax1 (b := a)`. Written as one term, the other implicit formulas
are then found by unification. If you instead start with `refine .mp ?_ ?_`, the cut formula is
unknown at that point and Lean reports "don't know how to synthesize implicit argument `a`": write
`refine .mp (a := …) ?_ ?_` with the cut formula spelled out.

---

## Part 4 · `deduction`

Statement: `Prov (a :: Γ) b → Prov Γ (a ⇒ b)`. Induction on the derivation of `b`; in each case build
`Prov Γ (a ⇒ ·)`.

**R6 · `induction h`** (h a proof of an inductive predicate) changes the **goal list**: one goal per
rule (constructor), with an induction hypothesis (IH) for each premise that is itself a derivation.
The list argument is the same in every rule, so Lean treats it as a *parameter*: `induction h` works
although it is `e :: E`, not a variable, and it stays `e :: E` in every goal. Placeholders: the
guide's `Reach`, `(P : Nat → Nat → Prop) (e : Nat × Nat) (E : List (Nat × Nat))`.

| Before | After |
|---|---|
| `h : Reach (e :: E) x y ⊢ P x y` | `⊢ P x✝ y✝`, `⊢ P x✝ x✝`, `a_ih✝¹ : P x✝ y✝, a_ih✝ : P y✝ z✝ ⊢ P x✝ z✝` |

The `edge` goal also has `a✝ : (x✝, y✝) ∈ e :: E`. Name things with `case edge x y hm => …`, or write
`induction h with | edge hm => … | refl => … | trans h₁ h₂ ih₁ ih₂ => …`: there the names go to the
*explicit* premises, then the IHs; implicit fields (`{x y}`, in `Prov` the formulas `{a b c}`) are not
named and stay `x✝`. In `deduction` the `mp` goal is `Prov Γ (a.imp b✝)` with IHs
`Prov Γ (a.imp (a✝².imp b✝))` and `Prov Γ (a.imp a✝²)`; an axiom's goal is `Prov Γ (a.imp X)` with `X`
that axiom's instance; the `hyp` goal is `Prov Γ (a.imp a✝¹)` with `a✝ : a✝¹ ∈ a :: Γ`.

**R7 · `List.mem_cons`** changes the **context** (used as `List.mem_cons.mp hm`). The lemma is
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`; `.mp` is its left-to-right direction, a function from
`a ∈ b :: l` to `a = b ∨ a ∈ l`. Placeholders: `{α : Type} (a b : α) (l : List α)`.

| Before | After `have hm' := List.mem_cons.mp hm` |
|---|---|
| `hm : a ∈ b :: l ⊢ P` | `hm' : a = b ∨ a ∈ l ⊢ P` |

**R8 · `rcases h with rfl | h`** changes the **goal list and the context**: one goal per side of the
`∨`. On the left the pattern `rfl` uses the equation `x = a` up, replacing `a` by `x` everywhere
(both are variables); on the right `h` names the membership. Placeholders:
`(Q : Nat → Prop) (a x : Nat) (S : List Nat)`.

| Before | After |
|---|---|
| `h : x = a ∨ x ∈ S ⊢ Q x` | `ha : Q x ⊢ Q x`, `h : x ∈ S ⊢ Q x` |

In `deduction` (case `hyp`, `hm : a✝ ∈ a :: Γ`) the left goal becomes `Prov Γ (a✝.imp a✝)`: the
theorem's `a` was replaced by the rule's `a✝` (close it with `prov_self`). The right goal is
`Prov Γ (a.imp a✝)` with the new `hm : a✝ ∈ Γ` (the old one shows as `hm✝`): `imp_intro` of `.hyp hm`. **W2** runs R7 and R8 together.

---

## Part 5 · `prov_trans`

Statement: `Prov Γ ((a ⇒ b) ⇒ ((b ⇒ c) ⇒ (a ⇒ c)))` (hypothetical syllogism). Use `deduction`
backwards three times, then finish with two `mp`s from hypotheses.

**R9 · `apply lem`** changes the **goal**: a goal matching `lem`'s conclusion becomes `lem`'s premise.
`lem`'s implicit arguments are read off the goal. Placeholders:
`(Q R : Nat → Prop) (lem : ∀ {n : Nat}, Q n → R n) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ R n` | `⊢ Q n` |

`apply deduction` turns `Prov Γ (x.imp y)` into `Prov (x :: Γ) y`, so three of them leave
`Prov (a :: b.imp c :: a.imp b :: Γ) c`: the last hypothesis introduced is the head of the list.

**R10 · `by simp`** **closes** a goal `x ∈ t₁ :: t₂ :: … :: S` when `x` is literally one of the listed
terms `tᵢ` (`b ∈ a :: b :: c :: S`). It fails if `x` is still a metavariable `?a`: name the cut formula of
`mp` first (R5). **W1** builds a whole derivation this way: `.trans (y := 2) (.edge (by simp)) (.edge (by simp))`.

---

## Part 6 · `soundness`

Statement: if `Prov Γ a` and `v` makes every formula of `Γ` true, then `eval v a = true`. Induction on
the derivation (R6), one Boolean check per rule. The milestone `eval_imp` (Part 2) turns every `⇒`
into a Lean `→`.

**R11 · `hS x hx`** with `hS : ∀ g ∈ S, Q g` **closes** the goal `Q x`: `hS` is a function taking `g`
and a proof of `g ∈ S`. Lean prints `hS` as `hS : ∀ (g : Nat), g ∈ S → Q g`. Placeholders:
`(Q : Nat → Prop) (S : List Nat) (x : Nat)`.

| Before | After |
|---|---|
| `hx : x ∈ S ⊢ Q x` | no goals (`exact hS x hx`) |

**R12 · `simp only [hQR]`** with `hQR : ∀ n, Q n ↔ R n` changes the **goal**: every `Q _` becomes
`R _`. `simp` (and `rw`) use an `↔` as an equation between propositions. Placeholders:
`(Q R : Nat → Prop) (x y : Nat)`.

| Before | After |
|---|---|
| `⊢ Q x → Q y` | `⊢ R x → R y` |

With `eval_imp`, `simp only [eval_imp]` turns `eval v (a.imp (b.imp a)) = true` into
`eval v a = true → eval v b = true → eval v a = true`, which `intro`s and `exact` close.

**R13 · `simp`** **closes** a Bool identity that the Bool laws reduce to `true = true`, e.g.
`(!(x || false) || x) = true` (`x || false = x`, then `!x || x = true`). Not every tautology: `simp`
leaves `(!(x && y) || y) = true` as `(x = false ∨ y = false) ∨ y = true`; finish such a goal with
`cases x <;> simp` (R2). In `soundness` the `ax3` case is one `simp [eval]`: unfolding `eval` gives
`(!(!(!eval v a✝ || false) || false) || eval v a✝) = true`, and the same laws then close it.

**R14 · `hiff.mp hq`** changes the **context**: it adds the right side of `hiff : Q ↔ (A → B)`. That
side is an implication, so `hiff.mp hq ha` applies it at once. Placeholders: `(Q A B : Prop)`.

| Before | After `have hab := hiff.mp hq` |
|---|---|
| `hiff : Q ↔ A → B, hq : Q ⊢ B` | `hab : A → B ⊢ B` |

Note `Q ↔ A → B` is `Q ↔ (A → B)`. In the `mp` case of `soundness` the IHs are
`ih1 : eval v (a.imp b) = true` and `ih2 : eval v a = true`; `eval_imp`'s `.mp` turns `ih1` into a
function that takes `ih2` to the goal `eval v b = true`.

**W3** is a soundness proof by induction for `Reach` ("every edge goes up, so every reachable point
is above").

---

## Part 7 · `consistent`

Statement: `¬ Prov [] ⊥`. Assume `h : Prov [] Form.bot`; `soundness` at the valuation
`fun _ => true` gives `eval (fun _ => true) Form.bot = true`, i.e. `false = true`.

**R15 · `simpa [D] using e`** **closes** the goal: it simplifies the type of the term `e` and the goal,
then matches them. A type that simplifies to `False` closes any goal. Placeholders:
`(v : Nat → Bool) (hf : ∀ a, beval v a = true)`, `e := hf (.neg .tt)`.

| Before | After |
|---|---|
| `⊢ False` | no goals (`simpa [beval] using hf (.neg .tt)`) |

**R16 · `by simp`** **closes** `∀ g ∈ ([] : List α), Q g`: nothing is a member of `[]`. This is the
hypothesis argument `soundness` needs for `Γ = []`.

---

## Traps

- `.imp a b` is implication **inside** the object logic (a `Form`); Lean's `→` is the meta level.
  `Prov Γ (.imp a b)` and `Prov Γ a → Prov Γ b` are different statements (the deduction theorem
  relates them).
- `.mp h₁ h₂` cannot infer its cut formula when `h₂` is `.hyp (by simp)` or another axiom with free
  variables: `by simp` then meets a metavariable `?a ∈ …` and fails. Name it: `.mp (a := b) …` (R5).
- In `deduction`, the theorem's own `a` and the rules' implicit `a` both appear: the latter show as
  `a✝`. After `rcases … with rfl | hm`, one of them has been replaced by the other.
- `cases eval v a` without `h :` loses the equation that `simp` needs to rewrite `eval v a` inside
  `eval v (a.imp b)` (R2).
- `simp` does not prove every Bool tautology (R13); `cases` on the variables first.
- `try?` finds a one-line proof of `soundness`, and then `consistent` is one `simpa`. Doing
  `soundness` by hand, one case per rule, is the practice; the real work is `deduction`.
- `t1 ; t2` runs `t2` on the first goal only. After `induction` or `cases`, use `<;>` or `all_goals`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| apply a rule, implicits inferred | `exact .mp h₁ h₂`, `.ax1` | R1 |
| split on a Bool subterm, keep the equation | `cases h : eval v a` | R2 |
| unfold a pattern-matching def | `simp only [eval]` / `simp [eval, h]` | R3, R4 |
| fix a cut formula / free variable | `.mp (a := b) …`, `.ax1 (b := a)`, `refine .mp (a := b) ?_ ?_` | R5 |
| induction on a derivation | `induction h with \| hyp hm => … \| mp h₁ h₂ ih₁ ih₂ => …` | R6 |
| `x ∈ a :: Γ` → `x = a ∨ x ∈ Γ` | `List.mem_cons.mp hm` | R7 |
| split, substituting the equation | `rcases … with rfl \| hm` | R8 |
| reason backwards with a lemma | `apply deduction` | R9 |
| membership in an explicit list | `.hyp (by simp)` | R10 |
| use `hv : ∀ g ∈ Γ, …` | `hv _ hm` | R11 |
| rewrite with an `↔` lemma | `simp only [eval_imp]` | R12 |
| Bool identity | `simp [eval]` (else `cases x <;> simp`) | R13 |
| use an `↔` as a function | `(eval_imp v _ _).mp h` | R14 |
| derive `False` from a term | `simpa [eval] using e` | R15 |
| hypothesis about `[]` | `(by simp)` | R16 |
| see the state | infoview | |
