# M049 · A type checker for STLC: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types and inductive predicates, `match`, `Option`,
`induction`, `cases`, `simp`, `rw`, `exact`. **New here:** proving a *checker* (a function returning `Option`)
sound and complete for a *relation* (an inductive predicate): unfolding the checker one step at a hypothesis,
splitting on the `match`/`if` it unfolds to, induction on a term with a generalized IH, and induction on a
derivation. Core Lean only, no Mathlib.

## The objects

- **`Ty`**: simple types, `base` and `arr A B` (the function type `A → B`). `deriving DecidableEq` lets Lean
  decide `A = B` for two types, which makes `if A = A' then … else …` legal in `typeOf`.
- **`Tm`**: simply typed λ-terms with **de Bruijn indices**: a variable is a number, `var 0` is the nearest
  enclosing binder, `var 1` the next one out, and so on. `lam A t` binds one variable of type `A` in `t`;
  `app t u` applies `t` to `u`.
- **Context `Γ : List Ty`**: `Γ[n]` is the type of `var n`. Going under `lam A` pushes `A` on the front, so
  the body is checked in `A :: Γ` (the old `var 0` becomes `var 1`).
- **`HasType Γ t A`** (the typing relation): one rule per term former: `var` (look up the context), `lam`
  (body typed in `A :: Γ`), `app` (function of type `A.arr B` applied to an argument of type `A`).
- **`typeOf Γ t : Option Ty`** (the checker): the same rules as a structurally recursive function; `none`
  means "ill-typed".
- **Soundness** (`typeOf_sound`): if the checker answers `some A`, the relation derives `A`. **Completeness**
  (`typeOf_complete`): every derivable type is what the checker answers. The milestone `type_unique` follows
  from completeness.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses, goal `G`. A cell shows only the hypotheses that change (in this file
  `Γ` is also the exercise's context name; the meaning is clear from where it sits). `∅` means the goal is
  closed.
- `P`, `Q` are "the rest of your goal" (`P : α → Prop`, `Q : Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal.
- `{α : Type}` is any type; in the exercise it is `Ty`, `Tm` or `List Ty`. `[DecidableEq α]` means Lean can
  compute whether two elements of `α` are equal; `Ty` has it (`deriving DecidableEq`), so do `Nat` and `Bool`.
- Some entries use toy objects from `guide.lean`, **not** the exercise's: `Tr` (trees `leaf n`, `tag k t`,
  `node l r`, shaped like `var`, `lam`, `app`), the relation `Lv xs t d` (like `HasType`) and the checker
  `lv xs t : Option Nat` (like `typeOf`; `lv xs (.tag k t)` matches on `lv (k :: xs) t`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `B.arr B✝`, `A✝.arr A` | `Ty.arr B B✝`: Lean writes `Ty.arr X Y` as `X.arr Y` because its first argument is a `Ty` |
| `Tm.var n`, `Tm.lam B t`, `t.app u` | the terms `.var n`, `.lam B t`, `.app t u` (same printing rule) |
| `Γ[n]?` | list lookup returning `Option`: `some` (entry `n`, counted from 0), or `none` if `n` is out of range |
| `(A :: Γ)[0]?`, `(A :: Γ)[n + 1]?` | `simp` turns these into `some A` and `Γ[n]?` (`List.getElem?_cons_zero`, `List.getElem?_cons_succ`) |
| `(match typeOf (B :: Γ) t with \| some B_1 => some (B.arr B_1) \| none => none)` | the unfolded `lam` step of `typeOf`; `B_1` is the pattern variable `B`, renamed because `B` is taken |
| `(match typeOf Γ t, typeOf Γ u with \| some (A.arr B), some A' => … \| x, x_1 => none)` | the unfolded `app` step; `x, x_1` is how Lean prints the catch-all `_, _` |
| `B✝`, `A'✝`, `heq✝`, `h✝` | names introduced by `split` or `cases`; `✝` marks a name you cannot type (use `‹_›`, R6) |
| `heq✝ : typeOf (B :: Γ) t = some B✝` | what `split at h` learned about the `match` scrutinee |
| `x✝ : ∀ (A B A' : Ty), typeOf Γ t = some (A.arr B) → typeOf Γ u = some A' → False` | catch-all branch: "the first pattern did not match" (R9); you do not need it |
| `x✝ : Option Ty` | an auxiliary variable from `split`; ignore it |
| `ih : ∀ {Γ : List Ty} {A : Ty}, typeOf Γ t = some A → HasType Γ t A` | the generalized IH; `{…}` binders, so apply it as `ih h'` (R7) |
| `Γ✝`, `n✝`, `A✝`, `a✝` (completeness) | the implicit arguments and unnamed premises of a `HasType` rule, from `induction h` (R12) |
| `case h_1.isTrue.refl` | the goal for: first `match` branch, `if` condition true, after `cases` on `some _ = some _` |

---

## Part 1 · `typeOf_sound`

Statement: `typeOf Γ t = some A → HasType Γ t A`. Whatever type the checker returns, the typing relation
derives. Induct on the term `t`; in each case unfold `typeOf` once in `h`, split until `h` says
`some _ = some A`, and rebuild the derivation with the matching rule.

### Induction on the term

**R1 · `induction t generalizing Γ A with | var n => … | lam B t ih => … | app t u iht ihu => …`** changes the
**goal list and the context**: one goal per constructor of `Tm`, with one IH per recursive argument (`lam` has
one, `app` two, `var` none). `generalizing Γ A` first moves `Γ`, `A` (and `h`, which mentions them) back into
the goal, so the IH holds **for every** context and type. That is needed: `lam` checks its body in `B :: Γ`,
not `Γ`. Placeholders: `(P : List Nat → Tr → Prop) (xs : List Nat) (t : Tr)`.

| Before | After |
|---|---|
| `xs : List Nat, t : Tr ⊢ P xs t` | `n✝ : Nat ⊢ P xs (Tr.leaf n✝)`, `k✝ : Nat, t✝ : Tr ⊢ P xs (Tr.tag k✝ t✝)`, `l✝ r✝ : Tr ⊢ P xs (l✝.node r✝)` |

The `tag` goal also has `t_ih✝ : ∀ (xs : List Nat), P xs t✝`, the `node` goal `l_ih✝` and `r_ih✝`. Without
`with` these names are inaccessible; `with` (or `rename_i k t ih`, as in the guide) names them. In the exercise
the `lam` goal has `ih : ∀ {Γ : List Ty} {A : Ty}, typeOf Γ t = some A → HasType Γ t A` and
`h : typeOf Γ (Tm.lam B t) = some A`.

**R2 · `exact .ctor args`** **closes** the goal with a constructor. `.leaf` is short for `Lv.leaf`: Lean takes
the namespace from the goal's head (`Lv`, in the exercise `HasType`). Arguments are the rule's explicit
premises; its `{…}` arguments are inferred from the goal. `exact` checks up to unfolding definitions, so
`h : lv xs (Tr.leaf n) = some d` is accepted where `xs[n]? = some d` is expected: that is the exercise's `var`
case, `exact .var h`. Placeholders: `(xs : List Nat) (n d : Nat)`.

| Before | After |
|---|---|
| `h : lv xs (Tr.leaf n) = some d ⊢ Lv xs (Tr.leaf n) d` | ∅ (`exact .leaf h`) |

### Reading off what the checker did

**R3 · `simp only [f] at h`** changes the **context**: it rewrites `h` with the defining equation of `f` that
matches its arguments. `typeOf Γ (Tm.lam B t)` matches the `.lam A t` line of `typeOf` and becomes the `match`
on `typeOf (B :: Γ) t`. Placeholders: `(xs : List Nat) (n d : Nat)`, toy `lv`.

| Before | After `simp only [lv] at h` |
|---|---|
| `h : lv xs (Tr.leaf n) = some d ⊢ Q` | `h : xs[n]? = some d ⊢ Q` |

**R4 · `split at h`** on a `match` changes the **goal list and the context**: one goal per branch. In the
`some` branch the matched value is a new variable `y✝`, `heq✝` records `f a = some y✝`, and `h` is that
branch's equation. Placeholders: `{α β γ : Type} (f : α → Option β) (g : β → γ) (a : α) (z : γ)`. Before
the step the context has `h : (match f a with | some y => some (g y) | none => none) = some z` (the infoview
prints it over several lines).

| Before | After |
|---|---|
| `⊢ Q` | `y✝ : β, heq✝ : f a = some y✝, h : some (g y✝) = some z ⊢ Q`, `heq✝ : f a = none, h : none = some z ⊢ Q` |

In the exercise (`lam`) the `some` branch has `heq✝ : typeOf (B :: Γ) t = some B✝` and
`h : some (B.arr B✝) = some A`; the `none` branch closes with R8.

**R5 · `cases h`** on `h : some x = some y`, `y` a local variable, changes the **context and the goal**: `some`
is injective, so `cases` solves the equation, deletes `h`, and writes `x` for `y` everywhere. In the exercise
it replaces the result type `A` by `B.arr B✝`, so the goal becomes `HasType Γ (Tm.lam B t) (B.arr B✝)`, exactly
the conclusion of `HasType.lam`. When **both** sides are variables, `cases` may eliminate either one: in
the `app` case `h : some B✝ = some A` makes `B✝` disappear (`heq✝ : typeOf Γ t = some (A✝.arr A)`), and the
`heq✝` names may be renumbered. Placeholders: `{α : Type} (x y : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `h : some x = some y ⊢ P y` | `⊢ P x` |

**R6 · `‹T›`** is a **term**: "the hypothesis whose type is `T`". It is how you use `heq✝`/`h✝`, whose names
you cannot type. `‹_›` lets Lean infer `T` from the position it fills. Placeholders: `(A B : Prop) (f : A → B)`.

| Before | After `intro _` | After `exact f ‹_›` |
|---|---|---|
| `⊢ A → B` | `a✝ : A ⊢ B` | ∅ |

**R7 · `ih h`** is a **term**: the generalized IH applied to a hypothesis. The theorem binds `{Γ : List Ty}`
and `{A : Ty}` with braces, so after `generalizing Γ A` the IH is `ih : ∀ {Γ : List Ty} {A : Ty}, …`: you pass
**only** the hypothesis and Lean unifies `Γ`, `A` with it. In the exercise: `ih ‹_›` with `heq✝`, so
`exact .lam (ih ‹_›)` (R2, R7, R6). Placeholders: `(R S : List Nat → Nat → Prop) (ys : List Nat) (e : Nat)`,
`ih : ∀ {xs : List Nat} {d : Nat}, R xs d → S xs d`.

| Before | After |
|---|---|
| `h : R ys e ⊢ S ys e` | ∅ (`exact ih h`) |

**R8 · `simp at h`** changes the **goal list**: it closes the goal when `h` says two different constructors are
equal (`none = some a` simplifies to `False`). This is every "the checker returned `none`" branch.
Placeholders: `{α : Type} (a : α)`.

| Before | After |
|---|---|
| `h : none = some a ⊢ Q` | ∅ |

### The `app` case: a two-scrutinee `match`, then an `if`

**R9 · `split at h`** on `match e₁, e₂ with | p₁, p₂ => … | _, _ => …` changes the **goal list and the
context**: a goal for the first branch, with one `heq✝` per scrutinee, and a goal for the catch-all, whose
context has `x✝ : ∀ …, e₁ = … → e₂ = … → False` ("the first branch did not match") and `h : none = some z`
(close it with R8). Placeholders: `{α β : Type} (f g : α → Option β) (k : β → β → Option β) (a : α) (z : β)`.
Before the step the context has `h : (match f a, g a with | some x, some y => k x y | _, _ => none) = some z`;
in the catch-all goal it has `x✝ : ∀ (x y : β), f a = some x → g a = some y → False`.

| Before | After |
|---|---|
| `⊢ Q` | `heq✝¹ : f a = some x✝, heq✝ : g a = some y✝, h : k x✝ y✝ = some z ⊢ Q`, `h : none = some z ⊢ Q` |

In the exercise the first pattern is `some (A.arr B), some A'`, so the branch gives
`heq✝¹ : typeOf Γ t = some (A✝.arr B✝)`, `heq✝ : typeOf Γ u = some A'✝` and
`h : (if A✝ = A'✝ then some B✝ else none) = some A`.

**R10 · `split at h`** on an `if` changes the **goal list and the context**: two goals, with the condition
`h✝ : c` resp. `h✝ : ¬c`. Placeholders: `{α β : Type} [DecidableEq α] (a b : α) (t : Option β) (z : β)`.

| Before | After |
|---|---|
| `h : (if a = b then t else none) = some z ⊢ Q` | `h✝ : a = b, h : t = some z ⊢ Q`, `h✝ : ¬a = b, h : none = some z ⊢ Q` |

In the exercise the true branch has `h✝ : A✝ = A'✝` and `h : some B✝ = some A`: `cases h` (R5) next, and the
false branch closes with R8.

**R11 · `subst_vars`** changes the **context and the goal**: every hypothesis `x = e` or `e = x` with `x` a
local variable is used to replace `x` everywhere and is then deleted. In the exercise it uses `h✝ : A✝ = A'✝`,
so the argument's type `A'✝` and the function's domain `A✝` become one variable, and
`exact .app (iht ‹_›) (ihu ‹_›)` (R2, R7, R6) fits. Placeholders: `{α : Type} (a b c : α)
(P : α → α → α → Prop)`.

| Before | After |
|---|---|
| `h1 : a = b, h2 : b = c ⊢ P a b c` | `c : α ⊢ P c c c` |

(`subst h` does the same for one named equation; R5's `cases` is the `some x = some y` version.)

### Worked combination (W1 in `guide.lean`, on `lv`)

**W1** proves `lv xs t = some d → Lv xs t d` by R1 (generalizing `xs d`), then R2 (`leaf`); R3, R4, R5, R2 with
R7 and R6, and R8 (`tag`); `simp [lv] at h`, i.e. R3 + R8 in one call (`node`, which `lv` always rejects). The
exercise's `lam` case is the `tag` case; `app` adds R9, R10 and R11.

---

## Part 2 · `typeOf_complete`

Statement: `HasType Γ t A → typeOf Γ t = some A`. Induct on the derivation `h`; each goal is a `typeOf`
equation in which the recursive calls are exactly the IHs, so `simp` with the IHs closes it.

**R12 · `induction h with | var hn => … | lam _ ih => … | app _ _ ih1 ih2 => …`** changes the **goal list and
the context**: one goal per rule of the relation, one IH per premise that is itself a derivation. The pattern
names only the rule's explicit premises; the `{…}` arguments of the rule appear as `Γ✝`, `n✝`, `A✝`, …. Write
`_` for a premise you do not need. No `generalizing` here: the derivation already carries its own context.
Placeholders: `(Q : List Nat → Tr → Nat → Prop) (xs : List Nat) (t : Tr) (d : Nat)`, toy `Lv`.

| Before | After |
|---|---|
| `h : Lv xs t d ⊢ Q xs t d` | `a✝ : xs✝[n✝]? = some d✝ ⊢ Q xs✝ (Tr.leaf n✝) d✝`, `a_ih✝ : Q (k✝ :: xs✝) t✝ d✝ ⊢ Q xs✝ (Tr.tag k✝ t✝) (k✝ + d✝)` |

In the exercise the `lam` goal is `typeOf Γ✝ (Tm.lam A✝ t✝) = some (A✝.arr B✝)` with
`ih : typeOf (A✝ :: Γ✝) t✝ = some B✝`.

**R13 · `simpa [f] using h`** **closes** the goal when the goal and `h` simplify to the same statement (here:
`f` unfolds to `xs[n]?`). This is the `var` case, `simpa [typeOf] using hn`. Placeholders:
`(xs : List Nat) (n d : Nat)`.

| Before | After |
|---|---|
| `hn : xs[n]? = some d ⊢ lv xs (Tr.leaf n) = some d` | ∅ |

**R14 · `simp [ih]` through a `match`** **closes** the goal: `ih : f a = some b` rewrites the scrutinee to
`some b`, and `simp` reduces `match some b with | some y => k y | …` to `k b`. In the exercise write
`simp [typeOf, ih]`: `typeOf` unfolds the step (R3, in the goal), `ih` rewrites the inner call.
Placeholders: `{α β γ : Type} (f : α → Option β) (k : β → Option γ) (a : α) (b : β) (c : γ)`.

```lean-goal
⊢ (match f a with | some y => k y | none => none) = some c
```

**R15 · `simp` on `if a = a then t else e`** changes the **goal**: `a = a` is `True`, so the `if` becomes its
`then` branch. In the exercise's `app` case, after `ih1`, `ih2` rewrite the scrutinees, the goal holds
`if A✝ = A✝ then some B✝ else none`, and the same `simp [typeOf, ih1, ih2]` call does R14 and R15 together.
Placeholders: `{α β : Type} [DecidableEq α] (a : α) (t e : β)`.

| Before | After |
|---|---|
| `⊢ P (if a = a then t else e)` | `⊢ P t` |

### Worked combination (W2 in `guide.lean`, on `lv`)

**W2** proves `Lv xs t d → lv xs t = some d` by R12, then R13 (`leaf`) and R14 (`tag`, `simp [lv, ih]`).

---

## Part 3 · `type_unique` (milestone)

Statement: `HasType Γ t A → HasType Γ t B → A = B`. Both derivations give, by `typeOf_complete`, an equation
`typeOf Γ t = some _`; rewrite one into the other and strip the `some`.

**R16 · `rw [e] at h`** changes the **context**: `h` is rewritten with the equation `e` (left side → right
side). Use `have h1 := typeOf_complete hA` first (TACTIC_STATES, "Adding facts"), then
`rw [typeOf_complete hB] at h1`. Placeholders: `{α : Type} (o : Option α) (a b : α) (e : o = some b)`.

| Before | After `rw [e] at h` |
|---|---|
| `h : o = some a ⊢ Q` | `h : some b = some a ⊢ Q` |

**R17 · `Option.some.inj`** is a **term**: `Option.some.inj : some a = some b → a = b`, and it **closes**
`a = b`. Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `h : some a = some b ⊢ a = b` | ∅ (`exact Option.some.inj h`) |

**R18 · `h.symm`** (`Eq.symm : a = b → b = a`) is a **term**; it **closes** `b = a`. After R16 the equation is
`some B = some A`, the wrong way round for `A = B`: combine as `(Option.some.inj h1).symm`.
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `h : a = b ⊢ b = a` | ∅ (`exact h.symm`) |

---

## Traps

- **Generalize.** `induction t` without `generalizing Γ A` gives an IH only for the very `Γ` and `A` of the
  statement; the `lam` body lives in `B :: Γ` and has another type, so it never applies.
- **Soundness: induct on `t`, not on `h`.** `h : typeOf Γ t = some A` is an equation, not an inductive
  predicate. Completeness is the opposite: induct on the derivation `h`, not on `t`.
- **`split at h`, not `split`.** In soundness the goal is a `HasType` and has no `match`; the information is
  in `h`.
- **The `app` case splits twice**: first the two-scrutinee `match` (R9), then, in its first branch, the `if`
  (R10). Each split leaves a `none = some A` branch for R8.
- **`cases h` needs a variable on one side** once the `some`s are peeled (`some (B.arr B✝) = some A`, with
  `A` a local variable). If both sides are compound terms, use `Option.some.inj h` (R17) to get an equation and
  rewrite with it.
- **`‹_›` can pick the wrong hypothesis** when several fit; in `app` the IHs need `heq✝¹ : typeOf Γ t = …` for
  `iht` and `heq✝ : typeOf Γ u = …` for `ihu`, and each IH's own premise selects the right one. If a step
  fails, write the type: `‹typeOf Γ t = some _›`.
- **Banned: `grind`, `try?`.** `try?` finds `(induction h) <;> grind [= typeOf]` for completeness, so both are
  banned. Do not leave `exact?`/`apply?` in the file either.
- Indent the body of each `| case =>` alternative consistently; a `·` bullet must cover one goal exactly.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on the term, IH for all `Γ`, `A` | `induction t generalizing Γ A with \| var n => … \| lam B t ih => … \| app t u iht ihu => …` | R1 |
| apply a typing rule | `exact .var h`, `exact .lam …`, `exact .app … …` | R2 |
| unfold one step of `typeOf` in `h` | `simp only [typeOf] at h` | R3 |
| which `match` branch ran | `split at h` | R4, R9 |
| `h : some x = some A` → replace `A` | `cases h` | R5 |
| use an unnamed hypothesis | `‹_›`, `‹T›` | R6 |
| use the IH | `ih ‹_›` | R7 |
| close a goal with `h : none = some _` | `simp at h` | R8 |
| which `if` branch ran | `split at h` | R10 |
| merge variables equal by a hypothesis | `subst_vars` | R11 |
| induction on the derivation | `induction h with \| var hn => … \| lam _ ih => … \| app _ _ ih1 ih2 => …` | R12 |
| goal and `h` the same after unfolding | `simpa [typeOf] using hn` | R13 |
| unfold the goal and rewrite inner calls with the IHs | `simp [typeOf, ih1, ih2]` | R14, R15 |
| rewrite a hypothesis | `rw [e] at h` | R16 |
| `some a = some b → a = b` | `Option.some.inj h` | R17 |
| flip an equation | `h.symm` | R18 |
| see the state | infoview | |
