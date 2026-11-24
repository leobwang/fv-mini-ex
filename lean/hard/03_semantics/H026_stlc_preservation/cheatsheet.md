# H026 · STLC progress and preservation with de Bruijn substitutions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033: `intro`, `exact`, `cases`/`rcases`/`obtain` on `∨` and `∃`,
`refine`, `<;>`, named arguments) and de Bruijn indices (M048: `var 0` is the innermost binder).
**New here:** induction on a *derivation* (a proof of an inductive predicate such as `HasType Γ t A`),
inversion with `cases`, `generalize`, `subst`, and the renaming → substitution → preservation chain.
No Mathlib: everything is core Lean.

## How to read an entry

Each entry is one tactic or one proof term. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `Q`, `G` are "the rest of your goal". The step changes only the part shown inside `P (…)`.
- The guide does not use the exercise's `Tm`, `Ctx`, `HasType`. It uses a toy language with the same shape:

  | Toy (guide) | Exercise | Role |
  |---|---|---|
  | `Expr` with `leaf n`, `pair a b`, `bind a` | `Tm` with `var n`, `app t u`, `lam A t` | syntax; `bind`/`lam` opens index 0 |
  | scope `s : Nat → Bool` | context `Γ : Ctx = Nat → Option Ty` | what each index means |
  | `ext s` (`0 ↦ true`, `n + 1 ↦ s n`) | `Ctx.cons A Γ` (`0 ↦ some A`, `n + 1 ↦ Γ n`) | context under a binder |
  | `Ok s e` (rules `leaf`, `pair`, `bind`) | `HasType Γ t A` (rules `var`, `app`, `lam`) | the judgement you induct on |
  | `IsBind e` (one rule) | `Value t` (one rule) | a "value" predicate |

- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `HasType Γ t A` | the typing judgement (on paper written with a turnstile, "Γ proves t : A"): in context `Γ`, term `t` has type `A`; a proof of it is a derivation tree of the rules `var`, `lam`, `app` |
| `Value t` | `t` is a value; the only rule is `Value.lam`, so values are exactly the `Tm.lam A t` |
| `Step t t'` | `t` reduces to `t'` in one call-by-value step (rules `beta`, `appL`, `appR`) |
| `Ctx` | `Nat → Option Ty`. `Γ n = some A`: index `n` has type `A`; `Γ n = none`: `n` is unbound |
| `Ctx.cons A Γ` | the context `Γ` under one more binder of type `A` (source: `Γ.cons A`). Index `0 ↦ some A`, `n + 1 ↦ Γ n` |
| `(fun x => none)` | the empty context: no index is bound |
| `A.arr B` | `Ty.arr A B`, the function type `A → B` |
| `t.app u`, `Tm.lam A t`, `Tm.var n` | `Tm.app t u` (application), `λ x : A. t`, the variable with index `n` |
| `rename ρ t` | `t` with every free `var n` replaced by `var (ρ n)`; under `lam` it uses `upRen ρ` (`0 ↦ 0`, `n + 1 ↦ ρ n + 1`) |
| `subst σ t` | `t` with every free `var n` replaced by the term `σ n`; under `lam` it uses `up σ` (`0 ↦ var 0`, `n + 1 ↦ rename Nat.succ (σ n)`) |
| `upRen ρ`, `up σ` | `ρ` / `σ` lifted under one binder: index `0` goes to `0` / `var 0`; index `n + 1` goes to the image of `n`, shifted up by one |
| `beta v` | the substitution of a beta step: `0 ↦ v`, `n + 1 ↦ var n` |
| `x.f y` (`t.app u`, `A.arr B`; toy `a.pair b`, `a.bind`) | dot notation: `T.f x y` where `T` is the type of `x` (`Tm.app t u`, `Expr.pair a b`) |
| `.var hn`, `.lam h`, `.inl x` | a constructor whose namespace (`HasType`, `Or`, …) Lean reads off the expected type (R2) |
| `a✝`, `t✝`, `A✝¹` | an *inaccessible* name: Lean made it, you cannot type it. Name it with `with \| rule x y =>` |
| `a_ih✝` | an induction hypothesis Lean made (R1) |
| `∀ {Δ : Ctx} {ρ : Nat → Nat}, …` in an IH | the IH holds for every `Δ`, `ρ`; Lean fills them in when you apply it |
| `case lam.zero` | the goal for the `lam` rule, then the `zero` case of `cases n` |
| `case refl` | the goal left after `cases` on an equation (R9) |

---

## Part 1 · `rename_typing` (milestone)

Statement: if a renaming `ρ` sends every index typed in `Γ` to an index with the same type in `Δ`
(`hρ : ∀ n A, Γ n = some A → Δ (ρ n) = some A`), then `HasType Γ t A → HasType Δ (rename ρ t) A`.
Induction on the typing derivation `h`. Under `lam` both contexts grow (`Ctx.cons A Γ`, `Ctx.cons A Δ`)
and `ρ` becomes `upRen ρ`, so the IH must hold for every `Δ` and `ρ`: generalize them.
After the induction the goals read `HasType Δ (rename ρ (Tm.var n✝)) A✝`,
`HasType Δ (rename ρ (Tm.lam A✝ t✝)) (A✝.arr B✝)` and `HasType Δ (rename ρ (t✝.app u✝)) B✝`: `rename` has not
been unfolded on screen, but it computes (R5), so `.var`, `.lam`, `.app` apply directly (R2, R3).

**R1 · `induction h generalizing s'`** changes the **goal list**: one goal per rule of the inductive
predicate. Each goal has the rule's premises as hypotheses and one IH per premise that is itself a
derivation. `generalizing s'` makes the IH `∀ {s'}, …`; `hs` mentions `s` and `s'`, so Lean takes it along by
itself and it becomes a premise of the IH. Placeholders: `{s s' : Nat → Bool} {e : Expr}`,
`(P : (Nat → Bool) → Expr → Prop)`, `(hs : ∀ n, s n = true → s' n = true)`, `(h : Ok s e)`.

| Before | After (one goal per rule) |
|---|---|
| `h : Ok s e ⊢ P s' e` | `a✝ : s✝ n✝ = true ⊢ P s' (Expr.leaf n✝)` |
| | `⊢ P s' (a✝².pair b✝)` |
| | `a✝ : Ok (ext s✝) a✝¹ ⊢ P s' a✝¹.bind` |

In the `bind` goal the IH reads `a_ih✝ : ∀ {s' : Nat → Bool}, (∀ (n : Nat), ext s✝ n = true → s' n = true) → P s' a✝¹`:
its premise is about `ext s✝`, the scope under the binder. In the exercise, `induction h generalizing Δ ρ with
| var hn => … | lam _ ih => … | app _ _ ih1 ih2 => …` gives the `lam` IH
`ih : ∀ {Δ ρ}, (∀ n A, Ctx.cons A✝ Γ✝ n = some A → Δ (ρ n) = some A) → HasType Δ (rename ρ t✝) B✝`.
In `| rule x y =>` you name only the rule's explicit premises, then the IHs; the implicit `{Γ A B t}` stay `✝`.

**R2 · `exact .leaf hn`** **closes** the goal with a rule. A rule is a function from its premises to its
conclusion: `Ok.leaf : s n = true → Ok s (.leaf n)`. `.leaf` is short for `Ok.leaf` because the goal's head is
`Ok`. Nest them: `.app (ih1 hρ) (ih2 hρ)`, `.inr ⟨_, .beta hv⟩`. Placeholders: `{s : Nat → Bool} {n : Nat}`.

| Before | After |
|---|---|
| `hn : s n = true ⊢ Ok s (Expr.leaf n)` | no goals |

**R3 · `refine .bind (ih ?_)`** changes the **goal**: apply the rule, feed its premise from the IH, and leave
the IH's own premise as the new goal. Lean finds the IH's implicit `{s₂}` from the goal. Placeholders:
`{s s' : Nat → Bool} {a : Expr}`, `ih : ∀ {s₂}, (∀ n, ext s n = true → s₂ n = true) → Ok s₂ a`.

| Before | After |
|---|---|
| `⊢ Ok s' a.bind` | `⊢ ∀ (n : Nat), ext s n = true → ext s' n = true` |

In the exercise the new goal is the lifted hypothesis
`∀ (n : Nat) (A : Ty), Ctx.cons A✝ Γ✝ n = some A → Ctx.cons A✝ Δ (upRen ρ n) = some A`. Next: `intro n A hn`.

**R4 · `cases n`** changes the **goal list**: one goal for index `0`, one for `n + 1`. Write
`cases n with | zero => … | succ n => …` to name the new `n`. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n✝ : Nat ⊢ P (n✝ + 1)` |

**R5 · definitions compute** changes the **goal** (with `show`) or nothing (with `exact`). A function defined
by `| 0 => … | n + 1 => …` reduces on `0` and on `n + 1`: `ext s (n + 1)` *is* `s n`, `ext s 0` *is* `true`.
`exact` checks types up to this computation, so `exact hn` and `exact hρ n A hn` work as they are. `show T`
replaces the goal by a `T` that computes to the same thing, only to make it readable. Placeholders:
`(s s' : Nat → Bool) (n : Nat)`.

| Before | After `show s' n = true` |
|---|---|
| `hn : ext s (n + 1) = true ⊢ ext s' (n + 1) = true` | `⊢ s' n = true` |

In the exercise: `rename ρ (Tm.lam A t)` is `Tm.lam A (rename (upRen ρ) t)`, `subst σ (Tm.var n)` is `σ n`,
`Ctx.cons A Γ (n + 1)` is `Γ n`, `Ctx.cons A Γ 0` is `some A`, `upRen ρ 0` is `0`,
`upRen ρ (n + 1)` is `ρ n + 1`, `up σ (n + 1)` is `rename Nat.succ (σ n)`, `beta v 0` is `v`,
`beta v (n + 1)` is `Tm.var n`.

**W1** in the guide is the whole pattern on the toy language: `Ok.mono` widens a scope with R1, R2, R3,
`intro`, R4, R5.

---

## Part 2 · `subst_typing` (milestone)

Statement: if `σ` sends every index typed in `Γ` to a term of the same type in `Δ`
(`hσ : ∀ n A, Γ n = some A → HasType Δ (σ n) A`), then `HasType Γ t A → HasType Δ (subst σ t) A`.
Same shape as Part 1 (R1, R2, R3, `intro`, R4). New: the `n + 1` case of the lifted hypothesis is
`HasType (Ctx.cons A✝ Δ) (up σ (n + 1)) A`, which computes (R5) to a typing of `rename Nat.succ (σ n)`. That is
Part 1 with `ρ := Nat.succ`.

**R6 · named argument `(f := Nat.succ)`** fixes an implicit argument. It **closes** the goal when the lemma's
conclusion matches. Placeholders: `(s : Nat → Bool) (e : Expr) (Q : (Nat → Bool) → Expr → Prop)` and a lemma
`L : ∀ {s₁ s₂ : Nat → Bool} {f : Nat → Nat}, (∀ n, s₁ n = true → s₂ (f n) = true) → Q s₂ e`. With `f` fixed, the
premise for `s₂ = ext s` is `∀ n, s₁ n = true → ext s (Nat.succ n) = true`, which computes to
`∀ n, s n = true → s n = true` (R5): `fun _ h => h` proves it.

| Before | After `exact L (f := Nat.succ) (fun _ h => h)` |
|---|---|
| `⊢ Q (ext s) e` | no goals |

Without `(ρ := Nat.succ)` in the exercise, Lean solves `ρ` from `fun _ _ h => h` first and picks
`ρ := fun x => x`, so the result has type `HasType Δ (rename (fun x => x) (σ n)) A` and does not match.

---

## Part 3 · `value_arr` (milestone, canonical forms)

Statement: a value `v` whose type is `A.arr B` is a `Tm.lam A t` for some `t`. Take `hv` apart (R7), then `h`
(R8); the goal is then `∃ t, Tm.lam A t✝ = Tm.lam A t`, closed by `⟨_, rfl⟩`.

**R7 · `cases hv`** with `hv : IsBind e` changes the **context and goal**: `IsBind` has one rule, whose
conclusion is `IsBind (.bind a)`, so `e` is replaced by `.bind a✝` everywhere. Placeholders: `{e : Expr}`,
`(P : Expr → Prop)`.

| Before | After |
|---|---|
| `hv : IsBind e ⊢ P e` | `a✝ : Expr ⊢ P a✝.bind` |

**R8 · `cases h`** (inversion) changes the **context**: `h` is replaced by the premises of the rules whose
conclusion can match `h`'s indices; rules that cannot match are dropped, and indices that must be equal are
unified. Name the premises with `cases h with | pair ha hb => …`. Placeholders: `{s : Nat → Bool} {a b : Expr}`,
`(h : Ok s (.pair a b))`.

| Before | After |
|---|---|
| `h : Ok s (a.pair b) ⊢ P` | `a✝¹ : Ok s a, a✝ : Ok s b ⊢ P` |

In `value_arr`, after R7 the hypothesis is `h : HasType Γ (Tm.lam A✝ t✝) (A.arr B)`. Only the `lam` rule
concludes with a `Tm.lam`, and it forces the binder type `A✝` to be `A`; `cases h` leaves
`⊢ ∃ t, Tm.lam A t✝ = Tm.lam A t`.

---

## Part 4 · `preservation`

Statement: `HasType Γ t A → Step t t' → HasType Γ t' A`. Induct on the step `hs` (R1 on `Step`), generalizing
`A`: in the `appL` case the IH is needed at the arrow type of the function part. `h` mentions `t`, so Lean
takes it along and each IH reads `∀ {A}, HasType Γ t✝ A → HasType Γ t'✝ A`. In every case invert `h` (R8).

- `beta`: `cases h` gives `h1 : HasType Γ (Tm.lam A✝¹ t✝) (A✝.arr A)` and `h2 : HasType Γ v✝ A✝`; `cases h1`
  gives `hb : HasType (Ctx.cons A✝ Γ) t✝ A`. Apply Part 2 with `refine subst_typing ?_ hb` (R3): the goal is
  `∀ (n : Nat) (A : Ty), Ctx.cons A✝ Γ n = some A → HasType Γ (beta v✝ n) A`. `intro n B hn; cases n` (R4); index `n + 1` is
  `.var hn` (R2, R5); index `0` needs R9.
- `appL`, `appR`: `cases h with | app h1 h2 => …` and rebuild with `.app` (R2), using the IH on one side.

**R9 · `cases hn`** with `hn : some a = some b` changes the **context and goal**: `some` is injective, so `b`
is replaced by `a` everywhere and `hn` disappears. `cases` first computes `hn`, so it also works on
`hn : Ctx.cons A✝ Γ 0 = some B` (which is `some A✝ = some B`). Placeholders: `{α : Type} (a b : α)`,
`(P : α → α → Prop)`.

| Before | After |
|---|---|
| `hn : some a = some b ⊢ P a b` | `⊢ P a a` |

In `preservation` the goal `HasType Γ (beta v✝ 0) B` becomes `HasType Γ (beta v✝ 0) A✝`, which is `h2` (R5).

---

## Part 5 · `progress`

Statement: a term typed in the empty context `(fun _ => none)` is a `Value` or takes a `Step`. Induct on `h`.
`induction` needs the context index to be a variable, so first replace `(fun _ => none)` by a variable `Γ` (R10).
Then the `var` case is impossible (R12, R13), `lam` is a value (R2: `.inl .lam`), and `app` splits on the two
IHs with `rcases ih1 hΓ with hv1 | ⟨t', ht'⟩` (E006). Function part a value and argument a value: Part 3 turns
`hv1` into a `lam` (R14), and `.beta` fires.

**R10 · `generalize hs : e₀ = s at h`** changes the **context**: the expression `e₀` in `h` becomes a new
variable `s`, and `hs : e₀ = s` records what it was. Write the type of `e₀` out:
`(fun _ => none : Ctx)`. Placeholders: `{e : Expr}`, `(h : Ok (fun _ => false) e)`.

| Before | After |
|---|---|
| `h : Ok (fun x => false) e ⊢ P` | `hs : (fun x => false) = s, h : Ok s e ⊢ P` |

**R11 · `induction h`** after R10 changes the **goal list** as R1 does. `hs` mentions the index `s`, so every
goal gets its own `hs : (fun x => false) = s✝` and every IH gets the premise `(fun x => false) = s✝ → …`; apply
the IH to `hs` (`ih1 hΓ`). Placeholders: `{s : Nat → Bool} {e : Expr}`, `(P : Expr → Prop)`.

| Before | After (two of the three goals) |
|---|---|
| `hs : (fun x => false) = s, h : Ok s e ⊢ P e` | `a_ih✝¹ : (fun x => false) = s✝ → P a✝² ⊢ P (a✝².pair b✝)` |
| | `hs : (fun x => false) = s✝, a_ih✝ : (fun x => false) = ext s✝ → P a✝¹ ⊢ P a✝¹.bind` |

Under the binder the IH's premise is `(fun x => false) = ext s✝`, which you cannot prove. In `progress` the
`lam` case needs no IH, so this does not matter.

**R12 · `subst hs`** with `hs : e₀ = s` and `s` a variable changes the **context**: `s` is replaced by `e₀`
everywhere and `hs` disappears. Placeholders: `{s : Nat → Bool} {n : Nat}`, `(G : Prop)`.

| Before | After |
|---|---|
| `hs : (fun x => false) = s, hn : s n = true ⊢ G` | `hn : (fun x => false) n = true ⊢ G` |

**R13 · `cases hn`** with `hn : none = some a` **closes** the goal: two different constructors are never equal,
so no case is left. `cases` computes first, so `(fun x => none) n = some a` works too. Placeholders:
`{α : Type} (a : α) (n : Nat)`, `(G : Prop)`.

| Before | After |
|---|---|
| `hn : (fun x => none) n = some a ⊢ G` | no goals |

**R14 · `obtain ⟨a, rfl⟩ := hv`** with `hv : ∃ a, e = .bind a` changes the **context and goal**: the `rfl`
pattern substitutes the equation, so `e` is replaced by `.bind a` everywhere (in the goal and in every
hypothesis). Write `⟨_, rfl⟩` to leave the witness unnamed (it shows as `w✝`). Placeholders: `{e : Expr}`,
`(P : Expr → Prop)`.

| Before | After |
|---|---|
| `⊢ P e` | `a : Expr ⊢ P a.bind` |

In `progress`, `obtain ⟨_, rfl⟩ := value_arr hv1 h1` turns `t✝` into `Tm.lam A✝ w✝` in `h1`, `hv1`, `ih1` and the
goal, so `.inr ⟨_, .beta hv2⟩` type-checks.

**W2** in the guide runs R10, R11, R12, R13 on the toy language: with the empty scope, the leftmost part of a
scoped expression is a `bind`. R10 changes only the context; the goal stays

```lean-goal
⊢ IsBind (leftmost e)
```

---

## Traps

- Do not leave search tactics (`exact?`, `apply?`, `try?`) in the file: they are not proofs.
- `induction h` without `generalizing Δ ρ` fixes the IH at the original `Δ`, `ρ`. Under `lam` you need it at
  `Ctx.cons A Δ` and `upRen ρ`, so the IH is useless.
- `induction h` on `h : HasType (fun _ => none) t A` fails with "Index in target's type is not a variable".
  `generalize` first (R10).
- In `preservation`, induct on the step `hs`, not on `h`, and generalize `A`: without it the `appL` IH is stuck
  at type `A` and `ih h1` fails.
- `rename_typing (fun _ _ h => h) …` without `(ρ := Nat.succ)` elaborates with `ρ := fun x => x` (R6).
- `cases n with | zero => … | succ n => …` re-uses the name `n`; the old `n` is gone after `cases`.
- In `| lam _ ih =>` the names go to the explicit premises and the IHs only; the implicit `{Γ A B t}` stay `✝`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on a derivation, IH at other contexts | `induction h generalizing Δ ρ with \| var hn => … \| lam _ ih => … \| app _ _ ih1 ih2 => …` | R1 |
| use a rule | `exact .var hn`, `.app (ih1 hρ) (ih2 hρ)` | R2 |
| rule + IH, IH's premise left as goal | `refine .lam (ih ?_)` | R3 |
| index `0` vs `n + 1` | `intro n A hn; cases n with \| zero => … \| succ n => …` | R4 |
| `Ctx.cons A Γ (n + 1)` is `Γ n`, `up σ (n + 1)` is `rename Nat.succ (σ n)` | `exact` as is, or `show …` | R5 |
| fix an implicit argument | `rename_typing (ρ := Nat.succ) (fun _ _ h => h) h'` | R6 |
| value → its shape | `cases hv` | R7 |
| invert a typing | `cases h with \| app h1 h2 => …` | R8 |
| `some a = some b` | `cases hn` | R9 |
| induct with a fixed context | `generalize hΓ : (fun _ => none : Ctx) = Γ at h` then `induction h` | R10, R11 |
| use the context equation | `subst hΓ`, or apply the IH to it: `ih1 hΓ` | R12, R11 |
| `none = some a` | `cases hn` | R13 |
| `∃ t, v = Tm.lam A t` → replace `v` | `obtain ⟨_, rfl⟩ := value_arr hv h` | R14 |
| `Value t ∨ ∃ t', Step t t'` | `.inl .lam`, `.inr ⟨_, .appL ht'⟩`; split with `rcases … with hv \| ⟨t', ht'⟩` | R2 |
| see the state | infoview | |
