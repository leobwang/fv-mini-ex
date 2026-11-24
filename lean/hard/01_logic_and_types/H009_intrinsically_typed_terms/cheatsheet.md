# H009 · Intrinsically typed terms and a type checker: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, structural recursion, `induction`, `cases`,
`simp`, `rw`, `exact`, anonymous constructors `⟨…⟩`. **New here:** indexed families (`Expr : Ty → Type`),
dependent pairs `Σ t, Expr t`, heterogeneous equality `≍`, casts `h ▸ x`, and the tactics that take apart a
`match` inside a goal or a hypothesis (`split`, `split at h`, `rename_i`, `subst`, `obtain`). Core Lean
only: no imports, and `grind` and the search tactics are banned.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal". The step changes only the part inside `P (…)`, wherever it sits in a larger
  goal. `G` is a goal the step does not touch.
- Placeholders are written as Lean binders. `{ι : Type} {F : ι → Type}` is an arbitrary *family* of types: for
  each index `i : ι` a type `F i`. In the exercise `ι = Ty` and `F = Expr`.
- The guide's own objects (not the exercise's): `K` with kinds `a, b`; the family `Tm : K → Type` with
  `atom n : Tm .a`, `flag : Tm .b`, `pair l r : Tm k`; and `step : Nat → Option Nat`, whose clause
  `step (n + 1) = match step n with | some m => some (m + 1) | none => none` has the same shape as `check`.
- A goal containing `|` (a `match`) cannot sit in a table cell; it is shown in a `lean-goal` block instead.
  A hypothesis containing `, ` (such as `h : ⟨i, x⟩ = ⟨j, y⟩`) is written in its own span before the `⊢` span.
- Every `⊢` cell and every `lean-goal` line is a state Lean reaches in the companion file; `tools/guide_sync.py`
  checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Expr Ty.nat`, `Expr t` | the type of terms of object type `.nat`, or of `t`. `Expr` is an *indexed family*: one type per `t : Ty` |
| `Ty.denote t` | the Lean type of values of type `t`: `Nat` for `.nat`, `Bool` for `.bool`. `eval` returns one |
| `@[reducible] def` (in the spec) | Lean may unfold `Ty.denote .nat` to `Nat` on its own, so `a.eval + b.eval` typechecks as `Nat` addition |
| `def f : {t : Ty} → Expr t → …` with clauses `\| _, .lit n => …` (in the spec) | `f` takes the index `t` implicitly; each clause matches it with `_` (it is forced by the constructor) and then the term |
| `UExpr.lit n` vs `Expr.lit n` | same constructor names in two types: untyped syntax vs typed term. `.lit n` in the source picks the one the expected type asks for |
| `decide (p)` | the `Bool` that says whether the decidable proposition `p` holds |
| `if c.eval = true then x.eval else y.eval` | how Lean prints `if c.eval then …`: a `Bool` `b` used as a condition means `b = true` |
| `a.plus b`, `c'.ite x' y'` | `Expr.plus a b`, `Expr.ite c' x' y'` (dot notation) |
| `(t : Ty) × Expr t` | `Σ t, Expr t`: dependent pairs of a type `t` and a term of type `Expr t` |
| `⟨t, e⟩` | the pair `Sigma.mk t e`; `some ⟨t, e⟩ : Option (Σ t, Expr t)` is a successful check |
| `x ≍ y` | `HEq x y`: `x` equals `y`, where their types may differ (here `Expr t1` and `Expr t`) |
| `h ▸ x`, `⋯ ▸ x` | `x : Expr t1` cast to `Expr t2` along `h : t1 = t2`; `⋯` is a proof Lean does not print |
| `if h : c then a else b` | a *dependent* `if`: the branch `a` may use `h : c` (as `check` does with `h ▸ x'`) |
| `(match a.fold, b.fold with …)` | an unevaluated `match`: Lean cannot pick an arm until the discriminants are constructors |
| `\| x, x_1 => none` inside a printed `match` | the catch-all arm `\| _, _ => none`; Lean prints the wildcards as names |
| `x✝`, `heq✝`, `h✝`, `m✝`, `t✝` | *inaccessible* names Lean made up; you cannot type them. Name them with `rename_i` (R9) |
| `x✝¹ x✝`, `heq✝¹ heq✝` | several inaccessible names of the same base: the superscript counts back from the newest (`x✝`) |
| `heq✝ : a.fold = Expr.lit m✝` | added by `split`: the discriminant matched this arm's pattern |
| `x✝ : ∀ (m n : Nat), … → False` | added by `split` for a catch-all arm: the earlier arms did not match |
| `case h_1`, `case h_2` | the goals for the arms of a `match`, in order, after `split` |
| `case isTrue`, `case isFalse` | the goals for the two branches of an `if`, after `split`. Nested splits join names: `case h_1.isTrue` |
| `case refl` | the goal after `cases` substituted an equation |
| `c'_1`, `x'_1` | a bound name renamed because `c'` is already in the context |

---

## Part 1 · `fold_eval`

Statement: `e.fold.eval = e.eval` for every `e : Expr t`. Constant folding preserves meaning. Induction on
`e` (R1); `lit`, `tt`, `ff` are `rfl`; `le` is `simp` with the two definitions and the IHs; `plus` and `ite`
need R2 → R3 → R4 because `fold` matches on the folded subterms.

**R1 · `induction e with | c x ih => …`** changes the **goal list**: one goal per constructor of the family,
with the index replaced by the constructor's index and one IH per recursive field. Placeholders:
`(P : {k : K} → Tm k → Prop) {k : K} (e : Tm k)`. For a constructor with an implicit index (`pair {k}`,
like `ite {t}`) the index appears as `k✝`. In the guide `?_` leaves each case open; in a proof write the
case's tactics after `=>`.

| Before | After |
|---|---|
| `e : Tm k ⊢ P e` | `n : Nat ⊢ P (Tm.atom n)`, `⊢ P Tm.flag`, `k k✝ : K, l r : Tm k✝, ihl : P l, ihr : P r ⊢ P (l.pair r)` |

**R2 · `simp only [f]`** changes the **goal**: `f (constructor …)` is replaced by that clause's body, using
the equation lemmas Lean generated for `f`. When the body is a `match` on recursive calls, the `match` now
sits in the goal. Placeholders: `(n : Nat) (P : Option Nat → Prop)`, `f = step`.

```lean-goal
⊢ P (step (n + 1))
⊢ P (match step n with | some m => some (m + 1) | none => none)
```

**R3 · `split`** changes the **goal list**: one goal per arm of the first `match` (or `if`) in the goal. Each
goal records which arm it is: `heq✝ : discriminant = pattern` for a pattern arm, `x✝ : … → False` for a
catch-all arm (no earlier arm matched). The discriminant itself is generalised to `x✝`. Placeholders:
`(n : Nat) (P : Option Nat → Prop)`. Before:

```lean-goal
⊢ P (match step n with | some m => some (m + 1) | none => none)
```

| Before | After |
|---|---|
| the goal above | `x✝ : Option Nat, m✝ : Nat, heq✝ : step n = some m✝ ⊢ P (some (m✝ + 1))`, `heq✝ : step n = none ⊢ P none` |

**R4 · `simp_all [d]`** changes the **goal and the context**, and usually **closes** the goal. It simplifies
every hypothesis using the others, then the goal using all of them, unfolding the definitions `d`. After R3
this is what you want: `heq✝ : a.fold = Expr.lit m✝` rewrites inside `iha : a.fold.eval = a.eval`, which
then rewrites the goal. Placeholders: `{α β : Type} (f : α → β) (g : α → α) (a c : α) (P : β → Prop)`.

| Before | After |
|---|---|
| `ih : f (g a) = f a, heq : g a = c, hP : P (f c) ⊢ P (f a)` | closed |

---

## Part 2 · `check_erase`

Statement: `check e.erase = some ⟨t, e⟩`. Erasing the types and re-checking gives back the same typed term.
Induction on `e` (R1). In each recursive case, after unfolding `Expr.erase` and `check`, the goal has the
checker's `match` on `check a.erase, …`; the IHs rewrite those discriminants to `some ⟨…⟩` (R5) and, for
`ite`, the `if h : t = t` is decided by `rfl` (R6). One `simp [Expr.erase, check, ihs]` does all of it.

**R5 · `simp only [ih]`, with `ih : x = some a`** changes the **goal**: the discriminant becomes the
constructor `some a`, and `simp` then reduces the `match` to that arm. Placeholders:
`(n m : Nat) (ih : step n = some m) (P : Option Nat → Prop)`. Before:

```lean-goal
⊢ P (match step n with | some m => some (m + 1) | none => none)
```

| Before | After |
|---|---|
| the goal above | `ih : step n = some m ⊢ P (some (m + 1))` |

**R6 · `simp` on `if h : t = t then x else y`** changes the **goal**: `simp` proves the condition `t = t`
(first to `True`, then `dite_true`) and keeps the `then` branch. Placeholders:
`{α β : Type} [DecidableEq α] (t : α) (x y : β)`. `[DecidableEq α]` means `=` on `α` can be computed; `Ty`
has it from `deriving DecidableEq`.

| Before | After |
|---|---|
| `⊢ P (if _h : t = t then x else y)` | `⊢ P x` |

---

## Part 3 · `check_plus_inv` (MILESTONE)

Statement: if `check (.plus a b) = some ⟨t, e⟩` then both arguments check at `.nat`, with results `a'`, `b'`,
and `⟨t, e⟩ = ⟨.nat, .plus a' b'⟩` as Σ-pairs. That last conjunct is a Σ-equation because `e : Expr t` and
`.plus a' b' : Expr .nat` have different types, so `e = .plus a' b'` would not typecheck. Used in Part 5.

**R7 · `simp only [f] at h`** changes the **context**: R2 applied to the hypothesis `h`. Placeholders:
`(n k : Nat) (G : Prop)`, `f = step`.

| Before | After |
|---|---|
| `h : step (n + 1) = some k ⊢ G` | `h` is now the `match` below; goal `G` unchanged |

```text
h : (match step n with | some m => some (m + 1) | none => none) = some k
```

**R8 · `split at h`** changes the **goal list**: R3 applied to the first `match` or `if` in `h`. In each goal,
`h` is that arm's value. `next a b => tac` works on the first goal and names its inaccessible hypotheses
`a b` (like R9). Placeholders: `(n k : Nat) (G : Prop)`, `h` as after R7.

| Before | After |
|---|---|
| `h` as after R7 | `m✝ : Nat, heq✝ : step n = some m✝, h : some (m✝ + 1) = some k ⊢ G`, `heq✝ : step n = none, h : none = some k ⊢ G` |

On a dependent `if` (the inner test of `check`'s `ite` case) the cases are `isTrue` / `isFalse`, and the
condition arrives as `h✝`. Placeholders: `{α β : Type} [DecidableEq α] (t₁ t₂ : α) (x : t₁ = t₂ → β) (y z : β)`.

| Before | After |
|---|---|
| `h : (if e : t₁ = t₂ then x e else y) = z ⊢ G` | `h✝ : t₁ = t₂, h : x h✝ = z ⊢ G`, `h✝ : ¬t₁ = t₂, h : y = z ⊢ G` |

**R9 · `rename_i x hx`** changes the **context**: it names the *last* inaccessible hypotheses, in order. In
`check_plus_inv` after R8 the last four are `a'✝ b'✝ heq✝¹ heq✝`, so `rename_i a' b' ha hb` names them
(`x✝¹ x✝` before them stay unnamed). Placeholders: `(P : Nat → Prop)`.

| Before | After |
|---|---|
| `n✝ : Nat, a✝ : n✝ = 0 ⊢ P n✝` | `n : Nat, hn : n = 0 ⊢ P n` |

**R10 · `Option.some.inj`** changes the **context** (with `have`): `Option.some.inj : some a = some b → a = b`.
`h.symm` turns `h : a = b` into `b = a`. Placeholders: `{α : Type} (a b : α)`.

| Before | After `have h' := Option.some.inj h` |
|---|---|
| `h : some a = some b ⊢ b = a` | `h' : a = b ⊢ b = a` |

**R11 · `simp at h`, with `h : none = some a`** **closes** the goal: `simp` knows distinct constructors are
never equal, so `h` becomes `False` and the goal is done. Every fallback arm of `check` ends here.
Placeholders: `{α : Type} (a : α) (G : Prop)`.

| Before | After |
|---|---|
| `h : none = some a ⊢ G` | closed |

---

## Part 4 · `check_ite_inv` (MILESTONE)

Statement: if `check (.ite c x y) = some ⟨t, e⟩` then `c` checks at `.bool`, `x` and `y` both check at `t`, and
`e = .ite c' x' y'`. A plain equation is fine here: both sides have type `Expr t`. Used in Part 5. The
`isTrue` arm of the inner `if` leaves `h : some ⟨t2, c'.ite (h✝ ▸ x') y'⟩ = some ⟨t, e⟩`, which R12–R16 take
apart.

**R12 · `subst h`, with `h : i = j` and `j` a local variable** changes the **context**: `j` disappears and every
`j` (in types too) becomes `i`. Use it on the `h✝ : t1 = t2` from the inner `if`, after R9 names it.
Placeholders: `{ι : Type} {F : ι → Type} (i j : ι) (y : F j) (P : (k : ι) → F k → Prop)`.

| Before | After |
|---|---|
| `y : F j, h : i = j ⊢ P j y` | `y : F i ⊢ P i y` |

**R13 · `h ▸ x`, with `h : i = i`** changes the **goal** (under `simp`): a cast along an equation between equal
indices is the identity, and `simp` removes it. After R12, the `h✝ ▸ x'` of `check` is such a cast (printed
`⋯ ▸ x'`). Placeholders: `{ι : Type} {F : ι → Type} (i : ι) (h : i = i) (x : F i) (P : F i → Prop)`.

| Before | After `simp` |
|---|---|
| `h : i = i ⊢ P (h ▸ x)` | `⊢ P x` |

**R14 · `simp at h` on `some ⟨i, x⟩ = some ⟨j, y⟩`** changes the **context**. Two simp lemmas fire:
`Option.some.injEq : (some a = some b) = (a = b)` and `Sigma.mk.inj_iff : ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂`.
The second components get `≍`, because before you know `i = j` they have different types `F i`, `F j`.
Placeholders: `{ι : Type} {F : ι → Type} (i j : ι) (x : F i) (y : F j) (G : Prop)`.

| Before | After |
|---|---|
| `h : some ⟨i, x⟩ = some ⟨j, y⟩` and `⊢ G` | `h : i = j ∧ x ≍ y ⊢ G` |

**R15 · `obtain ⟨rfl, h⟩ := h`** changes the **context**: it splits the `∧`; the pattern `rfl` substitutes the
equation `i = j` at once (as R12; one side must be a local variable), and `h` keeps the `≍`. Now both sides of
the `≍` have the same type. Placeholders as in R14, `(P : (k : ι) → F k → Prop)`.

| Before | After |
|---|---|
| `h : i = j ∧ x ≍ y ⊢ P j y` | `y : F i, h : x ≍ y ⊢ P i y` |

**R16 · `cases h`, with `h : x ≍ y`, both of type `F i`, `y` a local variable** changes the **context**: `y`
is replaced by `x` everywhere. Placeholders: `{ι : Type} {F : ι → Type} (i : ι) (x y : F i) (P : F i → Prop)`.

| Before | After |
|---|---|
| `h : x ≍ y ⊢ P y` | `⊢ P x` |

### Worked combinations (W1–W3, on the guide's objects)

**W1: induction + R2 → R3 → R4** (the `fold_eval` pattern). `step n = some n` by `induction n`; the `succ`
case is `simp only [step]` then `split <;> simp_all`. In the `some` arm `simp_all` combines
`heq✝ : step n = some m✝` with `ih : step n = some n`.

```lean-goal
⊢ step n = some n
```

**W2: an inversion lemma for `step`** (the `check_plus_inv` pattern): R7, R8, then R9 + R10 in the matching
arm and R11 in the other.

| Step | State |
|---|---|
| start | `h : step (n + 1) = some k ⊢ ∃ m, step n = some m ∧ k = m + 1` |
| R8, arm `some` | `m✝ : Nat, heq✝ : step n = some m✝, h : some (m✝ + 1) = some k ⊢ ∃ m, step n = some m ∧ k = m + 1` |
| R8, arm `none` | `heq✝ : step n = none, h : none = some k ⊢ ∃ m, step n = some m ∧ k = m + 1` |

**W3: a Σ-equation inside `some`** (the end of `check_ite_inv`, and the base cases of `check_sound`):
R14 → R15 → R16, then `rfl`.

| Step | State |
|---|---|
| start | `h : some ⟨K.a, Tm.atom n⟩ = some ⟨k, e⟩` and `⊢ e.leaves = 1` |
| R14 `simp at h` | `h : K.a = k ∧ Tm.atom n ≍ e ⊢ e.leaves = 1` |
| R15 `obtain ⟨rfl, h⟩ := h` | `e : Tm K.a, h : Tm.atom n ≍ e ⊢ e.leaves = 1` |
| R16 `cases h` | `⊢ (Tm.atom n).leaves = 1` |

---

## Part 5 · `check_sound`

Statement: `check u = some ⟨t, e⟩ → e.erase = u`. Anything the checker accepts erases back to its input.
Induction on the *untyped* `u`, generalising `t e` (R17), since the subterms' results have other types and
terms. Base cases: R14 → R15 → R16. `plus` and `ite`: apply the milestones and destructure (R18, R19). `le`
has no milestone: repeat Part 3 inline (R7–R11), then R14–R16.

**R17 · `induction n generalizing m with …`** changes the **goal list** and the IH: `m` (and every hypothesis
mentioning it) is put back into the goal before the induction, so the IH reads
`ih : ∀ (m : Nat), Q n m → R n m`, usable for any `m`, not only the one in the goal. Placeholders:
`(Q R : Nat → Nat → Prop) (n m : Nat)`. Written for `check_sound`, the IHs become
`iha : ∀ (t : Ty) (e : Expr t), check a = some ⟨t, e⟩ → e.erase = a`; use them as `iha _ _ ha`.

| Before | After |
|---|---|
| `n m : Nat, h : Q n m ⊢ R n m` | `h : Q 0 m ⊢ R 0 m`, `h : Q (n + 1) m ⊢ R (n + 1) m` (with `ih` as above) |

**R18 · `obtain ⟨x, hx, hq⟩ := h`, with `h : ∃ x, A x ∧ B x`** changes the **context**: a witness and its
facts. `h` may be a lemma applied to a hypothesis (`check_plus_inv h`), and any component may be the pattern
`rfl` to substitute an equation at once (R15). Placeholders: `{α : Type} (A B : α → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `h : ∃ x, A x ∧ B x` and `⊢ G` | `x : α, hx : A x, hq : B x ⊢ G` |

**R19 · `cases h`, with `h : (⟨i, x⟩ : Σ k, F k) = ⟨j, y⟩` and `i x` local variables** changes the
**context**: both `i := j` and `x := y` at once (R15 and R16 in one step). Use it on the Σ-equation that
`check_plus_inv` returns. Placeholders: `{ι : Type} {F : ι → Type} (i j : ι) (x : F i) (y : F j)`.

| Before | After |
|---|---|
| `h : ⟨i, x⟩ = ⟨j, y⟩` and `⊢ P i x` | `⊢ P j y` |

---

## Traps

- `grind`, `exact?`, `apply?`, `try?` and `import` are banned: the point is the manual Σ/`≍` inversion, which
  `grind` would skip.
- `cases h` on `h : x ≍ y` fails with "Dependent elimination failed" while the types differ (`Expr t1` vs
  `Expr t`). Substitute the type equation first (R15), then `cases h` (R16).
- `obtain ⟨rfl, h⟩` and `subst` need one side of the equation to be a local variable. `Ty.nat = Ty.bool` cannot be
  substituted (it is false: `simp at h` closes that goal).
- Without `generalizing t e` the IH of `check_sound` talks about the fixed `t e` of the goal, which are not the
  results of checking the subterms: it is useless.
- `split` and `split at h` act on the *first* `match`/`if`. In `check`'s `ite` case the outer `match` comes first;
  the inner `if h : t1 = t2` needs a second `split at h`.
- `rename_i` names the *last* inaccessible hypotheses. Count from the end (`x✝¹ x✝` from the generalised
  discriminants come before the pattern variables).
- In `induction e`, a constructor with an implicit index (`ite {t}`) shows the index as `t✝` next to the outer `t`.
- `rfl` after the substitutions works because `erase` and `check` compute on constructors; on a variable they
  are stuck, which is why the recursive cases need the IHs.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| one goal per constructor of `Expr` | `induction e with \| lit n => … \| plus a b iha ihb => …` | R1 |
| unfold a definition (goal / hypothesis) | `simp only [Expr.fold]` / `simp only [check] at h` | R2, R7 |
| one goal per `match` arm (goal / hypothesis) | `split` / `split at h` | R3, R8 |
| finish an arm using its `heq✝` and the IHs | `simp_all [Expr.eval]` | R4 |
| rewrite `check a.erase` to `some …` and pick the arm | `simp [Expr.erase, check, iha, ihb]` | R5, R6 |
| name `a✝ heq✝` | `rename_i a' ha` | R9 |
| `some a = some b → a = b` | `Option.some.inj h`, flipped `(…).symm` | R10 |
| impossible arm `h : none = some _` | `simp at h` | R11 |
| substitute `h : t1 = t2` | `subst h` | R12 |
| drop a cast `⋯ ▸ x` | `simp` (on goal or `at h`) | R13 |
| `some ⟨t1, x⟩ = some ⟨t, e⟩` → `t1 = t ∧ x ≍ e` | `simp at h` | R14 |
| then substitute both | `obtain ⟨rfl, h⟩ := h; cases h` | R15, R16 |
| a Σ-equation `⟨t, e⟩ = ⟨.nat, …⟩` with `t e` variables | `cases h` | R19 |
| IH for every typed result | `induction u generalizing t e with …` | R17 |
| use an inversion lemma | `obtain ⟨a', b', ha, hb, heq⟩ := check_plus_inv h` | R18 |
| apply a generalised IH | `iha _ _ ha` | R17 |
| see the state | infoview | |
