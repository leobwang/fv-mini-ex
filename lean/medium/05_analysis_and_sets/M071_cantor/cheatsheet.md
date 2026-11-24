# M071 · Cantor's theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `intro`/`exact` (E003), `↔` with
`constructor`, `h.mp`, `h.mpr` and `obtain` (E005), `∃` and the anonymous constructor `⟨_, _⟩` (E007),
`¬A` as `A → False` (E008), `by_cases` (E013), `cases` on `Bool` and `simp_all` (E016), `have` (E021).
**New here:** Mathlib's `Set α`, set-builder notation `{x | p x}`, `Function.Surjective` and the
notation `ℕ`; the diagonal argument as a proof pattern; `congrFun`; `cases hb : e` on a compound
Bool term.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`, `exact` or `have`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Prop → Prop`); the step changes only the part inside `P (…)`.
  `G` is an arbitrary goal, and `k` a hypothesis that finishes the example.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The diagonal argument in one paragraph

Read `f : α → Set α` as a table: row `a` is the set `f a`, and the entry at column `x` is the
proposition `x ∈ f a`. The **diagonal** set `D := {x | x ∉ f x}` flips the diagonal entries: `x ∈ D`
holds exactly when `x ∉ f x`. If `f` hit every set, then `D = f a` for some row `a`; evaluating
membership at that row's own index gives `a ∈ f a ↔ a ∉ f a`, and no proposition is equivalent to its
own negation (W1). `diagonal` is the same idea for Boolean sequences: row `n` of `f : ℕ → ℕ → Bool` is the
sequence `f n : ℕ → Bool`, and `g := fun n => !f n n` differs from row `n` at position `n`.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | Mathlib's notation for `Nat` |
| `Set α` | Mathlib's type of sets of elements of `α`; by definition `α → Prop` (a predicate) |
| `{x \| p x}` | the set of all `x` with `p x` (`setOf p`); `a ∈ {x \| p x}` is by definition `p a` |
| `a ∈ s`, `a ∉ s` | membership; `a ∉ s` is notation for `¬(a ∈ s)` |
| `Function.Surjective f` | `∀ b, ∃ a, f a = b`: every `b` is `f` of something |
| `¬A` | `A → False` |
| `A ↔ B` | `A` iff `B`; a pair of `A → B` (`.mp`) and `B → A` (`.mpr`) |
| `a ≠ b` | `a = b → False` |
| `!b` | Bool negation `not b`: `!true = false`, `!false = true` |
| `f n n` | `(f n) n`: entry `n` of row `n` |
| `fun n => !f n n` | the flipped diagonal sequence. In `h : f n = fun n => !f n n` the `n` inside the `fun` is its own bound variable, not the `n : ℕ` of the context |
| `this` | the name `have :=` gives a fact when you do not name it |
| `case mp`, `case mpr` | the two directions made by `constructor` on `↔` |
| `case pos`, `case neg` | the two goals made by `by_cases` |
| `case false`, `case true` | the two goals made by `cases` on a Bool |

---

## Part 1 · `cantor`

Statement: for every type `α` and every `f : α → Set α`, `f` is not surjective: some set of elements of
`α` is no `f a`. Assume surjectivity (R1), ask it for the diagonal set (R2), prove
`a ∈ f a ↔ a ∉ f a` by rewriting with the equation you got (R6, R5, R4), and refute that `↔` (R7–R9, W1).

### Using a surjectivity hypothesis

**R1 · `intro hg`** on `¬ Function.Surjective g` changes the **goal and the context**: `¬A` is
`A → False`, so `hg` is assumed and the goal becomes `False`. Placeholders:
`{α β : Type} (g : α → β)`.

| Before | After |
|---|---|
| `⊢ ¬Function.Surjective g` | `hg : Function.Surjective g ⊢ False` |

**R2 · `obtain ⟨a, ha⟩ := hg b`** changes the **context**. `hg : Function.Surjective g` unfolds to
`∀ b, ∃ a, g a = b`, so `hg b : ∃ a, g a = b` for a `b` you choose, and `obtain` opens it. In the
exercise `g := f`, `β := Set α` and `b` is the diagonal set. Placeholders: `{α β : Type} (g : α → β)
(hg : Function.Surjective g) (b : β)`.

| Before | After |
|---|---|
| `⊢ G` | `a : α, ha : g a = b ⊢ G` |

### Sets and set-builder notation

**R3 · `rw [Set.mem_setOf_eq]`** changes the **goal**. The lemma is
`Set.mem_setOf_eq : (a ∈ {x | p x}) = p a`. Placeholders: `{α : Type} (p : α → Prop) (a : α)`. In the
exercise `p x` is `x ∉ f x`, so `a ∈ {x | x ∉ f x}` becomes `a ∉ f a`.

| Before | After |
|---|---|
| ⊢ P (a ∈ {x \| p x}) | `⊢ P (p a)` |

The same two goals, unescaped:

```lean-goal
⊢ P (a ∈ {x | p x})
⊢ P (p a)
```

**R4 · `exact h`** **closes** `a ∈ {x | p x}` from `h : p a`. R3 holds by definition (`rfl`), so `exact`
accepts either form without rewriting first; the same works the other way (`h : a ∈ {x | p x}` closes
`p a`). Placeholders: `{α : Type} (p : α → Prop) (a : α)`.

| Before | After |
|---|---|
| h : p a ⊢ a ∈ {x \| p x} | no goals |

The goal before, unescaped:

```lean-goal
⊢ a ∈ {x | p x}
```

**R5 · `rw [hs] at h2`** changes the **context**: the hypothesis `h2` is rewritten with `hs : s = t`; the goal
is unchanged. In the exercise `hs` is `ha : f a = {x | x ∉ f x}`. `rw` replaces `f a` only: the `f x`
inside `{x | x ∉ f x}` has the bound variable `x`, so it stays. `have h2 := h1` first keeps an
unrewritten copy. Placeholders: `{α : Type} (s t : Set α) (a : α)`.

| Before | After |
|---|---|
| `h2 : a ∈ s ⊢ a ∈ t` | `h2 : a ∈ t ⊢ a ∈ t` |

For the other direction, rewrite the **goal** instead (`rw [ha]`, TACTIC_STATES "Rewriting"), which turns
`a ∈ f a` into `a ∈ {x | x ∉ f x}`, and finish with R4.

### Working with `↔` and `¬`

**R6 · `constructor`** on `A ↔ B` changes the **goal list**: one goal per direction. Placeholders:
`(A B : Prop)`. Each goal is an implication; start it with `intro`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R7 · `by_cases hp : A`** changes the **goal list and the context**: two goals, one with `hp : A`, one
with `hp : ¬A` (excluded middle, available because Mathlib is imported). Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hp : A ⊢ G`, `hp : ¬A ⊢ G` |

**R8 · `Iff.mp`, `Iff.mpr`** **close** a goal by using an `↔` in one direction: for `h : A ↔ B`,
`h.mp : A → B` and `h.mpr : B → A`. With `B := ¬A`, `h.mp ha : ¬A` is itself a function, so
`h.mp ha ha : False`. Placeholders: `(A B : Prop) (h : A ↔ B)`.

| Before | After |
|---|---|
| `h : A ↔ B, ha : A, hb : B ⊢ B ∧ A` | no goals (`exact ⟨h.mp ha, h.mpr hb⟩`) |

**R9 · `exact hn ha`** **closes** `False`: `hn : a ∉ s` is `¬(a ∈ s)`, a function `a ∈ s → False`, applied to
`ha : a ∈ s`. Placeholders: `{α : Type} (s : Set α) (a : α)`.

| Before | After |
|---|---|
| `hn : a ∉ s, ha : a ∈ s ⊢ False` | no goals |

**W1: the liar.** No `Q : Prop` satisfies `h : Q ↔ ¬Q`. `by_cases hq : Q` (R7) leaves

```lean-goal
⊢ False
```

twice: with `hq : Q`, close it by `h.mp hq hq` (R8, R9); with `hq : ¬Q`, by `hq (h.mpr hq)` (R8, R9).

**W2: rewrite a hypothesis, then read off the predicate** (R5, R4). With `hs : s = {n | n < 3}` and
`h1 : 1 ∈ s`:

| Before `rw [hs] at h1` | After |
|---|---|
| `h1 : 1 ∈ s ⊢ 1 < 3` | h1 : 1 ∈ {n \| n < 3} ⊢ 1 < 3 |

then `exact h1` (R4).

---

## Part 2 · `diagonal`

Statement: for every `f : ℕ → ℕ → Bool` (a list of Bool sequences; row `n` is `f n : ℕ → Bool`) some
sequence `g` differs from every row: `∃ g, ∀ n, f n ≠ g`. Take the flipped diagonal (R10), evaluate the
assumed equation `f n = g` at `n` (R11), split on the Bool value of `f n n` (R12) and let `simp_all` see the
contradiction (R13).

**R10 · `refine ⟨w, fun n h => ?_⟩`** changes the **goal and the context**. The witness is `w`; the
`∀ n, F n ≠ w` part is a function, because `F n ≠ w` unfolds to `F n = w → False`. Placeholders:
`{γ : Type} (F : ℕ → γ) (w : γ)`; in the exercise `γ := ℕ → Bool` and `w := fun n => !f n n`.

| Before | After |
|---|---|
| `⊢ ∃ g, ∀ (n : ℕ), F n ≠ g` | `n : ℕ, h : F n = w ⊢ False` |

**R11 · `have := congrFun h x`** changes the **context**. The lemma is
`congrFun {f g : (x : α) → β x} (h : f = g) (a : α) : f a = g a`: equal functions take equal values. If
the right side is a `fun`, Lean shows the value β-reduced: `(fun y => s (u y)) x` appears as `s (u x)`.
Placeholders: `{α β : Type} (v u : α → β) (s : β → β) (x : α)`.

| Before | After |
|---|---|
| `h : v = fun y => s (u y) ⊢ G` | `this : v x = s (u x) ⊢ G` |

**R12 · `cases hb : e`** changes the **goal list and the context**: one goal for `e = false`, one for
`e = true`, each with `hb` recording which. `e` may be a compound Bool term such as `f n n`. Hypotheses
that mention `e` are **not** rewritten; R13 does that. Placeholders: `(e : Bool) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hb : e = false ⊢ G`, `hb : e = true ⊢ G` |

**R13 · `simp_all`** **closes** the goal here. It simplifies every hypothesis using the others (and the
goal using all of them); `hb : F n = false` turns `h : F n = !F n` into `false = !false`, i.e.
`false = true`, i.e. `False`. Placeholders: `(F : ℕ → Bool) (n : ℕ)`.

| Before | After |
|---|---|
| `h : F n = !F n, hb : F n = false ⊢ False` | no goals |

**W3: the same diagonal on `ℕ → ℕ → ℕ`.** R10 with `w := fun n => F n n + 1`, then R11, then `omega`
(linear arithmetic over `ℕ`; it refutes `x = x + 1`):

```lean-goal
⊢ ∃ g, ∀ (n : ℕ), F n ≠ g
⊢ False
```

| After R10 | After R11 |
|---|---|
| `h : F n = fun n => F n n + 1 ⊢ False` | `this : F n n = F n n + 1 ⊢ False` |

**W4.** `cases hb : F 0 <;> simp_all` refutes `h : F 0 = !F 0` (R12 then R13 in both goals; `<;>` runs
the second tactic on every goal the first one makes).

---

## Traps

- `Function.cantor_surjective` and `Function.cantor_injective` (Mathlib's versions of this theorem) are on
  the `BANNED:` line.
- Choose the diagonal **before** `obtain`: `hf {x | x ∉ f x}`. Lean infers that the argument is a
  `Set α` from `hf`.
- `rw [ha] at h1` changes `h1` itself; keep a copy (`have h2 := h1`) if you still need the original.
- In direction `a ∈ f a → a ∉ f a`, rewrite the **hypothesis**, not the goal: `rw [ha]` on the goal
  `a ∉ f a` gives `a ∉ {x | x ∉ f x}`, a double negation that no longer matches what you hold.
- After `rw [ha]` the result still mentions `f` (inside `{x | x ∉ f x}`): that is the bound `f x`, not
  `f a`, and it is expected.
- `cases f n n` without a name loses the link to `f n n`; write `cases hfn : f n n` (R12).
- `simp_all` can loop when a hypothesis such as `e = !e` has a plain variable on the left and is used as a
  rewrite rule before the fact that fixes `e`. If it reports "maximum recursion depth", use
  `simp [hfn] at this` instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `¬ Function.Surjective g` | `intro hg` | R1 |
| use surjectivity at a chosen `b` | `obtain ⟨a, ha⟩ := hg b` | R2 |
| `a ∈ {x \| p x}` → `p a` | `rw [Set.mem_setOf_eq]`, or just `exact` | R3, R4 |
| rewrite a hypothesis | `rw [hs] at h2` | R5 |
| prove `A ↔ B` | `constructor`, then `intro` in each goal | R6 |
| case on a proposition | `by_cases hp : A` | R7 |
| use `h : A ↔ B` | `h.mp`, `h.mpr` | R8 |
| `¬A` and `A` → `False` | `hn ha` | R9 |
| prove `∃ g, ∀ n, F n ≠ g` | `refine ⟨w, fun n h => ?_⟩` | R10 |
| equation of functions → values | `have := congrFun h x` | R11 |
| split on a Bool term | `cases hb : e` | R12 |
| finish from contradictory hypotheses | `simp_all` | R13 |
| `Q ↔ ¬Q` → `False` | `by_cases`, `h.mp hq hq`, `hq (h.mpr hq)` | W1 |
| see the state | infoview | |
