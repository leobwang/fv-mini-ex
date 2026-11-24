# M050 · A fuel-based interpreter is complete: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, functions by pattern matching,
`Option`, `∃`, `induction`/`cases` on `Nat` and lists, `simp`, `rw`, `exact`. M044 (soundness of the
same interpreter) helps but is not needed: its theorem `run_mono` is given here.
**New here:** induction on a *derivation* (a proof of an inductive predicate such as `BigStep c s s'`),
running a fuel interpreter one step with `simp only [run]`, lifting fuel with `max`, and `omega`.
Core Lean only, no Mathlib.

The objects. `State := Nat → Int` maps variable numbers to values. `Com` is IMP's command syntax
(`skip`, `assign`, `seq`, `ite`, `while`). `BigStep c s s'` ("`c` run from `s` ends in `s'`") is an
inductive predicate with one constructor per rule of big-step semantics. `run n c s : Option State` is an
interpreter: fuel `n` bounds the recursion depth; `none` means fuel ran out, `some s'` means it finished
in `s'`. *Completeness*: every terminating big-step run is found by `run` with some fuel.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P`, `Q` are "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type.
- `go`, `Task`, `Gen` are toy objects defined at the top of `guide.lean`: `go k p x` runs a toy task `p`
  on a counter `x` with fuel `k`, built like the exercise's `run`; `Gen n` is a toy derivation predicate.
- Every `⊢` cell and every line of a `lean-goal` block is a state Lean reaches in the companion file;
  `tools/guide_sync.py` checks that. Goals that contain a `match` are in `lean-goal` blocks (a `|` cannot
  sit inside a table cell); Lean prints them over several lines, written here on one.

## Reading the goals

| You see | It means |
|---|---|
| `.skip`, `.seq c1 c2`, `.num n` (in the spec) | a constructor with its type left out: `Com.skip`, `Com.seq c1 c2`, `AExp.num n`; Lean reads the type off what is expected there |
| `aeval s a`, `beval s b` | the value of an arithmetic (`Int`) / Boolean (`Bool`) expression in state `s` |
| `decide p`, `!b`, `b1 && b2` | the `Bool` that is `true` iff the proposition `p` holds; Boolean not; Boolean and |
| `update s x v` | the state `s` with variable `x` set to `v`: `fun y => if y = x then v else s y` |
| `‹_›` (in the given proof of `run_mono`) | "the hypothesis of the expected type", found in the context |
| `run n c s = some s'` | with fuel `n`, `c` from `s` finishes in state `s'` |
| `∃ n, run n c s = some s'` | some amount of fuel suffices |
| `s✝`, `c1✝`, `b✝` | *inaccessible* names: variables Lean introduced (here, a constructor's implicit arguments `{s s' : State}`). You cannot type them; name them with `@` patterns (Trap 5) or leave them alone |
| `a✝`, `a✝¹` | unnamed hypotheses; `¹` tells apart two with the same base name |
| `a_ih✝`, `a_ih✝¹` | unnamed induction hypotheses from `induction h` (R6) |
| `c : Com`, `s s' : State` next to `s✝ s'✝` in an induction case | the theorem's own variables; `induction h` leaves them in the context, unused. The case's states are the `✝` ones |
| `c1✝.seq c2✝` | `Com.seq c1✝ c2✝` in *dot notation*: a function `Com.f` applied to a first argument of type `Com` |
| `Com.while b✝ c✝`, `Com.ite b✝ c1✝ c2✝`, `Com.assign x✝ a✝` | no dot notation here, since the first argument is not a `Com` (`BExp`, `Nat`) |
| `if beval s b = true then x else y` | an `if` on a `Bool`: Lean turns the `Bool` into the proposition `beval s b = true` |
| `match run k c s with \| some s' => A \| none => none` | the `seq`/`while` step of `run`: inspect the first sub-run's result; continue with `A` on `some s'`, give up on `none` |
| `max n1 n2` | the larger of `n1`, `n2` (core `Nat.max`); `omega` understands it |
| `n ≥ m` | notation for `m ≤ n` |
| `case succ.inl` | goal tag: `succ` case of an induction, then the left alternative of an `∨` |

---

## Part 1 · `run_mono_le` (MILESTONE)

Statement: `n ≤ m → run n c s = some s' → run m c s = some s'`. More fuel never hurts, for any amount
more. The given `run_mono` does `n` to `n + 1`; iterate it by induction on `m`.

**R1 · `induction m`** changes the **goal list**: one goal for `m = 0`, one for `m = k + 1`. A hypothesis
that mentions `m` (here `hnm : n ≤ m`) is reverted and reintroduced in each case, so the IH gets it as a
premise: `ih : n ≤ k → Q k`, with the case's `hnm : n ≤ k + 1`. Hypotheses that do not mention `m` (the
exercise's `h : run n c s = some s'`) stay as they are. Placeholders: `(n m : Nat) (Q : Nat → Prop)`.
`induction m with | zero => tac₀ | succ k ih => tac₁` gives the same goals with `n✝ a✝` named `k ih`
(or write `case succ k ih => …` afterwards, as `guide.lean` does).

| Before | After |
|---|---|
| `hnm : n ≤ m ⊢ Q m` | `hnm : n ≤ 0 ⊢ Q 0`, `n✝ : Nat, a✝ : n ≤ n✝ → Q n✝, hnm : n ≤ n✝ + 1 ⊢ Q (n✝ + 1)` |

**R2 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int`: `+`, `-` (truncated on
`Nat`), multiplication by numerals, `≤ < = ≠`, `max`, `min`, using the hypotheses of that kind in the
context. Use it in `have : n = 0 := by omega` (from `hnm : n ≤ 0`), `have : n = m + 1 := by omega`, and
for an IH premise `n ≤ m` from `hlt : n < m + 1`. Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `hle : a ≤ b + 1, hge : a ≥ b + 1 ⊢ a = b + 1` | closed |

**R3 · `subst e`** changes the **context and the goal**: for `e : a = t` with `a` a local variable not
occurring in `t`, it deletes `a` and `e` and writes `t` for `a` everywhere. After `subst` on `n = m + 1`,
the hypothesis `h : run n c s = some s'` reads `run (m + 1) c s = some s'`, which is the goal.
Placeholders: `(a b : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `e : a = b + 1, h : P (b + 1) ⊢ P a` | `h : P (b + 1) ⊢ P (b + 1)` |

**R4 · `rcases Nat.lt_or_ge a b with hlt | hge`** changes the **goal list**: the lemma
`Nat.lt_or_ge : ∀ (n m : Nat), n < m ∨ n ≥ m` is split into two goals, each with its side as a new
hypothesis. Placeholders: `(a b : Nat) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hlt : a < b ⊢ G`, `hge : a ≥ b ⊢ G` |

**R5 · `exact thm _ _ (ih (by omega))`** **closes** the goal by applying a theorem. Each `_` is an explicit
argument Lean infers by matching the theorem's conclusion with the goal; `(by omega)` proves the IH's
premise right there. For the exercise: `run_mono _ _ _ _ (…)` has four explicit arguments `n c s s'`
before its hypothesis. Placeholders: `{α : Type} (Q : Nat → α → Prop)`,
`mono : ∀ (k : Nat) (x : α), Q k x → Q (k + 1) x`.

| Before | After |
|---|---|
| `ih : 1 ≤ k → Q k x, hk : 2 ≤ k ⊢ Q (k + 1) x` | closed |

---

## Part 2 · `run_complete`

Statement: `BigStep c s s' → ∃ n, run n c s = some s'`. Induct on the derivation; in each case give a
fuel and run `run` one step.

### Induction on a derivation

**R6 · `induction h`** with `h : Gen n` (an inductive predicate) changes the **goal list**: one goal per
constructor, with the constructor's arguments in the context and one IH per premise of the predicate's
own type. Implicit arguments (`{n : Nat}`) arrive as `n✝`, premises as `a✝`, IHs as `a_ih✝`. With
`induction h with | add2 hk ih => …` you name the explicit premises, then the IHs, in that order; `_`
skips one. For `BigStep`, the `whileT` case has the IH for the *same* loop `while b c` run from the
intermediate state, which induction on `c` could never give. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `h : Gen n ⊢ P n` | `⊢ P 0`, `a✝ : Gen n✝, a_ih✝ : P n✝ ⊢ P (n✝ + 2)`, `a✝¹ : Gen m✝, a✝ : Gen n✝, a_ih✝¹ : P m✝, a_ih✝ : P n✝ ⊢ P (m✝ + n✝)` |

For `BigStep` the cases are `skip assign seq iteT iteF whileF whileT`; `seq` and `whileT` have two IHs,
`iteT iteF` one, the others none. Each IH has the form `∃ n, run n c₁ s₁ = some s₂`.

### Existentials

**R7 · `exact ⟨1, rfl⟩`** **closes** `∃ k, go k p x = v` when `go 1 p x` *computes* to `v`: `rfl` proves
`a = b` whenever unfolding definitions makes both sides identical. Fuel `1` runs `skip` and `assign`
(no recursive call). Placeholders: `(x : Nat)`.

| Before | After |
|---|---|
| `⊢ ∃ k, go k Task.tick x = some (x + 1)` | closed |

**R8 · `obtain ⟨n, hn⟩ := ih`** changes the **context**: `ih : ∃ n, Q n` is replaced by a witness
`n : Nat` and its property `hn`. Placeholders: `(Q : Nat → Prop) (G : Prop)`.

| Before (context has `ih : ∃ n, Q n`) | After (`ih` is gone) |
|---|---|
| `⊢ G` | `n : Nat, hn : Q n ⊢ G` |

Then choose the fuel with `refine ⟨e, ?_⟩` (TACTIC_STATES, "Structure"): `⊢ ∃ n, R n` becomes `⊢ R e`.

### Running the interpreter one step

**R9 · `simp only [go]`** changes the **goal**: it rewrites with `go`'s defining equations, so
`go (k + 1) (p.pair q) x` becomes the body of the `pair` equation. It fires only when the fuel is
literally `_ + 1` and the task is a constructor; that is why the fuel you give must be `e + 1`.
Placeholders: `(k x : Nat) (p q : Task) (P : Option Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (go (k + 1) (p.pair q) x)` | the `match` below |

```lean-goal
⊢ P (match go k p x with | some y => go k q y | none => none)
```

**R10 · `Nat.le_max_left a b : a ≤ max a b`, `Nat.le_max_right a b : b ≤ max a b`** are the two facts
that let one fuel `max n1 n2` serve both sub-runs. Placeholders: `(a b : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `g : a ≤ max a b → b ≤ max a b → P ⊢ P` | closed by `exact g (Nat.le_max_left a b) (Nat.le_max_right a b)` |

**R11 · `rw [lift (Nat.le_max_left _ _) ha]`** changes the **goal**: rewrite with a lemma whose premises
you supply. `lift : k ≤ m → g k = some v → g m = some v` (the shape of `run_mono_le`) applied to
`Nat.le_max_left _ _ : a ≤ max a ?b` and `ha : g a = some v` is the equation `g (max a ?b) = some v`;
`rw` finds `g (max a b)` in the goal and sets `?b := b`. In the exercise this replaces the `match`'s
scrutinee `run (max n1 n2) c₁ s` by `some s₁`. Placeholders: `{α : Type} (g : Nat → Option α)
(a b : Nat) (v : α)`.

| Before | After |
|---|---|
| `ha : g a = some v ⊢ P (g (max a b))` | `⊢ P (some v)` |

**R12 · `exact e`** **closes** a goal that equals `e`'s type up to computation. A `match` on a
constructor reduces: `match some v with | some y => F y | none => none` *is* `F v`, so no rewrite is
needed after R11. Placeholders: `{α β : Type} (v : α) (F : α → Option β) (w : Option β)`,
`h : F v = w`.

| Before | After |
|---|---|
| the goal below, with `h : F v = w` | closed by `exact h` |

```lean-goal
⊢ (match some v with | some y => F y | none => none) = w
```

**R13 · `simp only [hb, if_true]`** changes the **goal**: with `hb : c = true`, the `Bool` test
`c = true` becomes `true = true`, and the `if` reduces to its `then` branch. The lemma is
`if_true : (if True then t else e) = t`. For a loop, put it in the same call as the unfolding:
`simp only [run, hb, if_true]`. Placeholders: `{α : Type} (c : Bool) (a b : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `hb : c = true ⊢ P (if c = true then a else b)` | `⊢ P a` |

**R14 · `simp [go, hb, h]`** **closes** the goal: it unfolds `go`, rewrites with the hypotheses `hb`,
`h` (each used as an equation left to right), and finishes with the default simp set (`some y = some y`
is `True`). Good for the one-IH cases (`iteT`, `iteF`) and `whileF`; with `hb : … = false` (`iteF`, `whileF`)
the default simp set turns `false = true` into `False` and takes the `else` branch. Placeholders:
`(k x y : Nat) (t : Nat → Bool) (p : Task)`.

| Before | After |
|---|---|
| `hb : t x = true, h : go k p x = some y ⊢ go (k + 1) (Task.guard t p) x = some y` | closed |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: one `pair` step, same fuel in both halves.** R9, then `rw [hp]`, then R12 (`exact hq`):

```lean-goal
⊢ go (k + 1) (p.pair q) x = some z
⊢ (match go k p x with | some y => go k q y | none => none) = some z
⊢ (match some y with | some y => go k q y | none => none) = some z
```

In the exercise the two IHs have *different* fuels `n1`, `n2`, so `rw [h1]` does not match
`run (max n1 n2) c1 s`; R11 lifts `h1` first.

**W2: one `loop` step with a true test.** `simp only [go, ht, if_true]` (R9 + R13), `rw [hp]`,
`exact hl` (R12):

```lean-goal
⊢ go (k + 1) (Task.loop t p) x = some z
⊢ (match go k p x with | some y => go k (Task.loop t p) y | none => none) = some z
⊢ (match some y with | some y => go k (Task.loop t p) y | none => none) = some z
```

**W3: induction on `Gen`, combining witnesses.** `Gen n → ∃ k, n = 2 * k`: in the `sum` case,
`obtain` both IHs (R8), then `exact ⟨k1 + k2, by omega⟩` (R2). Two IHs with separate witnesses, combined
into one, is the shape of the `seq` and `whileT` cases.

```lean-goal
⊢ ∃ k, n = 2 * k
```

---

## Traps

1. **Induct on `h`, not on `c`.** In `whileT` the second premise is a run of the same `while b c`; only
   the derivation gives an IH for it (R6).
2. **`simp only [run]` needs fuel `e + 1`.** Choose the fuel with `refine ⟨max n1 n2 + 1, ?_⟩` *before*
   unfolding; `run (max n1 n2) …` does not unfold (R9).
3. **`rw [h1]` fails after unfolding**: the goal says `run (max n1 n2) c1 s`, `h1` says `run n1 c1 s`.
   Rewrite with the lifted fact `run_mono_le (Nat.le_max_left _ _) h1` (R10, R11).
4. **`run_mono_le` first.** It is the milestone; `run_complete` uses it twice in `seq` and twice in
   `whileT`. In its `induction m`, `hnm` is carried into the IH automatically (R1); do not `revert` it.
5. **Implicit constructor arguments are not named** by `| seq h1 h2 ih1 ih2`: these names bind the two
   premises and the two IHs, and the states stay `s✝ s'✝ s''✝`. To name them too, write
   `| @seq c1 c2 s1 s2 s3 h1 h2 ih1 ih2 => …`.
6. **`run_mono _ _ _ _ h` has four explicit arguments** before `h` (R5); `run_mono_le` has them implicit,
   so it takes only `hnm` and `h`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on `m` keeping `n ≤ m` | `induction m with \| zero => … \| succ m ih => …` | R1 |
| arithmetic on `Nat` (incl. `max`) | `omega`, `have : n = 0 := by omega` | R2 |
| replace a variable by its value | `subst this` | R3 |
| split `n < m + 1` vs. `n ≥ m + 1` | `rcases Nat.lt_or_ge n (m + 1) with hlt \| hge` | R4 |
| apply a theorem, args inferred | `exact run_mono _ _ _ _ (ih (by omega))` | R5 |
| induction on a derivation | `induction h with \| skip => … \| seq _ _ ih1 ih2 => … \| …` | R6 |
| fuel `1` for `skip`, `assign` | `exact ⟨1, rfl⟩` | R7 |
| unpack an IH `∃ n, …` | `obtain ⟨n1, h1⟩ := ih1` | R8 |
| choose the fuel | `refine ⟨max n1 n2 + 1, ?_⟩` | TACTIC_STATES |
| run one step | `simp only [run]` | R9 |
| `n1 ≤ max n1 n2`, `n2 ≤ max n1 n2` | `Nat.le_max_left _ _`, `Nat.le_max_right _ _` | R10 |
| lift a sub-run to the max fuel | `rw [run_mono_le (Nat.le_max_left _ _) h1]` | R11 |
| finish through a reduced `match` | `exact run_mono_le (Nat.le_max_right _ _) h2` | R12 |
| loop step with true test | `simp only [run, hb, if_true]` | R13 |
| one-IH cases, `whileF` | `exact ⟨n + 1, by simp [run, hb, h]⟩` | R14 |
| see the state | infoview | |
