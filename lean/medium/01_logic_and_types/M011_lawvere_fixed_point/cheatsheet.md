# M011 · Lawvere's fixed-point theorem: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `intro`/`apply`/`exact` (E003–E004), the
anonymous constructor `⟨_, _⟩` and `obtain` (E005, E007), `∃` (E007), `¬` as `→ False` (E008), `simp` (E010),
`cases` on `Bool` (E016), `funext` (E022).
**New here:** the diagonal argument as a proof pattern, and the core facts about equality of functions and
of propositions: `congrFun`, `funext`, `propext`, `cast`. Core Lean only: no Mathlib, no extra imports.

## How to read an entry

Each entry is one tactic or one lemma used with `exact`, `have`, `apply` or `obtain`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `G` is an arbitrary goal and `k` a hypothesis that finishes the example; they only show what changed.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `f a0 = fun a => t (f a a)` | an equation between two *functions* `α → β` |
| `f a0 a0` | `f` applied to `a0`, and the resulting function applied to `a0` again: `(f a0) a0` |
| `!b` | `not b`, Bool negation: `!true = false`, `!false = true` |
| `!f n n` | `!(f n n)`: application binds tighter than `!` |
| `a ≠ b` | `Ne a b`, which unfolds to `a = b → False` |
| `¬A` | `Not A`, which unfolds to `A → False`; `Not : Prop → Prop` is an ordinary function |
| `(¬q) = q` | an equation in `Prop`: the proposition `¬q` *is* the proposition `q` |
| `(fun y => mem y x)` | the predicate "`y` is a member of `x`" as a function `V → Prop` (the "set" `x`) |
| `mem x_1 x = P x_1` | after `apply funext` in Part 3: an equation of Props; `x_1` is a fresh name Lean picks because `x` is taken |
| `∀ (d : δ), ∃ c, F c = d` | how Lean prints `∀ d : δ, ∃ c, F c = d` (`F` is surjective) |
| `case false`, `case true` | the two goals made by `cases` on a Bool |

## The diagonal argument in one paragraph

Let `f : α → α → β`, read as a table: row `a` is the function `f a : α → β`. "`f` reaches every function"
(`∀ g, ∃ a, f a = g`) means every `g : α → β` is some row. Given `t : β → β`, build the **diagonal**
`d := fun a => t (f a a)`, which applies `t` to the table's diagonal. `d` is some row `a0` (`f a0 = d`);
evaluate that equation of functions at the point `a0` itself: `f a0 a0 = d a0 = t (f a0 a0)`. So
`b := f a0 a0` is a fixed point of `t` (`t b = b`). Read contrapositively: if some `t` has **no** fixed point,
no `f` reaches every function. `Bool` with `t := not` (`!`) gives "no list of Bool sequences is complete";
`Prop` with `t := Not` (`¬`) gives Russell's paradox, because `(¬b) = b` is absurd.

---

## Part 1 · `lawvere`

Statement: if `f : α → α → β` satisfies `hf : ∀ g : α → β, ∃ a, f a = g`, then every `t : β → β` has a
fixed point, `∃ b, t b = b`. Ask `hf` for the diagonal (R1), evaluate the resulting function equation at
its own witness (R2), and give the witness with the flipped equation (R3, R4).

**R1 · `obtain ⟨c, h⟩ := hF d0`** changes the **context**: `hF d0 : ∃ c, F c = d0` is opened into a witness
`c` and its property `h`. You choose `d0`; in the exercise it is the diagonal `fun a => t (f a a)`, so
`F := f` and `δ := α → β`. Placeholders: `{γ δ : Type} (F : γ → δ) (hF : ∀ d : δ, ∃ c, F c = d) (d0 : δ)`.

| Before | After |
|---|---|
| `⊢ G` | `c : γ, h : F c = d0 ⊢ G` |

**R2 · `have h' := congrFun h x`** changes the **context**. The lemma is
`congrFun {f g : (x : α) → β x} (h : f = g) (a : α) : f a = g a`: equal functions take equal values. If `g`
is a `fun`, Lean shows the β-reduced value: `(fun y => s (u y)) x` appears as `s (u x)`. Placeholders:
`{α β : Type} (v u : α → β) (s : β → β) (h : v = fun y => s (u y)) (x : α)`.

| Before | After |
|---|---|
| `h : v = fun y => s (u y) ⊢ G` | `h' : v x = s (u x) ⊢ G` |

**R3 · `exact h.symm`** **closes** the goal. `Eq.symm (h : a = b) : b = a`; `h.symm` is the same with dot
notation. Use it when the equation you have points the wrong way. Placeholders: `{β : Type} (a b : β)`.

| Before | After |
|---|---|
| `h : a = b ⊢ b = a` | no goals |

**R4 · `exact ⟨w, hw⟩`** **closes** an `∃`. The witness `w` may be any term (`f a0 a0`), and `hw` proves the
property for it. Placeholders: `{β : Type} (Q : β → Prop) (w : β) (hw : Q w)`.

| Before | After |
|---|---|
| `hw : Q w ⊢ ∃ b, Q b` | no goals |

---

## Part 2 · `bool_sequences`

Statement: for every `f : Nat → Nat → Bool` (a list of Bool sequences, row `n` is `f n : Nat → Bool`),
some sequence `g` differs from every row: `∃ g, ∀ n, f n ≠ g`. Take the flipped diagonal
`fun n => !f n n` (R5); an equation `f n = g` evaluated at `n` (R2) says `f n n = !f n n`; split on the Bool
value of `f n n` (R6) and let `simp` see the contradiction (R7). This is Part 1's idea with `t := not`, which has no
fixed point; proving it directly as above is shortest.

**R5 · `refine ⟨w, fun n h => ?_⟩`** changes the **goal and the context**. The witness is `w`; the rest is a
function, because `F n ≠ w` unfolds to `F n = w → False`. Placeholders: `{γ : Type} (F : Nat → γ) (w : γ)`.

| Before | After |
|---|---|
| `⊢ ∃ g, ∀ (n : Nat), F n ≠ g` | `n : Nat, h : F n = w ⊢ False` |

**R6 · `cases hb : e`** changes the **goal list and the context**: one goal for `e = false`, one for
`e = true`, each with `hb` in the context. `e` can be a compound Bool term such as `f n n`. Hypotheses that
mention `e` are **not** rewritten; `simp [hb] at …` (R7) does that. Placeholders: `(e : Bool) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hb : e = false ⊢ G`, `hb : e = true ⊢ G` |

**R7 · `simp [hb] at h`** changes the **context**: `h` is rewritten with `hb : e = true` and simplified.
`simp` evaluates `!true` to `false` and `true = false` to `False`; a hypothesis `False` closes the goal.
Placeholders: `(e : Bool) (hb : e = true) (h : e = !e)`.

| Before | After |
|---|---|
| `hb : e = true, h : e = !e ⊢ False` | no goals |

**W1: the same diagonal on `Nat → Nat → Nat`.** R5 with `w := fun n => f n n + 1`, then R2, then `omega`
(linear arithmetic over `Nat`; it refutes `x = x + 1`):

```lean-goal
⊢ ∃ g, ∀ (n : Nat), f n ≠ g
⊢ False
```

| After R5 | After R2 |
|---|---|
| `h : f n = fun n => f n n + 1 ⊢ False` | `h' : f n n = f n n + 1 ⊢ False` |

---

## Part 3 · `russell`

Statement: for any type `V` with a membership relation `mem : V → V → Prop` (`mem y x` reads "`y ∈ x`"),
naive comprehension fails: it is not true that every predicate `P : V → Prop` is a set, i.e.
`¬ ∀ P, ∃ x, ∀ y, mem y x ↔ P y`.

Plan: assume comprehension (R8). Rewrite it into the shape `lawvere` wants, with
`f := fun x y => mem y x` (row `x` is the predicate "member of `x`"):
`∀ P, ∃ x, (fun y => mem y x) = P`. Each `↔` becomes an `=` of Props (R10), the pointwise `=` becomes an
`=` of predicates (R9). `(fun x y => mem y x) x` and `fun y => mem y x` are the same term up to
β-reduction, so this fact fits `lawvere`'s `hf` as it stands. Apply `lawvere` with `t := Not` (R11) to get
`hb : (¬b) = b`, and refute it: from `b`, transport along `hb` to get `¬b` (R12) and apply it (R13); that
proves `¬b`; transport once more to get `b`, and apply again.

**R8 · `intro hc`** on a negation changes the **goal and the context**: `¬A` is `A → False`. Term form:
`fun hc => …`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬A` | `hc : A ⊢ False` |

**R9 · `funext`** changes the **goal**: equal functions from equal values. The lemma is
`funext {f g : (x : α) → β x} (h : ∀ x, f x = g x) : f = g`. With `apply funext` the goal becomes the
pointwise statement; as a term, `funext fun x => (proof of u x = v x)`. Placeholders:
`{α β : Type} (u v : α → β)`.

| Before | After |
|---|---|
| `⊢ u = v` | `⊢ ∀ (x : α), u x = v x` |

**R10 · `propext`** changes the **goal**. It is one of the three axioms the checker allows (with `Classical.choice`,
`Quot.sound`): `propext {a b : Prop} : (a ↔ b) → a = b`, equivalent propositions are equal. Placeholders:
`(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A = B` | `⊢ A ↔ B` |

**R11 · `obtain ⟨q, hq⟩ := L Not`** changes the **context**: a lemma about every `F : Prop → Prop` is used at
`F := Not`, and its `∃` is opened. In the exercise `L` is `lawvere (fun x y => mem y x) hf`, whose implicit
`α β` Lean infers as `V` and `Prop` from the function you pass. Placeholders:
`(L : ∀ F : Prop → Prop, ∃ q : Prop, F q = q)`.

| Before | After |
|---|---|
| `⊢ G` | `q : Prop, hq : (¬q) = q ⊢ G` |

**R12 · `cast`** **closes** `B` from `h : A = B` and `ha : A`. The definition is
`cast {α β : Sort u} (h : α = β) (a : α) : β`; for Props it turns a proof of one statement into a proof of an
equal statement. `cast h.symm` goes the other way, `B → A`. Placeholders: `(A B : Prop) (h : A = B) (ha : A)`.

| Before | After |
|---|---|
| `h : A = B, ha : A ⊢ B` | no goals |

**R13 · `exact hn ha`** **closes** `False`: `hn : ¬A` is a function `A → False`, so applying it to `ha : A`
gives `False`. Placeholders: `(A : Prop) (hn : ¬A) (ha : A)`.

| Before | After |
|---|---|
| `hn : ¬A, ha : A ⊢ False` | no goals |

**W2: two predicates with the same truth values are equal** (R9, `intro`, R10):

```lean-goal
⊢ (fun n => n + 0 = n) = fun x => True
⊢ ∀ (x : Nat), (x + 0 = x) = True
⊢ (n + 0 = n) = True
⊢ n + 0 = n ↔ True
```

**W3: transport backwards.** From `h : p = True`, `cast h.symm trivial : p` (R12 with R3), since `trivial : True`.

---

## Traps

- **Core only.** The file has no `import` and may not get one (`import` is on the `BANNED:` line), and the
  search tactics `exact?`, `apply?`, `try?` must not stay in the file. Mathlib's
  `Function.exists_fixed_point_of_surjective` (which is this theorem) is banned too.
- Evaluate the equation of functions at the **witness itself** (`congrFun h a0`, not at some other point):
  that self-application is the diagonal argument.
- `cases f n n` without a name loses the link to `f n n`: hypotheses such as `h' : f n n = !f n n` are not
  rewritten. Write `cases hfn : f n n` and then `simp [hfn] at h'` (R6, R7).
- `a ≠ b` and `¬A` are functions to `False`: introduce them with `fun n h => …` / `intro`, and use them by
  applying them (R5, R8, R13).
- `hb : (¬b) = b` is an equation, not an `↔`: use it with `cast` (R12), in both directions (`hb`, `hb.symm`).
- `lawvere` is a theorem of this file: Part 3 may call it (`lawvere f hf Not`) once Part 1 is proved.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use `∀ g, ∃ a, f a = g` at a chosen `g` | `obtain ⟨a, h⟩ := hf g` | R1 |
| equation of functions → equation of values | `congrFun h x` | R2 |
| flip an equation | `h.symm` | R3 |
| prove `∃ b, Q b` | `exact ⟨w, hw⟩` | R4 |
| prove `∃ g, ∀ n, F n ≠ g` | `refine ⟨w, fun n h => ?_⟩` | R5 |
| split on a Bool term `e` | `cases hb : e` | R6 |
| use `hb` inside a hypothesis | `simp [hb] at h` | R7 |
| prove `¬A` | `intro hc` / `fun hc => …` | R8 |
| prove `u = v` for functions | `funext fun x => …` | R9 |
| prove `A = B` for Props | `propext (h : A ↔ B)` | R10 |
| a `Prop → Prop` argument for `¬` | `Not` | R11 |
| `A` and `A = B` → `B` | `cast h ha` (and `cast h.symm`) | R12 |
| `¬A` and `A` → `False` | `hn ha` | R13 |
| see the state | infoview | |
