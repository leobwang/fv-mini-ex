# H028 · Church-Rosser for combinatory logic: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`rw [h]`, `exact`, `rfl`, `refine`, `<;>`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types, `theorem`, `exact`, `rw`, `rfl`,
anonymous constructors. **New here:** core Lean only, no Mathlib. Proofs *about derivations* of inductive
relations: building them from their rules, inverting them with `cases`, inducting on them with
`induction … generalizing …`, and the Tait–Martin-Löf method for confluence.

**The proof plan.** Terms `Tm` are built from the constants `S`, `K` by application (`.app t u`, written `t u`, left
associative: `K x y` is `(K x) y`). One step `Step a b` (informally `a ⟶ b`) contracts one redex
anywhere in the term: `K x y ⟶ x` or `S x y z ⟶ x z (y z)`. `Star a b` is zero or more steps
(`⟶*`). **Confluence** (Church-Rosser): `a ⟶* b` and `a ⟶* c` imply `∃ d, b ⟶* d ∧ c ⟶* d`.
`Step` itself has no one-step diamond, since `S x y z ⟶ x z (y z)` copies `z`, and a step inside `z`
then has to be done twice. So define **parallel reduction** `Par` (contract any set of redexes already
present, all at once), and prove:

| Milestone | Statement | Role |
|---|---|---|
| `par_Kx`, `par_Sxy` | what `K x`, `S x y` can `Par`-reduce to | inversion, used in the overlap cases |
| `par_diamond` | `Par a b → Par a c → ∃ d, Par b d ∧ Par c d` | the one-step diamond |
| `par_of_step`, `star_of_par` | `Step ⊆ Par ⊆ Star` | move between the relations |
| `star_trans` | `Star a b → Star b c → Star a c` | glue sequences |
| `strip` | `Par a b → Star a c → ∃ d, Star b d ∧ Par c d` | one diamond column stacked along `Star` |
| `church_rosser` | the spec | strips stacked along the other `Star` |

## How to read an entry

Each entry is one tactic or proof-building move. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P`, `Q`, `G` are "the rest of your goal" (`P : T → Prop`, `Q : α → α → Prop`). The step changes only
  the part shown inside them.
- The entries run on toy objects defined at the top of `guide.lean`, not on the exercise's:
  `T` (constants `a`, `b`, binary `node`), a relation `R : T → T → Prop` with rules `refl`, `node`
  (congruence) and `drop` (`R x x' → R (node a x) x'`), and `RT r`, zero or more `r`-steps for any
  relation `r : α → α → Prop` on any type `α`. `T`/`R` play the role of `Tm`/`Par`; `RT` the role of `Star`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `t.app u` | `Tm.app t u`, the application `t u`. Lean prints `C.f x` for `f C x` ("field notation") |
| `(Tm.K.app x).app y` | `K x y`; in the toy, `l.node r` is `T.node l r` and `T.b.node x` is `node b x` |
| `Tm.K`, `T.a` | the constant constructors, printed with their type's name |
| `.app h1 h2`, `.K hx`, `.refl t` | dot notation: a constructor of the **expected** type (`Par.app`, `Par.K`, …) |
| `x✝`, `t'✝`, `a✝` | inaccessible names Lean made up (you cannot type them); name them with `with` or `rename_i` |
| `a✝¹`, `x'✝¹` | an older inaccessible variable with the same base name: `x'✝¹` and `x'✝` are two different terms |
| `case refl`, `case app.K` | the goal tag: which rule(s) this goal came from (`app.K` = `cases` inside `induction`) |
| `iht : ∀ {c : Tm}, Par t✝ c → ∃ d, …` | an induction hypothesis that holds for every `c`: apply it as `iht hc'` |
| `∃ d, Par b d ∧ Par c d` | build with `⟨d, h1, h2⟩`, take apart with `obtain ⟨d, h1, h2⟩ := e` |

---

## Part 1 · `par_Kx`

Statement: `Par (K x) t → ∃ x', t = K x' ∧ Par x x'`. The only `Par`-rules whose left side can be the
application `K x` are `refl` and `app`; in the `app` case the head `K` itself must reduce, and `K`
reduces only to `K`. Prove that as a helper first: `par_K : Par .K t → t = .K` (R3).

**R1 · `exact .ctor h₁ h₂`** **closes** the goal by one rule of the relation. `.node` means `R.node`:
Lean resolves the leading dot from the expected type. Implicit arguments (`{l l' r r'}`) are found by
unification; explicit ones are the premises' proofs. Placeholders: `(l l' r r' : T) (hl : R l l') (hr : R r r')`.

| Before | After |
|---|---|
| `hl : R l l', hr : R r r' ⊢ R (l.node r) (l'.node r')` | closed |

**R2 · `exact ⟨w, rfl, h⟩`** **closes** a goal `∃ y, t = f y ∧ Q y`. `⟨_, _, _⟩` builds the `∃` and the
`∧` at once (`∧` nests to the right). `rfl` proves the equation once `w` is fixed; write `_` for `w` and
Lean reads it off from `rfl`. Placeholders: `(x x' : T) (hx : R x x')`.

| Before | After |
|---|---|
| `hx : R x x' ⊢ ∃ y, T.b.node x' = T.b.node y ∧ R x y` | closed |

**R3 · `cases h`, index a constant** changes the **context and goal**. On `h : R .a t`, the rules `node`
and `drop` need a `node` on the left, so only `refl` survives, and it forces `t := .a`: `t` and `h`
leave the context, and the goal is rewritten. Placeholders: `(P : T → Prop) (t : T) (h : R .a t)`.

| Before | After |
|---|---|
| `h : R T.a t ⊢ P t` | `⊢ P T.a` |

**R4 · `cases h with | rule names => …`, index with variables** changes the **goal list**: one goal per
rule that can match, with the index unified against that rule's left side. On `h : R (.node l r) t`,
all three rules match; in the `drop` goal Lean learns `l = .a` and substitutes it *everywhere*, other
hypotheses included (`h2` becomes `… R T.a l' …`). The names after a rule go to its explicit premises.
Placeholders: `(P : T → Prop) (l r t : T) (h : R (.node l r) t)`.

| Before | After |
|---|---|
| `h : R (l.node r) t ⊢ P t` | `l r : T ⊢ P (l.node r)` (refl), `hl : R l l'✝, hr : R r r'✝ ⊢ P (l'✝.node r'✝)` (node), `r t : T, hx : R r t ⊢ P t` (drop) |

In `par_Kx`, the `app` goal has `h1 : Par Tm.K t'✝`: invert it with your `par_K` and `rw` the
equation (TACTIC_STATES `rw [h]`), then finish with R2.

## Part 2 · `par_Sxy`

Statement: `Par (S x y) t → ∃ x' y', t = S x' y' ∧ Par x x' ∧ Par y y'`. Same pattern one level deeper:
the `app` case has `h1 : Par (Tm.S.app x) _`, so first prove `par_S` (R3) and
`par_Sx : Par (S x) t → ∃ x', t = S x' ∧ Par x x'` (exactly as `par_Kx`), and destructure its result.

**R5 · `obtain ⟨w, rfl, hw⟩ := e`** changes the **context**: it unpacks `e : ∃ y, t = f y ∧ Q y`.
The pattern `rfl` substitutes the equation away: `t` disappears, and every `t` in the goal and in other
hypotheses becomes `f w`. Placeholders: `(t x : T)` and `e : ∃ y, t = T.b.node y ∧ R x y`.

| Before | After |
|---|---|
| `e : ∃ y, t = T.b.node y ∧ R x y` and `t x : T ⊢ P t` | `w : T, hw : R x w ⊢ P (T.b.node w)` |

## Part 3 · `par_diamond`

Statement: `Par a b → Par a c → ∃ d, Par b d ∧ Par c d`. Induction on `hb`, keeping `c` general, then
`cases hc` inside the `app`, `K`, `S` cases. The `refl` case needs no split: it has `hc : Par t c` and
the goal `∃ d, Par t d ∧ Par c d`, so join at `c`. Most rule pairs close by the IHs and R1. Watch the two same-rule pairs whose
goal is not rebuilt by that rule: in `K` vs `K` the goal is `∃ d, Par x'✝ d ∧ Par c d`, which is exactly
`ihx hx2`; in `S` vs `S` both sides are `x z (y z)` shapes, rebuilt with `.app (.app _ _) (.app _ _)`.

**R8 · `induction h with`, several recursive premises** changes the **goal list**: one goal per rule;
each rule's names are its explicit premises first, then one IH per premise that is itself an `R`
derivation. `R.node` has premises `R l l'`, `R r r'`, so its case reads `| node hl hr ihl ihr`; for `Par.S`
it is `| S hx hy hz ihx ihy ihz`. Placeholders: `(Q : T → T → Prop) (s t : T) (h : R s t)`.

| Before | After |
|---|---|
| `h : R s t ⊢ Q s t` | `t : T ⊢ Q t t`, `hl : R l✝ l'✝, hr : R r✝ r'✝, ihl : Q l✝ l'✝, ihr : Q r✝ r'✝ ⊢ Q (l✝.node r✝) (l'✝.node r'✝)`, `hx : R x✝ x'✝, ihx : Q x✝ x'✝ ⊢ Q (T.a.node x✝) x'✝` |

**R9 · `induction h generalizing c`** changes the **goal list** and makes each IH hold for **every**
`c`. Without it, `c` and `hc` stay fixed and the IH talks about that one `c`, but the IH must be applied
to a *different* `c` (another reduct of the subterm). `generalizing c` also takes along `hc`, which
mentions `c`. The IH's binder copies the statement's: `{c}` gives `∀ {c}, …`, applied as `ih hc'`;
`(c)` gives `∀ (c), …`, applied as `ih _ hc'`. Placeholders:
`{α : Type} (r : α → α → Prop) (Q G : α → α → Prop) {x y c : α} (h : RT r x y) (hc : Q x c)`.

| Before | After |
|---|---|
| `h : RT r x y, hc : Q x c ⊢ G x c` | `hc : Q x c ⊢ G x c` (refl), `s : r x✝ y✝, hc : Q x✝ c ⊢ G x✝ c` with `ih : ∀ {c : α}, Q y✝ c → G y✝ c` (step) |

**R6 · `cases he` on an equation of constructors** changes the **context**: constructors are injective,
so `node l r = node l' r'` makes Lean substitute `l' := l`, `r' := r`. (On `.a = .b` it closes the goal:
different constructors are never equal.) Use it when `obtain ⟨_, rfl, _⟩` cannot work because *both*
sides of the equation are compound terms. Placeholders: `(P : T → T → Prop) (l r l' r' : T)`.

| Before | After |
|---|---|
| `he : l.node r = l'.node r' ⊢ P l' r'` | `l r : T, hP : P l r ⊢ P l r` |

**The overlap cases.** With `hb` on `app` and `hc` on `K`, `cases hc` has already unified the head:
`ht : Par (Tm.K.app x✝) t'✝`, `hx2 : Par x✝ c`, and `iht : ∀ {c : Tm}, Par (Tm.K.app x✝) c → …` is
about the **head** `K x`, not about `x`. So:
1. invert `ht` with `par_Kx` (R5 with `rfl`: `t'✝` becomes `K x1`);
2. feed `iht` a `Par` of the head, built by R1: `.app (.refl .K) hx2 : Par (K x) (K c)`;
3. invert both results with `par_Kx`; the second equation `K e1 = K e2` has two compound sides: R6;
4. the witness is the `K`-argument, closed by R2 with `.K he1`.

The `S` overlap is the same with `par_Sxy`, plus `ihu` for the third argument `z`. The `K`/`S` vs `app`
cases are the mirror image (invert `h1` from `hc`).

## Part 4 · `par_of_step`

Statement: `Step a b → Par a b`. Induction on the step (R8 shape: `| K | S | appL _ ih | appR _ ih`),
each case one rule of `Par` (R1) with `.refl _` for the parts that do not move.

## Part 5 · `star_trans`

Statement: `Star a b → Star b c → Star a c`. Induction on the first sequence.

**R7 · `induction h with | refl x => … | step s _ ih => …`** changes the **goal list**: one goal per rule
of `RT` (`Star` in the exercise). `step` has two premises: `r x y`, not an `RT`, so no IH, and
`RT r y z`, which gets the IH `ih`. Names go to premises first, then IHs; `_` skips one. Placeholders:
`{α : Type} (r Q : α → α → Prop) (x z : α) (h : RT r x z)`.

| Before | After |
|---|---|
| `h : RT r x z ⊢ Q x z` | `x : α ⊢ Q x x` (refl), `s : r x✝ y✝, a✝ : RT r y✝ z✝, ih : Q y✝ z✝ ⊢ Q x✝ z✝` (step) |

In `star_trans`, the second sequence `h2 : Star b c` mentions the index `b`, so `induction` generalizes
it by itself: in the `step` case (`s : Step a✝¹ b✝`) you get `h2 : Star c✝ c` and
`ih : Star c✝ c → Star b✝ c`. Finish each case with R1 (or `exact h2` in `refl`).

## Part 6 · `star_of_par`

Statement: `Par a b → Star a b`. Two helpers first (R7 + R1, guide W2 is the general form):
`star_appL : Star t t' → Star (t u) (t' u)` and `star_appR : Star u u' → Star (t u) (t u')`. Then R8 on
`Par`: `app` is `star_trans (star_appL ih1) (star_appR ih2)`; `K` is one `Step.K` then `ih`; `S` is one
`Step.S`, then rebuild `x z (y z)` → `x' z' (y' z')` with the two helpers and `star_trans`.

## Part 7 · `strip`

Statement: `Par a b → Star a c → ∃ d, Star b d ∧ Par c d`. R9 on `hc` generalizing `b`. Step case, as
Lean prints it: `s : Step a✝¹ b✝`, `hb : Par a✝¹ b`, `ih : ∀ {b : Tm}, Par b✝ b → ∃ d, Star b d ∧ Par c✝ d`,
goal `∃ d, Star b d ∧ Par c✝ d` (`c✝` is the end of the sequence). `par_diamond hb (par_of_step s)` gives
`d` with `Par b d`, `Par b✝ d`; the IH at that second `Par` gives `e`; R5 to unpack both, R2 with
`star_trans (star_of_par _) _`.

## Part 8 · `church_rosser`

Statement (the spec): `Star a b → Star a c → ∃ d, Star b d ∧ Star c d`. The stub is `:= sorry`; write
`by` and the tactics in its place. R9 on `hb` generalizing `c`. Step case: `s : Step a✝¹ b✝`,
`hc : Star a✝¹ c`, `ih : ∀ {c : Tm}, Star b✝ c → ∃ d, Star c✝ d ∧ Star c d`, goal
`∃ d, Star c✝ d ∧ Star c d`. `strip (par_of_step s) hc` gives `d` with `Star b✝ d`, `Par c d`; the IH on
`Star b✝ d` gives `e`; R5 to unpack, R2 with `star_trans (star_of_par _) _` on the `c` side.

### Worked combinations (guide Part W, on the toy objects)

- **W1.** Inversion lemmas `R_b : R .b t → t = .b` (R3, then `rfl`) and `R_bx` for `node b x` (R4, `rw`, R2).
- **W2.** `RT r x y → RT s (f x) (f y)` when `f` maps `r`-steps to `s`-steps (R7, R1).
- **W3.** The diamond for the toy `R` (R9 with R8, `cases`, R5, R1, R2), with one overlap case
  (`node` vs `drop`, solved by inverting the left child).

---

## Traps

- `Step` has no one-step diamond: `S x y z ⟶ x z (y z)` duplicates `z`. Do not try `Step`-diamond; use `Par`.
- `induction hb` **without** `generalizing c`: the IH is about the one `c` in context and cannot be
  applied to the reducts you meet. Generalize before inducting; `cases hc` comes *after* `induction`.
- The same name means different constructors: `.K` is `Tm.K`, `Step.K` or `Par.K`, decided by the
  expected type. In `.app (.refl .K) hx2 : Par _ _`, `.app` is `Par.app`, `.refl` is `Par.refl` and
  `.K` is `Tm.K`.
- `obtain ⟨_, rfl, _⟩` needs a variable on one side of the equation. For `K e1 = K e2` name it and
  `cases he` (R6).
- In the `app` vs `K` case the IH `iht` is about the head `K x`, not `x`: give it a `Par` of the head.
- `cases` keeps unnamed premises as `a✝`; use `cases h with | app h1 h2 => …` (or `rename_i`).
- Leave no `exact?` / `apply?` / `try?` in the file: they are search commands, not proofs.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `Par`/`Step`/`Star` by a rule | `exact .app h1 h2`, `.K hx`, `.refl _`, `.step s h` | R1 |
| prove `∃ x', t = f x' ∧ Q x'` | `exact ⟨_, rfl, h⟩` | R2 |
| `Par .K t` → `t = .K` | `cases h; rfl` | R3 |
| case split on a derivation | `cases h with \| refl => … \| app h1 h2 => …` | R4 |
| use `∃ x', t = f x' ∧ …`, substituting `t` | `obtain ⟨x', rfl, hx⟩ := e` | R5 |
| `C u = C v` → `u = v` substituted | `cases he` | R6 |
| induction on `Star` | `induction h with \| refl => … \| step s _ ih => …` | R7 |
| induction on `Par` (IHs after premises) | `\| app ht hu iht ihu => …`, `\| S hx hy hz ihx ihy ihz => …` | R8 |
| IH for every `c` | `induction hb generalizing c with …` | R9 |
| apply a generalized IH | `obtain ⟨d, h1, h2⟩ := iht hc'` | R9, R5 |
| rewrite by an inversion fact | `rw [par_K h1]` | TACTIC_STATES `rw [h]` |
