# H027 · Typed combinators are normalising (Tait): cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`exact`, `rfl`, `refine`, `·`, `<;>`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): inductive types and relations, `theorem`, `exact`,
`intro`, `cases`, anonymous constructors `⟨_, _⟩`. **New here:** core Lean only, no Mathlib. Proofs
*about derivations* (of `Star`, `Step`, `HasTy`), a predicate defined *by recursion on types*, and
Tait's method of **logical relations** (reducibility).

**The proof plan.** Types `Ty` are `base` and arrows `.arr A B` (informally `A → B`). Terms `Tm` are the
constants `S`, `K` and application `.app t u` (written `t u`, left associative: `K x y` is `(K x) y`).
`HasTy t A` is the typing judgement (`K : A → B → A`, `S : (A → B → C) → (A → B) → A → C`, and an
application rule). One step `Step a b` (informally `a ⟶ b`) contracts `K x y ⟶ x` or
`S x y z ⟶ x z (y z)` anywhere in the term; `Star a b` is zero or more steps (`⟶*`). `Normal v`: no step
leaves `v`. `WN t` (weakly normalising): `∃ v, t ⟶* v ∧ Normal v`.

Induction on `HasTy` directly fails: `WN t` and `WN u` say nothing about `WN (t u)`. So strengthen the
statement to the **reducibility** predicate `Red A t`, defined by recursion on `A`:
`Red base t := WN t` and `Red (A → B) t := WN t ∧ ∀ u, Red A u → Red B (t u)`.
Then the `app` case is exactly the second half of `Red (A → B) t`.

| Milestone | Statement | Role |
|---|---|---|
| `star_trans`, `star_appL`, `star_appR` (add them) | `⟶*` is transitive and a congruence on both sides of `app` | build reduction sequences of `K x`, `S x`, `S x y` |
| `normal_K`, `normal_S`, `normal_Kx`, `normal_Sx`, `normal_Sxy` (add them) | `K`, `S`, `K x`, `S x`, `S x y` are normal when `x`, `y` are | the normal forms of partial applications |
| `red_wn` (add it) | `Red A t → WN t` | read `WN` off any `Red` |
| `red_back` | `Step t t' → Red A t' → Red A t` | `Red` is closed under backward steps |
| `red_K`, `red_S` | `Red` (type of `K`) `K`, `Red` (type of `S`) `S` | the two base cases of the induction |
| `fundamental` (add it) | `HasTy t A → Red A t` | induction on the typing |
| `weak_normalization` | the spec | `red_wn (fundamental h)` |

## How to read an entry

Each entry is one tactic or proof-building move. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `P`, `Q`, `G` are "the rest of your goal" (`P : Prop`, `Q : α → Prop`, `G : E → U → Prop`, …). The
  step changes only the part shown inside them.
- The entries run on toy objects defined at the top of `guide.lean`, not on the exercise's:
  - `U`: toy types `o` and `fn A B` (plays `Ty`);
  - `E`: toy terms `a`, `b`, `node l r` (plays `Tm`);
  - `Stp : E → E → Prop`: `drop : Stp (node a x) x`, and `left`/`right` steps in a child (plays `Step`);
  - `RT r`: zero or more `r`-steps for any relation `r : α → α → Prop` (plays `Star`);
  - `Nf t := ∀ t', ¬ Stp t t'` and `Ends t := ∃ v, RT Stp t v ∧ Nf v` (play `Normal`, `WN`);
  - `Good Q : U → E → Prop`: `Q t` at `o`; at `fn A B`, `Q t ∧ ∀ u, Good Q A u → Good Q B (node t u)`
    (plays `Red`, for any predicate `Q : E → Prop`);
  - `Ok : E → U → Prop`: a toy typing judgement with rules `a`, `b`, `node` (plays `HasTy`).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `⟶`, `⟶*` | only in comments: one `Step`, and `Star` (zero or more steps). The infoview shows `Step a b`, `Star a b` |
| `t.app u` | `Tm.app t u`, the application `t u`. Lean prints `C.f x` for `f C x` ("field notation") |
| `(Tm.K.app x).app y` | `K x y`; `((Tm.S.app x).app y).app z` is `S x y z` |
| `A.arr B`, `Ty.base` | the arrow type `A → B` and the base type; in the toy, `A.fn B`, `U.o` |
| `Tm.K`, `E.a`, `E.b.node x` | constructors printed with their type's name; `E.b.node x` is `node b x` |
| `.step s h`, `.appL s`, `.refl _`, `.K` | dot notation: a constructor (rule) of the **expected** type (`Star.step`, `Step.appL`, …) |
| `Red (A.arr B) t` | not unfolded in the infoview, but it *is* `WN t ∧ ∀ u, Red A u → Red B (t.app u)` |
| `Normal t` | it *is* `∀ t', ¬ Step t t'`; `intro` sees through it |
| `x✝`, `y✝`, `a✝`, `A_ih✝` | inaccessible names Lean made up (you cannot type them); name them with `with` or `rename_i`. `A_ih✝` is the IH you dropped with `_` |
| `case refl`, `case arr` | the goal tag: which rule or constructor this goal came from |
| `ihB : ∀ {t t' : Tm}, …` | an induction hypothesis for every `t t'` (from `generalizing`): apply it as `ihB s' h'` |

---

## Part 1 · helpers: `Star` lemmas and normal forms

Not in the stub; add them right after the first `-- END SPEC` (before `def Red`). `star_trans : Star a b → Star b c → Star a c`,
`star_appL : Star t t' → Star (t u) (t' u)`, `star_appR : Star u u' → Star (t u) (t u')`;
`normal_K`, `normal_S`; `normal_Kx`, `normal_Sx : Normal x → Normal (K x)`, `Normal (S x)`;
`normal_Sxy : Normal x → Normal y → Normal (S x y)`.

### Induction on a closure, building derivations

**R1 · `induction h with | refl x => ?_ | step s _ ih => ?_`** changes the **goal list**: one goal per rule
of `RT`. `RT.step` has premises `r x y` (no IH: it is not an `RT`) and `RT r y z` (IH `ih`). Names after a
rule go to its explicit premises, then to the IHs. A hypothesis mentioning the right end of `h` (here `hy`)
is reverted and re-introduced in each case, so the IH is an **implication**: use `ih hy`. This is how
`star_trans` works (induct on the first `Star`; the second rides along). Placeholders:
`{α : Type} (r : α → α → Prop) (Q : α → Prop) (x y : α) (h : RT r x y) (hy : Q y)`.

| Before | After |
|---|---|
| `h : RT r x y, hy : Q y ⊢ Q x` | `hy : Q x ⊢ Q x` (case `refl`) |
| | `s : r x✝ y✝, ih : Q z✝ → Q y✝, hy : Q z✝ ⊢ Q x✝` (case `step`) |

**R2 · `exact .step s h`** **closes** the goal by one rule. `.step` means `RT.step`, resolved from the
expected type; implicit `{x y z}` come from unification. Placeholders: `(s : r x y) (h : RT r y z)`.

| Before | After |
|---|---|
| `s : r x y, h : RT r y z ⊢ RT r x z` | closed |

**R3 · `exact .step (.left s) h`** **closes** the goal; rules nest. `.left s : Stp (node l r) (node l' r)` is
a step of the node made from a step of the left child, the shape of `star_appL`'s step case (`.appL`;
`.appR` for `star_appR`). Placeholders: `(l l' r v : E) (s : Stp l l') (h : RT Stp (node l' r) v)`.

| Before | After |
|---|---|
| `s : Stp l l', h : RT Stp (l'.node r) v ⊢ RT Stp (l.node r) v` | closed |

### Normal forms

**R4 · `intro t' h`** on a goal `Nf t` changes the **context and the goal**. `intro` unfolds `Nf` and reads
`¬ A` as `A → False`. Placeholders: `(t : E)`.

| Before | After |
|---|---|
| `⊢ Nf t` | `t' : E, h : Stp t t' ⊢ False` |

**R5 · `cases h`** with no rule able to produce `h` **closes** the goal. Every `Stp` rule has a `node` on
the left, so `Stp .b t'` has no case (in the exercise: `Step .K t'`, `Step .S t'`). Placeholders: `(t' : E)`.

| Before | After |
|---|---|
| `h : Stp E.b t' ⊢ False` | closed |

**R6 · `cases h with | left h => ?_ | right h => ?_`** changes the **goal list**: one goal per rule whose
left side fits `node b x`. `drop` needs `node a _` and is gone. In the exercise, `Step (K x) t'` leaves
`appL` (a step of `K`: R5 again) and `appR` (a step of `x`: R7). Placeholders:
`(P : Prop) (x t' : E) (h : Stp (node b x) t')`.

| Before | After |
|---|---|
| `h : Stp (E.b.node x) t' ⊢ P` | `l'✝ : E, h : Stp E.b l'✝ ⊢ P` (case `left`) |
| | `r'✝ : E, h : Stp x r'✝ ⊢ P` (case `right`) |

**R7 · `exact hx _ h`** **closes** `False`: `hx : Nf x` is a function, `hx y : ¬ Stp x y`, and
`hx y h : False`. A lemma such as `normal_Sx hx` is used the same way: `normal_Sx hx _ h`.
Placeholders: `(x y : E) (hx : Nf x) (h : Stp x y)`.

| Before | After |
|---|---|
| `hx : Nf x, h : Stp x y ⊢ False` | closed |

**W1** chains R4, R6, R5, R7 to prove `Nf (node b x)` from `Nf x`:

```lean-goal
⊢ Nf (E.b.node x)
⊢ False
```

---

## Part 2 · `Red`, `red_wn` and `red_back`

`Red : Ty → Tm → Prop` is given (it is the milestone `def`). Add `red_wn : Red A t → WN t` right after `def Red`.
`red_back : Step t t' → Red A t' → Red A t`.

**R8 · `cases A with | o => ?_ | fn A B => ?_`** changes the **goal list**: one goal per type former.
After the split `Good Q U.o t` **is** `Q t` and `Good Q (A.fn B) t` **is** a conjunction, by the
definition's equations (definitional unfolding), so `exact h` and `exact h.1` work without `unfold`. This is
all of `red_wn`. Placeholders: `(Q : E → Prop) (A : U) (t : E) (h : Good Q A t)`.

| Before | After |
|---|---|
| `h : Good Q A t ⊢ Q t` | `h : Good Q U.o t ⊢ Q t` (case `o`) |
| | `h : Good Q (A.fn B) t ⊢ Q t` (case `fn`) |

**R9 · `exact h.2 u hu`** **closes** the goal with the arrow clause: `h.1 : Q t`,
`h.2 : ∀ u, Good Q A u → Good Q B (node t u)`. Clauses chain: `(h.2 u hu).2 w hw` for two arguments.
Placeholders: `(A B : U) (t u : E) (h : Good Q (.fn A B) t) (hu : Good Q A u)`.

| Before | After |
|---|---|
| `h : Good Q (A.fn B) t, hu : Good Q A u ⊢ Good Q B (t.node u)` | closed |

**R10 · `induction A generalizing t with | o => ?_ | fn A B ihA ihB => ?_`** changes the **goal list**:
induction on the type, one IH per argument type. `generalizing t` makes the IHs hold for every term:
in the `fn` case the context gains `ihB : ∀ {t : E}, G B t → Good Q B t` (and `ihA`), which you can apply at
`node t u`. Hypotheses mentioning `t` (here `h`) come along. In `red_back`, generalize both `t t'`, and
`ihB` takes the step `.appL s : Step (t u) (t' u)`. Placeholders:
`(Q : E → Prop) (G : U → E → Prop) (A : U) {t : E} (h : G A t)`.

| Before | After |
|---|---|
| `h : G A t ⊢ Good Q A t` | `h : G U.o t ⊢ Good Q U.o t` (case `o`) |
| | `h : G (A.fn B) t ⊢ Good Q (A.fn B) t` (case `fn`) |

### `∃ … ∧ …`: taking apart and building

**R11 · `obtain ⟨v, hv, nv⟩ := h`** changes the **context**: `h : Ends t` (a definition hiding
`∃ v, RT Stp t v ∧ Nf v`) becomes a witness and two facts. Works on a term too: `obtain … := red_wn hx`.
Placeholders: `(t : E) (h : Ends t)`.

| Before | After |
|---|---|
| `h : Ends t ⊢ P` | `v : E, hv : RT Stp t v, nv : Nf v ⊢ P` |

**R12 · `obtain ⟨⟨v, hv, nv⟩, hf⟩ := h`** changes the **context**: nested patterns for
`h : (∃ v, A v ∧ B v) ∧ F`, the shape of `Red (A.arr B) t'` (its `WN` half and its clause `hf`).
Placeholders: `{α : Type} (A B : α → Prop) (F P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `hf : F, v : α, hv : A v, nv : B v ⊢ P` |

**R13 · `exact ⟨v, .step s hv, nv⟩`** **closes** `Ends t`: one more step in front of `hv`. The anonymous
constructor builds `∃` and `∧` at once and sees through the definition. Placeholders:
`(t t' v : E) (s : Stp t t') (hv : RT Stp t' v) (nv : Nf v)`.

| Before | After |
|---|---|
| `s : Stp t t', hv : RT Stp t' v, nv : Nf v ⊢ Ends t` | closed |

**R14 · `exact ⟨hq, fun u hu => e⟩`** **closes** `Q ∧ ∀ u, A u → B u`: the `∀ … → …` half is a function.
In `red_back` the body is `ihB (.appL s) (hf u hu)`. Placeholders:
`{α : Type} (Q : Prop) (A B : α → Prop) (hq : Q) (g : ∀ u, A u → B u)`.

| Before | After |
|---|---|
| `⊢ Q ∧ ∀ (u : α), A u → B u` | closed |

**W2** (R11 then R13) is `red_back`'s base case on the toy: `Ends` is closed under backward steps.

```lean-goal
⊢ Ends t
```

**W3** (R10 then R14 with the IH) proves `Good (fun _ => True) A t` by induction on `A`:

```lean-goal
⊢ Good (fun x => True) A t
```

---

## Part 3 · `red_K` and `red_S`

`red_K : Red (.arr A (.arr B A)) .K` and `red_S` for `S`'s type. Peel one arrow per argument: prove the `WN`
half of the partial application, then open the clause for the next argument. Only the fully applied
`K x y`, `S x y z` are not normal; there, step back with `red_back`.

**R15 · `refine ⟨⟨_, .refl _, nt⟩, fun x hx => ?_⟩`** changes the **goal and the context**: the `WN`
half is closed now (zero steps, `.refl _`, the witness `_` read off from it), and the one remaining goal sits
under `fun x hx`, so the context gains `x` and `hx`. In `red_K`: `nt` is `normal_K`, and the new goal is
`Red (B.arr A) (Tm.K.app x)`. Placeholders: `(A B : E → Prop) (t : E) (nt : Nf t)`.

| Before | After |
|---|---|
| `nt : Nf t ⊢ Ends t ∧ ∀ (x : E), A x → B x` | `x : E, hx : A x ⊢ B x` |

For a partial application such as `K x` the `WN` half is not `.refl`: take `hx` apart with
`obtain ⟨x', hx', nx'⟩ := red_wn hx` (R11), then `⟨_, star_appR hx', normal_Kx nx'⟩`. For `S x y`, chain the
two congruences with `star_trans`.

**R16 · `apply back .drop`** changes the **goal**: backward through one step. `back` is closed under backward
steps (like `red_back`); the step proof `.drop` fixes both terms by unification with the goal, and the remaining
premise `G x` is the new goal. In `red_S`: `apply red_back .S` turns `Red C (((Tm.S.app x).app y).app z)` into
`Red C ((x.app z).app (y.app z))`, which R9 twice closes. As a term the same move is `back .drop h : G (node a x)`; in `red_K`,
`red_back .K hx` proves the fully applied `K x y`. Placeholders:
`(G : E → Prop) (back : ∀ {t t'}, Stp t t' → G t' → G t) (x : E) (h : G x)`.

| Before | After |
|---|---|
| `h : G x ⊢ G (E.a.node x)` | `h : G x ⊢ G x` |

---

## Part 4 · `weak_normalization`

Statement: `HasTy t A → WN t`. Add `fundamental : HasTy t A → Red A t` after `red_S`, above the SKELETON comment; then the theorem is `red_wn` applied
to `fundamental h`, a term with no tactics.

**R17 · `induction h with | a => ?_ | b => ?_ | node _ _ ih1 ih2 => ?_`** changes the **goal list**: one goal
per typing rule; `t` and `A` become each rule's. `Ok.node` has two `Ok` premises, so two IHs after them
(`_ _` drops the premises' names). In `fundamental`: the cases are `K`, `S` (the milestones) and
`app _ _ ih1 ih2`, closed by the arrow clause `ih1.2 _ ih2` (R9). Placeholders:
`(G : E → U → Prop) {t : E} {A : U} (h : Ok t A)`.

| Before | After |
|---|---|
| `h : Ok t A ⊢ G t A` | `⊢ G E.a U.o` (case `a`) |
| | `A✝ : U ⊢ G E.b (A✝.fn A✝)` (case `b`) |
| | `ih1 : G l✝ (A✝.fn B✝), ih2 : G r✝ A✝ ⊢ G (l✝.node r✝) B✝` (case `node`) |

---

## Traps

- Do not leave search tactics (`exact?`, `apply?`, `try?`) in the file.
- `induction A` without `generalizing t t'` fixes the terms: the IH is then about the one `t` in context and
  useless at `.app t u`. Write `generalizing` (R10).
- `cases h with | appL h => .. | appR h => ..` lists only the rules that fit. Listing one that cannot fit
  (the `K` contraction on `K x`, which needs two arguments) is an error: "Alternative `K` is not needed".
- `|` alternatives of `cases … with` / `induction … with` go on their own lines; `?_` or a tactic after `=>`.
- `Red (.arr A B) t` is a conjunction by definition, but the infoview never shows it unfolded. You need no
  `unfold`: `h.1`, `h.2`, `obtain` and `⟨_, _⟩` see through it (R8). (`simp only [Red] at h` shows the body.)
- The second argument of the clause is the reducibility proof, not the term: `hx.2 z hz`, not `hx.2 hz`.
- `red_back` needs only one step backwards, so in `red_S` do not try to reduce `S x y z` further:
  `apply red_back .S` and use the clauses of `hx`, `hy`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct on `Star a b` (other hypotheses ride along) | `induction h with \| refl => .. \| step s _ ih => ..` | R1 |
| one rule / nested rules | `exact .step s h`, `.step (.appL s) ih` | R2, R3 |
| prove `Normal t` | `intro t' h`, then `cases h` | R4, R5 |
| `Normal (K x)` and friends | `cases h with \| appL h => .. \| appR h => ..` | R6 |
| use `hx : Normal x` | `hx _ h : False` | R7 |
| `Red A t → WN t` | `cases A with \| base => exact h \| arr A B => exact h.1` | R8 |
| use the arrow clause | `h.2 u hu`, `(h.2 u hu).2 w hw` | R9 |
| induct on the type | `induction A generalizing t t' with \| base => .. \| arr A B _ ihB => ..` | R10 |
| take `WN t` / `Red (A.arr B) t` apart | `obtain ⟨v, hv, nv⟩ := h`, `obtain ⟨⟨v, hv, nv⟩, hf⟩ := h` | R11, R12 |
| build `WN t` / a `Red` arrow | `⟨v, .step s hv, nv⟩`, `⟨wn, fun u hu => ..⟩` | R13, R14 |
| peel one arrow | `refine ⟨⟨_, .refl _, normal_K⟩, fun x hx => ?_⟩` | R15 |
| step back from a redex | `apply red_back .S` | R16 |
| induct on typing | `induction h with \| K => .. \| S => .. \| app _ _ ih1 ih2 => ..` | R17 |
| see the state | infoview | |
