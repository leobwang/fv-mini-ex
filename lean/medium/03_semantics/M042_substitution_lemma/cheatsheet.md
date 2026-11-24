# M042 · The substitution lemma: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rfl`, `have`, `·` focusing,
inductive types, definitions by pattern matching, `simp`. **New here:** structural induction on a
syntax tree with `induction … with`, one tactic shared by two cases, induction hypotheses that are
implications, `if … then … else` goals, and the boolean operators `==`, `||`. No Mathlib.
M043–M045 reuse the same `State`, `AExp`, `aeval` and `update`.

## How to read an entry

Each entry is one tactic or one proof move. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Form → Prop`, `P : Bool → Prop`, …). The step changes only the
  part inside `P (…)`, wherever it sits in a larger goal. `Q R : Form → Prop` are arbitrary predicates.
- `{α : Type}` is any type. `[Decidable c]` says the proposition `c` can be tested by a program, which
  `if c then … else …` needs; every `x = y` on `Nat` is decidable.
- Induction needs a concrete inductive type, so the entries use the guide's toy language, not `AExp`:
  `Form` (constructors `lit b`, `atom p`, `and f g`, `or f g`), valuations `σ : Nat → Bool`, and the
  functions `eval σ f : Bool`, `occ p f : Bool` ("does atom `p` occur in `f`"), `upd σ p b`
  ("`σ` with atom `p` reset to `b`") and `dual f` (swap `and`/`or`). They mirror the exercise's `AExp`,
  `aeval`, `occurs`, `update` and `subst`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The objects

- `State := Nat → Int`: a state maps variable number `x` to its value `s x`.
- `AExp`: arithmetic expressions `num n`, `var x`, `plus e1 e2`, `times e1 e2`; `aeval s e : Int` is the
  value of `e` in state `s`.
- `update s x v`: the state `s` with `x` set to `v`, written $s[x \mapsto v]$. It is
  `fun y => if y = x then v else s y`, so `update s x v y` unfolds to an `if` (R5).
- `subst x a e`: `e` with every `var x` replaced by the expression `a`, written $e[a/x]$.
- `occurs x e : Bool`: whether `var x` appears in `e`. `occurs x e = false` means "`x` does not occur".
- The three theorems: $\mathrm{aeval}\ s\ (e[a/x]) = \mathrm{aeval}\ (s[x \mapsto \mathrm{aeval}\ s\ a])\ e$
  (the semantic content of Hoare's assignment axiom $\{P[a/x]\}\ x := a\ \{P\}$); a variable that does
  not occur cannot change the value; and $e[a/x][b/x] = e[a/x]$ when `x` does not occur in `a`.

## Reading the goals

| You see | It means |
|---|---|
| `AExp.var y`, `AExp.num n` | the constructor written `.var y`, `.num n` in the source |
| `e1.plus e2`, `e1.times e2` | `AExp.plus e1 e2`, `AExp.times e1 e2`: Lean prints `C.f x y` as `x.f y` when `x : C` |
| `f.and g`, `Form.atom p` | the same for the guide's `Form` |
| `update s x (aeval s a)` | the state $s[x \mapsto \mathrm{aeval}\ s\ a]$ |
| `if y = x then v else s y` | the unfolded `update s x v y` |
| `y == x` | the *boolean* test `y == x : Bool` (class `BEq`), not the proposition `y = x : Prop` |
| `a \|\| b`, `a && b`, `!b` | boolean or, and, not |
| `q ≠ p` | `¬q = p` (`≠` is notation for it) |
| `ih1 : Q f → R f` | an induction hypothesis with a premise: it applies only once you prove `Q f` (R9) |
| `inst✝ : Decidable c` | an unnamed instance argument (`[Decidable c]`); you never mention it |
| `case var`, `case plus` | the goal for constructor `var` / `plus` after `induction` |
| `case pos`, `case neg` | the `h : c` and `h : ¬c` goals after `by_cases` |

---

## Part 1 · `aeval_subst`

Statement: `aeval s (subst x a e) = aeval (update s x (aeval s a)) e` for every expression `e`. Substituting
syntactically and evaluating equals evaluating in the updated state. By induction on `e`; only `var y`
needs a case split on `y = x`.

**R1 · `induction f with | lit b => … | atom p => … | and f g ih1 ih2 => … | or f g ih1 ih2 => …`** changes
the **goal list** and the **context**. One goal per constructor; each case gets the constructor's
arguments under the names you write, and one induction hypothesis per argument of the type itself
(`ih1` for `f`, `ih2` for `g`). The alternatives go in constructor order and must cover all
constructors. In the guide `?_` leaves a case open; in a proof write the case's tactics after `=>`.
Placeholders: `(P : Form → Prop) (f : Form)`.

| Before | After |
|---|---|
| `f : Form ⊢ P f` | `b : Bool ⊢ P (Form.lit b)`, `p : Nat ⊢ P (Form.atom p)`, `f g : Form, ih1 : P f, ih2 : P g ⊢ P (f.and g)`, `f g : Form, ih1 : P f, ih2 : P g ⊢ P (f.or g)` |

**R2 · `rfl`** **closes** a goal whose two sides compute to the same value. A function defined by pattern
matching reduces on a constructor by its defining equation, also when two of them are nested. In the
exercise, case `num n`: both sides reduce to `n`. Placeholders: `(σ : Nat → Bool) (p : Nat)`.

| Before | After |
|---|---|
| `⊢ eval σ (dual (Form.atom p)) = σ p` | no goals |

**R3 · `by_cases h : q = p`** changes the **goal list**: two copies of the goal, tagged `pos` with
`h : q = p` and `neg` with `h : ¬q = p`. Follow it with `<;> tac` to run `tac` on both. Placeholders:
`(p q : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `h : q = p ⊢ P`, `h : ¬q = p ⊢ P` |

**R4 · `simp only [dual]`** changes the **goal**: it applies a defining equation of `dual` wherever `dual`
meets a constructor (`dual (.and f g) = .or (dual f) (dual g)`); `dual f` for a variable `f` stays.
`simp [subst, aeval]` does this for the exercise's functions. Placeholders: `(f g : Form)`.

| Before | After |
|---|---|
| `⊢ P (dual (f.and g))` | `⊢ P ((dual f).or (dual g))` |

**R5 · `simp only [upd]`** changes the **goal**: `upd` is defined as `fun q => …`, so unfolding it in
`upd σ p b q` also applies the `fun` to `q` (β-reduction). `update` in the exercise works the same way.
Placeholders: `(σ : Nat → Bool) (p q : Nat) (b : Bool) (P : Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P (upd σ p b q)` | `⊢ P (if q = p then b else σ q)` |

**R6 · `simp [h]`** with `h : c` or `h : ¬c` changes the **goal**: it decides the `if`. `simp` turns the
condition into `True` or `False` using `h`, then applies `if_pos : c → (if c then t else e) = t` or
`if_neg : ¬c → (if c then t else e) = e`. `h : q ≠ p` works like `h : ¬q = p`. With `h : y = x` between
two variables, `simp` first rewrites `y` into `x`, and `x = x` is `True`: same result.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (t e : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `h : c ⊢ P (if c then t else e)` | `h : c ⊢ P t` |
| `h : ¬c ⊢ P (if c then t else e)` | `h : ¬c ⊢ P e` |

**R7 · `simp only [eval]`, then `rw [ih1, ih2]`** changes the **goal**: in a recursive case the IHs speak
about `f` and `g` while the goal speaks about `f.and g`. Unfold one step so that `eval σ f` and
`eval σ g` appear, then rewrite with the IHs; `rw` closes the goal with `rfl` when both sides become
equal without unfolding further definitions (otherwise finish with `rfl`, R2). `simp [eval, ih1, ih2]`
does all of it in one call. Placeholders: `(σ τ : Nat → Bool) (f g : Form)`,
`ih1 : eval σ f = eval τ f`, `ih2 : eval σ g = eval τ g`.

| Before | After `simp only [eval]` | After `rw [ih1, ih2]` |
|---|---|---|
| `⊢ eval σ (f.and g) = eval τ (f.and g)` | `⊢ (eval σ f && eval σ g) = (eval τ f && eval τ g)` | no goals |

**R8 · `| and f g ih1 ih2 | or f g ih1 ih2 => tac`** changes the **goal list**: two alternatives that bind
the same names share one tactic, which runs on each case separately. In the exercise `plus` and `times`
have the same shape, so one line handles both. Placeholders: `(P : Form → Prop)`.

| Before | After |
|---|---|
| `⊢ P f` | `ih1 : P f, ih2 : P g ⊢ P (f.and g)`, `ih1 : P f, ih2 : P g ⊢ P (f.or g)` (both handled by `tac`) |

**W1** (`dual (dual f) = f`) chains R1 with R8, `rfl`/`simp [dual]` at the leaves and R4 → R7 at the nodes.
**W2** (`upd σ p (σ p) q = σ q`) is R3 followed by `simp [upd, h]` (R5, R6) in each case: the shape of
the `var y` case.

---

## Part 2 · `aeval_update_irrelevant`

Statement: if `occurs x e = false`, then `aeval (update s x v) e = aeval s e`. By induction on `e` again,
but now the hypothesis `h` is about `e`, which changes the IHs.

**R9 · `induction f` when `h` mentions `f`** changes the **context**: `induction` generalises `h` by
itself, so in each case `h` is about that constructor and each IH carries the hypothesis as a premise.
You cannot use `ih1` until you prove `Q f`; R12 gets it from `h`. Placeholders: `(Q R : Form → Prop)`,
`h : Q f`.

| Before | After (case `and`) |
|---|---|
| `h : Q f ⊢ R f` | `ih1 : Q f → R f, ih2 : Q g → R g, h : Q (f.and g) ⊢ R (f.and g)` |

**R10 · `simp` on `(q == p) = false`** changes the **goal**: `==` is the boolean test, `=` the
proposition, and `simp` translates between them with `beq_iff_eq : (a == b) = true ↔ a = b` and
`beq_eq_false_iff_ne : (a == b) = false ↔ a ≠ b`. The exercise's `occurs x (.var y)` unfolds to
`y == x`. Placeholders: `(p q : Nat)`.

| Before | After |
|---|---|
| `⊢ (q == p) = false` | `⊢ ¬q = p` |

**R11 · `simpa [occ] using h`** **closes** the goal: it simplifies `h` and the goal with the same lemmas
(here `occ p (.atom q)` → `q == p` → R10), then closes the goal with the simplified `h`. Used as
`have hne : q ≠ p := by simpa [occ] using h` it adds a fact for R6 instead. Placeholders: `(p q : Nat)`.

| Before | After |
|---|---|
| `h : occ p (Form.atom q) = false ⊢ q ≠ p` | no goals |

**R12 · `simp only [occ, Bool.or_eq_false_iff] at h`** changes the **context**: `h` about a node becomes
the two facts the IHs need. The lemma is `Bool.or_eq_false_iff : (a || b) = false ↔ a = false ∧ b = false`.
Placeholders: `(p : Nat) (f g : Form) (G : Prop)`.

| Before | After |
|---|---|
| `h : occ p (f.and g) = false ⊢ G` | `h : occ p f = false ∧ occ p g = false ⊢ G` |

**R13 · `rw [ih1 h.1]`** changes the **goal**: `h.1 : A` and `h.2 : B` are the two halves of `h : A ∧ B`
(`And.left`, `And.right`), and `ih1 h.1` is the IH with its premise supplied, an ordinary equation for
`rw` or `simp`. In the exercise: `simp [aeval, ih1 h.1, ih2 h.2]`. Placeholders:
`(Q : Form → Prop) (F G : Form → Int) (f g : Form)`, `ih1 : Q f → F f = G f`.

| Before | After `rw [ih1 h.1]` | After `rw [ih2 h.2]` |
|---|---|---|
| `h : Q f ∧ Q g ⊢ F f + F g = G f + G g` | `⊢ G f + F g = G f + G g` | no goals |

**W3** (`occ p f = false → occ p (dual f) = false`) chains R9, R11 at the atom, and R12 → R13 at the
nodes: the shape of this whole theorem.

---

## Part 3 · `subst_twice`

Statement: if `occurs x a = false`, then `subst x b (subst x a e) = subst x a e`. After replacing `x` by
`a`, `x` is gone, and substituting for an absent variable does nothing. Prove two milestone lemmas
first (above the theorem, outside the spec regions; their statements are in the SKELETON), then
compose them.

- **M1** (`x` stays absent): induction on `e` as in Part 1 (R1, R2, R8); case `var y`: R3, then in
  both cases one call `simp [subst, occurs, …]` with the split hypothesis and `h` (R4, R6, R10).
  Separate calls fail: `simp only [subst, occurs]` leaves `occurs x (if y = x then a else AExp.var y)`,
  because `occurs` cannot unfold until the `if` is decided. Nodes: R4 → R7; here `rw [ih1, ih2]` leaves
  `(false || false) = false`, which `rw`'s own `rfl` does not compute, so finish with `rfl` (R2), or do it all with
  `simp [subst, occurs, ih1, ih2]`.
- **M2** (absent ⇒ unchanged): the shape of Part 2 (R1, R8, R9, R2), with `subst` for `aeval`. Case
  `var y`: `have hne : y ≠ x` by R11, then unfold `subst` and decide the `if` (R4, R6). Nodes: R12 → R4,
  R13.

**R14 · `apply g`** changes the **goal**: to prove `C e` from `g : ∀ e, B e → C e`, apply `g`; what
is left is its premise. Prove that with the other lemma: `exact f e h`. As a term the whole proof is
`g e (f e h)`. Implicit arguments `{x : Nat}` of a milestone are found by Lean and not written.
Placeholders: `{α : Type} (A B C : α → Prop) (e : α)`, `f : ∀ e, A e → B e`, `h : A e`.

| Before | After |
|---|---|
| `⊢ C e` | `⊢ B e` |

---

## Traps

- `grind` and `try?` are banned: `induction e <;> grind […]` closes the first two theorems outright, and
  the point is the induction itself. Do not leave search tactics (`exact?`, `apply?`) in the file either.
- Indent the `| …` alternatives at least as far as `induction`, and put a case's tactics after its `=>`
  (or on more-indented lines below it).
- In `| plus e1 e2 ih1 ih2 | times e1 e2 ih1 ih2 => tac`, both alternatives must bind the same names,
  since `tac` mentions them.
- `y == x` (a `Bool`) and `y = x` (a `Prop`) are different; `rw [h]` with `h : ¬y = x` will not find
  `y == x`. Let `simp` translate (R10).
- In Part 2, `ih1 : occurs x e1 = false → …` is not an equation; `simp [ih1]` may fail to use it. Supply
  the premise: `ih1 h.1` (R12, R13).
- `simp [h]` with `h : y = x` rewrites `y` to `x` in the whole goal. That is harmless here, but do not be
  surprised that `y` disappears.
- `rw` ends with a weak `rfl` that unfolds only reducible definitions, not `||`: after `rw [ih1, ih2]` in M1 the goal
  `(false || false) = false` stays open. It computes, so `rfl` (R2) closes it.
- `t1 ; t2` runs `t2` on the first goal only. After `by_cases`, use `<;>` or `·` for both cases.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on an expression | `induction e with \| num n => … \| var y => … \| plus e1 e2 ih1 ih2 => … \| times e1 e2 ih1 ih2 => …` | R1 |
| two cases, one tactic | `\| plus e1 e2 ih1 ih2 \| times e1 e2 ih1 ih2 => tac` | R8 |
| both sides compute | `rfl` | R2 |
| split on `y = x` | `by_cases h : y = x` (then `<;> tac`) | R3 |
| unfold a recursive def on a constructor | `simp [subst, aeval]` | R4 |
| unfold `update s x v y` | `simp [update]` | R5 |
| decide `if y = x then … else …` | `simp [h]` with `h : y = x` or `h : ¬y = x` | R6 |
| node case with plain IHs | `simp [defs, ih1, ih2]` | R7 |
| hypothesis about `e` ⇒ IH with a premise | (automatic in `induction`) | R9 |
| `(y == x) = false` ↔ `¬y = x` | `simp` (`beq_eq_false_iff_ne`) | R10 |
| `y ≠ x` from `occurs x (.var y) = false` | `have hne : y ≠ x := by simpa [occurs] using h` | R11 |
| split `occurs x (e1.plus e2) = false` | `simp only [occurs, Bool.or_eq_false_iff] at h` | R12 |
| use an IH with a premise | `simp [defs, ih1 h.1, ih2 h.2]` | R13 |
| theorem from milestones | `apply g; exact f e h`, or the term `g e (f e h)` | R14 |
| see the state | infoview | |
