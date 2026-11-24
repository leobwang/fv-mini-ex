# H002 · Kripke semantics: excluded middle is not intuitionistic: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `have`, `⟨_, _⟩`, `.1`/`.2`, `fun`,
`·` focusing. **New here:** core Lean only (no Mathlib): induction on an inductive type and on an
inductive predicate, definitions by pattern matching that unfold by themselves, structures and
structure values, list membership, `rcases`/`rintro`/`obtain` patterns, named implicit arguments.

The mathematics. A *formula* is built from variables `p₀, p₁, …`, `⊥` (falsity), `∧`, `∨`, `→`; `¬a`
is `a → ⊥`. `ND Γ a` says `a` is derivable from the hypothesis list `Γ` in intuitionistic natural
deduction (one constructor per rule). A *Kripke model* `M` is a set of worlds `M.W` with a preorder
`M.le` (reflexive, transitive; `M.le w w'` reads "`w'` is a later world than `w`") and a valuation
`M.val n w` ("`pₙ` holds at `w`") that stays true at later worlds. `Forces M w a` (written `w ⊩ a`)
is truth at a world, defined by recursion on `a`; the `→` clause quantifies over all later worlds.
Soundness: whatever `ND` derives is forced at every world forcing the hypotheses. A model with a
world not forcing `p ∨ ¬p` then shows `p ∨ ¬p` is not derivable.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  (This `⊢` is Lean's; the exercise's own `ND Γ a` is a Lean proposition, not a proof state.)
- `P` is "the rest of your goal" (`P : α → Prop`, or with more arguments). The step changes only the
  part inside `P (…)`.
- `{α : Type}` is any type. The guide's own objects (`Tree`, `Tag`, `Sem`, `Graph`, `Gen`) are
  declared at the top of `guide.lean`; they stand in for the exercise's `Form`, `Forces`, `Kripke`,
  `ND` without being them.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Form.var 0`, `Form.bot` | the variable `p₀`; falsity `⊥` |
| `a.or b`, `a.imp b`, `a.and b` | `Form.or a b` (`a ∨ b`), `Form.imp a b` (`a → b`), `Form.and a b`: Lean prints `C.f x y` as `x.f y` |
| `.or a b` in your own code | `Form.or a b`; the leading dot looks `or` up in the type Lean expects there |
| `neg a` | `a.imp Form.bot`, i.e. `¬a`; an `abbrev`, so Lean unfolds it whenever needed |
| `ND Γ a` | `a` is derivable from the list `Γ` |
| `M.W`, `M.le w v`, `M.val n w` | the fields of the structure `M : Kripke` |
| `Forces M w a` | `w ⊩ a`; unfolds by itself to the clause for the outer constructor of `a` |
| `a :: Γ`, `[]`, `[a, b]` | list with head `a` and tail `Γ`; the empty list; `a :: b :: []` |
| `g ∈ Γ` | list membership (`List.Mem`) |
| `∀ (g : Form), g ∈ Γ → Q g` | how Lean prints `∀ g ∈ Γ, Q g` |
| `¬X` | `X → False` |
| `x✝`, `a✝¹`, `Γ✝` | inaccessible names made by a tactic; name them with `case`/`with`/`rename_i` |
| `M : Kripke := { W := Bool, … }` | a `let`: `M` with a visible value. `⋯` hides proofs |
| `∀ {w w' : M.W}, …` | `∀` with implicit binders: when you apply it, Lean fills `w w'` from the later arguments |
| `case inl`, `case orE` | the tag of a goal: which side of an `∨`, which constructor |
| `case refine_1`, `case refine_2` | the goals left by the first and second `?_` of a `refine` |

---

## Part 1 · `forces_mono` (milestone)

Statement: if `w ⊩ a` and `M.le w w'` then `w' ⊩ a` (forcing is monotone). Induction on `a`. Used by
Part 5 in the `impI` case.

**R1 · `induction t generalizing k`** changes the **goal list**: one goal per constructor of the
inductive type, with an induction hypothesis (IH) for each recursive field. `generalizing k` first
reverts `k`, so the IH reads `∀ (k : Nat), …`: it can be used at another `k`. Placeholders: the guide's
`Tree` (constructors `leaf (n : Nat)`, `node (l r : Tree)`), `(P : Tree → Nat → Prop) (t : Tree) (k : Nat)`.
Name the new variables with `case leaf n => …`, or write `induction t generalizing k with | leaf n => …
| node l r ihl ihr => …`.

| Before | After |
|---|---|
| `t : Tree, k : Nat ⊢ P t k` | `n✝ k : Nat ⊢ P (Tree.leaf n✝) k`, `l✝ r✝ : Tree ⊢ P (l✝.node r✝) k` |

The `node` goal also has `l_ih✝ : ∀ (k : Nat), P l✝ k` and `r_ih✝ : ∀ (k : Nat), P r✝ k`.

A generalized variable keeps its binder. In `forces_mono` the worlds are implicit (`{w w' : M.W}`), so
the IH reads `iha : ∀ {w w' : M.W}, M.le w w' → Forces M w a → Forces M w' a`: Lean fills the worlds
from the order fact, and you write `iha hle h.1`, not `iha w w' hle h.1`.

**R2 · `show G'`** changes the **goal** to a definitionally equal one: a definition by pattern matching,
applied to a constructor, becomes its defining clause. The guide's `Sem le p q .both n` is defined as
`p n ∧ q n`. Lean does this unfolding by itself: `exact`, `intro`, `h.1`, `h.elim` and applying `h`
all see through it. `show` only makes it visible. Placeholders: `(le : Nat → Nat → Prop) (p q : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ Sem le p q Tag.both n` | `⊢ p n ∧ q n` |

In the exercise, `Forces M w (Form.var n)` is `M.val n w`, `Forces M w Form.bot` is `False`, and the
`and`/`or` clauses are `∧`/`∨`, so `h.1`, `⟨_, _⟩`, `.inl` work on forced formulas directly.

**R3 · a structure field as a lemma, `G.symm h`**, **closes** the goal. A field that is a proof is a
function; `G.symm : ∀ {u v : G.V}, G.adj u v → G.adj v u`, and the implicit `u v` are read off `h`.
Placeholders: the guide's `Graph`, `(G : Graph) (u v : G.V) (h : G.adj u v)`. In the exercise:
`M.mono hle h`, `M.trans h1 h2`, `M.refl w`.

| Before | After |
|---|---|
| `h : G.adj u v ⊢ G.adj v u` | closed |

**R4 · `h.elim (fun a => …) (fun b => …)`** (`Or.elim : A ∨ B → (A → C) → (B → C) → C`) changes the
**goal list**: with `refine` and `?_` you get one goal per side of `h`. `.inl x : A ∨ B` from `x : A`;
`.inr y` from `y : B`. Placeholders: `(A B C D : Prop) (h : A ∨ B)`.

| Before | After |
|---|---|
| `h : A ∨ B ⊢ C ∨ D` | `a : A ⊢ C ∨ D`, `b : B ⊢ C ∨ D` |

**R5 · `intro m hm hp` on a definition that unfolds to `∀`** changes the **context**. `Sem le p q .later n`
is `∀ m, le n m → p m → q m`; `intro` unfolds it. In the exercise `Forces M w (a.imp b)` unfolds to
`∀ w', M.le w w' → Forces M w' a → Forces M w' b`, so `intro v hv ha` works on it.

| Before | After |
|---|---|
| `⊢ Sem le p q Tag.later n` | `m : Nat, hm : le n m, hp : p m ⊢ q m` |

---

## Part 2 · `forces_cons` (milestone)

Statement: if every formula of `Γ` and also `a` are forced at `w`, then every formula of `a :: Γ` is.
Used by Part 5 in the `orE` and `impI` cases (the rules that add a hypothesis to `Γ`).

**R6 · `intro x hx` on `∀ x ∈ l, Q x`** changes the **context**. `∀ x ∈ l, Q x` is `∀ x, x ∈ l → Q x`.
Placeholders: `{α : Type} (l : List α) (Q : α → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (x : α), x ∈ l → Q x` | `x : α, hx : x ∈ l ⊢ Q x` |

**R7 · `List.mem_cons`** changes the **context** (with `have`). The lemma is
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`; `.mp` is its left-to-right direction. Placeholders:
`{α : Type} (a b : α) (l : List α)`.

| Before | After `have h' := List.mem_cons.mp h` |
|---|---|
| `h : a ∈ b :: l ⊢ G` | `h' : a = b ∨ a ∈ l ⊢ G` |

**R8 · `rcases h with rfl | h`** changes the **goal list and context**: one goal per side of the `∨`.
The pattern `rfl` uses the equation `a = b` to replace `b` by `a` everywhere (so `hb : P b` becomes
`hb : P a`); `h` names the other side. `rcases h with h | h` splits without substituting.
Placeholders: `{α : Type} (a b : α) (l : List α) (P : α → Prop)`.

| Before | After |
|---|---|
| `h : a = b ∨ a ∈ l, hb : P b ⊢ P a` | `hb : P a ⊢ P a`, `h : a ∈ l ⊢ P a` |

Then `·` (TACTIC_STATES, "Structure") focuses each goal.

---

## Part 3 · `lem_countermodel` (milestone)

Statement: some model `M` and world `w` with `¬ (w ⊩ p₀ ∨ ¬p₀)`. Used by Part 6.

**R9 · `let G : Graph := { V := …, adj := …, symm := … }`** changes the **context**: it adds `G`
together with its value, so later goals can unfold `G.V`, `G.adj`. A field whose type starts with
implicit binders (`∀ {u v}, …`) is written without them: `symm := fun h => h.symm`. Placeholders: the
guide's `Graph`, `(P : Graph → Prop)`.

| Before | After |
|---|---|
| `⊢ ∃ G, P G` | `⊢ ∃ G, P G` and the context gains `G : Graph := { V := Bool, adj := fun a b => a = b, symm := ⋯ }` |

Then `refine ⟨G, ?_⟩` (TACTIC_STATES, "Structure") picks it as the witness.

**R10 · `rintro (h | h)` on `¬(A ∨ B)`** changes the **goal list**: `¬X` is `X → False`, so `rintro`
introduces the disjunction and splits it in one step. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ ¬(A ∨ B)` | `h : A ⊢ False`, `h : B ⊢ False` |

**R11 · `Bool.false_ne_true`** **closes** `False` from `h : false = true`. The lemma is
`Bool.false_ne_true : false ≠ true`, and `x ≠ y` is `x = y → False`.

| Before | After `exact Bool.false_ne_true h` |
|---|---|
| `h : false = true ⊢ False` | closed |

**R12 · apply a hypothesis that unfolds to `∀`: `h m hm hp`** **closes** the goal. `h : Sem le p q .later n`
is definitionally `∀ m, le n m → p m → q m`, so it is a function. In the exercise a forced `neg a` at
`w` is a function: given a later world, a proof that it is later, and a proof it forces `a`, it
returns `False`.

| Before | After `exact h m hm hp` |
|---|---|
| `h : Sem le p q Tag.later n, hm : le n m, hp : p m ⊢ q m` | closed |

**W3** (guide): `let G`, then `refine ⟨G, false, true, ?_⟩`, then R10:

```lean-goal
⊢ ¬(G.adj false true ∨ G.adj true false)
```

Each branch is closed by R11, because `h : G.adj false true` unfolds through the `let` value to
`false = true`.

---

## Part 4 · `nnlem`

Statement: `ND [] (neg (neg (a.or (neg a))))`: `¬¬(a ∨ ¬a)` is derivable from no hypotheses. Build the
derivation bottom up; each rule is a constructor of `ND`.

**R13 · `refine .dbl ?_`** changes the **goal**: a constructor of an inductive predicate is a rule, and
applying it to the goal (its conclusion) leaves its premises as goals. Placeholders: the guide's
`Gen` (rule `dbl : Gen S n → Gen S (2 * n)`), `(S : List Nat) (n : Nat)`. In term mode you write the
same tree directly: `.dbl (.seed …)`.

| Before | After |
|---|---|
| `⊢ Gen S (2 * n)` | `⊢ Gen S n` |

**R14 · `refine .push (m := 3) ?_ ?_`** changes the **goal list**: one goal per premise. The rule
`push : Gen (m :: S) n → Gen S m → Gen S n` has an implicit `m` that appears only in the premises, so
Lean cannot read it off the goal; `(m := 3)` gives it by name. The exercise's `impE` has the same shape:
its implicit `a` is the cut formula, `.impE (a := …) … …`.

| Before | After |
|---|---|
| `⊢ Gen S n` | `⊢ Gen (3 :: S) n`, `⊢ Gen S 3` |

**R15 · `by simp` proves list membership** such as `c ∈ [a, b, c]` (it uses `List.mem_cons` and
`List.mem_singleton`). Use it as the premise of a hypothesis rule: `.seed (by simp)`, `.hyp (by simp)`.
It only works once the element is known: with an unnamed implicit it sees `?m ∈ …` and fails.

**W1** (guide): `.push (m := 2 * 1) (.dbl (.seed (by simp))) (.dbl (.seed (by simp)))` proves
`Gen [1] (2 * 2)` in one term.

In the exercise, after the first `impI` the goal reads `ND [neg (a.or (neg a))] Form.bot`; after an
`impE` with cut formula `a.or (neg a)` whose first premise is the hypothesis, it reads
`ND [neg (a.or (neg a))] (a.or (neg a))`. If you work in tactic mode with `refine .impE (a := …) ?_ ?_`,
the first goal is printed with `neg` unfolded, `ND [neg (a.or (neg a))] ((a.or (neg a)).imp Form.bot)`;
`.hyp (by simp)` still closes it, since `neg` is an `abbrev`.

---

## Part 5 · `soundness`

Statement: from `h : ND Γ a` and `hΓ : ∀ g ∈ Γ, Forces M w g`, conclude `Forces M w a`. Induction on
the derivation `h`, generalizing `w`. Prove Parts 1 and 2 first.

**R16 · `induction h generalizing k` on a derivation `h : Gen S n`** changes the **goal list**: one goal
per rule. In each goal the indices `S n` are replaced by the rule's conclusion, there is one hypothesis
per premise, and one IH per premise that is itself a derivation. With
`induction h generalizing k with | seed hn => … | push h1 h2 ih1 ih2 => …`, the names go to the explicit
premises and then the IHs, in order; implicit fields (`{S} {n} {m}`) stay unnamed (`_` in terms, or
`| @seed S n hn => …`). Placeholders: `(P : List Nat → Nat → Nat → Prop) (S : List Nat) (n k : Nat)`.

| Before | After |
|---|---|
| `h : Gen S n, k : Nat ⊢ P S n k` | `a✝ : n✝ ∈ S✝ ⊢ P S✝ n✝ k`, `a✝ : Gen S✝ n✝ ⊢ P S✝ (2 * n✝) k`, `a✝¹ : Gen (m✝ :: S✝) n✝, a✝ : Gen S✝ m✝ ⊢ P S✝ n✝ k` |

The `dbl` goal also has `a_ih✝ : ∀ (k : Nat), P S✝ n✝ k`; the `push` goal has `a_ih✝¹` and `a_ih✝` for
its two premises. In the exercise the IH reads
`ih : ∀ (w : M.W), (∀ (g : Form), g ∈ Γ✝ → Forces M w g) → Forces M w …`: use it at any world, after
proving the hypotheses there.

**R17 · `h.elim`** (`False.elim : False → C`) **closes** any goal from `h : False`, also when `h`'s type
only unfolds to `False` (`Sem le p q .none n`, or the exercise's `Forces M w Form.bot`).

| Before | After `exact h.elim` |
|---|---|
| `h : Sem le p q Tag.none n ⊢ G` | closed |

**W2** (guide) is the whole pattern on `Gen`: induction on the derivation, and in the `push` case
the property of the longer seed list `m :: S` comes from R6, R7, R8.

---

## Part 6 · `lem_not_derivable`

Statement: `¬ ND [] ((Form.var 0).or (neg (Form.var 0)))`. Assume a derivation, apply soundness in the
countermodel, contradiction.

**R18 · `obtain ⟨x, y, hxy⟩ := h`** changes the **context**: `h : ∃ x y, R x y` is replaced by a
witness and its property. Placeholders: `{α : Type} (R : α → α → Prop)`.

| Before | After |
|---|---|
| `⊢ G`, with `h : ∃ x y, R x y` in the context | `x y : α, hxy : R x y ⊢ G` (and `h` is gone) |

**R19 · `by simp` proves `∀ x ∈ [], Q x`** (`List.not_mem_nil`: nothing is in `[]`). Use it for the
hypothesis argument of `soundness` when `Γ = []`.

---

## Traps

- `neg a` is `a.imp Form.bot`, so forcing `neg a` at `w` is "no later world forces `a`", not "`w`
  does not force `a`". `Forces` unfolds by itself (R2): `intro w' hle ha` works on a forced `.imp` goal
  (R5), and a forced `.imp` hypothesis can be applied as a function (R12).
- `impE` has an implicit cut formula. Write `.impE (a := …) … …` (R14); otherwise each `.hyp (by simp)`
  meets a metavariable and `simp` fails (R15).
- `soundness`: induct with `generalizing w`. In `impI` the IH is needed at a later world `v`, not at `w`.
- `induction … with` alternatives name explicit premises and IHs only (R16); `| orE _ _ _ ih ih1 ih2`
  has three premises then three IHs.
- In `impI`, `hΓ` is about `w`; the IH at `v` needs every hypothesis at `v`: move each one with
  `forces_mono` and the order fact `hv : M.le w v`, then add `ha` with `forces_cons`.
- Build the model with `let`, not `have`: `have M : Kripke := …` forgets the value, and then
  `Forces M false (Form.var 0)` no longer unfolds to `false = true`.
- Kripke fields with implicit binders (`trans`, `mono`) are given as `fun h1 h2 => …`, without
  the implicit worlds (R9).
- `forces_mono`: the IH's worlds are implicit (R1); pass only the order fact and the forced formula.
- `lem_countermodel`: write the lower world in `refine ⟨M, …, ?_⟩`; a `_` there is not inferred and
  Lean reports "don't know how to synthesize placeholder".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction on a formula, IH for every world | `induction a generalizing w w' with \| var n => … \| imp a b iha ihb => …` | R1 |
| see what a forced formula means | `show …` (or just use it) | R2 |
| model axioms | `M.mono hle h`, `M.trans h1 h2`, `M.refl w` | R3 |
| use / build `∨` | `h.elim (fun a => …) (fun b => …)`, `.inl x`, `.inr y` | R4 |
| prove a forced `→` | `intro v hv ha` | R5 |
| prove `∀ g ∈ a :: Γ, …` | `intro g hg` | R6 |
| `g ∈ a :: Γ → g = a ∨ g ∈ Γ` | `List.mem_cons.mp hg` | R7 |
| split, substituting the equation | `rcases … with rfl \| hg` | R8 |
| a concrete model | `let M : Kripke := { W := …, le := …, … }` | R9 |
| prove `¬(A ∨ B)` | `rintro (h \| h)` | R10 |
| `false = true` is absurd | `Bool.false_ne_true h` | R11 |
| use a forced `→` | `h v hv ha` | R12 |
| apply a rule | `refine .impI ?_` / term `.impI …` | R13 |
| fix the cut formula | `.impE (a := φ) … …` | R14 |
| hypothesis rule | `.hyp (by simp)` | R15 |
| induction on a derivation | `induction h generalizing w with \| hyp hm => … \| …` | R16 |
| from `False` (or forced `⊥`) | `h.elim` | R17 |
| unpack `∃ M w, …` | `obtain ⟨M, w, hw⟩ := …` | R18 |
| hypotheses of `[]` | `(by simp)` | R19 |
| see the state | infoview | |
