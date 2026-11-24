# H007 · Integers as a quotient of Nat × Nat: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def`, `theorem`, `intro`, `exact`, `rw`, `rfl`, `∃`,
`∧`, pairs. **New here** (all core Lean, no Mathlib): equivalence relations (`Equivalence`), setoids
(`Setoid`, notation `≈`), quotient types (`Quotient`, `Quotient.mk`, `Quotient.lift`, `Quotient.lift₂`,
`Quotient.sound`, `Quotient.exact`, `Quotient.inductionOn`), the `Nat → Int` cast `↑`, `Int.toNat`, and
the tactics `unfold`, `show`, `obtain`, `omega`, `grind`.

The math. Write $p = (a, b) \in \mathbb{N}^2$ for "the integer $a - b$". Two pairs name the same
integer iff $a + d = c + b$ (no subtraction needed, so it makes sense in $\mathbb{N}$). That relation
$\sim$ is an equivalence; the quotient $\mathbb{N}^2/\!\sim$ is a copy of $\mathbb{Z}$. A function
$F$ on the quotient is defined by a function $f$ on pairs that gives equal results on related pairs
(*well-definedness*); then $F([p]) = f(p)$ holds by definition, where $[p]$ is the class of $p$.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `{s : Setoid α}` is any
  equivalence relation on `α` packaged as a setoid (in the exercise: `α := Nat × Nat`, `s := intSetoid`).
- "Definitionally equal" means equal after unfolding definitions; Lean accepts one for the other in
  `show`, `intro (h : T)`, `exact` and `rfl`. `rw`, `omega` and `grind` do **not** unfold a definition
  such as `≈` or `R`: to them `(a, b) ≈ (c, d)` is an opaque fact. (They do reduce a projection of an
  explicit pair, `(a, b).fst` to `a`.)
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Nat × Nat`, `(a, b)` | pairs of naturals; `(a, b)` stands for the integer `a − b` |
| `x.fst`, `x.snd` | `x.1`, `x.2`: the components of the pair `x` (Lean prints `.1` as `.fst`) |
| `(a, b).fst` | the first component of `(a, b)`; reduces to `a` (`omega`, `grind`, `rw` see this; `show` tidies it, R13) |
| `Equivalence r` | `r` is reflexive, symmetric and transitive (a structure with fields `refl`, `symm`, `trans`) |
| `Setoid α` | a type `α` together with an equivalence relation on it; `⟨r, proof⟩` builds one |
| `a ≈ b` | `a` and `b` are related by the setoid in use; by definition it is `r a b` (for `intSetoid`: `R a b`) |
| `Quotient s` | the type of equivalence classes of `s`; `MyInt` is `Quotient intSetoid` |
| `Quotient.mk s a` | the class of `a`; `MyInt.mk a b` is `Quotient.mk intSetoid (a, b)` |
| `mk a b` | `MyInt.mk a b`, printed short inside a `MyInt.…` definition |
| `Quotient.lift f h` | the function on classes induced by `f`, given `h : f` respects `≈` |
| `∀ {x y : α}, …` | implicit binders: callers do not pass `x y`; inside a proof `intro x y` names them |
| `↑a` | the natural `a` cast to `Int` (`(a : Int)`); `↑b - ↑a` is integer subtraction; `↑(a, b).fst` is `↑((a, b).fst)` |
| `x.add y`, `x.neg`, `x.toInt` | dot notation: `MyInt.add x y`, `MyInt.neg x`, `MyInt.toInt x` (because `x : MyInt`) |
| `n.toNat` | `Int.toNat n`: `n` as a natural if `0 ≤ n`, else `0` |
| `case refine_1`, `case mp`, `case h` | labels of the goals produced by `refine`, `constructor` (on `↔`), `induction` |

---

## Part 1 · `R_equiv`

Statement: the relation `R x y := x.1 + y.2 = y.1 + x.2` is an equivalence. In words:
$a + b = a + b$; $a + d = c + b \Rightarrow c + b = a + d$; and
$a + d = c + b,\ c + f = e + d \Rightarrow a + f = e + b$ (add and cancel $c + d$).

**R1 · `refine ⟨?_, ?_, ?_⟩`** changes the **goal list**: `Equivalence r` becomes its three fields.
Placeholders: `{α : Type} (r : α → α → Prop)`. Note the curly braces in symm and trans: they are
implicit binders, but `intro` still names them (R2).

| Before | After |
|---|---|
| `⊢ Equivalence r` | `⊢ ∀ (x : α), r x x`, `⊢ ∀ {x y : α}, r x y → r y x`, `⊢ ∀ {x y z : α}, r x y → r y z → r x z` |

**R2 · `intro x y h`** changes the **context**: it names the bound variables (implicit or not) and the
premise. Placeholders: `{α : Type} (r : α → α → Prop) (Q : Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ {x y : α}, r x y → Q` | `x y : α, h : r x y ⊢ Q` |

**R3 · `unfold D at *`** changes the **goal and the context**: every occurrence of the defined name `D`
is replaced by its body, in the goal and all hypotheses (`at h` for one hypothesis, `at h ⊢` for `h`
and the goal). Placeholders: `def Par (m n : Nat) : Prop := m % 2 = n % 2`, `(m n : Nat)`.

| Before | After |
|---|---|
| `h : Par m n ⊢ Par n m` | `h : m % 2 = n % 2 ⊢ n % 2 = m % 2` |

**R4 · `omega`** **closes** a goal of linear arithmetic over `Nat` or `Int` (`+`, `-`, numerals,
multiplication and `%` by a numeral), using the hypotheses in context. A product of two variables
is an opaque atom to it (use `grind`, R8), and it does not unfold definitions or `≈` (unfold or
`show` first, R3, R13). Placeholders: `(a b c d : Nat)`.

| Before | After |
|---|---|
| `h1 : a + b = c, h2 : c + d = a + 5 ⊢ b + d = 5` | no goals |

**R5 · `exact h.symm`** **closes** `b = a` from `h : a = b` (`Eq.symm`). It also works on
`h : D x y` when the body of `D` is an equation, as `R` is. Placeholders: `(m n : Nat)`.

| Before | After |
|---|---|
| `h : Par m n ⊢ Par n m` | no goals |

The refl field needs only `rfl`: `R x x` is by definition `x.1 + x.2 = x.1 + x.2`.

---

## Part 2 · `exists_mk` (milestone)

Statement: every `x : MyInt` is `MyInt.mk a b` for some naturals `a b`. Prove it first: it lets every
later theorem about an arbitrary `x : MyInt` work with an explicit pair (R19).

**R6 · `induction x using Quotient.inductionOn with | h a => …`** changes the **context and the goal**:
`x : Quotient s` is replaced by a representative `a : α`, and `x` in the goal by its class
`Quotient.mk s a`. The principle: a property holding on every class `Quotient.mk s a` holds on all of
`Quotient s`. Placeholders: `{α : Type} {s : Setoid α} (P : Quotient s → Prop)`.

| Before | After |
|---|---|
| `x : Quotient s ⊢ P x` | `a : α ⊢ P (Quotient.mk s a)` |

**R7 · `exact ⟨a, b, rfl⟩`** **closes** `∃ a b, G a b`: name both witnesses, then prove `G`. A pair
`p` is by definition `(p.1, p.2)`, so `rfl` proves `p = (p.1, p.2)`. In the exercise the goal after
R6 is `∃ a b, Quotient.mk intSetoid p = MyInt.mk a b`, and `MyInt.mk a b` unfolds to
`Quotient.mk intSetoid (a, b)`. Placeholders: `{α β : Type} (p : α × β)`.

| Before | After |
|---|---|
| `⊢ ∃ a b, p = (a, b)` | no goals |

---

## Part 3 · `mul_wd` (milestone)

Statement: if $a - b = a' - b'$ and $c - d = c' - d'$ (stated without subtraction), then
$(a-b)(c-d) = (a'-b')(c'-d')$, expanded into naturals. This is exactly the well-definedness
obligation of `MyInt.mul` (Part 6), separated out so it is a plain `Nat` fact.

**R8 · `grind`** **closes** goals that need products of variables: it normalises both sides as
polynomials and combines that with linear arithmetic over the hypotheses, where `omega` gives up.
Placeholders: `(a b a' b' c : Nat)`.

| Before | After |
|---|---|
| `h : a + b' = a' + b ⊢ a * c + b' * c = a' * c + b * c` | no goals |

---

## Part 4 · `MyInt.add`

Statement: `add : MyInt → MyInt → MyInt`, pinned down by `add_mk`:
`[(a, b)] + [(c, d)] = [(a + c, b + d)]`. Write the body as `Quotient.lift₂ f (by …)`, where `f` is
the function on pairs and `by …` proves it respects `≈`. Inside `by …` the goal is R9's "After" state
with `α = β = Nat × Nat` and your `f` already applied (β-reduced: `f a₁ b₁` shows as `mk (a₁.fst + …) …`,
`mk` being `MyInt.mk`). After R10, R11 and R12 the goal is a `≈` between two explicit pairs whose
components are sums of `(a, b).fst`-style projections; R13 restates it as the Nat equation that `R`
gives (`x.1 + y.2 = y.1 + x.2` with `x`, `y` those two pairs).

**R9 · `Quotient.lift₂ f ?_`** changes the **goal**: a function of two classes becomes the proof that
`f` respects `≈` in both arguments. Argument order: the representatives `a₁ b₁` of the two inputs,
then the representatives `a₂ b₂` related to them (`a₁ ≈ a₂`, `b₁ ≈ b₂`). Placeholders:
`{α β γ : Type} {s₁ : Setoid α} {s₂ : Setoid β} (f : α → β → γ)`.

| Before | After |
|---|---|
| `⊢ Quotient s₁ → Quotient s₂ → γ` | `⊢ ∀ (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂` |

In a `def`, write `Quotient.lift₂ f (by …)`: the `by` block starts in the "After" state.

**R10 · `intro ⟨a, b⟩`** changes the **context**: a pair is introduced already split into components.
Placeholders: `{α β : Type} (P : α × β → Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (p : α × β), P p` | `a : α, b : β ⊢ P (a, b)` |

**R11 · `intro (h : T)`** changes the **context**: the premise is named `h` and stated as `T`, which
must be definitionally its type. Use it to turn `(a, b) ≈ (a', b')` into the Nat equation
`a + b' = a' + b`, which `omega` can read. Placeholders: the setoid `parSetoid` on `Nat`, whose
`m ≈ n` is `m % 2 = n % 2`; `(Q : Prop)`.

| Before | After |
|---|---|
| `⊢ ∀ (m n : Nat), m ≈ n → Q` | `m n : Nat, h : m % 2 = n % 2 ⊢ Q` |

**R12 · `apply Quotient.sound`** changes the **goal**. The lemma is
`Quotient.sound : a ≈ b → Quotient.mk s a = Quotient.mk s b`: to show two classes are equal, show the
representatives are related. `apply` sees through `MyInt.mk`. Placeholders:
`{α : Type} {s : Setoid α} (a b : α)`.

| Before | After |
|---|---|
| `h : a ≈ b ⊢ Quotient.mk s a = Quotient.mk s b` | `h : a ≈ b ⊢ a ≈ b` |

**R13 · `show T`** changes the **goal** to a definitionally equal `T`. It removes `≈` (which `omega`
cannot read) and can tidy `(a, b).fst` to `a` at the same time. Placeholders: `parSetoid`, `(m n : Nat)`; and
`{α β : Type} (a : α) (b : β) (P : α → β → Prop)`.

| Before | After |
|---|---|
| `⊢ m ≈ n` | `⊢ m % 2 = n % 2` |
| `⊢ P (a, b).fst (a, b).snd` | `⊢ P a b` |

**W1** in `guide.lean` (`Bit.add`, addition of parity classes) chains R9 → R10, R11 → R12 → R13 → R4
exactly as `MyInt.add` needs.

---

## Part 5 · `MyInt.neg`

Statement: `neg : MyInt → MyInt`, pinned down by `neg_mk`: `−[(a, b)] = [(b, a)]`. One argument, so
`Quotient.lift`.

**R14 · `Quotient.lift f ?_`** changes the **goal**: a function of one class becomes the proof that `f`
respects `≈`. Placeholders: `{α β : Type} {s : Setoid α} (f : α → β)`.

| Before | After |
|---|---|
| `⊢ Quotient s → β` | `⊢ ∀ (a b : α), a ≈ b → f a = f b` |

Then R10, R11, R12, R13, R4 as in Part 4.

---

## Part 6 · `MyInt.mul`

Statement: `mul`, pinned down by `mul_mk`: `[(a, b)]·[(c, d)] = [(ac + bd, ad + bc)]`, i.e.
$(a-b)(c-d) = (ac+bd) - (ad+bc)$. R9, then R10 for the four pairs. The obligation is the milestone
`mul_wd` (Part 3): `Quotient.sound (mul_wd …)` is the term form of R12. The hypotheses
`h1 : (a, b) ≈ (a', b')` can be passed to `mul_wd` as they are: an argument only has to match up to
definitional equality.

---

## Part 7 · `MyInt.toInt`

Statement: `toInt : MyInt → Int`, pinned down by `toInt_mk`: `toInt [(a, b)] = ↑a − ↑b` (in `Int`,
where subtraction does not truncate). R14, then R10, R11. No `≈` is left in the goal (both sides are
`Int`s), so `omega` closes it directly; R13 to clear `(a, b).fst` first is optional:

**R15 · `omega` over `Int` with casts** **closes** linear goals mixing `Nat` and `Int`: it knows that
`↑a ≥ 0` and how `↑` interacts with `+`. Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `h : a + 2 = b ⊢ ↑b - ↑a = 2` | no goals |

---

## Part 8 · `add_mk`

Statement: `(MyInt.mk a b).add (MyInt.mk c d) = MyInt.mk (a + c) (b + d)`.

**R16 · `rfl`** **closes** the computation rule `Quotient.lift f h (Quotient.mk s a) = f a`: lifting
then applying to a class is, by definition, applying `f` to the representative. Same for
`Quotient.lift₂` on two classes. So `add_mk` is `rfl` exactly when your `add` lifts the intended `f`.
Placeholders: `{α β : Type} {s : Setoid α} (f : α → β) (a : α)`.

| Before | After |
|---|---|
| `⊢ Quotient.lift f h (Quotient.mk s a) = f a` | no goals |

**W2** shows the same for `Bit.add`.

## Part 9 · `neg_mk`

Statement: `(MyInt.mk a b).neg = MyInt.mk b a`. R16.

## Part 10 · `mul_mk`

Statement: `(MyInt.mk a b).mul (MyInt.mk c d) = MyInt.mk (a * c + b * d) (a * d + b * c)`. R16.

## Part 11 · `toInt_mk`

Statement: `(MyInt.mk a b).toInt = (a : Int) - (b : Int)`. R16.

---

## Part 12 · `mk_eq_mk`

Statement: `MyInt.mk a b = MyInt.mk c d ↔ a + d = c + b`: equal classes iff related pairs. It turns
every equation between `MyInt`s into a Nat equation.

**R17 · `constructor`** on `↔` changes the **goal list**: two implications. Term form:
`⟨proof of →, proof of ←⟩`. Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R18 · `Quotient.exact`** changes the **context** (after `intro h` on the `→` goal). The lemma is
`Quotient.exact : Quotient.mk s a = Quotient.mk s b → a ≈ b`, the converse of R12. Here
`(a, b) ≈ (c, d)` is by definition `a + d = c + b`, so the result closes the `→` direction as it is.
Placeholders: `{α : Type} {s : Setoid α} (a b : α)`.

| Before | After `have h' := Quotient.exact h` |
|---|---|
| `h : Quotient.mk s a = Quotient.mk s b ⊢ a ≈ b` | `h' : a ≈ b ⊢ a ≈ b` |

The `←` direction is R12. **W4** combines R18 with a restatement on parity classes.

---

## Part 13 · `add_neg`

Statement: `x + (−x) = [(0, 0)]` for every `x : MyInt`.

**R19 · `obtain ⟨a, b, rfl⟩ := e`** with `e : ∃ a b, x = f a b` changes the **context**: `a b` are
added, and the pattern `rfl` substitutes `x := f a b` everywhere, so `x` disappears. With
`e := exists_mk x` this replaces an arbitrary `x : MyInt` by `MyInt.mk a b`. Placeholders:
`{α β : Type} (f : α → α → β) (x : β) (P : β → Prop)`.

| Before (with `e` in context) | After |
|---|---|
| `x : β ⊢ P x` | `a b : α ⊢ P (f a b)` |

Then `rw [neg_mk, add_mk]` (generic `rw`, TACTIC_STATES) computes, and:

**R20 · `rw [e]` with an `↔` lemma** changes the **goal**: `rw` rewrites propositions too, replacing
`Q a b` by `S a b` when `e : ∀ x y, Q x y ↔ S x y`. With `e := mk_eq_mk` it turns
`MyInt.mk _ _ = MyInt.mk _ _` into a Nat equation. Placeholders:
`{α : Type} (Q S : α → α → Prop) (a b : α)`.

| Before | After |
|---|---|
| `h : S a b ⊢ Q a b` | `h : S a b ⊢ S a b` |

Finish with `omega` (R4).

**W3** does Part 13 for parity classes, with R6 instead of a milestone: the goal after `induction`
still shows `Bit.add` applied to two classes; `apply Quotient.sound` computes it by definition:

```lean-goal
⊢ Bit.add (Quotient.mk parSetoid m) (Quotient.mk parSetoid m) = Bit.mk 0
⊢ m + m ≈ 0
⊢ (m + m) % 2 = 0 % 2
```

---

## Part 14 · `mul_add`

Statement: `x·(y + z) = x·y + x·z`. R19 three times, then `rw` with `add_mk` (the inner sum: `rw`
rewrites the first match it finds, and the outer `.add` does not match yet), the three `mul_mk`, the
outer `add_mk`, and `mk_eq_mk` (R20). The resulting Nat identity has products: `grind` (R8).

---

## Part 15 · `toInt_injective`

Statement: `x.toInt = y.toInt → x = y`. R19 twice; then compute inside the hypothesis:

**R21 · `rw [e] at h`** changes the **context**: the rewrite is applied to hypothesis `h`, not the
goal. Placeholders: `{α : Type} (f : α → α) (a b : α) (P : α → Prop)`, `e : f a = b`.

| Before | After |
|---|---|
| `h : P (f a) ⊢ P b` | `h : P b ⊢ P b` |

Then R20 (`mk_eq_mk`) on the goal. `h` is an `Int` equation with casts and the goal a `Nat` one;
`omega` (R15) relates them.

---

## Part 16 · `toInt_surjective`

Statement: every `n : Int` is `toInt` of some class. Give the witness with `refine ⟨MyInt.mk p q, ?_⟩`
(TACTIC_STATES), where naturals `p q` satisfy `↑p − ↑q = n`. Then `rw [toInt_mk]` and:

**R22 · `Int.toNat` with `omega`** **closes** goals about `n.toNat`; `omega` knows
`↑n.toNat = n` when `0 ≤ n` and `0` otherwise. (The library lemma
`Int.toNat_sub_toNat_neg : ↑n.toNat - ↑(-n).toNat = n` states the decomposition you need; `omega`
proves it too.) Placeholders: `(n : Int)`.

| Before | After |
|---|---|
| `h : 0 ≤ n ⊢ ↑n.toNat = n` | no goals |

---

## Part 17 · `toInt_mul`

Statement: `(x·y).toInt = x.toInt · y.toInt`. R19 twice, `rw` with `mul_mk` and then `toInt_mk` three
times. The goal is an `Int` identity with casts of Nat products:

**R23 · `grind` over `Int` with casts** **closes** it: it pushes `↑` through `+` and `*` itself
(`↑(a * b) = ↑a * ↑b`), then normalises the polynomials. Placeholders: `(a b c : Nat)`.

| Before | After |
|---|---|
| `⊢ ↑(a * b + c) - ↑c = ↑a * ↑b` | no goals |

---

## Traps

- The four `_mk` theorems pin down your definitions: with the intended ones they are `rfl` (R16). If
  `rfl` fails, the function you lifted is not the one the theorem states (e.g. arguments swapped).
- `Quotient.lift₂`'s obligation takes `a₁ b₁ a₂ b₂` (both inputs, then both related inputs), not
  `a₁ a₂ b₁ b₂`. Match your `intro` order: `intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2` gives
  `h1 : (a, b) ≈ (a', b')`, `h2 : (c, d) ≈ (c', d')`.
- `omega` and `grind` do not see through `≈`: a hypothesis `h1 : (a, b) ≈ (a', b')` or a goal
  `… ≈ …` is an opaque fact to them. Restate with R11 and R13. (`(a, b).fst` is harmless: they reduce it.)
- `Nat` subtraction truncates (`2 - 5 = 0`), which is why `R` uses `a + d = c + b` and `toInt` casts to
  `Int` before subtracting: write `(x.1 : Int) - x.2`, not `((x.1 - x.2 : Nat) : Int)`.
- `rw [lemma]` rewrites the first instance of the pattern (and its copies). In `mul_add` do the inner
  `add_mk` first; if `rw` fails with "did not find instance", look at what is still not computed.
- `obtain ⟨a, b, rfl⟩` substitutes only when one side of the equation is a local variable (here `x`);
  on `x.add y = …` it fails. That is why `exists_mk` is stated as `x = MyInt.mk a b`.
- A pattern `intro ⟨a, b⟩` splits only a pair; on a class `x : MyInt` use R6 or R19 instead.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `Equivalence r` | `refine ⟨?_, ?_, ?_⟩` or `⟨fun x => …, fun h => …, fun h1 h2 => …⟩` | R1 |
| name binders, implicit too | `intro x y h` | R2 |
| expand a definition | `unfold R at *` | R3 |
| linear Nat/Int arithmetic | `omega` | R4, R15, R22 |
| flip an equation | `h.symm` | R5 |
| `x : Quotient s` → representative | `induction x using Quotient.inductionOn with \| h p => …` | R6 |
| `∃ a b, …` with a pair | `⟨p.1, p.2, rfl⟩` | R7 |
| products of variables | `grind` | R8, R23 |
| define a function on classes | `Quotient.lift f (by …)` / `Quotient.lift₂ f (by …)` | R14, R9 |
| split a pair | `intro ⟨a, b⟩` | R10 |
| state `≈` as its definition | `intro (h : a + d = c + b)` / `show a + d = c + b` | R11, R13 |
| equal classes ← related | `apply Quotient.sound` | R12 |
| related ← equal classes | `Quotient.exact h` | R18 |
| `lift f h (mk a) = f a` | `rfl` | R16 |
| split `↔` | `constructor` or `⟨…, …⟩` | R17 |
| arbitrary `x : MyInt` → `MyInt.mk a b` | `obtain ⟨a, b, rfl⟩ := exists_mk x` | R19 |
| `MyInt` equation → Nat equation | `rw [mk_eq_mk]` | R20 |
| rewrite a hypothesis | `rw [e] at h` | R21 |
| see the state | infoview | |
