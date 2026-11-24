# H022 · Regex matcher: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `constructor` on `∧`/`↔`, `obtain`,
`rintro`, `rcases`, `cases` on a `List`/`Bool`, `induction` on `Nat`/`List`, `simp`, `split`, implicit and
named arguments, constructor injectivity. **New here:** inductive *predicates* (a `Prop`-valued
inductive family whose constructors are inference rules), inverting a derivation with `cases`, rule
induction, `generalize` for non-variable indices, and the core list lemmas about `++`. No Mathlib.

The guide works on a toy pattern language `Sh` (`atom n` produces `[n, n]`, `two a b` concatenates,
`many a` repeats) with the relation `Gen : Sh → List Nat → Prop`. It is built like the exercise's `Re`
and `Matches` so that every move transfers, but it is not the exercise.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`, or `P : Prop → Prop` when the changing part is itself a
  proposition). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type.
- `∅` means no goal is left. A cell with several states lists the goals the step leaves, in order.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Matches r w` | the derivation relation: regex `r` matches word `w` (a `Prop`, proved by building a derivation from the rules `eps`, `chr`, `altL`, …) |
| `.cat r s`, `.eps`, `.altL h` (in the spec and in your proofs) | `Re.cat r s`, `Re.eps`, `Matches.altL h`: a leading `.` takes the namespace from the expected type |
| `r.cat s`, `r.alt s`, `r.star` | `Re.cat r s`, `Re.alt r s`, `Re.star r`: Lean prints a constructor applied to its first argument with dot notation |
| `Re.empty`, `Re.eps`, `Re.chr d` | constructors with no `Re` argument print with the type name |
| `c :: w`, `[c]`, `u ++ v` | cons, the one-letter word, concatenation (`List Char`) |
| `c :: u ++ v` | `(c :: u) ++ v`: `::` binds tighter than `++` |
| `nullable r = true` | the `Bool` `nullable r` used as a `Prop`; `if nullable r then …` prints as `if nullable r = true then …` |
| `(a \|\| b)`, `(a && b)` | Boolean or / and on `Bool` |
| `u✝`, `a✝¹`, `h✝` | inaccessible names: Lean made these up; name them with `rename_i` (R2) or in a `with \| tag x y =>` pattern |
| `a_ih✝`, `ihv` | an induction hypothesis (IH) |
| `∀ {w : List Char}, r.star = r'.star → c :: w = v → …` | an IH whose premises are the generalized equations (R13, R14); feed them `rfl` and your hypothesis |
| `case starCons.refl.nil` | goal tag: rule `starCons`, after `cases` on an equation (`refl`), list case `nil` |
| `case cat.mp.isTrue`, `case cat.mpr.inl` | constructor `cat`; `mp` = the `→` half of `constructor` on `↔`, `mpr` = the `←` half; `isTrue`/`isFalse` = the two `split` branches; `inl`/`inr` = the two `rcases` alternatives |

---

## Part 1 · `cat_inv`

Statement: from `h : Matches (.cat r s) w`, get `u v` with `w = u ++ v`, `Matches r u`, `Matches s v`.
The only rule concluding `Matches (.cat _ _) _` is `cat`, so inverting `h` gives exactly its premises.

**R1 · `cases h`** changes the **context and the goal**: `h` is replaced by the premises of the one rule
whose conclusion fits, and the index `w` (a variable) is replaced by that rule's word `u✝ ++ v✝`.
`cases` must solve "rule's conclusion = `h`'s type" by substituting variables. That works here because
`w` is a variable, and also for `h : Matches (.alt r s) (c :: w)` because the `altL`/`altR` word is a
variable. It fails for `h : Matches (.cat r s) (c :: w)`: `c :: w = u ++ v` cannot be solved (Traps).
Placeholders: `(a b : Sh) (w : List Nat)`. Writing `cases h with | two hu hv => …` names the premises at
once (the exercise's rule is `cat`).

| Before | After |
|---|---|
| `h : Gen (a.two b) w ⊢ P w` | `a✝¹ : Gen a u✝, a✝ : Gen b v✝ ⊢ P (u✝ ++ v✝)` |

**R2 · `rename_i u v hu hv`** changes the **context**: it names the most recent inaccessible hypotheses,
oldest first.

| Before | After |
|---|---|
| `a✝¹ : Gen a u✝, a✝ : Gen b v✝ ⊢ P (u✝ ++ v✝)` | `hu : Gen a u, hv : Gen b v ⊢ P (u ++ v)` |

**R3 · `exact ⟨_, _, rfl, hu, hv⟩`** **closes** an `∃ x y, e = x ++ y ∧ A x ∧ B y` goal. The anonymous
constructor nests to the right, `rfl` proves `e = ?x ++ ?y` and in doing so fills the two `_`.
Placeholders: `(u v : List Nat) (hu : Gen a u) (hv : Gen b v)`.

| Before | After |
|---|---|
| `hu : Gen a u, hv : Gen b v ⊢ ∃ x y, u ++ v = x ++ y ∧ Gen a x ∧ Gen b y` | ∅ |

---

## Part 2 · `nullable_iff`

Statement: `nullable r = true ↔ Matches r []`, for every regex `r`. Induction on `r`; each case unfolds
`nullable` and compares with the rules.

**R4 · `induction t with | c₁ … => … | …`** changes the **goal list**: one goal per constructor of the
inductive *type*, with an IH for each argument of that type. Placeholders: `(P : Sh → Prop) (t : Sh)`.
In the exercise write `induction r with | empty => … | eps => … | chr c => … | alt r s ihr ihs => … | …`.

| Before | After |
|---|---|
| `t : Sh ⊢ P t` | `n✝ : Nat ⊢ P (Sh.atom n✝)`, `a_ih✝ : P a✝, b_ih✝ : P b✝ ⊢ P (a✝.two b✝)`, `a_ih✝ : P a✝ ⊢ P a✝.many` |

**R5 · `simp [f]`** changes the **goal**: it unfolds `f` at a constructor using `f`'s defining equations,
then simplifies. `false = true ↔ Q` becomes `¬Q`, and `true = true ↔ Q` becomes `Q`. Placeholders:
`(Q : Prop)`, `f := hasMany`. For `Re.empty` and `Re.chr c` you then get `¬Matches … []`: finish with
`intro h; cases h` (R6). For `eps` and `star` you get the bare `Matches … []`: give a rule.

| Before | After |
|---|---|
| `⊢ hasMany (Sh.atom n) = true ↔ Q` | `⊢ ¬Q` |
| `⊢ hasMany a.many = true ↔ Q` | `⊢ Q` |

**R6 · `cases h`, no rule fits** **closes** the goal: every rule's conclusion clashes with the indices of
`h` (here `[n, n]` vs `[]`), so there is nothing to prove.

| Before | After |
|---|---|
| `h : Gen (Sh.atom n) [] ⊢ P` | ∅ |

**R7 · `simp only [Bool.or_eq_true]`** changes the **goal**. The lemma is
`Bool.or_eq_true : ((a || b) = true) = (a = true ∨ b = true)`: a Boolean `||` becomes a logical `∨`.
Placeholders: `(a b : Bool) (P : Prop → Prop)`.

```lean-goal
⊢ P ((a || b) = true)
⊢ P (a = true ∨ b = true)
```

**R8 · `simp only [Bool.and_eq_true]`** changes the **goal**. The lemma is
`Bool.and_eq_true : ((a && b) = true) = (a = true ∧ b = true)`. Placeholders: `(a b : Bool)`.

| Before | After |
|---|---|
| `⊢ P ((a && b) = true)` | `⊢ P (a = true ∧ b = true)` |

**R9 · `simp only [ih]`** changes the **goal**: with `ih : ∀ x, f x = true ↔ Q x`, every `f e = true` is
rewritten to `Q e` (simp rewrites with `↔` like with `=`, and picks the instance `x := e` itself).
Placeholders: `{α : Type} (f : α → Bool) (Q : α → Prop) (e : α)`. In the exercise, R7/R8 with the two
IHs turn `nullable (r.alt s) = true ↔ …` into `Matches r [] ∨ Matches s [] ↔ Matches (r.alt s) []`.

| Before | After |
|---|---|
| `⊢ P (f e = true)` | `⊢ P (Q e)` |

**R10 · `exact .two (u := x) (v := y) h₁ h₂`** **closes** the goal with a rule. `.two` is read as
`Gen.two` from the goal's type. `(u := x)` sets the implicit argument `u`: the rule concludes
`Gen (.two a b) (u ++ v)`, and the goal's word must equal `x ++ y` by computation (`[] ++ []` is `[]`,
`(x :: u) ++ v` is `x :: (u ++ v)`). Lean can often infer `u`, but naming it makes the intent explicit.
Placeholders: `(h₁ : Gen a …) (h₂ : Gen b …)`.

| Before | After |
|---|---|
| `h₁ : Gen a [], h₂ : Gen b [] ⊢ Gen (a.two b) []` | ∅ |
| `h₁ : Gen a (x :: u), h₂ : Gen b v ⊢ Gen (a.two b) (x :: (u ++ v))` | ∅ |

**R11 · `obtain ⟨rfl, rfl⟩ := h`** changes the **context**: each `rfl` pattern consumes an equation
`u = e` whose side `u` is a variable, and replaces `u` by `e` everywhere. Placeholders:
`{α : Type} (u v : List α) (h : u = [] ∧ v = [])`.

| Before | After |
|---|---|
| `h : u = [] ∧ v = [] ⊢ P u v` | `⊢ P [] []` |

**R12 · `List.append_eq_nil_iff`** turns an equation into a conjunction. The lemma is
`List.append_eq_nil_iff : p ++ q = [] ↔ p = [] ∧ q = []`; use it as `List.append_eq_nil_iff.mp h.symm`
when you have `h : [] = p ++ q` (`h.symm` flips an equation). With R11 it changes the **context**.
Placeholders: `{α : Type} (p q : List α)`.

| Before | After |
|---|---|
| `h : [] = p ++ q ⊢ P p q` | `h : [] = [] ++ [] ⊢ P [] []` |

---

## Part 3 · `star_cons_inv`

Statement: from `h : Matches (.star r) (c :: w)`, split off a first chunk that starts with `c`:
`∃ u v, w = u ++ v ∧ Matches r (c :: u) ∧ Matches (.star r) v`. Plain `cases h` is not enough: the
first chunk in a `starCons` derivation may be `[]`, and then the rest `v` is again `c :: w`, so you need
an IH. Rule induction needs variable indices, so generalize both first.

**R13 · `generalize hy : e = y at h`** changes the **context**: the expression `e` inside `h` becomes a
fresh variable `y`, and `hy : e = y` remembers it. Placeholders: `(x : Nat) (w : List Nat)`,
`e := x :: w`. In the exercise generalize both indices: `Re.star r = R` and `c :: w = x`.

| Before | After |
|---|---|
| `h : Gen a.many (x :: w) ⊢ P` | `hy : x :: w = y, h : Gen a.many y ⊢ P` |

**R14 · `induction h generalizing w`** (rule induction) changes the **goal list**: one goal per rule of
`Gen`. Equations that mention the indices (`hs`, `hy`) are restated in each goal with that rule's indices,
and each IH takes them as premises. `generalizing w` makes the IH hold for every `w`; in the manyCons
goal the IH for the tail `v✝` is `a_ih✝ : ∀ (w : List Nat), a.many = a✝².many → x :: w = v✝ → P`.
Placeholders: `(s : Sh) (y : List Nat) (h : Gen s y) (hs : Sh.many a = s) (hy : x :: w = y)`.
Name everything with `induction h generalizing w with | @manyCons b u v hu hv ihu ihv => …`; the `@`
also names the rule's implicit arguments (`{a} {u v}`).

| Before | After (the four goals: atom, two, manyNil, manyCons) |
|---|---|
| `hs : a.many = s, hy : x :: w = y ⊢ P` | `hs : a.many = Sh.atom n✝ ⊢ P`, `hs : a.many = a✝².two b✝, hy : x :: w = u✝ ++ v✝ ⊢ P`, `hs : a.many = a✝.many, hy : x :: w = [] ⊢ P`, `hs : a.many = a✝².many, hy : x :: w = u✝ ++ v✝ ⊢ P` |

Without R13 Lean refuses: `Invalid target: Index in target's type is not a variable`.

**R15 · `cases h` on an equation between equal constructors** changes the **context**: constructors are
injective, so `h : C a = C b` with `b` a variable replaces `b` by `a`. Placeholders: `(a b : Sh)`.

| Before | After |
|---|---|
| `h : a.many = b.many ⊢ P b` | `⊢ P a` |

**R16 · `cases h` on an equation between different constructors** **closes** the goal (no constructor
equals another). Also for `x :: w = []`.

| Before | After |
|---|---|
| `h : a.many = b.two c ⊢ P` | ∅ |
| `h : x :: w = [] ⊢ P` | ∅ |

**R17 · `| _ => tac`** changes the **goal list**: in `induction … with` or `cases … with`, the alternative
`_` runs `tac` on every case not listed above it. In the exercise, `| _ => cases hR` kills every rule
other than `starNil`/`starCons` (their `hR : r.star = …` relates different constructors, R16).
Placeholders: `(t : Sh) (P : Sh → Prop)`. In the guide, `| atom n => …` takes the `atom` goal and `_`
takes the other two, the `two` and `many` goals of R4.

| Before | After |
|---|---|
| `t : Sh ⊢ P t` | `atom` handled by its own line; `_` gets `⊢ P (a✝.two b✝)` and `⊢ P a✝.many`, `tac` closes both: ∅ |

**R18 · `rw [List.cons_append]`** changes the **goal**. The lemma is
`List.cons_append : a :: as ++ bs = a :: (as ++ bs)`. Placeholders: `{α : Type} (a : α) (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

**R19 · `simp only [List.cons.injEq] at h`** changes the **context**. The lemma is
`List.cons.injEq : (a :: as = b :: bs) = (a = b ∧ as = bs)`. Together with R18 (`simp only
[List.cons_append, List.cons.injEq] at hx`) it turns `c :: w = c' :: u' ++ v` into `c = c' ∧ w = u' ++ v`,
ready for R11. Placeholders: `{α : Type} (a b : α) (as bs : List α)`.

| Before | After |
|---|---|
| `h : a :: as = b :: bs ⊢ P` | `h : a = b ∧ as = bs ⊢ P` |

---

## Part 4 · `deriv_iff`

Statement: `Matches (deriv c r) w ↔ Matches r (c :: w)`, for all `c r w`. Induction on `r`, generalizing
`w`; each case unfolds `deriv` (`simp only [deriv]`, R28 in Part 5), then proves both directions.

**R20 · `induction t generalizing w`** changes the **goal list** as R4, but `w` is re-introduced in each
goal and every IH is `∀ w, …`, e.g. `a_ih✝ : ∀ (w : List Nat), P a✝ w`. You need this in the `cat` and
`star` cases, where the IH is used at a shorter word `u`, not at `w`. Placeholders: `(t : Sh) (w : List Nat)`.

| Before | After |
|---|---|
| `t : Sh, w : List Nat ⊢ P t w` | `⊢ P (Sh.atom n✝) w`, `⊢ P (a✝.two b✝) w`, `⊢ P a✝.many w` |

**R21 · `split`** changes the **goal list**: a goal containing `if c then t else e` becomes two goals,
with `h✝ : c` and with `h✝ : ¬c`. Name `h✝` with `rename_i` (R2). Placeholders:
`(c : Prop) [Decidable c] {α : Type} (t e : α)`.

| Before | After |
|---|---|
| `⊢ P (if c then t else e)` | `h✝ : c ⊢ P t`, `h✝ : ¬c ⊢ P e` |

**R22 · `split at h`** changes the **goal list**: the same split for an `if` inside a hypothesis.

| Before | After |
|---|---|
| `h : P (if c then t else e) ⊢ Q` | `h✝ : c, h : P t ⊢ Q`, `h✝ : ¬c, h : P e ⊢ Q` |

**R23 · `subst h`** changes the **context**: with `h : a = b` and `b` a variable, `b` is replaced by `a`
everywhere and `h` disappears. Placeholders: `(a b : Char)`.

| Before | After |
|---|---|
| `h : a = b ⊢ P a b` | `⊢ P a a` |

**R24 · `exact absurd rfl h`** **closes** any goal from `h : ¬x = x`. The lemma is
`absurd : a → ¬a → b`. In the `chr` case, after `cases` on `Matches (.chr d) (c :: w)` the letter `d`
becomes `c`, and `hcd : ¬c = d` becomes `¬c = c`.

| Before | After |
|---|---|
| `h : ¬x = x ⊢ P` | ∅ |

**R25 · `(ih x).mp h`, `(ih x).mpr h`** **close** the goal with one direction of an IH
`ih : ∀ x, A x ↔ B x` at the word `x` you choose. `Iff.mp : (A ↔ B) → A → B`, `Iff.mpr : (A ↔ B) → B → A`.
They also work as arguments: `.altL ((ihr w).mp h)`.

| Before | After |
|---|---|
| `h : A w ⊢ B w` | ∅ |
| `h : B w ⊢ A w` | ∅ |

**R26 · `List.append_eq_cons_iff`** splits a word. The lemma is
`List.append_eq_cons_iff : as ++ bs = x :: c ↔ (as = [] ∧ bs = x :: c) ∨ ∃ as', as = x :: as' ∧ c = as' ++ bs`.
With `rcases List.append_eq_cons_iff.mp h.symm with ⟨rfl, rfl⟩ | ⟨u', rfl, rfl⟩` it changes the
**goal list**: either the first part `u` is `[]`, or it is `x :: u'`. Placeholders:
`{α : Type} (u v w : List α) (x : α)`.

| Before | After |
|---|---|
| `h : x :: w = u ++ v ⊢ P u v` | `h : x :: w = [] ++ x :: w ⊢ P [] (x :: w)`, `u' : List α ⊢ P (x :: u') v` |

**R27 · `simp only [hb, if_true]`** changes the **goal**: with `hb : b = true`, the condition becomes
`true = true`, simp reduces it to `True`, and `if_true : (if True then t else e) = t` picks the branch.
Placeholders: `(b : Bool) {α : Type} (t e : α)`.

| Before | After |
|---|---|
| `hb : b = true ⊢ P (if b = true then t else e)` | `⊢ P t` |

---

## Part 5 · `rmatch_iff`

Statement: `rmatch r w = true ↔ Matches r w`. Induction on the word `w`, generalizing `r` (R20 on a list:
cases `nil` and `cons c w ih`, with `ih : ∀ (r : Re), rmatch r w = true ↔ Matches r w`). The `nil` case
is `nullable_iff`. The `cons` case is three rewrites: unfold one step of `rmatch` (R28), the IH (R9),
then `deriv_iff` (R9 again, with an `↔` lemma); `simp only` closes the resulting `A ↔ A`.

**R28 · `simp only [f]`** changes the **goal**: one defining equation of a structurally recursive
function, here `countOf n (x :: xs) = (if x = n then 1 else 0) + countOf n xs`. Placeholders:
`(n x : Nat) (xs : List Nat)`.

| Before | After |
|---|---|
| `⊢ P (countOf n (x :: xs))` | `⊢ P ((if x = n then 1 else 0) + countOf n xs)` |

---

## Worked combinations (W1–W2, on objects that are not the exercise's)

**W1: generalize, rule induction, kill impossible rules.** Every letter of a word of `many (atom n)` is `n`.
After `generalize hs : Sh.many (.atom n) = s at h` (R13) the goal is unchanged and `h : Gen s w`:

```lean-goal
⊢ ∀ (x : Nat), x ∈ w → x = n
```

Then `induction h with` (R14): `manyNil` is immediate; in `manyCons`, `cases hs` (R15) fixes the pattern,
`cases hu` inverts the atom (R1), and the IH is used as `ihv rfl x hx`; `| _ => cases hs` (R17, R16)
kills `atom` and `two`.

**W2: a Bool test agrees with a Prop, by list induction.** `allEq n xs = true ↔ ∀ x ∈ xs, x = n`:
`nil` by `simp [allEq]`, `cons` by `simp only [allEq, Bool.and_eq_true, ih, …]` (R28, R8, R9).

---

## Traps

- `cases h` with `h : Matches (.cat r s) (c :: w)` fails: `Dependent elimination failed` (Lean cannot solve
  `c :: w = u ++ v` for the rule's `u v`). Use `cat_inv`, whose word is a variable, or generalize (R13).
- `induction h` needs every index of `h` to be a variable: generalize `Re.star r` and `c :: w` first
  (R13), and keep `w` general (`generalizing w`) so the IH applies to the tail.
- `star_cons_inv` is not a `cases`: a `starCons` step may consume `[]` first. Then `hx : c :: w = [] ++ v`,
  which is `c :: w = v` by computation, so `ihv rfl hx` finishes that case.
- Forgetting `generalizing w` in `deriv_iff` gives an IH only at the same `w`; the `cat`/`star` cases need it
  at the first chunk `u`.
- `if nullable r then …` is displayed `if nullable r = true then …`; `split` gives `h✝ : nullable r = true`
  or `h✝ : ¬nullable r = true`. Get the Prop fact from `nullable_iff` (R25).
- `a :: as ++ bs` is `(a :: as) ++ bs`, not `a :: (as ++ bs)`; they are equal by R18 and by computation.
- `simp [nullable]` on the `empty`/`chr` cases leaves `¬Matches … []`, not `False`: `intro h; cases h`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| invert a derivation (variable word) | `cases h with \| cat hu hv => …` | R1, R2 |
| witnesses fixed by an equation | `exact ⟨_, _, rfl, hu, hv⟩` | R3 |
| induction on the regex | `induction r with \| empty => … \| alt r s ihr ihs => …` | R4 |
| … and keep the word general | `induction r generalizing w with …` | R20 |
| unfold `nullable`/`deriv`/`rmatch` | `simp [nullable]`, `simp only [deriv]` | R5, R28 |
| no rule applies | `cases h` | R6 |
| `(a \|\| b) = true`, `(a && b) = true` | `simp only [Bool.or_eq_true, Bool.and_eq_true]` | R7, R8 |
| rewrite with an `↔` IH or lemma | `simp only [ih, deriv_iff]` | R9 |
| apply a rule, fix its word split | `exact .cat (u := []) (v := []) h₁ h₂` | R10 |
| substitute equations away | `obtain ⟨rfl, rfl⟩ := h` | R11 |
| `p ++ q = []` | `List.append_eq_nil_iff.mp h.symm` | R12 |
| make an index a variable | `generalize hx : c :: w = x at h` | R13 |
| rule induction | `induction h generalizing w with \| @starCons r' u v hu hv _ ihv => …` | R14 |
| equal / different constructors | `cases hR` | R15, R16 |
| all other cases | `\| _ => cases hR` | R17 |
| `c :: w = c' :: u' ++ v` | `simp only [List.cons_append, List.cons.injEq] at hx` | R18, R19 |
| case on an `if` | `split`, `split at h`, then `rename_i h` | R21, R22, R2 |
| use `c = d` | `subst hcd` | R23 |
| `¬c = c` | `exact absurd rfl hcd` | R24 |
| IH at a chosen word | `(ihr u).mp hu`, `(ihr u).mpr hu` | R25 |
| `c :: w = u ++ v` | `rcases List.append_eq_cons_iff.mp huv.symm with ⟨rfl, rfl⟩ \| ⟨u', rfl, rfl⟩` | R26 |
| pick an `if` branch | `simp only [hn, if_true]` | R27 |
| see the state | infoview | |
