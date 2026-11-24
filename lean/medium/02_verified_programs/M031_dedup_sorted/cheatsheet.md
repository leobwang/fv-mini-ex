# M031 · Dedup a sorted list: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`simp`, `exact`, `have`, `·`) are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `match` and structural recursion (E002), lists and
list induction (E015), `rcases` on `∨` (E006), `omega` (E011), bounded `∀ x ∈ xs` (E025).
E084 (functional induction) and M030 (merge sorted lists) help but are not needed.
**New here:** a recursion that looks at the first *two* entries of a list, `fun_induction` through an
`if`, and core Lean's `List.Pairwise` (sortedness) with its lemmas. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal". The step changes only what sits inside `P (…)`.
- Placeholders are written as Lean binders: `{α : Type}` is any type, `(R : α → α → Prop)` any
  relation on it (in the exercise `R` is `≤` or `<` on `Nat`), `(l t : List α)` lists.
- The guide's function, not the exercise's: `squash l` keeps one of every pair of equal adjacent
  entries and continues after the pair, so `squash [1, 1, 1, 2, 3, 3] = [1, 1, 2, 3]`. Arms `[]`,
  `[a]`, `a :: b :: t` with `if a = b`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `[a]` | the one-element list `a :: []` |
| `a :: b :: t` | a list with first entry `a`, second `b`, rest `t` (`::` groups to the right) |
| `z ∈ l` | `z` occurs in the list `l` (`List.Mem`, notation from `Membership`) |
| `List.Pairwise R l` | `R x y` for every `x` that comes before `y` in `l` (not only neighbours) |
| `xs.Pairwise (· ≤ ·)` | dot notation for `List.Pairwise (· ≤ ·) xs` (`xs : List Nat`); `(· ≤ ·)` is `fun a b => a ≤ b` |
| `fun x1 x2 => x1 ≤ x2` | the relation `(· ≤ ·)` as Lean prints it: `Pairwise` of it means "sorted" |
| `fun x1 x2 => x1 < x2` | `(· < ·)`: `Pairwise` of it means "strictly increasing", so no repeats |
| `∀ (a' : α), a' ∈ l → R a a'` | `∀ a' ∈ l, R a a'`: `a` is related to every entry of `l` |
| `¬a = b` | the `else` condition of `if a = b` after `fun_induction` (`¬` is "not") |
| `case case3` | the goal for the third branch of the function (branches counted top to bottom, each `if` side separately) |
| `ih : Q t → …` | an IH that kept a hypothesis about the list as a premise (R5) |
| `case case4.inl`, `case case4.inr` | the two goals `rcases` makes from an `∨` inside case4: `inl` the left side, `inr` the right (R13) |

---

## Part 1 · `dedup`

Statement: write the body of `dedup : List Nat → List Nat`, which removes adjacent duplicates
(`dedup [1, 1, 2, 2, 2, 3] = [1, 2, 3]`). Look at the first two entries: if they are equal, drop
the first and recurse on the rest *including* the second; otherwise keep the first.

**R1 · `match l with | [] => … | [a] => … | a :: b :: t => if a = b then … else …`** **closes** a
test goal once the function is defined. The arms cover every list (empty, one entry, at least two)
and are tried top to bottom. Every recursive call is on a proper tail (`t` or `b :: t`), so Lean
accepts it by structural recursion without `termination_by`, and the function computes: `rfl` or
`decide` tests it. Placeholders: `(l : List Nat)`, `(a b : Nat) (t : List Nat)` bound by the patterns.

| Before | After |
|---|---|
| `⊢ squash [1, 1, 1, 2, 3, 3] = [1, 1, 2, 3]` | closed by `rfl` |

---

## Part 2 · `dedup_mem`

Statement: `z ∈ dedup xs ↔ z ∈ xs`: removing duplicates loses no element and adds none. Prove it
before `dedup_strict`, which needs it.

**R2 · `fun_induction f l with | case1 => … | case2 a => … | case3 a t ih => … | case4 a b t h ih => …`**
changes the **goal list**: one goal per branch of `f`. A three-arm function whose third arm has an
`if` gives four goals. In each, `l` becomes the branch's pattern and `f l` the branch's right-hand
side; every recursive call adds an IH. In the `then` branch of `if a = b` Lean *substitutes*
`b := a`: the pattern reads `a :: a :: t` and no hypothesis `a = b` is left, so that case names
only `a t ih`. The `else` branch keeps `hab : ¬a = b`. Names after the case: pattern variables,
then the `if` condition, then the IH. Placeholders: `(l : List Nat) (P : List Nat → List Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P l (squash l)` | `⊢ P [] []`, `a : Nat ⊢ P [a] [a]`, `ih : P t (squash t) ⊢ P (a :: a :: t) (a :: squash t)`, `hab : ¬a = b, ih : P (b :: t) (squash (b :: t)) ⊢ P (a :: b :: t) (a :: squash (b :: t))` |

In the exercise, case1 and case2 are `z ∈ [] ↔ z ∈ []` and `z ∈ [x] ↔ z ∈ [x]`: `simp` closes them.

**R3 · `List.mem_cons`** changes the **goal** (or, with `at hz`, the **context**). The lemma is
`a ∈ b :: l ↔ a = b ∨ a ∈ l`; `rw` uses an `↔` like an equation. `simp` and `simp_all` apply it by
themselves. Placeholders: `{α : Type} (z b : α) (l : List α)`.

| Before | After |
|---|---|
| `hz : z ∈ b :: l ⊢ P` | `hz : z = b ∨ z ∈ l ⊢ P` |

**R4 · `simp_all`** **closes** the goal. Unlike `simp`, it also rewrites with every hypothesis, so an IH
`ih : z ∈ f l ↔ z ∈ l` turns `z ∈ f l` in the goal into `z ∈ l`; then R3 and propositional clean-up
(`p ∨ p ∨ q ↔ p ∨ q`) finish. Placeholders: `{α : Type} (a z : α) (f : List α → List α) (l : List α)`.

| Before | After |
|---|---|
| `ih : z ∈ f l ↔ z ∈ l ⊢ z ∈ a :: f l ↔ z ∈ a :: a :: l` | closed |

**W1 · `squash` keeps the same elements.** `z ∈ squash l ↔ z ∈ l` by R2, with `simp` in case1 and
case2 and `simp_all` (R4) in case3 and case4.

| Before | After |
|---|---|
| `⊢ z ∈ squash l ↔ z ∈ l` | closed |

---

## Part 3 · `dedup_strict`

Statement: if `xs` is sorted (`Pairwise (· ≤ ·)`), then `dedup xs` is strictly increasing
(`Pairwise (· < ·)`). The work is all in the `else` case: the kept head `x` must be `<` every entry
of `dedup (y :: rest)`. By `dedup_mem` such an entry `z` lies in `y :: rest`, so `x ≤ z` from
sortedness; and `x ≠ y` with `y ≤ z` gives `x < z`.

**R5 · `fun_induction` with a hypothesis about the list** changes the **context** of every case. A
hypothesis `hq : Q l` that mentions the induction variable is taken into the induction: each case
gets `hq` about its own pattern, and each IH asks for `Q` of the recursive call's argument. In the
exercise `h : xs.Pairwise (· ≤ ·)` plays `hq`, and you feed the IH with `ih h.of_cons` (R7).
Placeholders: `(l : List Nat) (Q P : List Nat → Prop) (hq : Q l)`.

| Before | After |
|---|---|
| `hq : Q l ⊢ P (squash l)` | `hq : Q [] ⊢ P []`, `hq : Q [a] ⊢ P [a]`, `hq : Q (a :: a :: t), ih : Q t → P (squash t) ⊢ P (a :: squash t)`, `hab : ¬a = b, hq : Q (a :: b :: t), ih : Q (b :: t) → P (squash (b :: t)) ⊢ P (a :: squash (b :: t))` |

**R6 · `simp`** **closes** `Pairwise R []` and `Pairwise R [a]` (lemmas `List.Pairwise.nil`,
`List.pairwise_singleton`): a list with fewer than two entries has no pair to check, whatever `R` is.
Placeholders: `{α : Type} (R : α → α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ List.Pairwise R [] ∧ List.Pairwise R [a]` | closed |

**R7 · `List.Pairwise.of_cons`** changes the **context**. The lemma is
`Pairwise R (a :: l) → Pairwise R l`. Dot notation: for `h : List.Pairwise R (a :: l)`,
`h.of_cons` is `List.Pairwise.of_cons h`; `h.of_cons.of_cons` drops two entries. Usually written as
an argument, `ih h.of_cons`. Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `h : List.Pairwise R (a :: l) ⊢ P` | `h' : List.Pairwise R l ⊢ P` |

**R8 · `refine List.Pairwise.cons ?_ ?_`** changes the **goal list**. The lemma is
`(∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)`. `refine List.Pairwise.cons ?_ (ih …)`
fills the tail part at once and leaves only the head bound. Placeholders:
`{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ List.Pairwise R (a :: l)` | `⊢ ∀ (a' : α), a' ∈ l → R a a'`, `⊢ List.Pairwise R l` |

**R9 · `intro z hz`** changes the **context**: `∀ a' ∈ l, R a a'` is `∀ a', a' ∈ l → R a a'`, two
binders, two names. Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ ∀ (a' : α), a' ∈ l → R a a'` | `z : α, hz : z ∈ l ⊢ R a z` |

**R10 · `rw [thm] at hz`** changes the **context**. A theorem you proved earlier in the file (here
`dedup_mem`) is a rewrite rule like any library lemma; `rw` finds its arguments by matching `hz`.
Placeholders: `{α : Type} (z : α) (f : List α → List α) (l : List α)`,
`(thm : ∀ (l : List α) (z : α), z ∈ f l ↔ z ∈ l)`.

| Before | After |
|---|---|
| `hz : z ∈ f l ⊢ P` | `hz : z ∈ l ⊢ P` |

**R11 · `List.rel_of_pairwise_cons`** changes the **context**. The lemma is
`Pairwise R (a :: l) → a' ∈ l → R a a'`: the head of a pairwise list is related to every later
entry. Written `List.rel_of_pairwise_cons h hz`. Placeholders:
`{α : Type} (R : α → α → Prop) (a z : α) (l : List α)`.

| Before | After |
|---|---|
| `h : List.Pairwise R (a :: l), hz : z ∈ l ⊢ P` | `hr : R a z ⊢ P` |

**R12 · `List.mem_cons_self`** **closes** `b ∈ b :: l`. Its arguments are implicit, so it is written
with none. With R11 it gives the first two entries' relation:
`List.rel_of_pairwise_cons h List.mem_cons_self : R a b` for `h : Pairwise R (a :: b :: l)`.
Placeholders: `{α : Type} (b : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ b ∈ b :: l` | closed |

**R13 · `rcases hz with rfl | hz`** changes the **goal list**: one goal per side of `hz : z = b ∨ z ∈ l`.
In the first, the pattern `rfl` substitutes the equation away: `b` is replaced by `z` everywhere,
hypotheses included, and disappears from the context. Placeholders:
`{α : Type} (z b : α) (l : List α) (P : α → α → Prop)`.

| Before | After |
|---|---|
| `hz : z = b ∨ z ∈ l ⊢ P z b` | `h2 : z ∈ l → P z z ⊢ P z z`, `hz : z ∈ l ⊢ P z b` |

**R14 · `omega`** **closes** linear arithmetic over `Nat` from the hypotheses; it reads `¬x = y` too.
So `x ≤ y`, `¬x = y` give `x < y`, and with `y ≤ z` also `x < z`. Placeholders: `(x y z : Nat)`.

| Before | After |
|---|---|
| `h1 : x ≤ y, h2 : y ≤ z, hne : ¬x = y ⊢ x < z` | closed |

**W2 · sorted in, sorted out.** `squash` keeps `≤`-sortedness (not `<`: `squash [1, 1, 1] = [1, 1]`).
R5, then R6 for case1 and case2; in case3 and case4 R8 with R7 for the tail, R9, R10 with W1, R11.

| Before | After |
|---|---|
| `h : List.Pairwise (fun x1 x2 => x1 ≤ x2) l ⊢ List.Pairwise (fun x1 x2 => x1 ≤ x2) (squash l)` | closed |

**W3 · a strict bound from the second entry.** From `h : Pairwise (· ≤ ·) (a :: b :: l)`,
`hab : ¬a = b` and `hz : z ∈ b :: l`: R12 with R11 gives `h1 : a ≤ b`, R3 splits `hz`, R13 makes two
goals, R14 closes each (the second after a bound `b ≤ z`).

| Before `rcases` | After `rcases hz with rfl \| hz` |
|---|---|
| `hz : z = b ∨ z ∈ l ⊢ a < z` | `h1 : a ≤ z, hab : ¬a = z ⊢ a < z`, `hz : z ∈ l ⊢ a < z` |

---

## Traps

- Recurse on `dedup (y :: rest)`, not `dedup rest`, in *both* branches: dropping `y` loses it when it
  differs from what follows.
- `fun_induction` names the `then` case of `if x = y` with only `x rest ih`: `y` is already replaced
  by `x`. Writing `case3 x y rest ih` fails with "Too many variable names provided".
- `h` is a hypothesis about `xs`, so in every case it is about the pattern and the IH is an
  implication: write `ih h.of_cons`, not `ih`. In the `then` case `h : Pairwise (x :: x :: rest)` and
  the call is on `x :: rest`, so one `.of_cons` is right.
- `List.Pairwise (· < ·)` asks for `x < z` for *every* later `z`, not just the next entry. That is why
  you need `dedup_mem`: to know that the entries of `dedup (y :: rest)` come from `y :: rest`.
- `rcases hz with rfl | hz` on `z = y` removes `y`: afterwards the hypotheses mention `z` instead
  (`hxy : ¬x = z`).
- `rw [List.mem_cons] at hz` rewrites only the outermost `∈ _ :: _`; on `z ∈ x :: y :: rest` it
  gives `z = x ∨ z ∈ y :: rest`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define by the first two entries | `match xs with \| [] => … \| [x] => … \| x :: y :: rest => if x = y then … else …` | R1 |
| test the definition | `example : f [1, 1, 2] = [1, 2] := by rfl` | R1 |
| induct along the function | `fun_induction f xs with \| case1 => … \| case2 x => … \| case3 x rest ih => … \| case4 x y rest h ih => …` | R2, R5 |
| `z ∈ b :: l` → `z = b ∨ z ∈ l` | `rw [List.mem_cons] at hz` | R3 |
| close using an `↔` IH | `simp_all` | R4 |
| `Pairwise R []`, `Pairwise R [x]` | `simp` | R6 |
| tail of a pairwise list | `h.of_cons` | R7 |
| prove `Pairwise R (a :: l)` | `refine List.Pairwise.cons ?_ (ih h.of_cons)` | R8 |
| take an element of the tail | `intro z hz` | R9 |
| move `hz` along your own `↔` theorem | `rw [thm] at hz` | R10 |
| head ≤ a later entry | `List.rel_of_pairwise_cons h hz` | R11 |
| head ≤ second entry | `List.rel_of_pairwise_cons h List.mem_cons_self` | R11, R12 |
| split `z = b ∨ z ∈ l`, substituting | `rcases hz with rfl \| hz` | R13 |
| `x ≤ y`, `x ≠ y` ⇒ `x < y` | `omega` | R14 |
| see the state | infoview | |
