# M024 · Is sorted: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`simp`, `exact`, `have`, `·`, `⟨_, _⟩`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): recursive definitions by `match` (E002, E018), lists
(E015), `Bool` (E016), `∧`/`↔`, `constructor`, `rintro` and `⟨_, _⟩` (E005), `rcases` on `∨` (E006),
`rw … at h` (E009), bounded `∀ x ∈ xs` (E025), `refine` with `?_` (E031).
E084 (functional induction) and E062 (Bool vs Prop) help but are not needed.
**New here:** a Bool test that looks at the first *two* entries of a list, `decide` (Prop → Bool),
`fun_induction` on it, and core Lean's `List.Pairwise` (sortedness) with its lemmas. No Mathlib.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Prop → Prop`, or `P : List Nat → Bool → Prop` in R2). The step
  changes only what sits inside `P (…)`.
- Placeholders are written as Lean binders: `{α : Type}` is any type, `(R : α → α → Prop)` any
  relation on it (in the exercise `R` is `≤` on `Nat`), `(l t : List α)` lists.
- The guide's function, not the exercise's: `chainLt l` is `true` when each entry is strictly below
  the next, so `chainLt [1, 2, 5] = true` and `chainLt [2, 2] = false`. Arms `[]`, `[_]`, `a :: b :: t`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Bool and Prop in two sentences

`Bool` is data (`true | false`), computed by running code; `&&` is Bool "and". `Prop` is the type of
statements, established by proofs; a Bool `b` is turned into the statement `b = true`, and a decidable
statement `p` into the Bool `decide p`. The lemmas R4 (`&&` ↔ `∧`) and R5 (`decide p = true` ↔ `p`)
carry you from the Bool side of `isSorted xs = true` to the Prop side `xs.Pairwise (· ≤ ·)`.

## Reading the goals

| You see | It means |
|---|---|
| `[_]`, `[x]` | the one-element list `x :: []` (`_`: the entry is not named) |
| `x :: y :: rest` | a list with first entry `x`, second `y`, rest `rest` (`::` groups to the right) |
| `decide (x ≤ y)` | `Decidable.decide (x ≤ y) : Bool`: `true` if `x ≤ y`, else `false` |
| `inst✝ : Decidable p` | an anonymous instance in the context: "`p` has a decision procedure" |
| `b && c` | Bool "and" (computed); `(b && c) = true` is the Prop "it computes to `true`" |
| `z ∈ l` | `z` occurs in the list `l` (`List.Mem`, notation from `Membership`) |
| `List.Pairwise R l` | `R x y` for every `x` that comes before `y` in `l` (not only neighbours) |
| `xs.Pairwise (· ≤ ·)` | `List.Pairwise (fun x1 x2 => x1 ≤ x2) xs`: "sorted"; Lean prints the second form |
| `∀ (a' : α), a' ∈ l → R a a'` | `∀ a' ∈ l, R a a'`: `a` is related to every entry of `l` |
| `case case3` | the goal for the third arm of the function (arms counted top to bottom) |
| `case mp`, `case mpr` | the `→` and `←` halves of an `↔` after `constructor` |
| `case inl`, `case inr` | the left and right side of an `∨` after `rcases` |
| `case case3.mp.inl` | nested case names joined by `.`: arm 3, then `→`, then the left side of the `∨` |

---

## Part 1 · `isSorted`

Statement: write the body of `isSorted : List Nat → Bool`. It must return `true` exactly on sorted lists,
and compare only *adjacent* entries: `[]` and `[x]` are sorted; `x :: y :: rest` is sorted when `x ≤ y`
and `y :: rest` is sorted.

**R1 · `match l with | [] => … | [_] => … | a :: b :: t => decide (a < b) && f (b :: t)`** **closes** a
test goal once the function is defined. The arms cover every list (empty, one entry, at least two) and are
tried top to bottom. `decide p : Bool` evaluates a decidable Prop `p` (`<`, `≤`, `=` on `Nat` are
decidable). The recursive call is on the proper tail `b :: t` (keep `b`: it is compared with what follows),
so Lean accepts it by structural recursion without `termination_by`, and the function computes: the
`decide` tactic or `rfl` tests it. Placeholders: `(l : List Nat)`, `(a b : Nat) (t : List Nat)` bound by
the patterns.

| Before | After |
|---|---|
| `⊢ chainLt [1, 2, 5] = true ∧ chainLt [2, 2] = false` | closed by `decide` |

---

## Part 2 · `isSorted_iff`

Statement: `isSorted xs = true ↔ xs.Pairwise (· ≤ ·)`: the adjacent-pairs test agrees with "every earlier
entry is ≤ every later one". Induct along `isSorted` (R2). The short cases are trivial (R3). In the
third case turn the Bool side into Props and use the IH (R4–R6); then prove the two directions (R7).
→ : the head `x` is below `y`, and `y` is below everything later, so by transitivity `x` is below
everything later (R8–R14). ← : read off `x ≤ y` and the tail's sortedness (R14–R16).

### Induction along the function

**R2 · `fun_induction f l with | case1 => … | case2 a => … | case3 a b t ih => …`** changes the
**goal list**: one goal per arm of `f`. In each, `l` becomes the arm's pattern and `f l` that arm's
right-hand side; the recursive call `f (b :: t)` gives the IH. Names after the case: the pattern
variables, then the IH. In the exercise `P l b` is `b = true ↔ List.Pairwise (· ≤ ·) l`, so the IH is
the whole statement for `y :: rest`. Placeholders: `(l : List Nat) (P : List Nat → Bool → Prop)`.

| Before | After |
|---|---|
| `⊢ P l (chainLt l)` | `⊢ P [] true`, `a : Nat ⊢ P [a] true`, `ih : P (b :: t) (chainLt (b :: t)) ⊢ P (a :: b :: t) (decide (a < b) && chainLt (b :: t))` |

**R3 · `simp`** **closes** the two short cases. It uses `List.Pairwise.nil`, `List.pairwise_singleton`
(a list with fewer than two entries has no pair to check, whatever `R` is) and `true = true ↔ True`.
Placeholders: `{α : Type} (R : α → α → Prop) (a : α)`.

| Before | After |
|---|---|
| `⊢ (true = true ↔ List.Pairwise R []) ∧ (true = true ↔ List.Pairwise R [a])` | closed |

### From Bool back to Prop

**R4 · `simp only [Bool.and_eq_true]`** changes the **goal**. The lemma is
`Bool.and_eq_true (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true)`, an equation between Props.
Placeholders: `(a b : Bool) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((a && b) = true)` | `⊢ P (a = true ∧ b = true)` |

**R5 · `simp only [decide_eq_true_eq]`** changes the **goal**. The lemma is
`decide_eq_true_eq {p : Prop} [Decidable p] : (decide p = true) = p`: the Bool test of `p` is `true`
exactly when `p` holds. Placeholders: `(p : Prop) [Decidable p] (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (decide p = true)` | `⊢ P p` |

**R6 · `simp only [ih]`** changes the **goal**: an `↔` hypothesis is a rewrite rule, left side to right
side. In the exercise, the IH turns `isSorted (y :: rest) = true` into `List.Pairwise … (y :: rest)`.
R4–R6 go in one call: `simp only [Bool.and_eq_true, decide_eq_true_eq, ih]`. Placeholders:
`(f : List Nat → Bool) (Q : List Nat → Prop) (l : List Nat) (ih : f l = true ↔ Q l)`.

| Before | After |
|---|---|
| `ih : f l = true ↔ Q l ⊢ P (f l = true)` | `⊢ P (Q l)` |

After R4–R6 the exercise's third case reads
`x ≤ y ∧ List.Pairwise (fun x1 x2 => x1 ≤ x2) (y :: rest) ↔ List.Pairwise (fun x1 x2 => x1 ≤ x2) (x :: y :: rest)`.

### Proving the `↔`

**R7 · `constructor`** changes the **goal list**: `A ↔ B` becomes `A → B` (case `mp`) and `B → A`
(case `mpr`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R8 · `rintro ⟨ha, hb⟩`** changes the **goal and the context**: it introduces the premise `A ∧ B` and
takes it apart at once. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ B → C` | `ha : A, hb : B ⊢ C` |

**R9 · `refine List.Pairwise.cons ?_ ?_`** changes the **goal list**. The lemma is
`List.Pairwise.cons : (∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)`.
`refine List.Pairwise.cons ?_ hp` fills the tail part with a hypothesis at once and leaves only the head
bound. Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ List.Pairwise R (a :: l)` | `⊢ ∀ (a' : α), a' ∈ l → R a a'`, `⊢ List.Pairwise R l` |

**R10 · `intro z hz`** changes the **context**: `∀ a' ∈ l, R a a'` is `∀ a', a' ∈ l → R a a'`, two
binders, two names. Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ ∀ (a' : α), a' ∈ l → R a a'` | `z : α, hz : z ∈ l ⊢ R a z` |

**R11 · `rw [List.mem_cons] at hz`** changes the **context**. The lemma is
`List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l`; `rw` uses an `↔` like an equation. Placeholders:
`{α : Type} (z b : α) (l : List α)`.

| Before | After |
|---|---|
| `hz : z ∈ b :: l ⊢ P` | `hz : z = b ∨ z ∈ l ⊢ P` |

**R12 · `rcases hz with rfl | hz`** changes the **goal list**: one goal per side of `hz : z = b ∨ z ∈ l`.
In the first, the pattern `rfl` substitutes the equation away: one of the two variables is replaced by
the other everywhere, hypotheses included, and disappears from the context (here `b` by `z`; in the
exercise `y` by `a`, so `hxy : x ≤ y` becomes `hxy : x ≤ a`). Placeholders:
`{α : Type} (z b : α) (l : List α) (P : α → α → Prop)`.

| Before | After |
|---|---|
| `hz : z = b ∨ z ∈ l ⊢ P z b` | `h2 : z ∈ l → P z z ⊢ P z z`, `hz : z ∈ l ⊢ P z b` |

**R13 · `Nat.le_trans`** **closes** `n ≤ k`. The lemma is
`Nat.le_trans {n m k : Nat} : n ≤ m → m ≤ k → n ≤ k` (transitivity; `Nat.lt_trans` is the `<` version).
Use it as `exact Nat.le_trans h1 h2`, where `h2` may itself be a term such as R14. Placeholders:
`(n m k : Nat)`.

| Before | After |
|---|---|
| `h1 : n ≤ m, h2 : m ≤ k ⊢ n ≤ k` | closed |

**R14 · `List.rel_of_pairwise_cons`** changes the **context** (or closes `R a z` with `exact`). The lemma
is `List.rel_of_pairwise_cons : Pairwise R (a :: l) → a' ∈ l → R a a'`: the head of a pairwise list is
related to every later entry. Written `List.rel_of_pairwise_cons h hz`. Placeholders:
`{α : Type} (R : α → α → Prop) (a z : α) (l : List α)`.

| Before | After |
|---|---|
| `h : List.Pairwise R (a :: l), hz : z ∈ l ⊢ P` | `hr : R a z ⊢ P` |

**R15 · `List.mem_cons_self`** **closes** `b ∈ b :: l`. Its arguments are implicit, so it is written
with none. With R14 it gives the first two entries' relation:
`List.rel_of_pairwise_cons h List.mem_cons_self : R a b` for `h : Pairwise R (a :: b :: l)`.
Placeholders: `{α : Type} (b : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ b ∈ b :: l` | closed |

**R16 · `List.Pairwise.of_cons`** changes the **context**. The lemma is
`List.Pairwise.of_cons : Pairwise R (a :: l) → Pairwise R l`. Dot notation: for
`h : List.Pairwise R (a :: l)`, `h.of_cons` is `List.Pairwise.of_cons h`. Usually written as a term,
e.g. inside `⟨…, h.of_cons⟩`. Placeholders: `{α : Type} (R : α → α → Prop) (a : α) (l : List α)`.

| Before | After |
|---|---|
| `h : List.Pairwise R (a :: l) ⊢ P` | `h' : List.Pairwise R l ⊢ P` |

### Worked combinations (W1–W3, on `chainLt` and `<`, not the exercise's objects)

**W1 · the first comparison of `chainLt`.** `simp only [chainLt, Bool.and_eq_true, decide_eq_true_eq] at h`
unfolds the definition on `a :: b :: t` and applies R4, R5 to the hypothesis; `h.1` finishes.

| Before | After |
|---|---|
| `h : chainLt (a :: b :: t) = true ⊢ a < b` | `h : a < b ∧ chainLt (b :: t) = true ⊢ a < b` |

**W2 · strict order, building it up.** From `hab : a < b` and `hl : Pairwise (· < ·) (b :: l)`: R9 with
`hl`, R10, R11, R12; the `rfl` goal is `hab` itself, the other is `Nat.lt_trans hab (…R14…)`.

```lean-goal
⊢ ∀ (a' : Nat), a' ∈ b :: l → a < a'
⊢ a < z
```

| Before `rcases` | After `rcases hz with rfl \| hz` |
|---|---|
| `hz : z = b ∨ z ∈ l ⊢ a < z` | `hab : a < z ⊢ a < z`, `hz : z ∈ l ⊢ a < z` |

**W3 · strict order, taking it apart.** `⟨List.rel_of_pairwise_cons h List.mem_cons_self, h.of_cons⟩`
proves `a < b ∧ Pairwise (· < ·) (b :: l)` from `h : Pairwise (· < ·) (a :: b :: l)` (R14 with R15, R16).

---

## Traps

- Recurse on `isSorted (y :: rest)`, not `isSorted rest`: dropping `y` skips the comparison of `y`
  with the entry after it.
- `decide (x ≤ y)` is a `Bool`, `x ≤ y` a `Prop`: `&&` needs the Bool, so write `decide (x ≤ y) && …`.
- `Bool.and_eq_true` and `decide_eq_true_eq` are `=` between Props, not `↔`: use them with `simp only`
  or `rw`, not `exact`.
- `List.Pairwise (· ≤ ·)` asks for `x ≤ z` for *every* later `z`, not only the next entry; that is why
  the → direction needs transitivity (R13) and the case split on `z ∈ y :: rest` (R11, R12).
- `rcases ha with rfl | ha` on `a = y` removes `y`: afterwards the hypotheses mention `a`
  (`hxy : x ≤ a`, `hp : Pairwise … (a :: rest)`).
- `rw [List.mem_cons] at hz` rewrites only the outermost `∈ _ :: _`.
- In case3 use `simp only [Bool.and_eq_true, decide_eq_true_eq, ih]`, not plain `simp [ih]`: plain `simp`
  also unfolds `Pairwise R (x :: …)` (lemma `List.pairwise_cons`) and leaves a long chain of `→` and
  bounded `∀`s instead of the `↔` the skeleton continues from.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| define by the first two entries | `match xs with \| [] => … \| [_] => … \| x :: y :: rest => decide (x ≤ y) && …` | R1 |
| test the definition | `example : isSorted [1, 2, 2] = true := by decide` | R1 |
| induct along the function | `fun_induction f xs with \| case1 => … \| case2 x => … \| case3 x y rest ih => …` | R2 |
| `Pairwise R []`, `Pairwise R [x]` | `simp` | R3 |
| `&&` → `∧`, `decide p = true` → `p`, use the IH | `simp only [Bool.and_eq_true, decide_eq_true_eq, ih]` | R4, R5, R6 |
| split `↔` | `constructor` | R7 |
| introduce and split `A ∧ B` | `rintro ⟨ha, hb⟩` | R8 |
| prove `Pairwise R (a :: l)` | `refine List.Pairwise.cons ?_ hl` | R9 |
| take an element of the tail | `intro z hz` | R10 |
| `z ∈ b :: l` → `z = b ∨ z ∈ l` | `rw [List.mem_cons] at hz` | R11 |
| split `z = b ∨ z ∈ l`, substituting | `rcases hz with rfl \| hz` | R12 |
| chain `n ≤ m`, `m ≤ k` | `Nat.le_trans h1 h2` | R13 |
| head related to a later entry | `List.rel_of_pairwise_cons h hz` | R14 |
| head related to the second entry | `List.rel_of_pairwise_cons h List.mem_cons_self` | R14, R15 |
| tail of a pairwise list | `h.of_cons` | R16 |
| see the state | infoview | |
