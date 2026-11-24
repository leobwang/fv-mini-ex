# M025 · Binary search: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics (`intro`, `rw`, `have`, `<;>`, `·`) are in
[`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` with `if … then … else`, `Option`, `intro`,
`exact`, `have`, `rw`, `simp`, `omega`, `·`. E084 (functional induction) helps but is not needed.
**New here:** core Lean only (no Mathlib): `Array` lookups `a[i]` and `a[i]?`; `fun_induction` on a
function defined by well-founded recursion with a dependent `if h :`, a `let`, and nested `if`s;
hypotheses that `fun_induction` carries into the IHs; `subst`; `by_cases`; applying a `def`-valued
hypothesis such as `Sorted a`; `omega` with array entries and `let` variables; the lemmas
`Array.getElem?_eq_getElem`, `Nat.le_refl`, `Nat.zero_le`.

The problem in one paragraph. `bsearch a key lo hi` searches the half-open range `[lo, hi)` of the
array `a`. If the range is non-empty and inside the array (`h : lo < hi ∧ hi ≤ a.size`), it looks at
`mid = (lo + hi) / 2`: on a hit it returns `some mid`, if `a[mid] < key` it continues in
`[mid + 1, hi)`, otherwise in `[lo, mid)`. Lean accepts the recursion with `termination_by hi - lo`
(the width shrinks). You prove: a returned index holds `key`, and (for a sorted array) `none` means
`key` is nowhere. Both top-level theorems fix `lo = 0`, `hi = a.size`; the induction needs `lo` and
`hi` to vary, so you first prove a **general version for all `lo hi`** (a MILESTONE) and specialise.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P`, `C` are "the rest of your goal" (`P : Prop`, `C : Nat → Nat → Prop`, …). The step changes only
  what sits inside `P (…)`. `Q` is an arbitrary proposition. A hypothesis `h…` in an example is there
  only to finish it.
- The guide's recursive functions, none of them the exercise's: `probe a l r` (bisection of `[l, r)`
  with the same branch shape as `bsearch`: hit if `a[m] = 0`, right half if `a[m]` is odd, left half
  otherwise) and `scan a t l r` (linear search for `t` from `l` upwards). `Desc a` says the array is
  non-increasing; it plays the role of `Sorted a`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `a.size` | `Array.size a`, the number of entries of `a` |
| `a[i]` | entry `i` of `a`. It needs a proof of `i < a.size`, which Lean finds itself (`get_elem_tactic`, which tries `omega` on the context) |
| `a[i]?` | lookup that returns an `Option Nat`: `some a[i]` in bounds, `none` out of bounds; it needs no proof |
| `some x`, `none` | the two constructors of `Option Nat` ("a result `x`", "no result") |
| `h : lo < hi ∧ hi ≤ a.size` | the condition of `if h : …`; the name `h` is what lets `a[mid]` inside the branch find its bound |
| `mid : Nat := (lo + hi) / 2` | a `let` from the definition, kept after `fun_induction` as a local definition: `omega` sees its value (R12) |
| `hm : ¬a[mid] = key` | the `else` branch of `if a[mid] = key` |
| `case case1`, …, `case case4` | the goals `fun_induction` makes, one per branch of the function, in source order |
| `ih : P → Q` | an induction hypothesis (IH) for a recursive call; its premises are the hypotheses that were carried (R2, R9) |
| `l✝`, `h✝¹`, `ih1✝` | names Lean chose; `✝` means you cannot type them. Name them in the `with` arms (R1) |
| `∀ (h2 : i < r), a[i] ≠ t` | how a named premise `(h2 : i < r) → a[i] ≠ t` is printed; the name is used by `a[i]`. The IHs of Part 2 print `∀ (hsz : hi ≤ a.size), …` and `∀ (hi2 : i < hi), …` for the same reason: read them as `hi ≤ a.size → …` |
| `∀ i (_ : lo ≤ i) (hi2 : i < hi), …` | in a statement: `_` is a premise without a name (printed `lo ≤ i → …`), `hi2` is a named one |
| `case pos`, `case neg` | the two goals of `by_cases` (R10) |
| `this : …` | the fact added by `have := …` without a name (R11) |
| `Sorted a` | the exercise's `def`: `∀ i j, i ≤ j → j < a.size → a[i] ≤ a[j]`; apply it like a function (R11) |

---

## Part 1 · `bsearch_some`

Statement: from `h : bsearch a key 0 a.size = some i`, conclude `a[i]? = some key`. Prove FIRST the
MILESTONE for all ranges,
`bsearch_some_gen (a) (key lo hi i) (h : bsearch a key lo hi = some i) : a[i]? = some key`,
by `fun_induction bsearch a key lo hi`; then `bsearch_some` is that milestone at `lo := 0`,
`hi := a.size` (R8).

### Why generalise

**W3 · `fun_induction` on the constants `0 a.size`** changes the **goal list** but loses the link to
`h`. The arguments are not variables, so `fun_induction` replaces them by fresh `l✝ r✝` and does not
carry `h` (compare R2): `h` stays about `probe a 0 a.size` in every case and each IH is the goal itself.
A goal that mentions `0` or `a.size` is even replaced by one about `l✝ r✝`, usually false.

| Before | After (case2) |
|---|---|
| `h : probe a 0 a.size = some i ⊢ C i` | `h : probe a 0 a.size = some i, ih1✝ : C i ⊢ C i` |

### Following the branches

**R1 · `fun_induction f a l r with | case1 … => … | …`** changes the **goal list**: one goal per branch.
It applies the induction principle Lean generates for every recursive definition (`#check @probe.induct`
shows it). `if h : c then (let m := e; if c₁ then A else if c₂ then B else D) else E` has four branches:
`case1` (hit), `case2` (first recursive call), `case3` (second recursive call), `case4` (`else`). Each arm
names, in order: the arguments that change in the recursion (`l r`; an argument passed unchanged, like
`a`, is not named), the outer condition `hb`, the `let` variable `m`, the inner conditions, then the IH.
In each goal the call `f a l r` is already replaced by that branch's right-hand side. Placeholders:
`(a : Array Nat) (l r : Nat) (P : Nat → Nat → Option Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P l r (probe a l r)` | `hb : l < r ∧ r ≤ a.size, m : Nat := (l + r) / 2, hm : a[m] = 0 ⊢ P l r (some m)`, `hm : ¬a[m] = 0, hodd : a[m] % 2 = 1, ih : P (m + 1) r (probe a (m + 1) r) ⊢ P l r (probe a (m + 1) r)`, `hodd : ¬a[m] % 2 = 1, ih : P l m (probe a l m) ⊢ P l r (probe a l m)`, `hb : ¬(l < r ∧ r ≤ a.size) ⊢ P l r none` |

For `bsearch` the arms are `| case1 lo hi hb mid hm => … | case2 lo hi hb mid hm hlt ih => … |
case3 lo hi hb mid hm hlt ih => … | case4 lo hi hb => …`.

**R2 · a hypothesis about the call** changes the **context** of every case. `h : probe a l r = some i`
mentions `l r`, so `fun_induction` takes it into the induction: in each case `h` is about that branch's
right-hand side, and each IH gains the premise. Placeholders: `(i : Nat) (h : probe a l r = some i)
(C : Nat → Nat → Prop)`.

| Before | After |
|---|---|
| `h : probe a l r = some i ⊢ C l r` | `hm : a[m] = 0, h : some m = some i ⊢ C l r`, `ih : probe a (m + 1) r = some i → C (m + 1) r, h : probe a (m + 1) r = some i ⊢ C l r`, `ih : probe a l m = some i → C l m, h : probe a l m = some i ⊢ C l r`, `hb : ¬(l < r ∧ r ≤ a.size), h : none = some i ⊢ C l r` |

### The hit: `case1`

**R3 · `simp at h`** on `h : some x = some y` changes the **context**: `h` becomes `x = y`. `simp` uses
`Option.some.injEq : (some x = some y) = (x = y)` (`some` is injective). Placeholders: `(x y : Nat)`.

| Before | After |
|---|---|
| `h : some x = some y ⊢ P y` | `h : x = y ⊢ P y` |

**R4 · `subst h`** with `h : x = y` and `y` a local variable changes the **context and the goal**: `y`
and `h` disappear, and `y` is replaced by `x` everywhere. In `case1` this turns `i` into `mid`.
Placeholders: `(x y : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `h : x = y ⊢ P y` | `⊢ P x` |

Then `rw [← hm]` (with `hm : a[mid] = key`, TACTIC_STATES "Rewriting") turns `some key` into
`some a[mid]`, so that the goal has exactly the form of R5.

**R5 · `Array.getElem?_eq_getElem`** **closes** the goal. The lemma is
`Array.getElem?_eq_getElem {xs : Array α} {i : Nat} (h : i < xs.size) : xs[i]? = some xs[i]`: in
bounds, the `Option` lookup is `some` of the proof-carrying lookup. Write `exact
Array.getElem?_eq_getElem _`; Lean reads `h` off the goal. Placeholders: `(xs : Array Nat) (i : Nat)`.

| Before | After |
|---|---|
| `hi : i < xs.size ⊢ xs[i]? = some xs[i]` | closed |

### The recursive calls and the empty range

**R6 · `exact ih h`** **closes** the goal: in `case2` and `case3` the carried `h` (R2) is exactly the
IH's premise, and the IH's conclusion is the goal. Placeholders: `(Q C : Prop)`.

| Before | After |
|---|---|
| `ih : Q → C, h : Q ⊢ C` | closed |

**R7 · `simp at h`** on `h : none = some y` (or `h : some x = none`) **closes** the goal. The two sides
start with different constructors, so `simp` rewrites `h` to `False`, and a goal with `False` in the
context is done. This is `case4` here and `case1` in Part 2. Placeholders: `(y : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `h : none = some y ⊢ P` | closed |

### Specialising

**R8 · apply the general fact** **closes** the goal: `hgen 0 n i h` instantiates `l := 0`, `r := n`.
In the exercise this is the whole proof of `bsearch_some`, in term mode: `bsearch_some_gen a key 0 a.size i h`.
Placeholders: `(n i : Nat) (Q : Nat → Nat → Nat → Prop) (C : Nat → Prop)`, and in the context
`hgen : ∀ (l r i : Nat), Q l r i → C i` (the milestone).

| Before | After |
|---|---|
| `h : Q 0 n i ⊢ C i` | closed |

**W1 · a `some` result lies in the range.** `probe a l r = some i → l ≤ i ∧ i < r`: R1 + R2; `case1`
by R3, R4, `omega`; `case2`, `case3` by `have := ih h` then `omega`; `case4` by R7.

| Before | After |
|---|---|
| `h : probe a l r = some i ⊢ l ≤ i ∧ i < r` | closed |

---

## Part 2 · `bsearch_none`

Statement: for a sorted `a`, `bsearch a key 0 a.size = none` implies `a[i] ≠ key` for every
`i < a.size`. Prove FIRST the MILESTONE with the range invariant "key is not at any index in `[lo, hi)`":
`bsearch_none_gen (a) (key lo hi) (hs : Sorted a) (hsz : hi ≤ a.size) (h : bsearch a key lo hi = none) :
∀ i (_ : lo ≤ i) (hi2 : i < hi), a[i] ≠ key`. The hypothesis `hsz` is needed for `a[i]` to make sense
(Lean derives `i < a.size` from `hi2` and `hsz`), and `hi2` must be a named binder for the same reason.

**R9 · two carried hypotheses** change the **context** of every case: `hr : r ≤ a.size` and
`h : probe a l r = none` mention `l r`, so both become IH premises (in this order), while `hq : Q`
(like `hs : Sorted a`) does not and stays put. In `case3` the first premise is `m ≤ a.size`: the bound
for the recursive call `probe a l m`. Placeholders: `(Q : Prop) (hq : Q) (hr : r ≤ a.size)
(h : probe a l r = none) (C : Nat → Nat → Prop)`.

| Before | After |
|---|---|
| `hr : r ≤ a.size, h : probe a l r = none ⊢ C l r` | `h : some m = none ⊢ C l r`, `ih : r ≤ a.size → probe a (m + 1) r = none → C (m + 1) r, hr : r ≤ a.size, h : probe a (m + 1) r = none ⊢ C l r`, `ih : m ≤ a.size → probe a l m = none → C l m, h : probe a l m = none ⊢ C l r`, `h : none = none ⊢ C l r` |

`case1` (`h : some mid = none`) is closed by R7. In the other cases start with `intro i h1 h2`.

**R10 · `by_cases hle : i ≤ m`** changes the **goal list**: two goals, one with `hle : i ≤ m`
(`case pos`) and one with `hle : ¬i ≤ m` (`case neg`). In `case2` split on `i ≤ mid` (left of the
probe: sortedness; right: the IH); in `case3` on `mid ≤ i`. Choose a name that is not in the context:
`by_cases hi : …` inside an arm that named the range end `hi` hides it, and the goals then show `hi✝`.
Placeholders: `(i m : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `⊢ P` | `hle : i ≤ m ⊢ P`, `hle : ¬i ≤ m ⊢ P` |

**R11 · `have := hs i j hij (by omega)`** changes the **context**: it adds `this`. `hs : Desc a` is a
`def` whose body is `∀ i j (hij : i ≤ j) (hj : j < a.size), a[j] ≤ a[i]`, so `hs` is applied like a
function, one argument per binder; `Sorted a` works the same way and gives `a[i] ≤ a[j]`. The bound
argument `j < a.size` is not in the context, so `(by omega)` proves it from the context. Placeholders:
`(a : Array Nat) (hs : Desc a) (i j n : Nat) (hij : i ≤ j) (hj : j < n) (hn : n ≤ a.size)`.

| Before | After |
|---|---|
| `hs : Desc a, hij : i ≤ j, hj : j < n, hn : n ≤ a.size ⊢ P` | `this : a[j] ≤ a[i] ⊢ P` |

**R12 · `omega` with a `let` variable** **closes** the goal. `omega` uses the value of
`m : Nat := (l + r) / 2`, takes `∧` in a hypothesis apart, and knows `/ 2`. This is how `(by omega)`
proves `mid < a.size` in R11 and `mid + 1 ≤ i` in R14. Placeholders: `(l r n : Nat)`.

| Before | After |
|---|---|
| `hb : l < r ∧ r ≤ n, m : Nat := (l + r) / 2 ⊢ m < n` | closed |

**R13 · `omega` with array entries** **closes** the goal. Each `a[i]` is one unknown number to `omega`,
so it chains `this : a[i] ≤ a[j]` with `hm : ¬a[i] = t` and `hlt : ¬a[i] < t` (together `t < a[i]`).
It does NOT know `a[i] = a[j]` from `i = j`; for that use `subst` (R4). Placeholders:
`(a : Array Nat) (i j t : Nat)`.

| Before | After |
|---|---|
| `hm : ¬a[i] = t, hlt : ¬a[i] < t, this : a[i] ≤ a[j] ⊢ a[j] ≠ t` | closed |

**R14 · `exact ih hr h i (by omega) h2`** **closes** the goal: the IH with its premises in order, the
carried hypotheses (R9), then `i` and its two range conditions. A premise that is not literally in the
context (`m + 1 ≤ i` from `¬i ≤ m`, or `mid ≤ a.size` in `case3`) gets `(by omega)`. Placeholders:
`(n r m : Nat) (Q : Prop) (C : Nat → Prop)`, and in the context
`ih : r ≤ n → Q → ∀ (i : Nat), m + 1 ≤ i → i < r → C i` (the shape of `case2`'s IH from R9). In the
exercise the infoview prints the bound premises as `∀ (hsz : hi ≤ a.size), …` and `∀ (hi2 : i < hi), …`
(see Reading the goals); they are fed in the same order.

| Before | After |
|---|---|
| `hr : r ≤ n, h : Q, h2 : i < r, hi : ¬i ≤ m ⊢ C i` | closed |

**R15 · `omega` on contradictory hypotheses** **closes** any goal. In the empty branch
`hb : ¬(l < r ∧ r ≤ n)` is incompatible with `l ≤ i`, `i < r`, `r ≤ n`. Placeholders: `(l r n i : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `hb : ¬(l < r ∧ r ≤ n), hr : r ≤ n, h1 : l ≤ i, h2 : i < r ⊢ P` | closed |

**R16 · `fun i hi => hgen 0 n (Nat.le_refl n) i (Nat.zero_le i) hi`** **closes** the goal. `fun i hi => …`
is `intro i hi` in term mode; `Nat.le_refl n : n ≤ n` and `Nat.zero_le i : 0 ≤ i` discharge the
premises that become trivial at `l := 0`, `r := n`. In the exercise `n` is `a.size`. Placeholders:
`(n : Nat) (C : Nat → Prop)`, and in the context
`hgen : ∀ (l r : Nat), r ≤ n → ∀ (i : Nat), l ≤ i → i < r → C i` (the milestone).

| Before | After |
|---|---|
| `⊢ ∀ (i : Nat), i < n → C i` | closed |

**W2 · `none` means absent, for the linear scan.** `scan a t l r = none → a[i] ≠ t` on `[l, r)`. Only
`l` changes in `scan`'s recursion, so the arms name only `l`, and `hr : r ≤ a.size` is not carried
(the IH asks only for `h`). R9, then `case1` by R7; `case2` by `intro`, `by_cases hi : i = l`,
`subst hi` (R4) for the hit and R14 for the rest; `case3` by R15.

| Before | After |
|---|---|
| `hr : r ≤ a.size, h : scan a t l r = none ⊢ ∀ (i : Nat), l ≤ i → ∀ (h2 : i < r), a[i] ≠ t` | closed |

---

## Traps

- `fun_induction bsearch a key 0 a.size` runs but is useless (W3): generalise to `lo hi` first.
- A hypothesis is carried into the IH only if it mentions an argument that changes in the recursion
  (R2, R9). State `hsz` and `h` before the colon of the milestone, after `lo hi`, so they are carried.
- `∀ i, lo ≤ i → i < hi → a[i] ≠ key` fails with "failed to prove index is valid": the premise
  `i < hi` has no name, so `a[i]` cannot see it. Write `(hi2 : i < hi) →` and keep `hsz : hi ≤ a.size`
  in scope.
- `by_cases hi : i ≤ mid` inside `| case2 lo hi …` reuses the name `hi`: the range end becomes `hi✝`
  and can no longer be typed. Use a fresh name (`hle`).
- `omega` treats `a[i]` and `a[j]` as unrelated unknowns even when `i = j` (R13); `subst` first.
- In `case3` the IH's bound premise is `mid ≤ a.size`, not `hi ≤ a.size`: pass `(by omega)`, not `hsz`.
- Arm names bind by position: `| case2 lo hi hb mid hm hlt ih` (variables, `hb`, `mid`, the two
  inner conditions, `ih`). One name too many is an error ("Too many variable names provided").
- `t1 ; t2` runs `t2` on the first goal only; use one `with` arm per case or `<;>`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction along `bsearch`'s branches | `fun_induction bsearch a key lo hi with \| case1 lo hi hb mid hm => … \| …` | R1 |
| keep `h` usable in the IH | state `h` (and `hsz`) as hypotheses about `lo hi` | R2, R9 |
| `h : some x = some y` → `x = y` | `simp at h` | R3 |
| eliminate `i` using `h : mid = i` | `subst h` | R4 |
| `key` → `a[mid]` in the goal | `rw [← hm]` | TACTIC_STATES |
| `xs[i]? = some xs[i]` | `exact Array.getElem?_eq_getElem _` | R5 |
| recursive case of `some` | `exact ih h` | R6 |
| `h : none = some i` / `h : some m = none` | `simp at h` | R7 |
| `lo := 0`, `hi := a.size` | `gen a key 0 a.size i h` | R8 |
| left or right of `mid` | `by_cases hle : i ≤ mid` | R10 |
| use `Sorted a` | `have := hs i mid hle (by omega)` | R11 |
| bounds with `mid` | `omega` (sees `mid := (lo + hi) / 2`) | R12 |
| `a[i] ≤ a[mid] < key` → `a[i] ≠ key` | `omega` | R13 |
| recursive case of `none` | `exact ih hsz h i (by omega) h2` | R14 |
| empty range | `omega` | R15 |
| `≤` premises at `0`, `a.size` | `Nat.le_refl _`, `Nat.zero_le _` | R16 |
| see the state | infoview | |
