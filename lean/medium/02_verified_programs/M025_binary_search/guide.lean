/- Guide for M025 (Binary search).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` (or `C`) stands for "the rest of your goal": the step changes only the part shown inside `P (…)`.
A hypothesis `h…` in an entry is only there to finish the example; it shows what the goal became.
The `fun_induction` entries use the guide's own function `probe` (a bisection that looks for a `0`
and steers by parity, NOT the exercise's search); the case alternatives are written `=> ?_` so that
every case stays open as a goal you can inspect. In a proof you write tactics after `=>` instead.
Part W: worked combinations on `probe` and on the linear scan `scan`, not on the exercise's objects.
Assumed: Lean basics (E001–E033). No Mathlib: everything here is core Lean.
-/

namespace M025Guide

/-- `probe a l r`: look at the middle index `m` of the range `[l, r)`. Return `some m` if `a[m] = 0`;
otherwise continue in `(m, r)` if `a[m]` is odd and in `[l, m)` if it is even. Well-founded
recursion on the width `r - l`, with a `let` for the middle index. -/
def probe (a : Array Nat) (l r : Nat) : Option Nat :=
  if h : l < r ∧ r ≤ a.size then
    let m := (l + r) / 2
    if a[m] = 0 then some m
    else if a[m] % 2 = 1 then probe a (m + 1) r
    else probe a l m
  else none
termination_by r - l

/-- `scan a t l r`: the first index `i` in `[l, r)` with `a[i] = t`, scanning left to right. -/
def scan (a : Array Nat) (t : Nat) (l r : Nat) : Option Nat :=
  if h : l < r ∧ r ≤ a.size then
    if a[l] = t then some l else scan a t (l + 1) r
  else none
termination_by r - l

/-- A non-increasing array: a later entry is never larger. A `def` whose body is a `∀`. -/
def Desc (a : Array Nat) : Prop := ∀ i j (hij : i ≤ j) (hj : j < a.size), a[j] ≤ a[i]

/-! # Part R · Reference entries -/

/-! ## Following the function's branches -/

/-! ### R1. `fun_induction f a l r with | case1 … => … | …` · goal list: one goal per branch
`if h : c then (let m := e; if c₁ then … else if c₂ then … else …) else …` has four branches, so four
goals `case1 … case4` in source order. Each arm names, in order: the varying arguments `l r`, the
outer condition `hb`, the `let` variable `m` (it stays in the context as `m : Nat := e`), the inner
conditions, then one IH per recursive call. In each goal the call `f a l r` is already replaced by
that branch's right-hand side. -/
example (a : Array Nat) (l r : Nat) (P : Nat → Nat → Option Nat → Prop)
    (h1 : ∀ l r m, P l r (some m))
    (h2 : ∀ l r m, P l r (probe a (m + 1) r))
    (h3 : ∀ l r m, P l r (probe a l m))
    (h4 : ∀ l r, P l r none) : P l r (probe a l r) := by
  fun_induction probe a l r with
    | case1 l r hb m hm => ?_
    | case2 l r hb m hm hodd ih => ?_
    | case3 l r hb m hm hodd ih => ?_
    | case4 l r hb => ?_
  · exact h1 l r m
  · exact h2 l r m
  · exact h3 l r m
  · exact h4 l r

/-! ### R2. A hypothesis about the call · context: it is rewritten in every case and becomes a premise
of every IH
`h : probe a l r = some i` mentions `l r`, so `fun_induction` takes it into the induction: in each
case `h` is about that branch's right-hand side, and `ih` reads `probe a … = some i → …`. -/
example (a : Array Nat) (l r i : Nat) (h : probe a l r = some i) (C : Nat → Nat → Prop)
    (h1 : ∀ l r, C l r) : C l r := by
  fun_induction probe a l r with
    | case1 l r hb m hm => ?_
    | case2 l r hb m hm hodd ih => ?_
    | case3 l r hb m hm hodd ih => ?_
    | case4 l r hb => ?_
  all_goals exact h1 _ _

/-! ## Options and array lookups -/

/-! ### R3. `simp at h` on `h : some x = some y` · context: `h` becomes `x = y`
`simp` uses `Option.some.injEq : (some x = some y) = (x = y)` (the constructor `some` is injective). -/
example (x y : Nat) (h : some x = some y) (P : Nat → Prop) (hp : P x) : P y := by
  simp at h
  rw [← h]
  exact hp

/-! ### R4. `subst h` with `h : x = y` and `y` a local variable · context: `y` disappears;
goal: `y` → `x` everywhere -/
example (x y : Nat) (h : x = y) (P : Nat → Prop) (hp : P x) : P y := by
  subst h
  exact hp

/-! ### R5. `Array.getElem?_eq_getElem` · `(h : i < xs.size) → xs[i]? = some xs[i]` · closes the goal
`xs[i]?` is the lookup that returns an `Option` (`none` out of bounds); `xs[i]` is the lookup that
needs a proof of `i < xs.size`. In bounds they agree. Give `_` for `h`: Lean reads it off the goal. -/
example (xs : Array Nat) (i : Nat) (hi : i < xs.size) : xs[i]? = some xs[i] := by
  exact Array.getElem?_eq_getElem _

/-! ### R6. `exact ih h` · closes the goal: the IH applied to the carried hypothesis (R2) -/
example (Q C : Prop) (ih : Q → C) (h : Q) : C := by
  exact ih h

/-! ### R7. `simp at h` on `h : none = some y` (or `some x = none`) · closes the goal
The two sides start with different constructors, so `simp` turns `h` into `False`, and a goal with
`h : False` in the context is closed. -/
example (y : Nat) (h : none = some y) (P : Prop) : P := by
  simp at h

/-! ### R8. Specialise a general fact · closes the goal
A fact proved for all `l r` (here `hgen`) gives the instance `l := 0`, `r := n` by application. -/
example (n i : Nat) (Q : Nat → Nat → Nat → Prop) (C : Nat → Prop)
    (hgen : ∀ l r i, Q l r i → C i) (h : Q 0 n i) : C i := by
  exact hgen 0 n i h

/-! ## Ranges, sortedness and `omega` -/

/-! ### R9. Two carried hypotheses · context: both become IH premises; an unrelated one stays put
`hr : r ≤ a.size` and `h : probe a l r = none` mention `l r` and are carried (R2); `hq : Q` does not
and stays as it is. Note `case3`: the IH premise is `m ≤ a.size`, about the recursive call's bound. -/
example (a : Array Nat) (l r : Nat) (Q : Prop) (hq : Q) (hr : r ≤ a.size)
    (h : probe a l r = none) (C : Nat → Nat → Prop) (h1 : ∀ l r, Q → C l r) : C l r := by
  fun_induction probe a l r with
    | case1 l r hb m hm => ?_
    | case2 l r hb m hm hodd ih => ?_
    | case3 l r hb m hm hodd ih => ?_
    | case4 l r hb => ?_
  all_goals exact h1 _ _ hq

/-! ### R10. `by_cases hle : i ≤ m` · goal list: two goals, with `hle : i ≤ m` and with `hle : ¬i ≤ m`
Pick a name not already in the context: reusing one hides the old hypothesis (it shows as `name✝`). -/
example (i m : Nat) (P : Prop) (h1 : i ≤ m → P) (h2 : ¬i ≤ m → P) : P := by
  by_cases hle : i ≤ m
  · exact h1 hle
  · exact h2 hle

/-! ### R11. `have := hs i j hij (by omega)` · context gains `this`
`hs : Desc a` is a `def` whose body is a `∀`, so `hs` applies like a function, one argument per
binder. `(by omega)` proves the bound argument `j < a.size` on the spot. `have :=` without a name
calls the new fact `this`. -/
example (a : Array Nat) (hs : Desc a) (i j n : Nat) (hij : i ≤ j) (hj : j < n) (hn : n ≤ a.size)
    (P : Prop) (hp : a[j] ≤ a[i] → P) : P := by
  have := hs i j hij (by omega)
  exact hp this

/-! ### R12. `omega` · reads a `let` variable's value: closes `m < n` from `m : Nat := (l + r) / 2`
`omega` also takes apart `∧` in a hypothesis, and knows `/ 2`. -/
example (l r n : Nat) (hb : l < r ∧ r ≤ n) : let m := (l + r) / 2; m < n := by
  intro m
  omega

/-! ### R13. `omega` · array entries are unknown numbers: closes `a[j] ≠ t` from linear facts
Each `a[i]` is one opaque number to `omega`, so it chains `a[i] ≤ a[j]` with `¬a[i] < t`; it reads
`¬`, `≠`, `<`, `≤`. It does NOT know `a[i] = a[j]` from `i = j` (use `subst`, R4). -/
example (a : Array Nat) (i j t : Nat) (hi : i < a.size) (hj : j < a.size) (hm : ¬a[i] = t)
    (hlt : ¬a[i] < t) (this : a[i] ≤ a[j]) : a[j] ≠ t := by
  omega

/-! ### R14. `exact ih hr h i (by omega) h2` · closes the goal: an IH with premises, fed in order
The IH's premises are the carried hypotheses (R9), then the `∀ i` and its range conditions; a premise
that is not literally in the context (`m + 1 ≤ i`, or `m ≤ a.size` in `case3`) gets `(by omega)`. -/
example (n r m : Nat) (Q : Prop) (C : Nat → Prop) (hr : r ≤ n) (h : Q)
    (ih : r ≤ n → Q → ∀ i, m + 1 ≤ i → i < r → C i)
    (i : Nat) (h2 : i < r) (hi : ¬i ≤ m) : C i := by
  exact ih hr h i (by omega) h2

/-! ### R15. `omega` · closes any goal whose hypotheses contradict each other
In the empty branch `hb : ¬(l < r ∧ r ≤ n)` contradicts `l ≤ i`, `i < r`, `r ≤ n`. -/
example (l r n i : Nat) (hb : ¬(l < r ∧ r ≤ n)) (hr : r ≤ n) (h1 : l ≤ i) (h2 : i < r)
    (P : Prop) : P := by
  omega

/-! ### R16. `exact fun i hi => hgen 0 n (Nat.le_refl n) i (Nat.zero_le i) hi` · closes the goal
`fun i hi => …` is `intro i hi` in term mode. `Nat.le_refl n : n ≤ n` and `Nat.zero_le i : 0 ≤ i`
discharge the premises that the specialisation `l := 0`, `r := n` makes trivial. -/
example (n : Nat) (C : Nat → Prop) (hgen : ∀ l r, r ≤ n → ∀ i, l ≤ i → i < r → C i) :
    ∀ i, i < n → C i := by
  exact fun i hi => hgen 0 n (Nat.le_refl n) i (Nat.zero_le i) hi

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A `some` result lies in the range: R1 + R2, then R3, R4 and `omega`; R7 for `case4` -/
example (a : Array Nat) (l r i : Nat) (h : probe a l r = some i) : l ≤ i ∧ i < r := by
  fun_induction probe a l r with
    | case1 l r hb m hm =>
      simp at h
      subst h
      omega
    | case2 l r hb m hm hodd ih =>
      have := ih h
      omega
    | case3 l r hb m hm hodd ih =>
      have := ih h
      omega
    | case4 l r hb => simp at h

/-! ### W2. `none` means absent, for the linear scan: R9, R7, then `intro`, a case split, R14, R15
Only `l` varies in `scan`'s recursion (`r` is passed unchanged), so the arms name only `l`, and
`hr : r ≤ a.size`, which does not mention `l`, is NOT carried: the IH asks only for `h`. In the
hit-or-skip branch, `i = l` is handled by `subst` (R4) because `omega` cannot use it (R13). The
binder `(h2 : i < r)` is named so that `a[i]` can find its bound (see the cheatsheet's Traps). -/
example (a : Array Nat) (t l r : Nat) (hr : r ≤ a.size) (h : scan a t l r = none) :
    ∀ i, l ≤ i → (h2 : i < r) → a[i] ≠ t := by
  fun_induction scan a t l r with
    | case1 l hb hm => simp at h
    | case2 l hb hm ih =>
      intro i h1 h2
      by_cases hi : i = l
      · subst hi
        exact hm
      · exact ih h i (by omega) h2
    | case3 l hb =>
      intro i h1 h2
      omega

/-! ### W3. Why generalise first: `fun_induction` on the constants `0 a.size`
The arguments are not variables, so `h` is NOT carried (compare R2): every case keeps the useless
`h : probe a 0 a.size = some i`, and each IH is just the goal again. (A goal that mentions `0` or
`a.size` is worse: they are replaced by fresh `l✝ r✝`, and `0 ≤ i` becomes the false `l✝ ≤ i`.) -/
example (a : Array Nat) (i : Nat) (h : probe a 0 a.size = some i) (C : Nat → Prop)
    (hc : probe a 0 a.size = some i → C i) : C i := by
  fun_induction probe a 0 a.size
  all_goals exact hc h

end M025Guide
