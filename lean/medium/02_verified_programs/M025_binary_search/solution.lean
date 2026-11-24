/- M025 | Binary search | 20 min | Array, termination_by, fun_induction, range invariant [R09]
GOAL
  Prove binary search on a sorted `Array Nat` correct: a returned index holds the key, and
  `none` means the key is absent.

REFERENCE
  example (a : Array Nat) (i : Nat) (h : i < a.size) : a[i]? = some a[i] := Array.getElem?_eq_getElem h
  example (a : Array Nat) (i j : Nat) (hi : i ≤ j) (hj : j < a.size) : Nat := a[i]  -- bound by omega
  -- fun_induction bsearch a key lo hi  → one case per branch (found / go right / go left / empty),
  -- with the `if` conditions as hypotheses and IHs for the recursive calls.
  -- The top-level theorems fix lo = 0, hi = a.size: state general versions for any lo, hi first.
  -- Invariant for `none`: the key is not at any index in [lo, hi).
-/

namespace M025

-- BEGIN SPEC
def Sorted (a : Array Nat) : Prop := ∀ i j (hi : i ≤ j) (hj : j < a.size), a[i] ≤ a[j]

def bsearch (a : Array Nat) (key : Nat) (lo hi : Nat) : Option Nat :=
  if h : lo < hi ∧ hi ≤ a.size then
    let mid := (lo + hi) / 2
    if a[mid] = key then some mid
    else if a[mid] < key then bsearch a key (mid + 1) hi
    else bsearch a key lo mid
  else none
termination_by hi - lo
-- END SPEC

theorem bsearch_some_gen (a : Array Nat) (key lo hi i : Nat) (h : bsearch a key lo hi = some i) :
    a[i]? = some key := by
  fun_induction bsearch a key lo hi with
  | case1 lo hi hb mid hm =>
    simp at h
    subst h
    rw [← hm]
    exact Array.getElem?_eq_getElem _
  | case2 lo hi hb mid hm hlt ih => exact ih h
  | case3 lo hi hb mid hm hlt ih => exact ih h
  | case4 lo hi hb => simp at h

theorem bsearch_none_gen (a : Array Nat) (key lo hi : Nat) (hs : Sorted a) (hsz : hi ≤ a.size)
    (h : bsearch a key lo hi = none) : ∀ i (_ : lo ≤ i) (hi2 : i < hi), a[i] ≠ key := by
  fun_induction bsearch a key lo hi with
  | case1 lo hi hb mid hm => simp at h
  | case2 lo hi hb mid hm hlt ih =>
    intro i h1 h2
    by_cases hi : i ≤ mid
    · have := hs i mid hi (by omega)
      omega
    · exact ih hsz h i (by omega) h2
  | case3 lo hi hb mid hm hlt ih =>
    intro i h1 h2
    by_cases hi : mid ≤ i
    · have := hs mid i hi (by omega)
      omega
    · exact ih (by omega) h i h1 (by omega)
  | case4 lo hi hb =>
    intro i h1 h2
    omega

-- BEGIN SPEC
theorem bsearch_some (a : Array Nat) (key i : Nat) (h : bsearch a key 0 a.size = some i) :
    a[i]? = some key :=
-- END SPEC
  bsearch_some_gen a key 0 a.size i h

-- BEGIN SPEC
theorem bsearch_none (a : Array Nat) (key : Nat) (hs : Sorted a)
    (h : bsearch a key 0 a.size = none) : ∀ i (hi : i < a.size), a[i] ≠ key :=
-- END SPEC
  fun i hi => bsearch_none_gen a key 0 a.size hs (Nat.le_refl _) h i (Nat.zero_le _) hi

end M025

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Generalise: prove both facts for arbitrary `lo hi` (with `hi ≤ a.size` for the `none` case), then specialise.
H2. `none` case "go right" (`a[mid] < key`): indices ≤ mid hold values ≤ a[mid] < key by sortedness; the rest come from the IH. "Go left" is symmetric.
H3. `theorem bsearch_none_gen (a key lo hi) (hs : Sorted a) (hsz : hi ≤ a.size) (h : bsearch a key lo hi = none) : ∀ i, lo ≤ i → (hi2 : i < hi) → a[i] ≠ key` by `fun_induction bsearch a key lo hi`.
-/
