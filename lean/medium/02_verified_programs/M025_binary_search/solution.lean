/- M025 | Binary search | 20 min | Array, termination_by, fun_induction, range invariant [R09]
GOAL
  Prove binary search on a sorted `Array Nat` correct: a returned index holds the key, and
  `none` means the key is absent.

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · bsearch_some
  1. MILESTONE first, for every range (the induction needs `lo hi` to vary; cheatsheet W3).
     Write it above this SKELETON, outside the SPEC markers:
       theorem bsearch_some_gen (a : Array Nat) (key lo hi i : Nat)
           (h : bsearch a key lo hi = some i) : a[i]? = some key
     a. `fun_induction bsearch a key lo hi with` one arm per branch:
        `case1 lo hi hb mid hm`, `case2 lo hi hb mid hm hlt ih`, `case3 …` (same names),
        `case4 lo hi hb`; `h` is carried into every case and every IH                 R1, R2
     b. case1 (hit, `h : some mid = some i`): `h` → `mid = i`, eliminate `i`,
        turn `some key` into `some a[mid]`, then the lookup lemma                     R3, R4, rw [← hm], R5
     c. case2, case3 (recursive calls): the IH applied to `h`                         R6
     d. case4 (`h : none = some i`): contradiction                                    R7
  2. bsearch_some: the milestone at lo := 0, hi := a.size                             R8
-/
-- BEGIN SPEC
theorem bsearch_some (a : Array Nat) (key i : Nat) (h : bsearch a key 0 a.size = some i) :
    a[i]? = some key :=
-- END SPEC
  bsearch_some_gen a key 0 a.size i h

/- SKELETON · bsearch_none
  1. MILESTONE first, with the range invariant "key is not at any index in [lo, hi)".
     Write it above this SKELETON, outside the SPEC markers:
       theorem bsearch_none_gen (a : Array Nat) (key lo hi : Nat) (hs : Sorted a)
           (hsz : hi ≤ a.size) (h : bsearch a key lo hi = none) :
           ∀ i (_ : lo ≤ i) (hi2 : i < hi), a[i] ≠ key
     (`hsz` and the NAMED binder `hi2` are what let `a[i]` find its bound.)
     a. `fun_induction bsearch a key lo hi with` the same arms as above; `hsz` and `h`
        become IH premises, `hs` stays as it is (in case3 the bound premise is
        `mid ≤ a.size`)                                                               R1, R9
     b. case1 (`h : some mid = none`): contradiction                                  R7
     c. case2 (`a[mid] < key`, go right): `intro i h1 h2`, split on `i ≤ mid`
        (a fresh name such as `hle`; `hi` would hide the range end as `hi✝`)         R10
          i ≤ mid: sortedness gives `a[i] ≤ a[mid]` (bound by omega), then arithmetic  R11, R12, R13
          ¬i ≤ mid: the IH, with the range premise `mid + 1 ≤ i` by omega              R14
     d. case3 (go left): the mirror image, split on `mid ≤ i`
          mid ≤ i: `a[mid] ≤ a[i]` with `¬a[mid] < key` and `¬a[mid] = key`            R11, R12, R13
          ¬mid ≤ i: the IH; its bound premise `mid ≤ a.size` and `i < mid` by omega     R14
     e. case4 (empty range): `intro i h1 h2`; the range contradicts `hb`               R15
  2. bsearch_none: the milestone at lo := 0, hi := a.size; `Nat.le_refl` for the bound,
     `Nat.zero_le` for `0 ≤ i`                                                          R16
-/
-- BEGIN SPEC
theorem bsearch_none (a : Array Nat) (key : Nat) (hs : Sorted a)
    (h : bsearch a key 0 a.size = none) : ∀ i (hi : i < a.size), a[i] ≠ key :=
-- END SPEC
  fun i hi => bsearch_none_gen a key 0 a.size hs (Nat.le_refl _) h i (Nat.zero_le _) hi

end M025

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems fix `lo = 0`, `hi = a.size`, but `fun_induction` needs them to vary: prove a general
    MILESTONE for every `lo hi` (with `hsz : hi ≤ a.size` for the `none` case), then specialise (R8, R16).
H2. `fun_induction bsearch a key lo hi` gives four cases (hit / go right / go left / empty), with `h`
    (and `hsz`) carried into every IH. `some`: the hit by `simp at h` and `subst h`, the recursive calls
    by `ih h`, the empty range by `simp at h`. `none`: in "go right" (`a[mid] < key`) split on `i ≤ mid`:
    indices ≤ mid hold values ≤ a[mid] < key by sortedness; the rest come from the IH. "Go left" is
    symmetric; the empty range is `omega`.
H3. `theorem bsearch_none_gen (a key lo hi) (hs : Sorted a) (hsz : hi ≤ a.size) (h : bsearch a key lo hi = none) : ∀ i (_ : lo ≤ i) (hi2 : i < hi), a[i] ≠ key`.
    Go right: `by_cases hle : i ≤ mid`, then `have := hs i mid hle (by omega); omega` or
    `exact ih hsz h i (by omega) h2`. Hit of `some`: `simp at h; subst h; rw [← hm]; exact Array.getElem?_eq_getElem _`.
-/
