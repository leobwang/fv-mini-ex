/- H011 | Dutch national flag | 1-1.5 h | Array, swap, loop invariant, fun_induction [R19]
GOAL
  Dijkstra's one-pass three-way partition sorts an array of colours by swapping. Prove the
  result is a permutation of the input and is sorted by colour (all reds, then whites, then blues).

REFERENCE
  #check Array.swap_perm     -- (xs.swap i j h₁ h₂).Perm xs
  #check Array.Perm.trans    -- xs.Perm ys → ys.Perm zs → xs.Perm zs
  #check Array.getElem_swap  -- (xs.swap i j ..)[k] = if k = i then xs[j] else if k = j then xs[i] else xs[k]
  example (a : Array Nat) (h0 : 0 < a.size) (h1 : 1 < a.size) : (a.swap 0 1).size = a.size := by simp
  -- Loop state: [0, lo) red, [lo, mid) white, [mid, hi) unknown, [hi, size) blue.
  -- fun_induction dnfLoop a lo mid hi : cases red / white / blue (with `a[mid] = ...`) and exit.
  -- After `rw [Array.getElem_swap]`, use `split` twice and `omega` to kill impossible index cases.
-/

namespace H011

-- BEGIN SPEC
inductive Color where
  | red
  | white
  | blue
  deriving DecidableEq

def rank : Color → Nat
  | .red => 0
  | .white => 1
  | .blue => 2

def dnfLoop (a : Array Color) (lo mid hi : Nat) : Array Color :=
  if h : lo ≤ mid ∧ mid < hi ∧ hi ≤ a.size then
    match a[mid] with
    | .red => dnfLoop (a.swap lo mid) (lo + 1) (mid + 1) hi
    | .white => dnfLoop a lo (mid + 1) hi
    | .blue => dnfLoop (a.swap mid (hi - 1)) lo mid (hi - 1)
  else a
termination_by hi - mid

def dnf (a : Array Color) : Array Color := dnfLoop a 0 0 a.size

def SortedByColor (a : Array Color) : Prop :=
  ∀ i j (hij : i ≤ j) (hj : j < a.size), rank a[i] ≤ rank a[j]
-- END SPEC

-- MILESTONE (optional: change or delete)
def FlagInv (a : Array Color) (lo mid hi : Nat) : Prop :=
  lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ a.size ∧
  (∀ i (h : i < a.size), i < lo → a[i] = .red) ∧
  (∀ i (h : i < a.size), lo ≤ i → i < mid → a[i] = .white) ∧
  (∀ i (h : i < a.size), hi ≤ i → a[i] = .blue)

-- MILESTONE (optional: change or delete)
theorem loop_perm (a : Array Color) (lo mid hi : Nat) : (dnfLoop a lo mid hi).Perm a := by
  fun_induction dnfLoop a lo mid hi with
  | case1 a lo mid hi h hc ih => exact ih.trans (Array.swap_perm _ _)
  | case2 a lo mid hi h hc ih => exact ih
  | case3 a lo mid hi h hc ih => exact ih.trans (Array.swap_perm _ _)
  | case4 a lo mid hi h => exact .refl a

-- MILESTONE (optional: change or delete)
theorem loop_sorted (a : Array Color) (lo mid hi : Nat) (hinv : FlagInv a lo mid hi) :
    SortedByColor (dnfLoop a lo mid hi) := by
  fun_induction dnfLoop a lo mid hi with
  | case1 a lo mid hi h hc ih =>
    obtain ⟨h1, h2, h3, hr, hw, hb⟩ := hinv
    apply ih
    refine ⟨by omega, by omega, by simp; omega, ?_, ?_, ?_⟩
    · intro i hk hil
      rw [Array.getElem_swap]
      split
      · exact hc
      · split
        · have := hr lo (by omega)
          omega
        · exact hr i (by simpa using hk) (by omega)
    · intro i hk hil him
      rw [Array.getElem_swap]
      split
      · omega
      · split
        · exact hw lo (by omega) (by omega) (by omega)
        · exact hw i (by simpa using hk) (by omega) (by omega)
    · intro i hk hil
      rw [Array.getElem_swap]
      split
      · omega
      · split
        · omega
        · exact hb i (by simpa using hk) hil
  | case2 a lo mid hi h hc ih =>
    obtain ⟨h1, h2, h3, hr, hw, hb⟩ := hinv
    apply ih
    refine ⟨by omega, by omega, h3, hr, ?_, hb⟩
    intro i hk hil him
    by_cases him' : i = mid
    · subst him'; exact hc
    · exact hw i hk hil (by omega)
  | case3 a lo mid hi h hc ih =>
    obtain ⟨h1, h2, h3, hr, hw, hb⟩ := hinv
    apply ih
    refine ⟨by omega, by omega, by simp; omega, ?_, ?_, ?_⟩
    · intro i hk hil
      rw [Array.getElem_swap]
      split
      · omega
      · split
        · omega
        · exact hr i (by simpa using hk) hil
    · intro i hk hil him
      rw [Array.getElem_swap]
      split
      · omega
      · split
        · omega
        · exact hw i (by simpa using hk) hil him
    · intro i hk hil
      rw [Array.getElem_swap]
      split
      · have e : hi - 1 = mid := by omega
        simp only [e]
        exact hc
      · split
        · exact hc
        · exact hb i (by simpa using hk) (by omega)
  | case4 a lo mid hi h =>
    obtain ⟨h1, h2, h3, hr, hw, hb⟩ := hinv
    have hmid : mid = hi := by omega
    subst hmid
    intro i j hij hj
    by_cases hi1 : i < lo
    · rw [hr i (by omega) hi1]; simp [rank]
    · by_cases hi2 : i < mid
      · rw [hw i (by omega) (by omega) hi2]
        by_cases hj2 : j < mid
        · rw [hw j hj (by omega) hj2]; exact Nat.le_refl _
        · rw [hb j hj (by omega)]; simp [rank]
      · rw [hb i (by omega) (by omega), hb j hj (by omega)]; exact Nat.le_refl _

-- BEGIN SPEC
theorem dnf_perm (a : Array Color) : (dnf a).Perm a :=
-- END SPEC
  loop_perm a 0 0 a.size

-- BEGIN SPEC
theorem dnf_sorted (a : Array Color) : SortedByColor (dnf a) :=
-- END SPEC
  loop_sorted a 0 0 a.size ⟨by omega, by omega, by omega, fun i _ h => absurd h (by omega),
    fun i _ _ h2 => absurd h2 (by omega), fun i h h2 => absurd h (by omega)⟩

end H011

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Permutation is easy (each step is a swap). Sortedness needs a loop invariant on `(a, lo, mid, hi)`, which `FlagInv` states.
H2. Show each branch preserves `FlagInv` (then the IH applies), and that at exit (`mid = hi`) the invariant implies `SortedByColor`. Every index lies in exactly one of the four regions.
H3. Red case: after `rw [Array.getElem_swap]; split; split`, the new red cell is `a[mid]` (= red), and the new white cell at `mid` is the old `a[lo]` (white when `lo < mid`). Blue case: the new blue cell at `hi - 1` is the old `a[mid]`.
-/
