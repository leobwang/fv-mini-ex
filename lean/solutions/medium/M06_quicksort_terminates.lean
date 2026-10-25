/- M06 | Quicksort terminates | 15-20 min | decreasing_by, termination_by, fun_induction
GOAL
  Lean cannot see that quicksort's recursive calls are on shorter lists. Prove termination in
  `decreasing_by`, then prove `qsort` keeps exactly the same elements and the same length.

REFERENCE
  -- decreasing_by gets one goal per recursive call, e.g. ⊢ (lows p xs).length < (p :: xs).length
  #check List.length_filter_le   -- (p : α → Bool) (l : List α) : (List.filter p l).length ≤ l.length
  #check List.filter_append_perm -- (List.filter p l ++ List.filter (fun x => !p x) l).Perm l
  #check List.Perm.length_eq     -- l₁.Perm l₂ → l₁.length = l₂.length
  -- fun_induction f x  : induction that follows f's recursion (one case per branch, with IHs)
  example (xs : List Nat) : xs.length = xs.length := by fun_induction List.length xs <;> rfl
  `rw [ih]` before unfolding `lows`/`highs`, or the IH will no longer match.
-/

-- BEGIN SPEC
def lows (p : Nat) (xs : List Nat) : List Nat := xs.filter (· < p)
def highs (p : Nat) (xs : List Nat) : List Nat := xs.filter (fun x => ¬ x < p)
-- END SPEC

theorem lows_le (p : Nat) (xs : List Nat) : (lows p xs).length ≤ xs.length :=
  List.length_filter_le _ _

theorem highs_le (p : Nat) (xs : List Nat) : (highs p xs).length ≤ xs.length :=
  List.length_filter_le _ _

-- BEGIN SPEC
def qsort : List Nat → List Nat
  | [] => []
  | p :: xs => qsort (lows p xs) ++ p :: qsort (highs p xs)
termination_by xs => xs.length
-- END SPEC
decreasing_by
  · have := lows_le p xs; simp only [List.length_cons]; omega
  · have := highs_le p xs; simp only [List.length_cons]; omega

-- BEGIN SPEC
theorem mem_qsort (x : Nat) (xs : List Nat) : x ∈ qsort xs ↔ x ∈ xs :=
-- END SPEC
  by
    fun_induction qsort xs with
    | case1 => simp
    | case2 p xs ih1 ih2 =>
      rw [List.mem_append, List.mem_cons, ih1, ih2]
      simp only [lows, highs, List.mem_filter, decide_eq_true_eq]
      grind

-- BEGIN SPEC
theorem qsort_length (xs : List Nat) : (qsort xs).length = xs.length :=
-- END SPEC
  by
    fun_induction qsort xs with
    | case1 => rfl
    | case2 p xs ih1 ih2 =>
      rw [List.length_append, List.length_cons, ih1, ih2, List.length_cons]
      have := (List.filter_append_perm (fun x => decide (x < p)) xs).length_eq
      rw [List.length_append] at this
      unfold lows highs
      simp only [decide_not]
      omega

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The helper lemmas `lows_le` / `highs_le` are exactly what `decreasing_by` needs.
H2. In `decreasing_by`, handle the two goals with `·`: get the helper with `have`, unfold `List.length_cons`, `omega`.
H3. `· have := lows_le p xs; simp only [List.length_cons]; omega` (same for highs). For the theorems: `fun_induction qsort xs with | case1 => .. | case2 p xs ih1 ih2 => rw [List.mem_append, List.mem_cons, ih1, ih2]; ...`.
-/
