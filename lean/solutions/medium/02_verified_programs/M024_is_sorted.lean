/- M024 | Is sorted | 15 min | List.Pairwise, Bool vs Prop, fun_induction [R08]
GOAL
  Implement a Boolean check `isSorted` that compares adjacent elements, and prove it returns
  `true` exactly when every earlier element is ≤ every later one (`List.Pairwise`).

REFERENCE
  -- xs.Pairwise R : R holds for every pair (earlier, later), i.e. ∀ i < j, R xs[i] xs[j]
  #check List.pairwise_cons   -- Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l
  #check List.Pairwise.cons   -- (∀ a' ∈ l, R a a') → Pairwise R l → Pairwise R (a :: l)
  #check List.rel_of_pairwise_cons   -- Pairwise R (a :: l) → a' ∈ l → R a a'
  #check List.Pairwise.of_cons       -- Pairwise R (a :: l) → Pairwise R l
  #check Bool.and_eq_true   -- ((a && b) = true) = (a = true ∧ b = true)   (use in simp only [..])
-/

namespace M024

-- BEGIN SPEC
def isSorted (xs : List Nat) : Bool :=
-- END SPEC
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x ≤ y) && isSorted (y :: rest)

-- BEGIN SPEC
theorem isSorted_iff (xs : List Nat) : isSorted xs = true ↔ xs.Pairwise (· ≤ ·) :=
-- END SPEC
  by
    fun_induction isSorted xs with
    | case1 => simp
    | case2 x => simp
    | case3 x y rest ih =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨hxy, hp⟩
        refine List.Pairwise.cons ?_ hp
        intro a ha
        rw [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact hxy
        · exact Nat.le_trans hxy (List.rel_of_pairwise_cons hp ha)
      · intro h
        exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, h.of_cons⟩

end M024

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Three cases: empty, singleton, and `x :: y :: rest` (compare `x ≤ y`, recurse on `y :: rest`).
H2. `fun_induction isSorted xs` gives the IH for `y :: rest`. For →, transitivity turns "x ≤ y and y ≤ everything later" into "x ≤ everything later".
H3. → : `refine List.Pairwise.cons ?_ hp` then case on `a ∈ y :: rest`; ← : `⟨List.rel_of_pairwise_cons h List.mem_cons_self, h.of_cons⟩`.
-/
