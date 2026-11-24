/- H018 | Kadane's maximum segment sum | 1-1.5 h | foldl invariant, List.IsInfix, List.IsSuffix, optimality spec, max
GOAL
  Kadane's one-pass algorithm returns the maximum sum over all contiguous segments of `xs` (the
  empty segment counts): it bounds the sum of every segment, and some segment attains it.

REFERENCE
  example : [2, 3] <:+: [1, 2, 3, 4] := ⟨[1], [4], rfl⟩   -- infix (segment): `∃ s t, s ++ ys ++ t = xs`
  example : [3, 4] <:+ [1, 2, 3, 4] := ⟨[1, 2], rfl⟩      -- suffix: `∃ t, t ++ ys = xs`
  #check List.suffix_concat_iff  -- l₁ <:+ l₂ ++ [a] ↔ l₁ = [] ∨ ∃ t, l₁ = t ++ [a] ∧ t <:+ l₂
  #check List.infix_concat_iff   -- l₁ <:+: l₂ ++ [a] ↔ l₁ <:+ l₂ ++ [a] ∨ l₁ <:+: l₂
  #check List.IsSuffix.isInfix   -- l₁ <:+ l₂ → l₁ <:+: l₂
  #check List.nil_infix          -- [] <:+: l      (also List.nil_suffix)
  #check List.eq_nil_of_infix_nil  -- l <:+: [] → l = []   (also List.eq_nil_of_suffix_nil)
  #check List.sum_append         -- (l₁ ++ l₂).sum = l₁.sum + l₂.sum
  #check List.foldl_cons         -- foldl f b (a :: l) = foldl f (f b a) l
  example (a b c : Int) (h : a ≤ c) (h' : b ≤ c) : max a b ≤ c := by omega  -- omega knows max
-/

namespace H018

-- BEGIN SPEC
/-- One step of Kadane's algorithm. State `(best, cur)`: `best` is the best segment sum seen so
    far, `cur` the best sum of a suffix of the prefix read so far (both ≥ 0: `[]` counts). -/
def kadaneStep (st : Int × Int) (x : Int) : Int × Int :=
  let cur := max 0 (st.2 + x)
  (max st.1 cur, cur)

def kadane (xs : List Int) : Int := (xs.foldl kadaneStep (0, 0)).1
-- END SPEC

-- MILESTONE (optional: change or delete)
-- The loop invariant after reading the prefix `p`: `st.1` is the maximum segment sum of `p`
-- and `st.2` the maximum suffix sum of `p` (each an upper bound that is attained).
def Inv (p : List Int) (st : Int × Int) : Prop :=
  (∀ ys, ys <:+: p → ys.sum ≤ st.1) ∧ (∀ ys, ys <:+ p → ys.sum ≤ st.2) ∧
  (∃ ys, ys <:+: p ∧ ys.sum = st.1) ∧ (∃ ys, ys <:+ p ∧ ys.sum = st.2)

-- MILESTONE (optional: change or delete)
theorem inv_nil : Inv [] (0, 0) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem inv_step (p : List Int) (st : Int × Int) (x : Int) (h : Inv p st) :
    Inv (p ++ [x]) (kadaneStep st x) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem inv_foldl (l p : List Int) (st : Int × Int) (h : Inv p st) :
    Inv (p ++ l) (l.foldl kadaneStep st) := by
  sorry

-- BEGIN SPEC
theorem kadane_upper (xs ys : List Int) (h : ys <:+: xs) : ys.sum ≤ kadane xs :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem kadane_attained (xs : List Int) : ∃ ys, ys <:+: xs ∧ ys.sum = kadane xs :=
-- END SPEC
  sorry

end H018

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems are projections of one invariant about `xs.foldl kadaneStep (0, 0)`; reading the input left to right, the new suffixes of `p ++ [x]` are `[]` and `t ++ [x]` for old suffixes `t`.
H2. `inv_step`: first prove the suffix half (bound with `List.suffix_concat_iff`, attainment by cases on `st.2 + x ≤ 0`), then the segment half with `List.infix_concat_iff`. `inv_foldl`: `induction l generalizing p st`, since the prefix read so far grows.
H3. Cons case of `inv_foldl`: `simpa using ih (p ++ [x]) _ (inv_step p st x h)`. Main theorems: `have hI : Inv xs (xs.foldl kadaneStep (0, 0)) := by simpa using inv_foldl xs [] (0, 0) inv_nil`; each theorem is then one projection of `hI`.
-/
