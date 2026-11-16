/- E062 | Bool vs Prop | 2-3 min | Bool, decide, = true, beq_iff_eq, List.all
GOAL
  Move between `Bool` computations (`&&`, `==`, `List.all`, `decide p`) and `Prop` statements
  (`∧`, `=`, `∀`, `p`). A Bool `b` is turned into a Prop as `b = true`.

REFERENCE
  example : decide (2 < 3) = true := rfl   -- `decide p : Bool` evaluates a decidable Prop `p`
  #check decide_eq_true       -- p → decide p = true
  #check of_decide_eq_true    -- decide p = true → p
  #check List.all_eq_true     -- l.all f = true ↔ ∀ x ∈ l, f x = true
  #check beq_iff_eq           -- (a == b) = true ↔ a = b   (`==` is Bool equality, `=` is Prop)
  #check Bool.and_eq_true     -- ((a && b) = true) = (a = true ∧ b = true)   an `=`, so use it with `rw`
  example (b : Bool) (h : b) : b = true := h   -- a Bool used as a Prop is coerced to `b = true`
BANNED: simp, simp_all, simpa, grind, decide, Bool.and_eq_true_iff, exact?, apply?, try?
NOTE: `decide` is banned as a tactic and as a term; the lemmas `decide_eq_true`, `of_decide_eq_true` are fine.
-/

namespace E062

-- BEGIN SPEC
def allPos (xs : List Nat) : Bool := xs.all (fun x => decide (0 < x))
-- END SPEC

-- BEGIN SPEC
theorem allPos_iff (xs : List Nat) : allPos xs = true ↔ ∀ x ∈ xs, 0 < x :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem decide_lt (n : Nat) : decide (n < n + 1) = true :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem beq_true_iff (m n : Nat) : (m == n) = true ↔ m = n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem coe_bool (b c : Bool) (h : b && c) : c = true :=
-- END SPEC
  sorry

end E062

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every item is one bridge lemma from the REFERENCE plus a little glue. `unfold allPos` shows the `List.all`.
H2. `allPos_iff`: rewrite with `List.all_eq_true`; each direction is `fun h x hx => …`, converting between
    `decide (0 < x) = true` and `0 < x`. `coe_bool`: `h` really has type `(b && c) = true`; rewrite it.
H3. `allPos_iff`: `⟨fun h x hx => of_decide_eq_true (h x hx), fun h x hx => decide_eq_true (h x hx)⟩`;
    `decide_lt`: `decide_eq_true (Nat.lt_add_one n)`; `coe_bool`: `rw [Bool.and_eq_true] at h; exact h.2`.
-/
