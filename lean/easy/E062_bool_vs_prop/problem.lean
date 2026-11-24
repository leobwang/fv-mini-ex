/- E062 | Bool vs Prop | 2-3 min | Bool, decide, = true, beq_iff_eq, List.all
GOAL
  Move between `Bool` computations (`&&`, `==`, `List.all`, `decide p`) and `Prop` statements
  (`∧`, `=`, `∀`, `p`). A Bool `b` is turned into a Prop as `b = true`.

BANNED: simp, simp_all, simpa, grind, decide, Bool.and_eq_true_iff, exact?, apply?, try?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E062

-- BEGIN SPEC
def allPos (xs : List Nat) : Bool := xs.all (fun x => decide (0 < x))
-- END SPEC

/- SKELETON · allPos_iff
  1. Show the Bool test inside `allPos`:                                        R1
  2. Bool `all … = true` → Prop `∀ x, x ∈ xs → decide (0 < x) = true`:           R2
  3. Split the `↔` into two functions `fun h x hx => …`:                         R3
  4. → direction: `h x hx : decide (0 < x) = true`; turn it into `0 < x`:        R4
     ← direction: `h x hx : 0 < x`; turn it into `decide (0 < x) = true`:        R5
-/
-- BEGIN SPEC
theorem allPos_iff (xs : List Nat) : allPos xs = true ↔ ∀ x ∈ xs, 0 < x :=
-- END SPEC
  sorry

/- SKELETON · decide_lt
  1. Reduce `decide (n < n + 1) = true` to a proof of `n < n + 1`:              R5
  2. That proof is a core `Nat` lemma:                                          R6
-/
-- BEGIN SPEC
theorem decide_lt (n : Nat) : decide (n < n + 1) = true :=
-- END SPEC
  sorry

/- SKELETON · and_true_iff
  1. Rewrite Bool `&&` into Prop `∧` on the left; `rw` then closes `X ↔ X`:     R7
-/
-- BEGIN SPEC
theorem and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true :=
-- END SPEC
  sorry

/- SKELETON · beq_true_iff
  1. The statement is the library lemma for lawful `==` at `α := Nat`; give it
     as the whole proof (term mode):                                           R8
-/
-- BEGIN SPEC
theorem beq_true_iff (m n : Nat) : (m == n) = true ↔ m = n :=
-- END SPEC
  sorry

/- SKELETON · coe_bool
  1. Read the hypothesis: `h : b && c` is `h : (b && c) = true`:                R9
  2. Rewrite `&&` into `∧` inside `h`:                                          R10
  3. The goal is the right half of `h`:                                         R11
-/
-- BEGIN SPEC
theorem coe_bool (b c : Bool) (h : b && c) : c = true :=
-- END SPEC
  sorry

end E062

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every item is one bridge lemma between a Bool operation and its Prop meaning, plus a little glue:
    `List.all` ↔ `∀` (R2), `decide p = true` ↔ `p` (R4, R5), `&&` ↔ `∧` (R7), `==` ↔ `=` (R8). A Bool `b`
    used as a Prop means `b = true` (R9). `simp` and `decide` are banned, so name each lemma.
H2. `allPos_iff`: `unfold allPos`, `rw [List.all_eq_true]`, then an anonymous pair of functions
    `fun h x hx => …` converting `decide (0 < x) = true` and `0 < x`. `decide_lt`: `decide_eq_true` of a
    proof of `n < n + 1`. `and_true_iff`: `Bool.and_eq_true` is an `=` of Props, so `rw`, not `exact`.
    `beq_true_iff`: one lemma. `coe_bool`: `h` really has type `(b && c) = true`; rewrite it, take a half.
H3. `allPos_iff`: `⟨fun h x hx => of_decide_eq_true (h x hx), fun h x hx => decide_eq_true (h x hx)⟩`;
    `decide_lt`: `decide_eq_true (Nat.lt_add_one n)`; `coe_bool`: `rw [Bool.and_eq_true] at h; exact h.2`.
-/
