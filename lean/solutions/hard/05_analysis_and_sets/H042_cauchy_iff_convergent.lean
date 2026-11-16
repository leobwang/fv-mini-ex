/- H042 | Cauchy ⇔ convergent in ℝ | 45-75 min | Cauchy sequences, completeness, sSup, epsilon-N, mathlib
GOAL
  A real sequence is Cauchy iff it converges, with explicit ε-N definitions (`|x|` is absolute value).
  For "Cauchy → convergent", build the limit yourself as a supremum: `L = sSup S`, where
  `S = {x | ∃ M, ∀ n ≥ M, x < a n}` is the set of eventual strict lower bounds of `a`.

REFERENCE
  #check le_csSup      -- BddAbove s → a ∈ s → a ≤ sSup s     (`sSup s`: least upper bound of s)
  #check csSup_le      -- s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a
  #check abs_lt        -- |a| < b ↔ -b < a ∧ a < b
  #check abs_add_le    -- |a + b| ≤ |a| + |b|     (triangle inequality)
  #check abs_sub_comm  -- |a - b| = |b - a|
  #check le_max_left   -- a ≤ max a b     (and le_max_right)
  example (S : Set ℝ) (M : ℝ) (h : ∀ y ∈ S, y ≤ M) : BddAbove S := ⟨M, h⟩
  example (x : ℝ) : x ∈ {y : ℝ | y < 1} ↔ x < 1 := Iff.rfl   -- set-builder membership unfolds
  -- `set S : Set ℝ := {x | ...}` names the set;  `rw [abs_lt] at h ⊢` then `linarith`
BANNED: import, CauSeq, IsCauSeq, LimZero, IsComplete, isComplete, complete, lim, equiv_lim, cauSeq_converges
BANNED: eq_lim_of_const_equiv, lim_eq_of_equiv_const, lim_le, le_lim, lim_lt, lt_lim, instIsCompleteAbs, Real.cauchy, ofCauchy
BANNED: Real.mk_near_of_forall_near, Real.mk_le_of_forall_le
NOTE: imports are frozen (no `import` may be added): ℝ's order and `sSup`, no filters or topology. `CauSeq` is banned.
-/
-- BEGIN SPEC
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
-- END SPEC

namespace H042

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

-- BEGIN SPEC
def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem converges_cauchy (a : ℕ → ℝ) (L : ℝ) (h : ConvergesTo a L) : IsCauchy a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := hN m hm
  have h2 := hN n hn
  calc |a m - a n| = |(a m - L) + (L - a n)| := by ring_nf
    _ ≤ |a m - L| + |L - a n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by rw [abs_sub_comm L]; exact add_lt_add h1 h2
    _ = ε := by ring

-- MILESTONE (optional: change or delete)
-- If the tail from `N` is ε-close, then `a N - ε` is an eventual lower bound ...
theorem tail_lower (a : ℕ → ℝ) (ε : ℝ) (N : ℕ) (hN : ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε) :
    a N - ε ∈ {x | ∃ M, ∀ n ≥ M, x < a n} := by
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn N le_rfl
  rw [abs_lt] at h
  linarith

-- MILESTONE (optional: change or delete)
-- ... and every eventual lower bound is at most `a N + ε`.
theorem tail_bound (a : ℕ → ℝ) (ε : ℝ) (N : ℕ) (hN : ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε) :
    ∀ x ∈ {x | ∃ M, ∀ n ≥ M, x < a n}, x ≤ a N + ε := by
  rintro x ⟨M, hM⟩
  have h1 := hM (max M N) (le_max_left _ _)
  have h2 := hN (max M N) (le_max_right _ _) N le_rfl
  rw [abs_lt] at h2
  linarith

-- BEGIN SPEC
theorem cauchy_iff_converges (a : ℕ → ℝ) : IsCauchy a ↔ ∃ L, ConvergesTo a L :=
-- END SPEC
  by
    constructor
    · intro h
      set S : Set ℝ := {x | ∃ M, ∀ n ≥ M, x < a n}
      obtain ⟨N0, hN0⟩ := h 1 one_pos
      have hne : S.Nonempty := ⟨_, tail_lower a 1 N0 hN0⟩
      have hbdd : BddAbove S := ⟨_, tail_bound a 1 N0 hN0⟩
      refine ⟨sSup S, fun ε hε => ?_⟩
      obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
      refine ⟨N, fun n hn => ?_⟩
      have h1 : a N - ε / 2 ≤ sSup S := le_csSup hbdd (tail_lower a _ N hN)
      have h2 : sSup S ≤ a N + ε / 2 := csSup_le hne (tail_bound a _ N hN)
      have h3 := hN n hn N le_rfl
      rw [abs_lt] at h3 ⊢
      constructor <;> linarith
    · rintro ⟨L, hL⟩
      exact converges_cauchy a L hL

end H042

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (←) is M068's ε/2 trick: `|a m - a n| ≤ |a m - L| + |L - a n|`. (→) needs `S` nonempty and bounded above; the Cauchy property at `ε = 1` gives both (from `N0`: `a N0 - 1 ∈ S`, and `a N0 + 1` bounds `S`).
H2. For `tail_bound`, given `x` with witness `M`, compare both facts at the index `max M N`. Then for the limit: take `N` from Cauchy at `ε / 2`; `tail_lower` + `le_csSup` give `a N - ε/2 ≤ sSup S`, `tail_bound` + `csSup_le` give `sSup S ≤ a N + ε/2`.
H3. `refine ⟨sSup S, fun ε hε => ?_⟩; obtain ⟨N, hN⟩ := h (ε / 2) (by positivity); refine ⟨N, fun n hn => ?_⟩`, then `have h3 := hN n hn N le_rfl; rw [abs_lt] at h3 ⊢; constructor <;> linarith`.
-/
