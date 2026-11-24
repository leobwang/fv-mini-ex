/- H042 | Cauchy ⇔ convergent in ℝ | 45-75 min | Cauchy sequences, completeness, sSup, epsilon-N, mathlib
GOAL
  A real sequence is Cauchy iff it converges, with explicit ε-N definitions (`|x|` is absolute value).
  For "Cauchy → convergent", build the limit yourself as a supremum: `L = sSup S`, where
  `S = {x | ∃ M, ∀ n ≥ M, x < a n}` is the set of eventual strict lower bounds of `a`.
BANNED: import, CauSeq, IsCauSeq, LimZero, IsComplete, isComplete, complete, lim, equiv_lim, cauSeq_converges
BANNED: eq_lim_of_const_equiv, lim_eq_of_equiv_const, lim_le, le_lim, lim_lt, lt_lim, instIsCompleteAbs, Real.cauchy, ofCauchy
BANNED: Real.mk_near_of_forall_near, Real.mk_le_of_forall_le

GUIDE
  Entries R1–R23: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · converges_cauchy   (milestone 1; used in `cauchy_iff_converges`, step 7)
  1. Unfold `IsCauchy a`: introduce ε and hε : ε > 0:                       R1
  2. N from h at ε / 2; the side goal ε / 2 > 0 inline:                     R2, R3
  3. Give N, introduce m hm n hn:                                           R4
  4. h1 : |a m - L| < ε / 2   and   h2 : |a n - L| < ε / 2  from hN:        R5
  5. One `calc` chain:                                                      R6
       |a m - a n| = |(a m - L) + (L - a n)|                                R7
         _ ≤ |a m - L| + |L - a n|                                          R8
         _ < ε / 2 + ε / 2      (flip |L - a n| first, then add h1, h2)     R9, R10
         _ = ε                                                              ring
-/
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

/- SKELETON · tail_lower   (milestone 2; used in `cauchy_iff_converges`, steps 3 and 5)
  1. The membership goal IS its property (∃ M, ∀ n ≥ M, a N - ε < a n):
     give M := N, introduce n hn:                                           R11, R4
  2. hN at (n, N); the side condition N ≥ N:   h : |a n - a N| < ε          R5, R12
  3. Unfold |·| < ε at h, finish:                                           R13, R14
-/
-- MILESTONE (optional: change or delete)
-- If the tail from `N` is ε-close, then `a N - ε` is an eventual lower bound ...
theorem tail_lower (a : ℕ → ℝ) (ε : ℝ) (N : ℕ) (hN : ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε) :
    a N - ε ∈ {x | ∃ M, ∀ n ≥ M, x < a n} := by
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn N le_rfl
  rw [abs_lt] at h
  linarith

/- SKELETON · tail_bound   (milestone 3; used in `cauchy_iff_converges`, steps 3 and 5)
  1. Introduce x and take x ∈ {x | ∃ M, …} apart into M, hM:               R15
  2. Both facts at the common index k := max M N:
       h1 : x < a k            from hM (side condition k ≥ M)               R5, R16
       h2 : |a k - a N| < ε    from hN at (k, N)                            R5, R16, R12
  3. Unfold |·| < ε at h2, finish:                                          R13, R14
-/
-- MILESTONE (optional: change or delete)
-- ... and every eventual lower bound is at most `a N + ε`.
theorem tail_bound (a : ℕ → ℝ) (ε : ℝ) (N : ℕ) (hN : ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε) :
    ∀ x ∈ {x | ∃ M, ∀ n ≥ M, x < a n}, x ≤ a N + ε := by
  rintro x ⟨M, hM⟩
  have h1 := hM (max M N) (le_max_left _ _)
  have h2 := hN (max M N) (le_max_right _ _) N le_rfl
  rw [abs_lt] at h2
  linarith

/- SKELETON · cauchy_iff_converges   (prove milestones 1, 2, 3 first)
  1. Split the ↔:                                                           R17
  (→) 2. Introduce h; name S := {x | ∃ M, ∀ n ≥ M, x < a n}:               R18
      3. Cauchy at ε = 1:  obtain N0, hN0                                   R2, R19
           hne  : S.Nonempty   from milestone 2 at (1, N0)                  R20
           hbdd : BddAbove S   from milestone 3 at (1, N0)                  R21
      4. The limit is sSup S: give it, introduce ε hε (through ConvergesTo): R4
      5. N, hN from h at ε / 2; give N, introduce n hn:                     R2, R3, R4
           h1 : a N - ε / 2 ≤ sSup S   milestone 2 at (ε / 2, N), then      R22
           h2 : sSup S ≤ a N + ε / 2   milestone 3 at (ε / 2, N), then      R23
           h3 : |a n - a N| < ε / 2    hN at (n, N)                         R5, R12
      6. Unfold |·| < at h3 and in the goal; split the ∧ with `constructor`,
         close both halves from h1, h2, h3:                                 R13, R14
  (←) 7. Take ⟨L, hL⟩ apart, apply milestone 1:                            R15
-/
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
H1. (←) is the ε/2 trick: `|a m - a n| ≤ |a m - L| + |L - a n|` (milestone 1). (→) `sSup S` is only
    meaningful when `S` is nonempty and bounded above (R22, R23 need both); the Cauchy property at `ε = 1`
    gives both: `a N0 - 1 ∈ S` (milestone 2) and `a N0 + 1` bounds `S` (milestone 3).
H2. Milestones 2 and 3 say "the tail from N squeezes sSup S into [a N - ε, a N + ε]". For `tail_bound`,
    given `x` with witness `M`, compare `x < a k` and `a k < a N + ε` at `k := max M N`. For the limit:
    take `N` from Cauchy at `ε / 2`; milestone 2 + `le_csSup` give `a N - ε/2 ≤ sSup S`, milestone 3 +
    `csSup_le` give `sSup S ≤ a N + ε/2`, and `hN n hn N le_rfl` gives `|a n - a N| < ε/2`.
H3. `refine ⟨sSup S, fun ε hε => ?_⟩; obtain ⟨N, hN⟩ := h (ε / 2) (by positivity); refine ⟨N, fun n hn => ?_⟩`,
    then `have h1 : a N - ε / 2 ≤ sSup S := le_csSup hbdd (tail_lower a _ N hN)` (likewise `h2` with
    `csSup_le hne (tail_bound a _ N hN)`), `have h3 := hN n hn N le_rfl; rw [abs_lt] at h3 ⊢; constructor <;> linarith`.
-/
