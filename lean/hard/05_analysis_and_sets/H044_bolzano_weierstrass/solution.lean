/- H044 | Bolzano–Weierstrass | 1.5-2 h | peaks, subsequences, Nat.nth, choose, iterate, mathlib
GOAL
  Every bounded real sequence has a convergent subsequence `a ∘ φ` (`(a ∘ φ) k = a (φ k)`, with
  `φ` strictly increasing: `StrictMono φ`). Route: every sequence has a monotone subsequence
  (peak lemma; a peak is an `n` with `a m ≤ a n` for all `m > n`), and bounded monotone ones converge.

BANNED: import, exists_increasing_or_nonincreasing_subseq, exists_increasing_or_nonincreasing_subseq', Nat.exists_subseq_of_forall_mem_union

GUIDE
  Entries R1–R35: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
-- BEGIN SPEC
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
-- END SPEC

namespace H044

-- BEGIN SPEC
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
-- END SPEC

/- SKELETON · monotone_converges   (milestone; prove it FIRST: antitone_converges and
                                   bolzano_weierstrass use it)
  1. Open the ε–N statement (it sees through `ConvergesTo`):                        R1
  2. `sSup (range a) - ε` is not an upper bound, so some value beats it. Get the
     index N and `hN : sSup (Set.range a) - ε < a N` in one `obtain`:               R2, R3 → R4 → R5
  3. Give N and open `∀ n ≥ N`:                                                     R6
  4. Two facts:  a n ≤ sSup (Set.range a)                                           R7
                 a N ≤ a n                                                          R8
  5. Split the absolute value, then each side is linear in the facts:               R9, constructor, R10
-/
-- MILESTONE (optional: change or delete)
-- Monotone convergence (M075); you may copy your proof.
theorem monotone_converges (a : ℕ → ℝ) (hm : Monotone a) (hb : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) := by
  intro ε hε
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty a) (sub_lt_self (sSup (Set.range a)) hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : a n ≤ sSup (Set.range a) := le_csSup hb ⟨n, rfl⟩
  have h2 := hm hn
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/- SKELETON · antitone_converges   (milestone; uses monotone_converges on `fun n => -a n`)
  1. Name the lower bound B, with hB ⟨n, rfl⟩ : B ≤ a n:                             R11
  2. have hm : Monotone (fun n => -a n), as `fun i j hij => …` from `ha hij`:        R8, R12
  3. have hc := monotone_converges _ hm ⟨-B, …⟩; the bound proof:                    R13 → R14 → R10 [hB ⟨n, rfl⟩]
  4. The limit is L = -sSup (Set.range fun n => -a n). Give L and open `∀ ε > 0` in one
     refine (shape of R6; the `fun ε hε` sees through ConvergesTo as in R1):          R6, R1
     take N, hN from hc ε hε (obtain), then give N and open `∀ n ≥ N`:               R6
  5. Rewrite |a n - -S| as |-(-a n - S)| and drop the minus; then exact hN n hn:     R15, R16
-/
-- MILESTONE (optional: change or delete)
theorem antitone_converges (a : ℕ → ℝ) (ha : Antitone a) (hb : BddBelow (Set.range a)) :
    ∃ L, ConvergesTo a L := by
  obtain ⟨B, hB⟩ := hb
  have hm : Monotone (fun n => -a n) := fun i j hij => neg_le_neg (ha hij)
  have hc := monotone_converges _ hm ⟨-B, by rintro _ ⟨n, rfl⟩; linarith [hB ⟨n, rfl⟩]⟩
  refine ⟨-sSup (Set.range fun n => -a n), fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hc ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [show a n - -sSup (Set.range fun n => -a n) = -(-a n - sSup (Set.range fun n => -a n)) by ring,
    abs_neg]
  exact hN n hn

/- SKELETON · monotone_subseq   (milestone: the peak lemma; bolzano_weierstrass uses it)
  1. Split on the set of peaks {n | ∀ m > n, a m ≤ a n}:                             R17
  Finite peaks (hfin):
  2. An upper bound N for the peaks:                                                 R18
  3. have h : ∀ n, ∃ m, n < m ∧ (N < n → a n < a m). For each n:                     R19
       N < n:  n is not a peak (hN would give n ≤ N):                                R20, R21
               push the ¬ inside and take m apart:                                   R22
       ¬N < n: m := n + 1; the implication is vacuous:                               R21, R20
  4. choose g hg1 hg2 using h:                                                       R23
  5. have hge : ∀ k, N < g^[k] (N + 1), by induction on k:
       zero: simp;  succ: R24, then R25 with hg1
  6. φ := fun k => g^[k] (N + 1); give it with Or.inl, reducing both goals to one step: R27, R28
       strict:   R24, then hg1
       monotone: R30, R24, then hg2 with hge, weakened by R26
  Infinite peaks (hinf):
  7. φ := Nat.nth (fun n => ∀ m > n, a m ≤ a n), strictly increasing; Or.inr:         R31, R29
  8. The step: φ k is a peak (R32: a function of m and `m > φ k`), and φ (k + 1) > φ k
     (R33 with hφ := the R31 fact); `exact` sees through `∘`:                         R32 applied to R33
-/
-- MILESTONE (optional: change or delete)
-- The peak lemma: infinitely many peaks give an antitone subsequence, finitely many a monotone one.
theorem monotone_subseq (a : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (Monotone (a ∘ φ) ∨ Antitone (a ∘ φ)) := by
  rcases Set.finite_or_infinite {n | ∀ m > n, a m ≤ a n} with hfin | hinf
  · obtain ⟨N, hN⟩ := hfin.bddAbove
    have h : ∀ n, ∃ m, n < m ∧ (N < n → a n < a m) := by
      intro n
      by_cases hn : N < n
      · have hnp : n ∉ {n | ∀ m > n, a m ≤ a n} := fun hn' => absurd (hN hn') (by omega)
        simp only [Set.mem_setOf_eq, not_forall, not_le] at hnp
        obtain ⟨m, hm, hlt⟩ := hnp
        exact ⟨m, hm, fun _ => hlt⟩
      · exact ⟨n + 1, by omega, fun h => absurd h hn⟩
    choose g hg1 hg2 using h
    have hge : ∀ k, N < g^[k] (N + 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Function.iterate_succ_apply']; exact lt_trans ih (hg1 _)
    refine ⟨fun k => g^[k] (N + 1), strictMono_nat_of_lt_succ fun k => ?_,
      Or.inl (monotone_nat_of_le_succ fun k => ?_)⟩
    · rw [Function.iterate_succ_apply']
      exact hg1 _
    · simp only [Function.comp]
      rw [Function.iterate_succ_apply']
      exact (hg2 _ (hge k)).le
  · refine ⟨Nat.nth (fun n => ∀ m > n, a m ≤ a n), Nat.nth_strictMono hinf,
      Or.inr (antitone_nat_of_succ_le fun k => ?_)⟩
    exact Nat.nth_mem_of_infinite hinf k _ (Nat.nth_strictMono hinf (Nat.lt_succ_self k))

/- SKELETON · bolzano_weierstrass
  0. Prove the three milestones first; this proof only assembles them.
  1. Take φ from monotone_subseq a and split the ∨:                                  R34
     In each case one refine gives φ, hφ and the limit (or `_`), leaving the bound:
  2. Monotone case: monotone_converges _ hmono ⟨M, …⟩; the bound proof:              R13 → R14 → R35 (.2)
  3. Antitone case: antitone_converges _ hanti ⟨-M, …⟩; the bound proof:             R13 → R14 → R35 (.1)
-/
-- BEGIN SPEC
theorem bolzano_weierstrass (a : ℕ → ℝ) (M : ℝ) (hb : ∀ n, |a n| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L, ConvergesTo (a ∘ φ) L :=
-- END SPEC
  by
    obtain ⟨φ, hφ, hmono | hanti⟩ := monotone_subseq a
    · refine ⟨φ, hφ, _, monotone_converges _ hmono ⟨M, ?_⟩⟩
      rintro _ ⟨n, rfl⟩
      exact (abs_le.mp (hb _)).2
    · refine ⟨φ, hφ, antitone_converges _ hanti ⟨-M, ?_⟩⟩
      rintro _ ⟨n, rfl⟩
      exact (abs_le.mp (hb _)).1

end H044

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones in order. monotone_converges is ε–N against `sSup (Set.range a)` (R1–R10);
    antitone_converges applies it to `fun n => -a n` with the limit `-sSup …` (R11–R16). For the peak
    lemma, case on `Set.finite_or_infinite {n | ∀ m > n, a m ≤ a n}` (the peaks, R17).
H2. Infinite: `φ = Nat.nth (fun n => ∀ m > n, a m ≤ a n)`; each `φ k` is a peak and `φ (k+1) > φ k`
    (R31–R33), so `a ∘ φ` is antitone (R29). Finite: all peaks are `≤ N` (R18), so every `n > N` has
    some `m > n` with `a n < a m` (R19–R22); `choose` such an `m` and iterate from `N + 1` (R23, R24,
    R27, R28). Bolzano–Weierstrass: split `monotone_subseq a` (R34), bound with `abs_le` (R35).
H3. Monotone convergence: `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (Set.range_nonempty a)
    (sub_lt_self (sSup (Set.range a)) hε)`. Finite case: `have h : ∀ n, ∃ m, n < m ∧ (N < n → a n < a m)`
    (the guard avoids a dependent `choose`), `choose g hg1 hg2 using h`, `φ k = g^[k] (N + 1)`; prove
    `∀ k, N < g^[k] (N + 1)` by induction with `Function.iterate_succ_apply'`.
-/
