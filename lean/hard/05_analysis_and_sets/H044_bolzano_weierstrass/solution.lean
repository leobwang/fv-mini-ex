/- H044 | Bolzano–Weierstrass | 1.5-2 h | peaks, subsequences, Nat.nth, choose, iterate, mathlib
GOAL
  Every bounded real sequence has a convergent subsequence `a ∘ φ` (`(a ∘ φ) k = a (φ k)`, with
  `φ` strictly increasing: `StrictMono φ`). Route: every sequence has a monotone subsequence
  (peak lemma; a peak is an `n` with `a m ≤ a n` for all `m > n`), and bounded monotone ones converge.

REFERENCE
  #check Set.finite_or_infinite      -- s.Finite ∨ s.Infinite
  #check Set.Finite.bddAbove         -- s.Finite → BddAbove s   (BddAbove s: ∃ N, ∀ n ∈ s, n ≤ N)
  #check Nat.nth_strictMono          -- (setOf p).Infinite → StrictMono (Nat.nth p)  (k-th n with p n)
  #check Nat.nth_mem_of_infinite     -- (setOf p).Infinite → ∀ k, p (Nat.nth p k)
  #check strictMono_nat_of_lt_succ   -- (∀ n, f n < f (n + 1)) → StrictMono f
  #check monotone_nat_of_le_succ     -- (∀ n, f n ≤ f (n + 1)) → Monotone f  (i ≤ j → f i ≤ f j; antitone_nat_of_succ_le)
  #check Function.iterate_succ_apply' -- f^[n.succ] x = f (f^[n] x)   (`g^[k]`: g applied k times)
  #check exists_lt_of_lt_csSup       -- s.Nonempty → b < sSup s → ∃ a ∈ s, b < a   (`sSup s`: least upper bound)
  #check le_csSup                    -- BddAbove s → a ∈ s → a ≤ sSup s
  #check abs_le                      -- |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
  #check abs_sub_lt_iff              -- |a - b| < c ↔ a - b < c ∧ b - a < c
  -- `choose g hg1 hg2 using h` turns h : ∀ n, ∃ m, P n m ∧ Q n m into g : ℕ → ℕ and hg1, hg2
BANNED: import, exists_increasing_or_nonincreasing_subseq, exists_increasing_or_nonincreasing_subseq', Nat.exists_subseq_of_forall_mem_union
NOTE: imports are frozen (no `import` may be added): ℝ's order, `sSup`, `Nat.nth`, finite sets; no filters or compactness.
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
H1. Case on `Set.finite_or_infinite {n | ∀ m > n, a m ≤ a n}` (the peaks). For `antitone_converges`, apply `monotone_converges` to `fun n => -a n` and use the limit `-sSup …`.
H2. Infinite: `φ = Nat.nth (fun n => ∀ m > n, a m ≤ a n)`; each `φ k` is a peak and `φ (k+1) > φ k`. Finite: all peaks are `≤ N`, so every `n > N` has some `m > n` with `a n < a m`; `choose` such an `m` and iterate from `N + 1`.
H3. Finite case: `have h : ∀ n, ∃ m, n < m ∧ (N < n → a n < a m)` (the guard avoids a dependent `choose`), `choose g hg1 hg2 using h`, `φ k = g^[k] (N + 1)`; prove `∀ k, N < g^[k] (N + 1)` by induction with `Function.iterate_succ_apply'`.
-/
