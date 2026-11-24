/- H045 | Extreme value theorem | 1-1.5 h | sequential compactness, Filter.Tendsto, subsequences, sSup, filter_upwards, mathlib
GOAL
  `f : X → ℝ` continuous on a nonempty `X` where every sequence `x` has a convergent subsequence `x ∘ φ`
  (`hX`; `φ : ℕ → ℕ` strictly increasing; e.g. `X = [a, b]` by Bolzano–Weierstrass) attains its max.
  Show `range f` is bounded above, then pass a maximizing sequence to a convergent subsequence.

BANNED: IsCompact, IsSeqCompact.isCompact, CompactSpace, Filter.cocompact, IsSeqCompact, IsCountablyCompact.isSeqCompact, SeqCompactSpace, seqCompactSpace_iff, compactSpace_iff_seqCompactSpace, isCompact_iff_isSeqCompact, Subtype.isSeqCompact_iff, isSeqCompact_univ, isSeqCompact_univ_iff, isSeqCompact_iff_isSeqCompact_univ, isSeqCompact_iff_seqCompactSpace, SeqCompactSpace.tendsto_subseq, IsSeqCompact.subseq_of_frequently_in, IsSeqCompact.exists_tendsto, IsSeqCompact.exists_tendsto_of_frequently_mem, CountablyCompactSpace, IsCountablyCompact, IsSeqCompact.isCountablyCompact, Subtype.isCountablyCompact_iff, isCountablyCompact_iff_isSeqCompact, CountablyCompactSpace.isCountablyCompact_univ, isCountablyCompact_univ_iff, isCountablyCompact_iff_seq_clusterPt, isCountablyCompact_iff_countablyCompactSpace, isCountablyCompact_iff_isCountablyCompact_univ, IsSeqCompact.image, isCompact_range, Continuous.exists_forall_ge, Continuous.exists_forall_ge', IsCompact.exists_isMaxOn, ContinuousOn.exists_isMaxOn', IsCompact.exists_isGreatest, IsCompact.isGreatest_sSup, IsCompact.sSup_mem, IsClosed.csSup_mem, IsLUB.mem_of_isClosed, IsClosed.isLUB_mem, IsCompact.exists_sSup_image_eq, exists_seq_tendsto_sSup

GUIDE
  Entries R1–R35: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H045

open Filter Topology Set

/- SKELETON · seq_limit   (milestone; prove it FIRST: bdd and extreme_value use it)
  1. Take the convergent subsequence of `x` from `hX x`, naming c φ hφ hlim:             R1
  2. Continuity of f at c, as a limit:  Tendsto f (𝓝 c) (𝓝 (f c))                       R2
  3. Compose it with hlim; the result prints as `Tendsto (f ∘ x ∘ φ) …`, and `f ∘ x ∘ φ`
     unfolds to the goal's `fun n => f (x (φ n))`. Give c, φ, hφ and the composite
     with one anonymous constructor:                                                     R3
-/
-- MILESTONE (optional: change or delete)
theorem seq_limit {X : Type*} [TopologicalSpace X]
    (hX : ∀ x : ℕ → X, ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 c))
    {f : X → ℝ} (hf : Continuous f) (x : ℕ → X) :
    ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => f (x (φ n))) atTop (𝓝 (f c)) := by
  obtain ⟨c, φ, hφ, hlim⟩ := hX x
  exact ⟨c, φ, hφ, (hf.tendsto c).comp hlim⟩

/- SKELETON · bdd   (milestone; uses seq_limit; extreme_value needs it for le_csSup)
  1. Suppose not:  hnb : ¬BddAbove (range f)                                             R4
  2. have : ∀ n : ℕ, ∃ x, (n : ℝ) < f x. For each n, again by contradiction,
     push the ¬ inside, then `apply hnb` and give the bound ↑n:                         R4, R5, R6 → R7
  3. Turn it into a sequence x with hfx : ∀ n, ↑n < f (x n):                            R8
  4. seq_limit hX hf x gives c φ hφ hlim with f (x (φ n)) → f c:                         R1
  5. One index n where both  f (x (φ n)) < f c + 1  and  ⌈f c + 1⌉₊ ≤ n  hold:
     R10 → R9 and R11, merged by R12, then R13 (obtain ⟨n, hn1, hn2⟩)
  6. Three facts:  h1 := hfx (φ n)
                   h2 : (n : ℝ) ≤ φ n                                                     R14, R15
                   h3 : f c + 1 ≤ n                                                       R16, R17 with R15
  7. They contradict hn1:                                                                R18
-/
-- MILESTONE (optional: change or delete)
theorem bdd {X : Type*} [TopologicalSpace X]
    (hX : ∀ x : ℕ → X, ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 c))
    {f : X → ℝ} (hf : Continuous f) : BddAbove (range f) := by
  by_contra hnb
  have : ∀ n : ℕ, ∃ x, (n : ℝ) < f x := by
    intro n
    by_contra h
    push Not at h
    exact hnb ⟨n, by rintro _ ⟨x, rfl⟩; exact h x⟩
  choose x hfx using this
  obtain ⟨c, φ, hφ, hlim⟩ := seq_limit hX hf x
  obtain ⟨n, hn1, hn2⟩ := ((hlim.eventually_lt_const (lt_add_one (f c))).and
    (eventually_ge_atTop ⌈f c + 1⌉₊)).exists
  have h1 := hfx (φ n)
  have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  have h3 : f c + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  linarith

/- SKELETON · maximizing_seq   (milestone; extreme_value takes its sequence from here)
  1. have : ∀ n : ℕ, ∃ x, sSup (range f) - 1 / (n + 1) < f x. For each n:
       sSup (range f) - 1 / (n + 1) < sSup (range f)                                     R20 with R21
       so a value of f beats it; name the point x in one obtain:                         R19, R22 → R23
  2. Turn it into the sequence and return it:                                            R8
-/
-- MILESTONE (optional: change or delete)
theorem maximizing_seq {X : Type*} [Nonempty X] (f : X → ℝ) :
    ∃ x : ℕ → X, ∀ n : ℕ, sSup (range f) - 1 / (n + 1) < f (x n) := by
  have : ∀ n : ℕ, ∃ x, sSup (range f) - 1 / (n + 1) < f x := by
    intro n
    obtain ⟨_, ⟨x, rfl⟩, h⟩ :=
      exists_lt_of_lt_csSup (range_nonempty f) (sub_lt_self _ (by positivity : (0 : ℝ) < 1 / (n + 1)))
    exact ⟨x, h⟩
  choose x hfx using this
  exact ⟨x, hfx⟩

/- SKELETON · extreme_value
  0. Prove the milestones first: maximizing_seq (step 1), seq_limit (step 2), bdd (step 4).
  1. Name M := sSup (range f); take x and hfx from maximizing_seq f:                     R24
  2. seq_limit hX hf x gives c φ hφ hlim with f (x (φ k)) → f c:                         R1
  3. c is the witness; introduce y:                                                      R25
  4. hyM : f y ≤ M, from bdd hX hf:                                                      R26 → R27
  5. It suffices to prove M ≤ f c (then linarith):                                       R28
  6. ε-argument: introduce ε hε, then n with 1 / ε < ↑n:                                 R29, R30
  7. hev : ∀ᶠ k in atTop, M - 1 / ((n : ℝ) + 1) ≤ f (x (φ k)):                           R31 with R11
       (n : ℝ) ≤ φ k                                                                     R17 with R14, R15
       1 / ((φ k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1)                                           R32
       then linarith [hfx (φ k)]                                                         R18
  8. Pass hev to the limit:  M - 1 / (↑n + 1) ≤ f c                                     R33
  9. h3 : 1 / ((n : ℝ) + 1) < ε: clear both denominators, then nlinarith:
       R34 (side goal by R21), R34 at hn, R35
 10. linarith                                                                            R18
-/
-- BEGIN SPEC
theorem extreme_value {X : Type*} [TopologicalSpace X] [Nonempty X]
    (hX : ∀ x : ℕ → X, ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 c))
    (f : X → ℝ) (hf : Continuous f) : ∃ c, ∀ x, f x ≤ f c :=
-- END SPEC
  by
    set M := sSup (range f)
    obtain ⟨x, hfx⟩ := maximizing_seq f
    obtain ⟨c, φ, hφ, hlim⟩ := seq_limit hX hf x
    refine ⟨c, fun y => ?_⟩
    have hyM : f y ≤ M := le_csSup (bdd hX hf) (mem_range_self y)
    suffices M ≤ f c by linarith
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    have hev : ∀ᶠ k in atTop, M - 1 / ((n : ℝ) + 1) ≤ f (x (φ k)) := by
      filter_upwards [eventually_ge_atTop n] with k hk
      have h2 : (n : ℝ) ≤ φ k := by exact_mod_cast hk.trans (hφ.id_le k)
      have : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by gcongr
      linarith [hfx (φ k)]
    have hMc := ge_of_tendsto hlim hev
    have h3 : 1 / ((n : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn
      nlinarith
    linarith

end H045

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the three milestones, then combine them. With `M = sSup (range f)`: a sequence with
    `M - 1/(n+1) < f (x n)` (maximizing_seq) has a subsequence with `f (x (φ k)) → f c` (seq_limit);
    then `f y ≤ M` for all `y` (`le_csSup`, which needs bdd) and `M ≤ f c` (a limit argument), so `c`
    is a maximizer. `hX` is the only compactness you have.
H2. seq_limit: `obtain ⟨c, φ, hφ, hlim⟩ := hX x` and `(hf.tendsto c).comp hlim`. bdd: by contradiction,
    `choose x hfx` with `(n : ℝ) < f (x n)`; eventually `f (x (φ n)) < f c + 1` and eventually
    `n ≥ ⌈f c + 1⌉₊` (`Nat.le_ceil`), merged with `.and` and `.exists`, but `n ≤ φ n < f (x (φ n))`.
    maximizing_seq: `exists_lt_of_lt_csSup (range_nonempty f) (sub_lt_self _ _)` for each `n`, then
    `choose`. Main: `suffices M ≤ f c by linarith`, and prove it for every `ε > 0`.
H3. For `M ≤ f c` use `refine le_of_forall_pos_lt_add fun ε hε => ?_`, pick `n` with `1 / ε < n`
    (`exists_nat_gt`), and `have hev : ∀ᶠ k in atTop, M - 1 / ((n : ℝ) + 1) ≤ f (x (φ k)) := by
    filter_upwards [eventually_ge_atTop n] with k hk; ...` (use `hk.trans (hφ.id_le k)` and `gcongr`);
    then `ge_of_tendsto hlim hev`. Finally `f y ≤ M` is `le_csSup (bdd hX hf) (mem_range_self y)`.
-/
