/- H045 | Extreme value theorem | 1-1.5 h | sequential compactness, Filter.Tendsto, subsequences, sSup, filter_upwards, mathlib
GOAL
  `f : X → ℝ` continuous on a nonempty `X` where every sequence `x` has a convergent subsequence `x ∘ φ`
  (`hX`; `φ : ℕ → ℕ` strictly increasing; e.g. `X = [a, b]` by Bolzano–Weierstrass) attains its max.
  Show `range f` is bounded above, then pass a maximizing sequence to a convergent subsequence.

REFERENCE
  -- `𝓝 c`: neighbourhoods of `c`; `Tendsto u atTop (𝓝 c)`: `u n → c`; `∀ᶠ n in atTop, P n`: `P n` for all large `n`
  -- `range f = {f x | x : X}`; `sSup s`: least upper bound (the `cs…` lemmas need `s.Nonempty` / `BddAbove s`)
  #check Continuous.tendsto          -- Continuous f → ∀ c, Tendsto f (𝓝 c) (𝓝 (f c));  chain with `Filter.Tendsto.comp`
  #check Filter.Tendsto.eventually_lt_const  -- v < w → Tendsto u l (𝓝 v) → ∀ᶠ n in l, u n < w
  #check Filter.eventually_ge_atTop  -- (N) : ∀ᶠ n in atTop, N ≤ n
  #check Filter.Eventually.exists    -- (∀ᶠ n in atTop, P n) → ∃ n, P n   (merge two facts first with `h1.and h2`)
  #check ge_of_tendsto               -- Tendsto u l (𝓝 c) → (∀ᶠ n in l, b ≤ u n) → b ≤ c
  #check StrictMono.id_le            -- StrictMono φ → id ≤ φ, so `hφ.id_le n : n ≤ φ n`
  #check exists_lt_of_lt_csSup       -- s.Nonempty → b < sSup s → ∃ a ∈ s, b < a   (`Set.range_nonempty f`)
  #check le_csSup                    -- BddAbove s → a ∈ s → a ≤ sSup s   (`Set.mem_range_self y : f y ∈ range f`)
  -- `filter_upwards [eventually_ge_atTop N] with n hn` proves `∀ᶠ n in atTop, P n` from a goal `P n` with `hn : N ≤ n`
NOTE: no compactness in any form: `X` has no compactness instance, and BANNED lists Mathlib's bridges to one.
BANNED: IsCompact, IsSeqCompact.isCompact, CompactSpace, Filter.cocompact, IsSeqCompact, IsCountablyCompact.isSeqCompact, SeqCompactSpace, seqCompactSpace_iff, compactSpace_iff_seqCompactSpace, isCompact_iff_isSeqCompact, Subtype.isSeqCompact_iff, isSeqCompact_univ, isSeqCompact_univ_iff, isSeqCompact_iff_isSeqCompact_univ, isSeqCompact_iff_seqCompactSpace, SeqCompactSpace.tendsto_subseq, IsSeqCompact.subseq_of_frequently_in, IsSeqCompact.exists_tendsto, IsSeqCompact.exists_tendsto_of_frequently_mem, CountablyCompactSpace, IsCountablyCompact, IsSeqCompact.isCountablyCompact, Subtype.isCountablyCompact_iff, isCountablyCompact_iff_isSeqCompact, CountablyCompactSpace.isCountablyCompact_univ, isCountablyCompact_univ_iff, isCountablyCompact_iff_seq_clusterPt, isCountablyCompact_iff_countablyCompactSpace, isCountablyCompact_iff_isCountablyCompact_univ, IsSeqCompact.image, isCompact_range, Continuous.exists_forall_ge, Continuous.exists_forall_ge', IsCompact.exists_isMaxOn, ContinuousOn.exists_isMaxOn', IsCompact.exists_isGreatest, IsCompact.isGreatest_sSup, IsCompact.sSup_mem, IsClosed.csSup_mem, IsLUB.mem_of_isClosed, IsClosed.isLUB_mem, IsCompact.exists_sSup_image_eq, exists_seq_tendsto_sSup
-/
import Mathlib

namespace H045

open Filter Topology Set

-- MILESTONE (optional: change or delete)
theorem seq_limit {X : Type*} [TopologicalSpace X]
    (hX : ∀ x : ℕ → X, ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 c))
    {f : X → ℝ} (hf : Continuous f) (x : ℕ → X) :
    ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => f (x (φ n))) atTop (𝓝 (f c)) := by
  obtain ⟨c, φ, hφ, hlim⟩ := hX x
  exact ⟨c, φ, hφ, (hf.tendsto c).comp hlim⟩

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
H1. Three steps: (1) for any sequence `x`, some subsequence makes `f (x (φ n)) → f c`; (2) so `range f` is bounded above; (3) with `M = sSup (range f)`, a sequence with `f (x n) > M - 1/(n+1)` has a subsequence converging to a maximizer `c`.
H2. (1): `obtain ⟨c, φ, hφ, hlim⟩ := hX x` and `(hf.tendsto c).comp hlim`. (2): by contradiction, `choose x hfx` with `(n : ℝ) < f (x n)`; eventually `f (x (φ n)) < f c + 1` and eventually `n ≥ ⌈f c + 1⌉₊` (`Nat.le_ceil`), but `n ≤ φ n < f (x (φ n))`. (3): `exists_lt_of_lt_csSup` for each `n`, then `choose`.
H3. For `M ≤ f c` use `le_of_forall_pos_lt_add fun ε hε => _`, pick `n` with `1 / ε < n` (`exists_nat_gt`), and `have hev : ∀ᶠ k in atTop, M - 1 / ((n : ℝ) + 1) ≤ f (x (φ k)) := by filter_upwards [eventually_ge_atTop n] with k hk; ...` (use `hk.trans (hφ.id_le k)` and `gcongr`); then `ge_of_tendsto hlim hev`. Finally `f y ≤ M` is `le_csSup (bdd hX hf) (mem_range_self y)`.
-/
