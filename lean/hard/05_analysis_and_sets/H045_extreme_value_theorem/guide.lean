/- Guide for H045 (Extreme value theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`, or `P` is
the whole goal. A hypothesis `h`/`k` in an entry is only there to finish the example; it shows what
the goal or the context became.
Part W: worked combinations on objects that are NOT the exercise's (a real sequence `u`, `sSup` of a
sequence, an `a ≤ b + 1/(n+1)` argument).
Assumed: Lean basics (E001–E033). New: Mathlib's limits as filters (`Tendsto`, `𝓝`, `atTop`, `∀ᶠ`),
`Continuous`, `StrictMono`, `Set.range`, `sSup`/`BddAbove`, casts `ℕ → ℝ`, `⌈x⌉₊`, and the tactics
`choose`, `push Not`, `set`, `filter_upwards`, `gcongr`, `positivity`, `exact_mod_cast`, `linarith`,
`nlinarith`.
-/
import Mathlib

open Filter Topology Set

namespace H045Guide

/-! # Part R · Reference entries -/

/-! ## Part 1 · a convergent subsequence of `f ∘ x` -/

/-! ### R1. `obtain ⟨c, φ, hφ, hlim⟩ := h` · context: a nested `∃ c, ∃ φ, A ∧ B` → four names -/
example {X : Type} [TopologicalSpace X] (u : ℕ → X) (P : Prop)
    (k : ∀ (c : X) (φ : ℕ → ℕ), StrictMono φ → Tendsto (u ∘ φ) atTop (𝓝 c) → P)
    (h : ∃ c, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 c)) : P := by
  obtain ⟨c, φ, hφ, hlim⟩ := h
  exact k c φ hφ hlim

/-! ### R2. `Continuous.tendsto` · `Continuous g → ∀ c, Tendsto g (𝓝 c) (𝓝 (g c))` · context -/
example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : X → Y) (hg : Continuous g)
    (c : X) (P : Prop) (k : Tendsto g (𝓝 c) (𝓝 (g c)) → P) : P := by
  have h2 := hg.tendsto c
  exact k h2

/-! ### R3. `Filter.Tendsto.comp` · `Tendsto g y z → Tendsto u x y → Tendsto (g ∘ u) x z` · context
`g ∘ u` unfolds to `fun n => g (u n)`, so `exact` accepts it for a goal written either way. -/
example {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (g : X → Y) (u : ℕ → X) (c : X)
    (hg : Tendsto g (𝓝 c) (𝓝 (g c))) (hu : Tendsto u atTop (𝓝 c)) :
    Tendsto (fun n => g (u n)) atTop (𝓝 (g c)) := by
  have h3 := hg.comp hu
  exact h3

/-! ## Part 2 · `range f` is bounded above -/

/-! ### R4. `by_contra hnb` · goal `Q` → `False`, context gains `hnb : ¬Q` -/
example (Q : Prop) (k : ¬Q → False) : Q := by
  by_contra hnb
  exact k hnb

/-! ### R5. `push Not at h` · context: push a `¬` inward (`¬∃ x, b < g x` → `∀ x, g x ≤ b`) -/
example {X : Type} (g : X → ℝ) (b : ℝ) (P : Prop) (k : (∀ x, g x ≤ b) → P)
    (h : ¬∃ x, b < g x) : P := by
  push Not at h
  exact k h

/-! ### R6. `refine ⟨b, ?_⟩` on `BddAbove s` · goal → `b ∈ upperBounds s`
`BddAbove s` unfolds to `∃ b, b ∈ upperBounds s`: give the bound, then prove it bounds. -/
example {X : Type} (g : X → ℝ) (b : ℝ) (k : b ∈ upperBounds (range g)) : BddAbove (range g) := by
  refine ⟨b, ?_⟩
  exact k

/-! ### R7. `rintro _ ⟨x, rfl⟩` · goal `b ∈ upperBounds (range g)` → context `x`, goal `g x ≤ b`
`b ∈ upperBounds s` unfolds to `∀ ⦃y⦄, y ∈ s → y ≤ b`, and `y ∈ range g` to `∃ x, g x = y`. -/
example {X : Type} (g : X → ℝ) (b : ℝ) (k : ∀ x, g x ≤ b) : b ∈ upperBounds (range g) := by
  rintro _ ⟨x, rfl⟩
  exact k x

/-! ### R8. `choose x hx using h` · context: `h : ∀ n, ∃ y, A n y` → `x : ℕ → X`, `hx : ∀ n, A n (x n)` -/
example {X : Type} (A : ℕ → X → Prop) (P : Prop) (k : ∀ x : ℕ → X, (∀ n, A n (x n)) → P)
    (h : ∀ n : ℕ, ∃ y, A n y) : P := by
  choose x hx using h
  exact k x hx

/-! ### R9. `Filter.Tendsto.eventually_lt_const` · `v < w → Tendsto u l (𝓝 v) → ∀ᶠ n in l, u n < w` -/
example (u : ℕ → ℝ) (v w : ℝ) (hvw : v < w) (hu : Tendsto u atTop (𝓝 v)) (P : Prop)
    (k : (∀ᶠ n in atTop, u n < w) → P) : P := by
  have h9 := hu.eventually_lt_const hvw
  exact k h9

/-! ### R10. `lt_add_one` · `a < a + 1` · context -/
example (a : ℝ) (P : Prop) (k : a < a + 1 → P) : P := by
  have h10 := lt_add_one a
  exact k h10

/-! ### R11. `Filter.eventually_ge_atTop` · `∀ᶠ n in atTop, N ≤ n` · context -/
example (N : ℕ) (P : Prop) (k : (∀ᶠ n in atTop, N ≤ n) → P) : P := by
  have h11 := eventually_ge_atTop N
  exact k h11

/-! ### R12. `Filter.Eventually.and` · `(∀ᶠ n in l, p n) → (∀ᶠ n in l, q n) → ∀ᶠ n in l, p n ∧ q n` -/
example (p q : ℕ → Prop) (h1 : ∀ᶠ n in atTop, p n) (h2 : ∀ᶠ n in atTop, q n) (P : Prop)
    (k : (∀ᶠ n in atTop, p n ∧ q n) → P) : P := by
  have h12 := h1.and h2
  exact k h12

/-! ### R13. `Filter.Eventually.exists` · `(∀ᶠ n in atTop, p n) → ∃ n, p n` · context
Then `obtain ⟨n, hn1, hn2⟩` splits an `∃ n, p n ∧ q n`. -/
example (p : ℕ → Prop) (h : ∀ᶠ n in atTop, p n) (P : Prop) (k : (∃ n, p n) → P) : P := by
  have h13 := h.exists
  exact k h13

/-! ### R14. `StrictMono.id_le` · `StrictMono φ → id ≤ φ`; applied to `n`: `n ≤ φ n` · context -/
example (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) (P : Prop) (k : n ≤ φ n → P) : P := by
  have h14 : n ≤ φ n := hφ.id_le n
  exact k h14

/-! ### R15. `exact_mod_cast h` · closes a goal about casts `↑m` from the same fact without casts -/
example (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := by
  exact_mod_cast h

/-! ### R16. `Nat.le_ceil` · `a ≤ ↑⌈a⌉₊` (`⌈a⌉₊ : ℕ` is the least natural number `≥ a`) · context -/
example (a : ℝ) (P : Prop) (k : a ≤ ↑⌈a⌉₊ → P) : P := by
  have h16 := Nat.le_ceil a
  exact k h16

/-! ### R17. `h1.trans h2` (`le_trans`) · `a ≤ b → b ≤ c → a ≤ c` · context -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (P : Prop) (k : a ≤ c → P) : P := by
  have h17 := h1.trans h2
  exact k h17

/-! ### R18. `linarith` · closes a linear (in)equality that follows from the hypotheses
`linarith [t]` also uses the extra fact `t`. It closes `False` from contradictory hypotheses. -/
example (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (h3 : c ≤ a) : False := by
  linarith

/-! ## Part 3 · a maximizing sequence -/

/-! ### R19. `Set.range_nonempty` · `[Nonempty X] → (range g).Nonempty` · context -/
example {X : Type} [Nonempty X] (g : X → ℝ) (P : Prop) (k : (range g).Nonempty → P) : P := by
  have h19 := range_nonempty g
  exact k h19

/-! ### R20. `sub_lt_self` · `0 < b → a - b < a` · context -/
example (a b : ℝ) (hb : 0 < b) (P : Prop) (k : a - b < a → P) : P := by
  have h20 := sub_lt_self a hb
  exact k h20

/-! ### R21. `positivity` · closes `0 < e` / `0 ≤ e` when `e` is built from positive pieces -/
example (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
  positivity

/-! ### R22. `exists_lt_of_lt_csSup` · `s.Nonempty → b < sSup s → ∃ a ∈ s, b < a` · context -/
example (s : Set ℝ) (b : ℝ) (hs : s.Nonempty) (hb : b < sSup s) (P : Prop)
    (k : (∃ a ∈ s, b < a) → P) : P := by
  have h22 := exists_lt_of_lt_csSup hs hb
  exact k h22

/-! ### R23. `obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h` · context: `∃ a ∈ range g, b < a` → `x`, `hx : b < g x`
The pattern `rfl` replaces the anonymous value `a` by `g x` everywhere. -/
example {X : Type} (g : X → ℝ) (b : ℝ) (P : Prop) (k : ∀ x, b < g x → P)
    (h : ∃ a ∈ range g, b < a) : P := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h
  exact k x hx

/-! ## Part 4 · the maximum is attained -/

/-! ### R24. `set M := e` · context gains `M : ℝ := e`; every `e` in goal and context becomes `M` -/
example (s : Set ℝ) (P : ℝ → Prop) (h : P (sSup s)) : P (sSup s) := by
  set M := sSup s
  exact h

/-! ### R25. `refine ⟨c, fun y => ?_⟩` · goal `∃ c, ∀ y, Q y c` → context gains `y`, goal `Q y c` -/
example {X : Type} (Q : X → X → Prop) (c : X) (k : ∀ y, Q y c) : ∃ c, ∀ y, Q y c := by
  refine ⟨c, fun y => ?_⟩
  exact k y

/-! ### R26. `Set.mem_range_self` · `g y ∈ range g` · context -/
example {X : Type} (g : X → ℝ) (y : X) (P : Prop) (k : g y ∈ range g → P) : P := by
  have h26 : g y ∈ range g := mem_range_self y
  exact k h26

/-! ### R27. `le_csSup` · `BddAbove s → a ∈ s → a ≤ sSup s` · context -/
example (s : Set ℝ) (a : ℝ) (hb : BddAbove s) (ha : a ∈ s) (P : Prop) (k : a ≤ sSup s → P) : P := by
  have h27 := le_csSup hb ha
  exact k h27

/-! ### R28. `suffices T by tac` · goal `G` → `T`; `tac` proves `G` from `this : T` -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  suffices b ≤ c by linarith
  exact h2

/-! ### R29. `le_of_forall_pos_lt_add` · `(∀ ε, 0 < ε → a < b + ε) → a ≤ b` · goal -/
example (a b : ℝ) (k : ∀ ε : ℝ, 0 < ε → a < b + ε) : a ≤ b := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  exact k ε hε

/-! ### R30. `exists_nat_gt` · `∃ n : ℕ, x < ↑n` (ℝ is Archimedean) · context -/
example (x : ℝ) (P : Prop) (k : ∀ n : ℕ, x < n → P) : P := by
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact k n hn

/-! ### R31. `filter_upwards [h₁] with k hk` · goal `∀ᶠ k in atTop, Q k` → `k`, `hk`, goal `Q k`
Each `hᵢ : ∀ᶠ k in atTop, pᵢ k` in the list becomes a hypothesis `pᵢ k` named after `with k`. -/
example (N : ℕ) (Q : ℕ → Prop) (h : ∀ k, N ≤ k → Q k) : ∀ᶠ k in atTop, Q k := by
  filter_upwards [eventually_ge_atTop N] with k hk
  exact h k hk

/-! ### R32. `gcongr` · goal `1 / (↑n + 1) ≤ 1 / (↑m + 1)` → `m ≤ n`
It peels off the matching parts of both sides, proves the side goals `0 < …` itself, and also strips
the cast. When a hypothesis states the remaining goal (say `h : m ≤ n`), `gcongr` closes it too. -/
example (m n : ℕ) (k : ∀ i : ℕ, i ≤ n) : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
  gcongr
  exact k m

/-! ### R33. `ge_of_tendsto` · `Tendsto u l (𝓝 a) → (∀ᶠ n in l, b ≤ u n) → b ≤ a` · context -/
example (u : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hev : ∀ᶠ n in atTop, b ≤ u n)
    (P : Prop) (k : b ≤ a → P) : P := by
  have h33 := ge_of_tendsto hu hev
  exact k h33

/-! ### R34. `div_lt_iff₀` · `0 < c → (b / c < a ↔ b < a * c)` · goal (or `at h`: context) -/
example (a b c : ℝ) (hc : 0 < c) (k : b < a * c) : b / c < a := by
  rw [div_lt_iff₀ hc]
  exact k

/-! ### R35. `nlinarith` · `linarith` that also multiplies pairs of hypotheses; closes the goal -/
example (x y : ℝ) (hx : 0 < x) (h : 1 < y * x) : 1 < x * (y + 1) := by
  nlinarith

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Eventually below, eventually far out, so one index does both: R9, R11, R12, R13 -/
example (u : ℕ → ℝ) (v : ℝ) (hu : Tendsto u atTop (𝓝 v)) :
    ∃ n, u n < v + 1 ∧ 10 ≤ n := by
  have h := (hu.eventually_lt_const (lt_add_one v)).and (eventually_ge_atTop 10)
  obtain ⟨n, hn1, hn2⟩ := h.exists
  exact ⟨n, hn1, hn2⟩

/-! ### W2. A lower bound that holds far out passes to the limit: R31, R33 -/
example (u : ℕ → ℝ) (a : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hb : ∀ n, 3 ≤ n → 2 ≤ u n) :
    2 ≤ a := by
  have hev : ∀ᶠ n in atTop, 2 ≤ u n := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact hb n hn
  exact ge_of_tendsto hu hev

/-! ### W3. Some value of a sequence beats `sSup - 1`: R19, R20, R22, R23 -/
example (u : ℕ → ℝ) : ∃ N, sSup (range u) - 1 < u N := by
  obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup (range_nonempty u) (sub_lt_self _ one_pos)
  exact ⟨N, hN⟩

/-! ### W4. `a ≤ b + 1/(n+1)` for every `n` gives `a ≤ b`: R29, R30, R34, R35, R18 -/
example (a b : ℝ) (h : ∀ n : ℕ, a ≤ b + 1 / ((n : ℝ) + 1)) : a ≤ b := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have h3 : 1 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hn
    nlinarith
  linarith [h n]

end H045Guide
