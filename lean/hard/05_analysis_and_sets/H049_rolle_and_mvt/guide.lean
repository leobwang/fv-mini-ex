/- Guide for H049 (Rolle and the mean value theorem).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. `G : Prop`
is an arbitrary goal, and a hypothesis `k : … → G` is only there to consume the new fact, so the entry
shows what entered the context. A hypothesis `h` that finishes an example shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (`[0, 1]`, `2 * y`, minima).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H049Guide

/-! # Part R · Reference entries -/

/-! ## Intervals as conjunctions (milestone `endpoint`) -/

/-! ### R1. `simp only [Set.mem_Icc] at h` · context: `x ∈ Set.Icc a b` → `a ≤ x ∧ x ≤ b` -/
example {α : Type} [Preorder α] (a b x : α) (G : Prop) (h : x ∈ Set.Icc a b)
    (k : a ≤ x ∧ x ≤ b → G) : G := by
  simp only [Set.mem_Icc] at h
  exact k h

/-! ### R2. `simp only [Set.mem_Ioo] at h` · context: `x ∈ Set.Ioo a b` → `a < x ∧ x < b` -/
example {α : Type} [Preorder α] (a b x : α) (G : Prop) (h : x ∈ Set.Ioo a b)
    (k : a < x ∧ x < b → G) : G := by
  simp only [Set.mem_Ioo] at h
  exact k h

/-! ### R3. `not_and_or` · `¬(A ∧ B) ↔ ¬A ∨ ¬B` · context -/
example (A B G : Prop) (h : ¬(A ∧ B)) (k : ¬A ∨ ¬B → G) : G := by
  simp only [not_and_or] at h
  exact k h

/-! ### R4. `not_lt` · `¬a < b ↔ b ≤ a` · context (needs a linear order such as `ℝ`) -/
example {α : Type} [LinearOrder α] (a b : α) (G : Prop) (h : ¬a < b) (k : b ≤ a → G) : G := by
  simp only [not_lt] at h
  exact k h

/-! ### R5. `rcases h with h1 | h2` · goal list: one goal per side of `h : A ∨ B` -/
example (A B G : Prop) (h : A ∨ B) (ka : A → G) (kb : B → G) : G := by
  rcases h with h1 | h2
  exact ka h1
  exact kb h2

/-! ### R6. `left` / `right` · goal: `A ∨ B` → `A` (`left`) or `B` (`right`) -/
example (A B : Prop) (hb : B) : A ∨ B := by
  right
  exact hb

/-! ### R7. `linarith` · closes a goal that follows linearly from hypotheses (`<`, `≤`, `=` on `ℝ`) -/
example (a b x : ℝ) (h1 : x ≤ a) (h2 : a ≤ x) (h3 : a < b) : x = a ∧ x < b := by
  constructor
  linarith
  linarith

/-! ## Fermat at an interior point (milestone `interior_max`) -/

/-! ### R8. `hx.1`, `hx.2` · `x ∈ Set.Ioo a b` IS `a < x ∧ x < b`, so the projections work directly -/
example (a b x : ℝ) (hx : x ∈ Set.Ioo a b) (G : Prop) (k : a < x → G) : G := by
  have h1 : a < x := hx.1
  exact k h1

/-! ### R9. `Icc_mem_nhds` · `a < x → x < b → Set.Icc a b ∈ nhds x` · context
`s ∈ nhds x`: `s` contains an open interval around `x` (`s` is a neighbourhood of `x`). -/
example (a b x : ℝ) (h1 : a < x) (h2 : x < b) (G : Prop) (k : Set.Icc a b ∈ nhds x → G) : G := by
  have hn := Icc_mem_nhds h1 h2
  exact k hn

/-! ### R10. `IsMaxOn.isLocalMax` · `IsMaxOn f s c → s ∈ nhds c → IsLocalMax f c` · context -/
example (f : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (hmax : IsMaxOn f s c) (hn : s ∈ nhds c) (G : Prop)
    (k : IsLocalMax f c → G) : G := by
  have hl := hmax.isLocalMax hn
  exact k hl

/-! ### R11. `IsLocalMax.hasDerivAt_eq_zero` · Fermat: `IsLocalMax f c → HasDerivAt f d c → d = 0` -/
example (f : ℝ → ℝ) (c d : ℝ) (hl : IsLocalMax f c) (hd : HasDerivAt f d c) (G : Prop)
    (k : d = 0 → G) : G := by
  have h0 := hl.hasDerivAt_eq_zero hd
  exact k h0

/-! ## Derivatives of lines (milestone `line_hasDerivAt`) -/

/-! ### R12. `hasDerivAt_id x` · context gains `HasDerivAt id 1 x` (`id y = y` has slope 1) -/
example (x : ℝ) (G : Prop) (k : HasDerivAt id 1 x → G) : G := by
  have h1 := hasDerivAt_id x
  exact k h1

/-! ### R13. `HasDerivAt.sub_const` · `HasDerivAt g d x → HasDerivAt (fun y => g y - c) d x` -/
example (g : ℝ → ℝ) (d c x : ℝ) (hg : HasDerivAt g d x) (G : Prop)
    (k : HasDerivAt (fun y => g y - c) d x → G) : G := by
  have h2 := hg.sub_const c
  exact k h2

/-! ### R14. `HasDerivAt.const_mul` · `HasDerivAt g d x → HasDerivAt (fun y => c * g y) (c * d) x` -/
example (g : ℝ → ℝ) (d c x : ℝ) (hg : HasDerivAt g d x) (G : Prop)
    (k : HasDerivAt (fun y => c * g y) (c * d) x → G) : G := by
  have h3 := hg.const_mul c
  exact k h3

/-! ### R15. `simpa using h` · closes the goal: `simp` cleans both the goal and `h`, then `h` must match
Here it turns `c * 1` into `c`; it also unfolds `id y` to `y`. -/
example (g : ℝ → ℝ) (c x : ℝ) (h : HasDerivAt (fun y => c * g y) (c * 1) x) :
    HasDerivAt (fun y => c * g y) c x := by
  simpa using h

/-! ## Extreme value theorem (theorem `rolle`) -/

/-! ### R16. `Set.nonempty_Icc` · `(Set.Icc a b).Nonempty ↔ a ≤ b`; use `.mpr` for `→` from right to left -/
example (a b : ℝ) (hab : a ≤ b) (G : Prop) (k : (Set.Icc a b).Nonempty → G) : G := by
  have hne := Set.nonempty_Icc.mpr hab
  exact k hne

/-! ### R17. `h.le` (`LT.lt.le`) · `a < b → a ≤ b` -/
example (a b : ℝ) (h : a < b) (G : Prop) (k : a ≤ b → G) : G := by
  have hle := h.le
  exact k hle

/-! ### R18. `isCompact_Icc` · context gains `IsCompact (Set.Icc a b)` (closed bounded intervals) -/
example (a b : ℝ) (G : Prop) (k : IsCompact (Set.Icc a b) → G) : G := by
  have hK : IsCompact (Set.Icc a b) := isCompact_Icc
  exact k hK

/-! ### R19. `IsCompact.exists_isMaxOn` · goal closed; EVT: `IsCompact s → s.Nonempty → ContinuousOn f s → ∃ c ∈ s, IsMaxOn f s c` -/
example (f : ℝ → ℝ) (s : Set ℝ) (hK : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ c ∈ s, IsMaxOn f s c := by
  exact hK.exists_isMaxOn hne hf

/-! ### R20. `IsCompact.exists_isMinOn` · goal closed: the same for a minimum point -/
example (f : ℝ → ℝ) (s : Set ℝ) (hK : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ c ∈ s, IsMinOn f s c := by
  exact hK.exists_isMinOn hne hf

/-! ### R21. `obtain ⟨c, hc, hP⟩ := h` · context: `h : ∃ c ∈ s, Q c` → a point, its membership, its property
Write `-` instead of a name to drop a part: `obtain ⟨c, -, hP⟩ := h`. -/
example (s : Set ℝ) (Q : ℝ → Prop) (h : ∃ c ∈ s, Q c) (G : Prop) (k : ∀ c ∈ s, Q c → G) : G := by
  obtain ⟨c, hc, hP⟩ := h
  exact k c hc hP

/-! ### R22. `by_cases h : p` · goal list: a copy of the goal with `h : p` and one with `h : ¬p` -/
example (p G : Prop) (h1 : p → G) (h2 : ¬p → G) : G := by
  by_cases h : p
  exact h1 h
  exact h2 h

/-! ### R23. `exact ⟨c, hc, hP⟩` · closes `∃ c ∈ s, Q c` (point, membership, property) -/
example (s : Set ℝ) (Q : ℝ → Prop) (c : ℝ) (hc : c ∈ s) (hP : Q c) : ∃ x ∈ s, Q x := by
  exact ⟨c, hc, hP⟩

/-! ### R24. `IsMinOn.isLocalMin` · `IsMinOn f s c → s ∈ nhds c → IsLocalMin f c` · context -/
example (f : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (hmin : IsMinOn f s c) (hn : s ∈ nhds c) (G : Prop)
    (k : IsLocalMin f c → G) : G := by
  have hl := hmin.isLocalMin hn
  exact k hl

/-! ### R25. `IsLocalMin.hasDerivAt_eq_zero` · Fermat at a minimum: `IsLocalMin f c → HasDerivAt f d c → d = 0` -/
example (f : ℝ → ℝ) (c d : ℝ) (hl : IsLocalMin f c) (hd : HasDerivAt f d c) (G : Prop)
    (k : d = 0 → G) : G := by
  have h0 := hl.hasDerivAt_eq_zero hd
  exact k h0

/-! ### R26. `rcases h with rfl | rfl` · goal list and context: split `h : c = a ∨ c = b` and substitute
In each goal one of the two variables is replaced by the other everywhere (here `a`, then `b`, by `c`). -/
example (a b c : ℝ) (P : ℝ → Prop) (h : c = a ∨ c = b) (ha : P a) (hb : P b) : P c := by
  rcases h with rfl | rfl
  exact ha
  exact hb

/-! ### R27. `intro x hx` on `IsMaxOn f s c` · goal: `IsMaxOn` unfolds to `∀ x ∈ s, …`
The new goal is a set-builder membership; R28 rewrites it. -/
example (f : ℝ → ℝ) (s : Set ℝ) (c : ℝ) (h : ∀ y ∈ s, f y ≤ f c) : IsMaxOn f s c := by
  intro x hx
  exact h x hx

/-! ### R28. `show T` · goal: replaced by a definitionally equal goal `T` you write out -/
example (f : ℝ → ℝ) (c x : ℝ) (h : f x ≤ f c) : x ∈ {y | f y ≤ f c} := by
  show f x ≤ f c
  exact h

/-! ### R29. `have h1 : f x ≤ f c := hmax hx` · context: apply `hmax : IsMaxOn f s c` to `hx : x ∈ s`
Write the type: without it Lean records the unreadable `x ∈ {x | (fun x => f x ≤ f c) x}`. -/
example (f : ℝ → ℝ) (s : Set ℝ) (c x : ℝ) (hmax : IsMaxOn f s c) (hx : x ∈ s) (G : Prop)
    (k : f x ≤ f c → G) : G := by
  have h1 : f x ≤ f c := hmax hx
  exact k h1

/-! ### R30. `Set.Ioo_subset_Icc_self` · `Set.Ioo a b ⊆ Set.Icc a b`; applied to `hx : x ∈ Set.Ioo a b` -/
example (a b x : ℝ) (hx : x ∈ Set.Ioo a b) (G : Prop) (k : x ∈ Set.Icc a b → G) : G := by
  have hx' := Set.Ioo_subset_Icc_self hx
  exact k hx'

/-! ### R31. `⟨h1, h2⟩ : x ∈ Set.Ioo a b` · context: build a membership from its two inequalities -/
example (a b x : ℝ) (h1 : a < x) (h2 : x < b) (G : Prop) (k : x ∈ Set.Ioo a b → G) : G := by
  have hx : x ∈ Set.Ioo a b := ⟨h1, h2⟩
  exact k hx

/-! ## Tilting by a line (theorem `mvt`) -/

/-! ### R32. `set k := e with hk` · goal and context: `e` is renamed `k` everywhere; `hk : k = e` -/
example (u v : ℝ) (P : ℝ → Prop) (h : P (u - v)) : P (u - v) := by
  set k := u - v with hk
  exact h

/-! ### R33. `ContinuousOn.sub` · `ContinuousOn g s → ContinuousOn h s → ContinuousOn (g - h) s` -/
example (g l : ℝ → ℝ) (s : Set ℝ) (hg : ContinuousOn g s) (hl : ContinuousOn l s) (G : Prop)
    (k : ContinuousOn (fun y => g y - l y) s → G) : G := by
  have hc := hg.sub hl
  exact k hc

/-! ### R34. `fun_prop` · closes continuity goals for functions built from `+ - *`, constants and `y` -/
example (c d : ℝ) (s : Set ℝ) : ContinuousOn (fun y => c * (y + d)) s := by
  fun_prop

/-! ### R35. `HasDerivAt.sub` · `HasDerivAt g d x → HasDerivAt l e x → HasDerivAt (g - l) (d - e) x`
`g - l` is the function `fun y => g y - l y`; `exact` accepts either spelling. -/
example (g l : ℝ → ℝ) (d e x : ℝ) (hg : HasDerivAt g d x) (hl : HasDerivAt l e x) :
    HasDerivAt (fun y => g y - l y) (d - e) x := by
  exact hg.sub hl

/-! ### R36. `simp only [sub_self, mul_zero, sub_zero]` · goal: apply a `fun` to an argument and clean up
`sub_self : a - a = 0`, `mul_zero : a * 0 = 0`, `sub_zero : a - 0 = a`; `simp only` also performs the
application `(fun y => …) a` (β-reduction). Add `hk` from R32 to unfold a `set` name. -/
example (g : ℝ → ℝ) (c a : ℝ) (P : ℝ → Prop) (h : P (g a)) :
    P ((fun y => g y - c * (y - a)) a) := by
  simp only [sub_self, mul_zero, sub_zero]
  exact h

/-! ### R37. `field_simp` · goal: multiplies out denominators it can prove nonzero (from `hd : d ≠ 0`) -/
example (u v d : ℝ) (hd : d ≠ 0) : v = u + (v - u) / d * d := by
  field_simp
  ring

/-! ## Constant from zero derivative (theorem `const_of_deriv_zero`) -/

/-! ### R38. `eq_or_lt_of_le` · `a ≤ b → a = b ∨ a < b` · context -/
example (a b : ℝ) (h : a ≤ b) (G : Prop) (k : a = b ∨ a < b → G) : G := by
  have h' := eq_or_lt_of_le h
  exact k h'

/-! ### R39. `ContinuousOn.mono` · `ContinuousOn g s → t ⊆ s → ContinuousOn g t` · context -/
example (g : ℝ → ℝ) (s t : Set ℝ) (hg : ContinuousOn g s) (hts : t ⊆ s) (G : Prop)
    (k : ContinuousOn g t → G) : G := by
  have hgt := hg.mono hts
  exact k hgt

/-! ### R40. `Set.Icc_subset_Icc_right` · `b₁ ≤ b₂ → Set.Icc a b₁ ⊆ Set.Icc a b₂` · context -/
example (a b₁ b₂ : ℝ) (h : b₁ ≤ b₂) (G : Prop) (k : Set.Icc a b₁ ⊆ Set.Icc a b₂ → G) : G := by
  have hsub : Set.Icc a b₁ ⊆ Set.Icc a b₂ := Set.Icc_subset_Icc_right h
  exact k hsub

/-! ### R41. `h1.trans_le h2` (`LT.lt.trans_le`) · `a < b → b ≤ c → a < c` · context -/
example (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) (G : Prop) (k : a < c → G) : G := by
  have h3 := h1.trans_le h2
  exact k h3

/-! ### R42. `field_simp at h` · context: clears the denominator of a hypothesis (`hd : d ≠ 0` in context) -/
example (u d : ℝ) (hd : d ≠ 0) (h : 0 = u / d) (G : Prop) (k : 0 * d = u → G) : G := by
  field_simp at h
  exact k h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. EVT on `[0, 1]`: R16, R18, R20 -/
example (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, IsMinOn g (Set.Icc 0 1) x := by
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  exact isCompact_Icc.exists_isMinOn hne hg

/-! ### W2. Fermat at an interior minimum of `[0, 2]`: R9, R24, R25 -/
example (g : ℝ → ℝ) (d : ℝ) (hmin : IsMinOn g (Set.Icc 0 2) 1) (hd : HasDerivAt g d 1) : d = 0 := by
  have hn : Set.Icc (0 : ℝ) 2 ∈ nhds 1 := Icc_mem_nhds (by norm_num) (by norm_num)
  exact (hmin.isLocalMin hn).hasDerivAt_eq_zero hd

/-! ### W3. Slope of `y ↦ 2 * y - c`: R12, R14, R13, then R15 -/
example (c x : ℝ) : HasDerivAt (fun y => 2 * y - c) 2 x := by
  simpa using ((hasDerivAt_id x).const_mul 2).sub_const c

/-! ### W4. Tilting `g` by `2 * y`: continuity (R33, R34) and derivative (R35) -/
example (g g' : ℝ → ℝ) (s : Set ℝ) (hg : ContinuousOn g s) (x : ℝ) (hd : HasDerivAt g (g' x) x) :
    ContinuousOn (fun y => g y - 2 * y) s ∧ HasDerivAt (fun y => g y - 2 * y) (g' x - 2) x := by
  constructor
  · exact hg.sub (by fun_prop)
  · exact hd.sub (by simpa using (hasDerivAt_id x).const_mul 2)

/-! ### W5. Restrict continuity from `[0, 2]` to `[0, 1]`: R39, R40 -/
example (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 2)) : ContinuousOn g (Set.Icc 0 1) :=
  hg.mono (Set.Icc_subset_Icc_right (by norm_num))

end H049Guide
