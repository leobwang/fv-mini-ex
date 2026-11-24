/- Guide for H073 (Euler's method for y' = y converges to exp).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` with `g : … → G` is an arbitrary goal, for entries that only add a fact to the context.
Part W: worked combinations on objects that are NOT the exercise's (a geometric recursion, `e^{y/3}`,
an abstract sequence `u`).
Infoview: `↑n` is `n : ℕ` cast to `ℝ`; `|a|` is `abs a`; `‖a‖` is the norm (for `ℝ`, also `|a|`).
Assumed: Lean basics (E001–E033).
-/
import Mathlib

open Filter Topology

namespace H073Guide

/-- A toy recursion used below (not the exercise's): `geo c k = c * c * … * c` (`k` factors). -/
noncomputable def geo (c : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => c * geo c k

/-! # Part R · Reference entries -/

/-! ## A recursive sequence in closed form -/

/-! ### R1. `induction k` · goal list: `P k` → `P 0` and `P (k + 1)` with the hypothesis `P k`
`case succ k ih =>` names the new variable and the induction hypothesis; the problem's
`induction k with | zero => … | succ k ih => …` is the same with both cases in one block. -/
example (P : ℕ → Prop) (h0 : P 0) (hs : ∀ k, P k → P (k + 1)) (k : ℕ) : P k := by
  induction k
  case zero => exact h0
  case succ k ih => exact hs k ih

/-! ### R2. `rw [f]` on a function defined by pattern matching · goal: `f (k + 1)` → its `k + 1` clause
`rw` uses the first equation of `f` that matches; `f 0` would become the `0` clause. -/
example (c : ℝ) (k : ℕ) (P : ℝ → Prop) (h : P (c * geo c k)) : P (geo c (k + 1)) := by
  rw [geo]
  exact h

/-! ### R3. `pow_succ` · `a ^ (n + 1) = a ^ n * a` · goal -/
example {M : Type} [Monoid M] (a : M) (n : ℕ) (P : M → Prop) (h : P (a ^ n * a)) :
    P (a ^ (n + 1)) := by
  rw [pow_succ]
  exact h

/-! ## One exact step versus one Euler step -/

/-! ### R4. `exact_mod_cast h` · closes a goal that is `h` up to casts (`ℕ → ℝ` here) -/
example (n : ℕ) (hn : 0 < n) : (0 : ℝ) < n := by
  exact_mod_cast hn

/-! ### R5. `abs_div` · `|a / b| = |a| / |b|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P (|a| / |b|)) : P |a / b| := by
  rw [abs_div]
  exact h

/-! ### R6. `abs_of_pos` · `0 < a → |a| = a` · goal -/
example (a : ℝ) (ha : 0 < a) (P : ℝ → Prop) (h : P a) : P |a| := by
  rw [abs_of_pos ha]
  exact h

/-! ### R7. `div_le_one` · `0 < b → (a / b ≤ 1 ↔ a ≤ b)` · goal -/
example (a b : ℝ) (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  rw [div_le_one hb]
  exact h

/-! ### R8. `Real.abs_exp_sub_one_sub_id_le` · `|y| ≤ 1 → |Real.exp y - 1 - y| ≤ y ^ 2` · context
The second-order Taylor bound for `exp` near 0. -/
example (y : ℝ) (hy : |y| ≤ 1) (G : Prop) (g : |Real.exp y - 1 - y| ≤ y ^ 2 → G) : G := by
  have h := Real.abs_exp_sub_one_sub_id_le hy
  exact g h

/-! ### R9. `sub_sub` · `a - b - c = a - (b + c)` · goal -/
example (a b c : ℝ) (P : ℝ → Prop) (h : P (a - (b + c))) : P (a - b - c) := by
  rw [sub_sub]
  exact h

/-! ### R10. `simpa [l] using e` · closes the goal: simplifies both the goal and `e`'s type, then matches -/
example (a b c r : ℝ) (e : |a - b - c| ≤ r) : |a - (b + c)| ≤ r := by
  simpa [sub_sub] using e

/-! ## Bounding both bases by `e^{|x|/n}` -/

/-! ### R11. `Real.abs_exp` · `|Real.exp y| = Real.exp y` · goal -/
example (y : ℝ) (P : ℝ → Prop) (h : P (Real.exp y)) : P |Real.exp y| := by
  rw [Real.abs_exp]
  exact h

/-! ### R12. `Real.exp_le_exp` · `Real.exp a ≤ Real.exp b ↔ a ≤ b` · goal -/
example (a b : ℝ) (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  rw [Real.exp_le_exp]
  exact h

/-! ### R13. `div_le_div_iff_of_pos_right` · `0 < c → (a / c ≤ b / c ↔ a ≤ b)` · goal -/
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b) : a / c ≤ b / c := by
  rw [div_le_div_iff_of_pos_right hc]
  exact h

/-! ### R14. `le_abs_self` · `a ≤ |a|` · closes the goal -/
example (a : ℝ) : a ≤ |a| := by
  exact le_abs_self a

/-! ### R15. `calc` · goal list: a chain `a ≤ b = c` → one goal per link (here left as `?_`)
Usually each link is proved right after its `:=`; `_` stands for the previous right-hand side. -/
example (a b c : ℝ) (h1 : a ≤ b) (h2 : b = c) : a ≤ c := by
  calc a ≤ b := ?_
    _ = c := ?_
  exacts [h1, h2]

/-! ### R16. `abs_add_le` · `|a + b| ≤ |a| + |b|` (triangle inequality) · context -/
example (a b : ℝ) (G : Prop) (g : |a + b| ≤ |a| + |b| → G) : G := by
  have h := abs_add_le a b
  exact g h

/-! ### R17. `Real.add_one_le_exp` · `y + 1 ≤ Real.exp y` · context -/
example (y : ℝ) (G : Prop) (g : y + 1 ≤ Real.exp y → G) : G := by
  have h := Real.add_one_le_exp y
  exact g h

/-! ## Powers of an exponential; truncated subtraction -/

/-! ### R18. `Real.exp_nat_mul` · `Real.exp (↑n * y) = Real.exp y ^ n`; `rw [← Real.exp_nat_mul]` · goal -/
example (y : ℝ) (n : ℕ) (P : ℝ → Prop) (h : P (Real.exp (n * y))) : P (Real.exp y ^ n) := by
  rw [← Real.exp_nat_mul]
  exact h

/-! ### R19. `Nat.cast_sub` · `m ≤ n → ↑(n - m) = ↑n - ↑m` · goal
`n - m` in `ℕ` is truncated (`2 - 5 = 0`), so moving it into `ℝ` needs `m ≤ n`. -/
example (n m : ℕ) (hmn : m ≤ n) (P : ℝ → Prop) (h : P ((n : ℝ) - (m : ℝ))) :
    P ((n - m : ℕ) : ℝ) := by
  rw [Nat.cast_sub hmn]
  exact h

/-! ### R20. `Nat.cast_one` · `↑1 = 1` (the natural number `1` cast to `ℝ`) · goal -/
example (P : ℝ → Prop) (h : P 1) : P ((1 : ℕ) : ℝ) := by
  rw [Nat.cast_one]
  exact h

/-! ### R21. `omega` · closes linear arithmetic over `ℕ` and `ℤ` (`max`, `min`, truncated `-` included) -/
example (n N : ℕ) (hn : max N 1 ≤ n) : 1 ≤ n := by
  omega

/-! ### R22. `field_simp` · goal: clears denominators it can prove nonzero (from hypotheses such as
`hk : 0 < k` or `k ≠ 0`); it may close the goal outright -/
example (y k : ℝ) (hk : 0 < k) (h : y + k = k * 2) : y / k + 1 = 2 := by
  field_simp
  exact h

/-! ### R23. `positivity` · closes `0 ≤ e` or `0 < e` when `e` is built from `|·|`, `Real.exp`, squares,
casts of `ℕ`, `+`, `*`, `/` -/
example (y : ℝ) (k : ℕ) : 0 ≤ |y| / k := by
  positivity

/-! ### R24. `linarith` · closes a linear (in)equality that follows from hypotheses by adding them up -/
example (a b c : ℝ) (h1 : a = b - c) (h2 : 0 ≤ c) : a ≤ b := by
  linarith

/-! ## The error bound -/

/-! ### R25. `set a := e` · context gains `a : T := e`; goal: every `e` → `a` -/
example (y : ℝ) (P : ℝ → Prop) (h : ∀ t, P t) : P (Real.exp y) := by
  set a := Real.exp y
  exact h a

/-! ### R26. `congr 1` · goal `f a = f b` → `a = b` (it closes that by itself when `a = b` is a hypothesis) -/
example (a b : ℝ) (h : a - b = 0) : Real.exp a = Real.exp b := by
  congr 1
  linarith

/-! ### R27. `obtain ⟨ha, hb⟩ := h` · context: `h : A ∧ B` → `ha : A`, `hb : B` -/
example (A B G : Prop) (h : A ∧ B) (g : A → B → G) : G := by
  obtain ⟨ha, hb⟩ := h
  exact g ha hb

/-! ### R28. `pow_le_pow_left₀` · `0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n` · context -/
example (a b : ℝ) (n : ℕ) (h0 : 0 ≤ a) (hab : a ≤ b) (G : Prop) (g : a ^ n ≤ b ^ n → G) : G := by
  have h := pow_le_pow_left₀ h0 hab n
  exact g h

/-! ### R29. `le_max_of_le_left` · `a ≤ b → a ≤ max b c` · context; with `abs_nonneg`
`abs_nonneg r : 0 ≤ |r|`. The second example chains the two into `0 ≤ max |r| s`. -/
example {α : Type} [LinearOrder α] (a b c : α) (hab : a ≤ b) (G : Prop) (g : a ≤ max b c → G) :
    G := by
  have h := le_max_of_le_left (c := c) hab
  exact g h

example (r s : ℝ) (G : Prop) (g : 0 ≤ max |r| s → G) : G := by
  have h0 := abs_nonneg r
  have h := le_max_of_le_left (c := s) h0
  exact g h

/-! ### R30. `max_le` · `a ≤ c → b ≤ c → max a b ≤ c` · context -/
example {α : Type} [LinearOrder α] (a b c : α) (hac : a ≤ c) (hbc : b ≤ c) (G : Prop)
    (g : max a b ≤ c → G) : G := by
  have h := max_le hac hbc
  exact g h

/-! ### R31. `h₁.trans h₂` (`le_trans`) · context: from `a ≤ b` and `b ≤ c` get `a ≤ c` -/
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) (G : Prop) (g : a ≤ c → G) : G := by
  have h := h₁.trans h₂
  exact g h

/-! ### R32. `abs_pow_sub_pow_le` · `|a ^ n - b ^ n| ≤ |a - b| * ↑n * max |a| |b| ^ (n - 1)` · context
The mean-value bound for `t ↦ tⁿ`: `aⁿ - bⁿ = (a - b)(aⁿ⁻¹ + aⁿ⁻²b + … + bⁿ⁻¹)`, `n` terms. -/
example (a b : ℝ) (n : ℕ) (G : Prop)
    (g : |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) → G) : G := by
  have h := abs_pow_sub_pow_le a b n
  exact g h

/-! ### R33. `gcongr` · goal `f s ≤ f S` (same shape both sides) → the goals `s ≤ S` for the parts
that differ. It closes a part by itself when that inequality is a hypothesis (here `hM`), and proves
the needed `0 ≤ …` side conditions with `positivity`. -/
example (s t r M : ℝ) (k m : ℕ) (hM : |t| ^ m ≤ M) (g : ∀ z : ℝ, |s| ≤ z ^ 2) :
    |s| * k * |t| ^ m ≤ r ^ 2 * k * M := by
  gcongr
  exact g r

/-! ## Limits along `atTop` -/

/-! ### R34. `tendsto_iff_norm_sub_tendsto_zero` · goal: `u → L` ↔ `‖u n - L‖ → 0` -/
example (u : ℕ → ℝ) (L : ℝ) (h : Tendsto (fun n => ‖u n - L‖) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h

/-! ### R35. `squeeze_zero'` · goal list: `f → 0` → `0 ≤ f` eventually, `f ≤ g` eventually (`g → 0` given)
`squeeze_zero' : (∀ᶠ t in l, 0 ≤ f t) → (∀ᶠ t in l, f t ≤ g t) → Tendsto g l (𝓝 0) → Tendsto f l (𝓝 0)`.
Give the third argument: it fixes `g`. -/
example (f g : ℕ → ℝ) (h1 : ∀ᶠ t in atTop, 0 ≤ f t) (h2 : ∀ᶠ t in atTop, f t ≤ g t)
    (hg : Tendsto g atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hg
  exacts [h1, h2]

/-! ### R36. `Eventually.of_forall` · goal: `∀ᶠ n in atTop, p n` → `∀ n, p n` (always ⇒ eventually) -/
example (p : ℕ → Prop) (h : ∀ n, p n) : ∀ᶠ n in atTop, p n := by
  apply Eventually.of_forall
  exact h

/-! ### R37. `norm_nonneg` · `0 ≤ ‖v‖` · closes the goal -/
example (v : ℝ) : 0 ≤ ‖v‖ := by
  exact norm_nonneg v

/-! ### R38. `tendsto_const_div_atTop_nhds_zero_nat` · `C / ↑n → 0` · closes the goal -/
example (C : ℝ) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat C

/-! ### R39. `exists_nat_ge` · `∃ N : ℕ, y ≤ ↑N` (ℝ is Archimedean) · context, with `obtain` (R27) -/
example (y : ℝ) (G : Prop) (g : ∀ N : ℕ, y ≤ N → G) : G := by
  obtain ⟨N, hN⟩ := exists_nat_ge y
  exact g N hN

/-! ### R40. `filter_upwards [eventually_ge_atTop N] with n hn` · goal: `∀ᶠ n in atTop, p n` →
`p n` for a fixed `n` with `hn : N ≤ n` (`eventually_ge_atTop N : ∀ᶠ n in atTop, N ≤ n`) -/
example (p : ℕ → Prop) (N : ℕ) (h : ∀ n, N ≤ n → p n) : ∀ᶠ n in atTop, p n := by
  filter_upwards [eventually_ge_atTop N] with n hn
  exact h n hn

/-! ### R41. `Real.norm_eq_abs` · `‖r‖ = |r|` for `r : ℝ` · goal -/
example (r : ℝ) (P : ℝ → Prop) (h : P |r|) : P ‖r‖ := by
  rw [Real.norm_eq_abs]
  exact h

/-! ### R42. `abs_sub_comm` · `|a - b| = |b - a|` · goal -/
example (a b : ℝ) (P : ℝ → Prop) (h : P |b - a|) : P |a - b| := by
  rw [abs_sub_comm]
  exact h

/-! ### R43. `le_of_max_le_left` · `max a b ≤ c → a ≤ c` · context -/
example {α : Type} [LinearOrder α] (a b c : α) (hm : max a b ≤ c) (G : Prop) (g : a ≤ c → G) :
    G := by
  have h := le_of_max_le_left hm
  exact g h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. A recursion in closed form: R1, R2, R3, then `ring` -/
example (c : ℝ) (k : ℕ) : geo c k = c ^ k := by
  induction k with
    | zero => rfl
    | succ k ih => rw [geo, ih, pow_succ]; ring

/-! ### W2. A power of an exponential is one exponential: R18, R26, R22, then `ring` -/
example (y : ℝ) : Real.exp (y / 3) ^ 3 = Real.exp y := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp
  ring

/-! ### W3. From an eventual `C / n` bound to a limit: R34, R35, R36 + R37, R38, R40, R41 -/
example (u : ℕ → ℝ) (L C : ℝ) (N : ℕ) (hb : ∀ n : ℕ, N ≤ n → |u n - L| ≤ C / n) :
    Tendsto u atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.norm_eq_abs]
  exact hb n hn

end H073Guide
