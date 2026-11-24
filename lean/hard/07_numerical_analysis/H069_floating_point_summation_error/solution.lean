/- H069 | Floating-point summation error | 1-1.5 h | inductive types, structural induction, relative error model, gcongr, mathlib
GOAL
  Standard model: each rounded addition returns `s (1 + δ)` with `|δ| ≤ u`. Adding along any binary tree has
  error `≤ ((1 + u)^depth - 1) · ∑ |xᵢ|`; also prove the list version (recursive summation, depth `n`) directly.
  (Pairwise summation has depth ⌈log₂ n⌉, which is why it is far more accurate.)

REFERENCE
  `induction t with | leaf x => _ | node l r ihl ihr => _`   -- structural induction on your own inductive type
  `simp only [STree.flSum, STree.exact]` unfolds definitions at a constructor; `obtain ⟨δ, hδ, hs⟩ := hfl s`
  #check abs_add_le           -- |a + b| ≤ |a| + |b|
  #check abs_mul              -- |a * b| = |a| * |b|
  #check pow_le_pow_right₀    -- 1 ≤ a → n ≤ m → a ^ n ≤ a ^ m
  #check one_le_pow₀          -- 1 ≤ a → 1 ≤ a ^ n
  example (l r : ℕ) : l ≤ max l r := le_max_left l r
  example (u δ : ℝ) (h : |δ| ≤ u) : -u ≤ δ ∧ δ ≤ u := abs_le.mp h
  example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by gcongr
  example (s e δ : ℝ) : (s + e) * (1 + δ) - s = e * (1 + δ) + s * δ := by ring   -- propagated + new error
  #check List.sum_nonneg      -- (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
NOTE: `RelErr u fl` is all you know about `fl`. Key identity: ((1 + u)^d - 1)(1 + u) + u = (1 + u)^(d+1) - 1.
-/
import Mathlib

namespace H069

-- BEGIN SPEC
/-- `fl` rounds every real with relative error at most `u`. -/
def RelErr (u : ℝ) (fl : ℝ → ℝ) : Prop := ∀ x, ∃ δ, |δ| ≤ u ∧ fl x = x * (1 + δ)

/-- a summation order: leaves hold the inputs, each node is one addition -/
inductive STree where
  | leaf (x : ℝ)
  | node (l r : STree)

/-- the exact sum of the leaves -/
def STree.exact : STree → ℝ
  | leaf x => x
  | node l r => l.exact + r.exact
/-- `∑ |xᵢ|` over the leaves -/
def STree.absSum : STree → ℝ
  | leaf x => |x|
  | node l r => l.absSum + r.absSum
/-- number of additions on the longest root-to-leaf path -/
def STree.depth : STree → ℕ
  | leaf _ => 0
  | node l r => max l.depth r.depth + 1
/-- the floating-point sum: every addition is rounded -/
def STree.flSum (fl : ℝ → ℝ) : STree → ℝ
  | leaf x => x
  | node l r => fl (l.flSum fl + r.flSum fl)

/-- recursive summation of a list: `[x₁, …, xₙ] ↦ fl (x₁ + fl (x₂ + … fl (xₙ + 0)))` -/
def fsum (fl : ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => fl (x + fsum fl xs)
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem abs_exact_le (t : STree) : |t.exact| ≤ t.absSum := by
  induction t with
  | leaf x => simp [STree.exact, STree.absSum]
  | node l r ihl ihr =>
    simp only [STree.exact, STree.absSum]
    exact (abs_add_le _ _).trans (add_le_add ihl ihr)

-- MILESTONE (optional: change or delete)
theorem abs_list_sum_le (xs : List ℝ) : |xs.sum| ≤ (xs.map abs).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le _ _).trans (by linarith)

-- MILESTONE (optional: change or delete)
theorem one_add_delta (u δ : ℝ) (hδ : |δ| ≤ u) : |1 + δ| ≤ 1 + u := by
  rw [abs_le] at hδ ⊢
  constructor <;> linarith

-- BEGIN SPEC
theorem tree_sum_error (u : ℝ) (hu : 0 ≤ u) (fl : ℝ → ℝ) (hfl : RelErr u fl) (t : STree) :
    |t.flSum fl - t.exact| ≤ ((1 + u) ^ t.depth - 1) * t.absSum :=
-- END SPEC
  by
    induction t with
    | leaf x => simp [STree.flSum, STree.exact, STree.depth]
    | node l r ihl ihr =>
      obtain ⟨δ, hδ, hs⟩ := hfl (l.flSum fl + r.flSum fl)
      simp only [STree.flSum, STree.exact, STree.absSum, STree.depth]
      rw [hs]
      set d := max l.depth r.depth
      have hAl : 0 ≤ l.absSum := (abs_nonneg _).trans (abs_exact_le l)
      have hAr : 0 ≤ r.absSum := (abs_nonneg _).trans (abs_exact_le r)
      -- WHY: the children have different depths; lift both bounds to the common depth `d`
      have el : |l.flSum fl - l.exact| ≤ ((1 + u) ^ d - 1) * l.absSum :=
        ihl.trans (by gcongr; exacts [by linarith, le_max_left _ _])
      have er : |r.flSum fl - r.exact| ≤ ((1 + u) ^ d - 1) * r.absSum :=
        ihr.trans (by gcongr; exacts [by linarith, le_max_right _ _])
      rw [show (l.flSum fl + r.flSum fl) * (1 + δ) - (l.exact + r.exact)
          = ((l.flSum fl - l.exact) + (r.flSum fl - r.exact)) * (1 + δ) + (l.exact + r.exact) * δ by ring]
      calc _ ≤ |((l.flSum fl - l.exact) + (r.flSum fl - r.exact)) * (1 + δ)|
              + |(l.exact + r.exact) * δ| := abs_add_le _ _
        _ ≤ (((1 + u) ^ d - 1) * l.absSum + ((1 + u) ^ d - 1) * r.absSum) * (1 + u)
              + (l.absSum + r.absSum) * u := by
            have hd1 : (1 : ℝ) ≤ (1 + u) ^ d := one_le_pow₀ (by linarith)
            rw [abs_mul, abs_mul]
            gcongr
            · exact (abs_add_le _ _).trans (add_le_add el er)
            · exact one_add_delta u δ hδ
            · exact (abs_add_le _ _).trans (add_le_add (abs_exact_le l) (abs_exact_le r))
        _ = ((1 + u) ^ (d + 1) - 1) * (l.absSum + r.absSum) := by ring

-- BEGIN SPEC
theorem fsum_error (u : ℝ) (hu : 0 ≤ u) (fl : ℝ → ℝ) (hfl : RelErr u fl) (xs : List ℝ) :
    |fsum fl xs - xs.sum| ≤ ((1 + u) ^ xs.length - 1) * (xs.map abs).sum :=
-- END SPEC
  by
    induction xs with
    | nil => simp [fsum]
    | cons x xs ih =>
      obtain ⟨δ, hδ, hs⟩ := hfl (x + fsum fl xs)
      simp only [fsum, List.sum_cons, List.map_cons, List.length_cons]
      rw [hs]
      have hA : 0 ≤ (xs.map abs).sum := List.sum_nonneg (by simp)
      have hn1 : (1 : ℝ) ≤ (1 + u) ^ xs.length := one_le_pow₀ (by linarith)
      rw [show (x + fsum fl xs) * (1 + δ) - (x + xs.sum)
          = (fsum fl xs - xs.sum) * (1 + δ) + (x + xs.sum) * δ by ring]
      calc _ ≤ |(fsum fl xs - xs.sum) * (1 + δ)| + |(x + xs.sum) * δ| := abs_add_le _ _
        _ ≤ ((1 + u) ^ xs.length - 1) * (xs.map abs).sum * (1 + u) + (|x| + (xs.map abs).sum) * u := by
            rw [abs_mul, abs_mul]
            gcongr
            · exact one_add_delta u δ hδ
            · exact (abs_add_le _ _).trans (by linarith [abs_list_sum_le xs])
        -- WHY: the new leaf `x` gets factor `u`, which is at most `(1 + u)^(n+1) - 1`
        _ ≤ ((1 + u) ^ (xs.length + 1) - 1) * (|x| + (xs.map abs).sum) := by
            rw [pow_succ]
            nlinarith [mul_nonneg (mul_nonneg (abs_nonneg x) (by linarith : (0 : ℝ) ≤ 1 + u))
              (sub_nonneg.mpr hn1)]

end H069

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on the tree. At a node, let `s = l.flSum fl + r.flSum fl` and take `δ` from `hfl s`; the new error
    is the children's errors times `(1 + δ)` plus the exact sum times `δ`.
H2. Raise both children's bounds to the common depth `d = max l.depth r.depth` (`pow_le_pow_right₀`, then `gcongr`;
    you need `0 ≤ absSum`, which follows from `abs_exact_le`). Then triangle inequality, `abs_mul`, `|1 + δ| ≤ 1 + u`,
    `|exact| ≤ absSum`, and finish with `ring` using the NOTE identity. The list version is the same induction on `xs`.
H3. Node: `rw [hs]` and `rw [show s * (1 + δ) - (l.exact + r.exact) = ((l.flSum fl - l.exact) + (r.flSum fl - r.exact)) * (1 + δ)
    + (l.exact + r.exact) * δ by ring]`, then `calc _ ≤ |… * (1 + δ)| + |… * δ| := abs_add_le _ _ ;
    _ ≤ (((1+u)^d - 1) * l.absSum + ((1+u)^d - 1) * r.absSum) * (1 + u) + (l.absSum + r.absSum) * u := by rw [abs_mul, abs_mul]; gcongr ...;
    _ = ((1 + u) ^ (d + 1) - 1) * (l.absSum + r.absSum) := by ring`. List: the last step needs `nlinarith` with `(1 + u)^n ≥ 1`.
-/
