/- H081 | Tsirelson's bound | 1.5-2 h | CHSH, Cauchy–Schwarz, Hermitian involutions, EuclideanSpace, mathlib
GOAL
  Alice measures `A₀` or `A₁`, Bob `B₀` or `B₁`: Hermitian matrices with square 1 (±1-valued observables),
  each of Alice's commuting with each of Bob's. For every unit vector `ψ`, the CHSH value
  `⟨ψ| A₀B₀ + A₀B₁ + A₁B₀ − A₁B₁ |ψ⟩` is at most `2√2` (local hidden variables only reach 2).

GUIDE
  Entries R1–R42: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

open Matrix

namespace H081

-- MILESTONE (optional: change or delete)
/- SKELETON · cauchy_schwarz
  1. Cauchy–Schwarz for `WithLp.toLp 2 x`, `WithLp.toLp 2 y` in `EuclideanSpace ℂ n`, as a hypothesis:  R1, R2
  2. Translate the inner product (R4 once per vector; R5's rewrite then closes it):  R3 → R4 → R4 → R5
       hi : inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y) = star x ⬝ᵥ y
  3. Translate the squared norms (one `∀ z` fact serves both):                 intro z, R6 → R3 → R4 → R5
       hn : ∀ z : n → ℂ, ‖(WithLp.toLp 2 z : EuclideanSpace ℂ n)‖ ^ 2 = (star z ⬝ᵥ z).re
     `rw` leaves `RCLike.re (star z ⬝ᵥ z) = (star z ⬝ᵥ z).re`: both sides are the same real part, `rfl`
  4. Put `hi` into the step-1 hypothesis:                                       R7
  5. calc ‖star x ⬝ᵥ y‖ ^ 2 ≤ (‖toLp x‖ * ‖toLp y‖) ^ 2   (square step 4)        R8, R9 with R10
                       _ = _                         (split, then rw [hn, hn])  R11
-/
/-- Cauchy–Schwarz for `star x ⬝ᵥ y` (same as H077's milestone) -/
theorem cauchy_schwarz {n : Type} [Fintype n] (x y : n → ℂ) :
    ‖star x ⬝ᵥ y‖ ^ 2 ≤ (star x ⬝ᵥ x).re * (star y ⬝ᵥ y).re := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · unitary_expect
  1. Milestone `cauchy_schwarz` with x := ψ, y := W *ᵥ ψ, as a hypothesis h
  2. Prove h2 : star (W *ᵥ ψ) ⬝ᵥ (W *ᵥ ψ) = 1:                               R12 → R13 → R14 → rw [hW] → R15 → rw [hψ]
  3. Rewrite hψ and h2 into h, then clean `Complex.re 1 * …`:                   R7, R16
       h : ‖star ψ ⬝ᵥ W *ᵥ ψ‖ ^ 2 ≤ 1
  4. ‖z‖ ^ 2 ≤ 1 and 0 ≤ ‖z‖ give ‖z‖ ≤ 1:                                       R17 with hint R10
-/
/-- an isometry `W` (`Wᴴ W = 1`) has expectation values of modulus at most 1 -/
theorem unitary_expect {n : Type} [Fintype n] [DecidableEq n] (W : Matrix n n ℂ) (hW : Wᴴ * W = 1)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : ‖star ψ ⬝ᵥ (W *ᵥ ψ)‖ ≤ 1 := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · chsh_sq_matrix
  1. Two helpers (each proved by intro, then R19 and rw with its hypothesis):  R18
       sw  : ∀ {a b : Matrix n n ℂ}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x)
       sq1 : ∀ {a : Matrix n n ℂ}, a * a = 1 → ∀ x, a * (a * x) = x
  2. ONE `simp only`: distribute, re-associate right, then move every A left of every B
     (sw c₀₀ … sw c₁₁) and cancel squares (sq1 sA₀, sq1 sA₁; the B squares sit at the end,
     so sB₀, sB₁ themselves):                                                   R20, R21, R22
  3. Remove the leftover `* 1`:                                                 R23
  4. Split the numeral 4, then match both sides:                                R24, R25
-/
/-- the CHSH operator squared (M142 on matrices) -/
theorem chsh_sq_matrix {n : Type} [Fintype n] [DecidableEq n] (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (sA₀ : A₀ * A₀ = 1) (sA₁ : A₁ * A₁ = 1) (sB₀ : B₀ * B₀ = 1) (sB₁ : B₁ * B₁ = 1)
    (c₀₀ : A₀ * B₀ = B₀ * A₀) (c₀₁ : A₀ * B₁ = B₁ * A₀) (c₁₀ : A₁ * B₀ = B₀ * A₁)
    (c₁₁ : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · expect_sq_le
  1. Milestone `cauchy_schwarz` with x := ψ, y := C *ᵥ ψ, as a hypothesis h
  2. Prove e : star (C *ᵥ ψ) ⬝ᵥ (C *ᵥ ψ) = star ψ ⬝ᵥ ((C * C) *ᵥ ψ):            R12 → R26 → R13 (←) → R27
  3. Rewrite hψ and e into h, then clean `Complex.re 1 * …`:                    R7, R16
       h : ‖star ψ ⬝ᵥ C *ᵥ ψ‖ ^ 2 ≤ (star ψ ⬝ᵥ (C * C) *ᵥ ψ).re
  4. hre : |(star ψ ⬝ᵥ C *ᵥ ψ).re| ≤ ‖star ψ ⬝ᵥ C *ᵥ ψ‖:                       R28
  5. Close:                                                                     R17 with hints abs_nonneg, R29
-/
/-- for Hermitian `C`: `⟨C⟩² ≤ ⟨C²⟩` -/
theorem expect_sq_le {n : Type} [Fintype n] [DecidableEq n] (C : Matrix n n ℂ) (hC : C.IsHermitian)
    (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (star ψ ⬝ᵥ (C *ᵥ ψ)).re ^ 2 ≤ (star ψ ⬝ᵥ ((C * C) *ᵥ ψ)).re := by
  sorry

/- SKELETON · tsirelson
  Prove the milestones first: cauchy_schwarz (used by the next two), unitary_expect (step 3),
  chsh_sq_matrix (step 4), expect_sq_le (step 6).
  1. Name the operator: C, with hCdef : C = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁:        R30
  2. hC : C.IsHermitian, one `simp only` with hCdef and the c's:                 R31, R32, R33, R26
  3. Each product of four observables has expectation modulus ≤ 1. Helpers:
       u  : P.IsHermitian → P * P = 1 → Pᴴ * P = 1                              R26, rw [sP]
       um : Pᴴ * P = 1 → Qᴴ * Q = 1 → (P * Q)ᴴ * (P * Q) = 1:
            R33, then re-associate until `Pᴴ * P` is one factor (`mul_assoc`, then R19 aimed at
            `Pᴴ`: plain `← mul_assoc` gives `Qᴴ * Pᴴ * P * Q`), then rw [hP], `one_mul`, rw [hQ]
       b  : (Hermitian involutions P Q R S) → ‖star ψ ⬝ᵥ ((P * Q * (R * S)) *ᵥ ψ)‖ ≤ 1
            = unitary_expect applied to um (um (u …) (u …)) (um (u …) (u …))
  4. e : star ψ ⬝ᵥ ((C * C) *ᵥ ψ) = 4 - (the four expectations of A·A·(B·B), signs + − − +):
       rw [hCdef, chsh_sq_matrix …]; `simp` with R20 (sub_mul, mul_sub), R34, R35, hψ
       (R36 is applied by `simp` itself); then `ring`
  5. For each of the four products: R28 (h1 … h4) and b (b1 … b4)
  6. h8 : (star ψ ⬝ᵥ C *ᵥ ψ).re ^ 2 ≤ 8:
       R37 with expect_sq_le, rw [e], R38, `norm_num` (R39), R40 on h1 … h4, R41
  7. From h8 to ≤ 2 * √2:                                                       R17 with R42 hints
-/
-- BEGIN SPEC
theorem tsirelson {n : Type} [Fintype n] [DecidableEq n] (A₀ A₁ B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian) (hA₁ : A₁.IsHermitian) (hB₀ : B₀.IsHermitian) (hB₁ : B₁.IsHermitian)
    (sA₀ : A₀ * A₀ = 1) (sA₁ : A₁ * A₁ = 1) (sB₀ : B₀ * B₀ = 1) (sB₁ : B₁ * B₁ = 1)
    (c₀₀ : A₀ * B₀ = B₀ * A₀) (c₀₁ : A₀ * B₁ = B₁ * A₀) (c₁₀ : A₁ * B₀ = B₀ * A₁)
    (c₁₁ : A₁ * B₁ = B₁ * A₁) (ψ : n → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (star ψ ⬝ᵥ ((A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) *ᵥ ψ)).re ≤ 2 * Real.sqrt 2 :=
-- END SPEC
  sorry

end H081

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Let `C` be the CHSH operator. It is Hermitian, so `⟨C⟩² ≤ ⟨C²⟩` (`expect_sq_le`). By `chsh_sq_matrix`,
    `C² = 4 − [A₀,A₁][B₀,B₁]`; the commutator product expands into four products like `A₀A₁B₀B₁`. Each is a
    product of Hermitian involutions, hence unitary, so its expectation has modulus ≤ 1 (`unitary_expect`).
    So `⟨C²⟩ ≤ 8` and `⟨C⟩ ≤ √8 = 2√2`.
H2. `cauchy_schwarz`: R2 on `WithLp.toLp 2 x`, `WithLp.toLp 2 y`, translate with R3–R6, square with
    `pow_le_pow_left₀` (R9) inside a `calc` (R8). `unitary_expect` and `expect_sq_le`: `cauchy_schwarz ψ (W *ᵥ ψ)`,
    then move the matrices across `⬝ᵥ` (R12–R15, R26, R27) and finish with `nlinarith` (R17).
    `chsh_sq_matrix`: helpers `sw`, `sq1` (R18) fed with `mul_assoc` to one `simp only` (R20–R22), then R23–R25.
    `tsirelson`: skeleton steps 1–7.
H3. `chsh_sq_matrix`: `simp only [add_mul, mul_add, sub_mul, mul_sub, mul_assoc, sw c₀₀, sw c₀₁, sw c₁₀, sw c₁₁,
    sq1 sA₀, sq1 sA₁, sB₀, sB₁]`, `simp only [mul_one]`, `rw [show (4 : Matrix n n ℂ) = 1 + 1 + 1 + 1 by norm_num]`,
    `abel`. `expect_sq_le`: `e` by `rw [star_mulVec, hC.eq, ← dotProduct_mulVec, mulVec_mulVec]`; close with
    `nlinarith [abs_nonneg (star ψ ⬝ᵥ (C *ᵥ ψ)).re, sq_abs (star ψ ⬝ᵥ (C *ᵥ ψ)).re]`. `tsirelson`, step 4:
    `simp [sub_mul, mul_sub, sub_mulVec, dotProduct_sub, hψ]` then `ring`; step 7:
    `nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]`.
-/
