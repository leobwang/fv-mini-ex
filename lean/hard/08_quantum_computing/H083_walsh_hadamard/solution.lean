/- H083 | Walsh–Hadamard: Bernstein–Vazirani and Deutsch–Jozsa | 1-1.5 h | Hadamard transform, character sums, Fintype.prod_sum, Finset.sum_comm, mathlib
GOAL
  `W` is the closed form of `H^{⊗n}` (defined directly, not as a Kronecker power): on amplitudes `v` over bit
  strings, `(W v) y = 2^{-n/2} ∑ₓ (−1)^{x·y} v x`. Prove `W ∘ W = id`,
  Bernstein–Vazirani (`W` maps the phase state `2^{-n/2}(−1)^{s·x}` to the basis state `|s⟩`) and
  Deutsch–Jozsa (for a balanced `f`, the amplitude of `|0…0⟩` after `W` is 0).

GUIDE
  Entries R1–R44: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace H083

-- BEGIN SPEC
/-- `x·y` (we only use its parity, through `(−1)^(x·y)`) -/
def dot {n : ℕ} (x y : Fin n → Fin 2) : ℕ := ∑ i, (x i).val * (y i).val

/-- `H^{⊗n}` in closed form: `(W v) y = 2^{-n/2} ∑ₓ (−1)^{x·y} v x` -/
noncomputable def W {n : ℕ} (v : (Fin n → Fin 2) → ℂ) : (Fin n → Fin 2) → ℂ :=
  fun y => (Real.sqrt (2 ^ n) : ℂ)⁻¹ * ∑ x, (-1) ^ dot x y * v x
-- END SPEC

/- SKELETON · char_sum   (MILESTONE 1: used in `W_W` and `bernstein_vazirani`, at the string `y + z`)
  1. Unfold `dot`; split each `(-1) ^ ∑ᵢ …` into `∏ᵢ (-1) ^ …`, under `∑ y`:      R1 with R2 (`simp_rw [dot, ← …]`)
  2. Sum over bit strings of a product → product of two-term sums:             R3
       explicit function: `fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val)`
  3. Evaluate each two-term sum:                                              R4, R5, R6 (one `simp only`)
       goal: `∏ x_1, (1 + (-1) ^ ↑(x x_1)) = if x = 0 then 2 ^ n else 0`
  4. Split the `if`:                                                          R7
       `x = 0`:  R8, then `norm_num` (it uses R9)
       `x ≠ 0`:  a coordinate `i` with `hi : x i ≠ 0`:                        R10, proved by R11 → R12 → R13
                 one factor is 0:                                             R14
                 `x i = 1` (R15), then `simp` with it
-/
-- MILESTONE (optional: change or delete)
/-- the character sum: `∑_y (−1)^{x·y}` is `2ⁿ` at `x = 0` and `0` otherwise -/
theorem char_sum {n : ℕ} (x : Fin n → Fin 2) :
    ∑ y : Fin n → Fin 2, (-1 : ℂ) ^ dot x y = if x = 0 then 2 ^ n else 0 := by
  simp_rw [dot, ← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val))]
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, mul_zero, mul_one, pow_zero]
  split_ifs with hx
  · subst hx; norm_num
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : x i = 1 := by omega
    simp [this]

/- SKELETON · neg_one_pow_dot_add   (MILESTONE 2: used in `W_W` and `bernstein_vazirani` to merge two characters)
  1. One `simp only`: unfold `dot`, split the three powers (R2, with `←`), merge the two
     products on the left (R16, with `←`), evaluate `(y + z) i` (R17)
  2. Equal products → equal factors:                                         R18
  3. Name the three bits `x i`, `y i`, `z i`:                                 R19 (×3)
  4. 8 cases: `fin_cases` on each bit, then `simp` with the `Fin 2` fact      R20
-/
-- MILESTONE (optional: change or delete)
theorem neg_one_pow_dot_add {n : ℕ} (x y z : Fin n → Fin 2) :
    (-1 : ℂ) ^ dot x y * (-1) ^ dot x z = (-1) ^ dot x (y + z) := by
  simp only [dot, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, Pi.add_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize x i = a; generalize y i = b; generalize z i = c
  -- WHY: `(1 + 1 : Fin 2)` is `0` only definitionally; tell `simp`
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [show (1 + 1 : Fin 2) = 0 from rfl]

/- SKELETON · dot_comm   (MILESTONE 3: used in `W_W` and `bernstein_vazirani`; `char_sum` sums over the
  second argument of `dot`, so flip it first)
  1. Unfold `dot` and commute each product:                                  R21
-/
-- MILESTONE (optional: change or delete)
theorem dot_comm {n : ℕ} (x y : Fin n → Fin 2) : dot x y = dot y x := by
  simp [dot, mul_comm]

/- SKELETON · bits_add_eq_zero   (MILESTONE 4: turns `char_sum`'s test `y + z = 0` into `z = y`)
  1. Split the `↔`: `constructor`
  2. `→`: `intro h; funext i`; evaluate `h` at `i` (R22) and simplify it (R23 with R17)
          → `this : y i + z i = 0`; then R24, R19 (×2), `fin_cases` both bits, `simp`
  3. `←`: R25; `funext i`; R17; R19; `fin_cases`, then `rfl`
-/
-- MILESTONE (optional: change or delete)
theorem bits_add_eq_zero {n : ℕ} (y z : Fin n → Fin 2) : y + z = 0 ↔ z = y := by
  constructor
  · intro h; funext i
    have := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at this
    revert this; generalize y i = a; generalize z i = b
    fin_cases a <;> fin_cases b <;> simp
  · rintro rfl; funext i; simp only [Pi.add_apply, Pi.zero_apply]; generalize z i = a; fin_cases a <;> rfl

/- SKELETON · W_W
  Prove the four MILESTONES first: step 5 uses all of them.
  1. `hsq : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹`:            R26 → R27 → R28 (side goal: R29) → R30, then `rfl`
  2. `funext y`
  3. Unfold `W`, push both scalars into the sums, flatten:            R31, R32 (one `simp only [W, …]`)
  4. Swap the sums: outer over the input `z` of `v`, inner over `x`:  R33
  5. `key : ∀ z, <inner sum over x> = if z = y then v y else 0`:
       a. each term `= ((Real.sqrt (2 ^ n) : ℂ)⁻¹ ^ 2 * v z) * (-1) ^ dot (y + z) x`:
          `rw` with `dot_comm z x`, `dot_comm (y + z) x` (give the arguments: a bare `dot_comm`
          flips the first `dot` it meets, and a second one flips it back), `← neg_one_pow_dot_add`,
          then `ring`
       b. rewrite with (a) under `∑ x` (R1), pull the constant out (R31 reversed),
          then `char_sum`, `bits_add_eq_zero`, `hsq`
       c. R7;  `z = y`: R8, R34;  `z ≠ y`: `simp`
  6. Rewrite with `key` under the outer sum, then                    R35, R36
-/
-- BEGIN SPEC
theorem W_W {n : ℕ} (v : (Fin n → Fin 2) → ℂ) : W (W v) = v :=
-- END SPEC
  by
    have hsq : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹ := by
      rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
    funext y
    simp only [W, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    have key : ∀ z, ∑ x : Fin n → Fin 2, (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot x y *
        (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot z x * v z = if z = y then v y else 0 := by
      intro z
      have : ∀ x : Fin n → Fin 2, (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot x y *
          (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot z x * v z
          = ((Real.sqrt (2 ^ n) : ℂ)⁻¹ ^ 2 * v z) * (-1) ^ dot (y + z) x := by
        intro x
        rw [dot_comm z x, dot_comm (y + z) x, ← neg_one_pow_dot_add]; ring
      simp only [this, ← Finset.mul_sum, char_sum, bits_add_eq_zero, hsq]
      split_ifs with h
      · subst h; field_simp
      · simp
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- SKELETON · bernstein_vazirani
  Uses the four MILESTONES (as in `W_W`).
  1. `hsq` again (a `have` belongs to one proof):                    R26 → R27 → R28 → R29 → R30, `rfl`
  2. `funext y`
  3. `∀ x, (-1) ^ dot x y * (c * (-1) ^ dot s x) = c * (-1) ^ dot (y + s) x`,
     `c = (Real.sqrt (2 ^ n) : ℂ)⁻¹`: `rw` with `dot_comm s x`, `dot_comm (y + s) x` (with arguments,
     as in `W_W`), `← neg_one_pow_dot_add`, then `ring`
  4. One `simp only`: unfold `W`, rewrite with step 3, pull `c` out (R31 reversed), `char_sum`,
     `bits_add_eq_zero`, flatten (R32), fold `c * c` (R37), `hsq`, `|s⟩` (R38), flip `s = y` (R39)
       goal: `((2 ^ n)⁻¹ * if y = s then 2 ^ n else 0) = if y = s then 1 else 0`
  5. R7;  `y = s`: R34;  `y ≠ s`: `simp`
-/
-- BEGIN SPEC
theorem bernstein_vazirani {n : ℕ} (s : Fin n → Fin 2) :
    W (fun x => (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot s x) = Pi.single s 1 :=
-- END SPEC
  by
    have hsq : ((Real.sqrt (2 ^ n) : ℂ)⁻¹) ^ 2 = (2 ^ n)⁻¹ := by
      rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; rfl
    funext y
    have : ∀ x : Fin n → Fin 2, (-1 : ℂ) ^ dot x y * ((Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot s x)
        = (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ dot (y + s) x := by
      intro x
      rw [dot_comm s x, dot_comm (y + s) x, ← neg_one_pow_dot_add]; ring
    simp only [W, this, ← Finset.mul_sum, char_sum, bits_add_eq_zero, ← mul_assoc, ← sq, hsq,
      Pi.single_apply, eq_comm (a := s)]
    split_ifs
    · field_simp
    · simp

/- SKELETON · deutsch_jozsa
  No milestone needed: at `y = 0` every `(-1) ^ dot x 0` is 1.
  1. `hdot : ∀ x, dot x 0 = 0`: `simp [dot]` (R17, R5, R6)
  2. `hsum : ∑ x, (-1 : ℂ) ^ (f x).val = 0`:
       a. split the sum by `f x = 0`:                                  R40
       b. Type each filter as `Finset.univ.filter (fun x => …)` (the infoview prints it `{x | …}`,
          but `{x | …}` typed in a `have` is a `Set`, and R42 then fails):
          `h0 : ∀ x ∈ Finset.univ.filter (fun x => f x = 0), (-1 : ℂ) ^ (f x).val = 1`:
               `intro x hx`, R41, `simp`
          `h1 : ∀ x ∈ Finset.univ.filter (fun x => ¬f x = 0), (-1 : ℂ) ^ (f x).val = -1`:
               `intro x hx`, R41 + R15 (`f x = 1`), `simp`
          `hset : Finset.univ.filter (fun x => ¬f x = 0) = Finset.univ.filter (fun x => f x = 1)`:
               R44, `simp`, R15
       c. rw: R42 (with h0, h1), R43 (×2), `hbal`, `hset`; then `simp` closes `k • 1 + k • -1 = 0`
  3. Unfold `W`, `hdot`, R6, pull the scalar out (R31 reversed), `hsum`, R6
-/
-- BEGIN SPEC
theorem deutsch_jozsa {n : ℕ} (f : (Fin n → Fin 2) → Fin 2)
    (hbal : (Finset.univ.filter fun x => f x = 0).card = (Finset.univ.filter fun x => f x = 1).card) :
    W (fun x => (Real.sqrt (2 ^ n) : ℂ)⁻¹ * (-1) ^ (f x).val) 0 = 0 :=
-- END SPEC
  by
    have hdot : ∀ x : Fin n → Fin 2, dot x 0 = 0 := by simp [dot]
    -- balanced: the `+1` and `−1` terms cancel
    have hsum : ∑ x, (-1 : ℂ) ^ (f x).val = 0 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = 0)]
      have h0 : ∀ x ∈ Finset.univ.filter (fun x => f x = 0), (-1 : ℂ) ^ (f x).val = 1 := by
        intro x hx; simp at hx; simp [hx]
      have h1 : ∀ x ∈ Finset.univ.filter (fun x => ¬ f x = 0), (-1 : ℂ) ^ (f x).val = -1 := by
        intro x hx
        have : f x = 1 := by simp at hx; omega
        simp [this]
      have hset : (Finset.univ.filter fun x => ¬ f x = 0) = Finset.univ.filter fun x => f x = 1 := by
        ext x; simp; omega
      rw [Finset.sum_congr rfl h0, Finset.sum_congr rfl h1, Finset.sum_const, Finset.sum_const,
        hbal, hset]
      simp
    simp only [W, hdot, pow_zero, one_mul, ← Finset.mul_sum, hsum, mul_zero]

end H083

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything reduces to the character sum (MILESTONE 1: `∑_y (−1)^{x·y}` is `2ⁿ` at `x = 0`, else 0) plus
    "multiplying characters adds the strings" (MILESTONE 2), applied at `x = y + z` with `y + z = 0 ↔ z = y`
    (MILESTONE 4). Deutsch–Jozsa needs none of them: at `y = 0` every `(−1)^{x·0}` is 1, and a balanced `f`
    has as many `+1` as `−1` terms.
H2. Character sum: `(−1)^{∑ᵢ xᵢyᵢ} = ∏ᵢ (−1)^{xᵢyᵢ}` (R2), then `Fintype.prod_sum` (R3) turns `∑_y ∏ᵢ` into
    `∏ᵢ ∑_{b : Fin 2}`; a factor with `xᵢ = 1` is `1 + (−1) = 0` (R14). MILESTONE 2: the same product trick,
    then `Finset.prod_congr` (R18) and 8 cases per coordinate (R19, R20). `W_W`: `funext y`, push the scalars
    in (R31), swap the sums (R33), regroup each term as `c² · v z · (−1)^{(y+z)·x}` and apply MILESTONE 1.
    Deutsch–Jozsa: split `∑ₓ (−1)^{f x}` by `f x = 0` (R40) into `card₀ • 1 + card₁ • (−1)`.
H3. `simp_rw [dot, ← Finset.prod_pow_eq_pow_sum]; rw [← Fintype.prod_sum (fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val))]`.
    In `W_W`, after `simp only [W, Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]`, show each inner sum is
    `if z = y then v y else 0` and close with `Finset.sum_ite_eq'`. Deutsch–Jozsa:
    `rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = 0)]`, then `Finset.sum_congr rfl`,
    `Finset.sum_const`, `hbal`.
-/
