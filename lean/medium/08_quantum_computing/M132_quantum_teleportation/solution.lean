/- M132 | Quantum teleportation | 15-20 min | state vectors, Fin 2 indices, corrections, normSq, mathlib
GOAL
  Teleport the state `χ : Fin 2 × R → ℂ` of qubit q₀ and a reference system `R` to Bob's qubit q₂:
  after CNOT, H and outcomes `(m₀, m₁)`, applying `X^m₁` then `Z^m₀` leaves `½ χ` (now on q₂ and `R`);
  each outcome has probability ¼.

GUIDE
  Entries R1–R27: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M132

-- BEGIN SPEC
variable {R : Type}

/-- `1/√2` as a complex number. -/
noncomputable def s : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- `χ` on (q₀, R) tensored with the Bell pair `(|00⟩ + |11⟩)/√2` on (q₁, q₂). -/
noncomputable def init (χ : Fin 2 × R → ℂ) : Fin 2 × Fin 2 × Fin 2 × R → ℂ :=
  fun p => χ (p.1, p.2.2.2) * (if p.2.1 = p.2.2.1 then s else 0)

/-- CNOT with control q₀ and target q₁. -/
def cnot01 (v : Fin 2 × Fin 2 × Fin 2 × R → ℂ) : Fin 2 × Fin 2 × Fin 2 × R → ℂ :=
  fun p => v (p.1, p.2.1 + p.1, p.2.2)

/-- Hadamard on q₀. -/
noncomputable def h0 (v : Fin 2 × Fin 2 × Fin 2 × R → ℂ) : Fin 2 × Fin 2 × Fin 2 × R → ℂ :=
  fun p => s * (v (0, p.2) + (if p.1 = 0 then 1 else -1) * v (1, p.2))

/-- Bob's unnormalised conditional state (on q₂ and R) after outcomes `m₀` on q₀ and `m₁` on q₁. -/
def bob (v : Fin 2 × Fin 2 × Fin 2 × R → ℂ) (m₀ m₁ : Fin 2) : Fin 2 × R → ℂ :=
  fun q => v (m₀, m₁, q)

/-- Bob's correction `X^m` (bit flip if `m = 1`). -/
def fixX (m : Fin 2) (w : Fin 2 × R → ℂ) : Fin 2 × R → ℂ := fun q => w (q.1 + m, q.2)

/-- Bob's correction `Z^m` (sign flip on `|1⟩` if `m = 1`). -/
def fixZ (m : Fin 2) (w : Fin 2 × R → ℂ) : Fin 2 × R → ℂ :=
  fun q => (if m = 1 ∧ q.1 = 1 then -1 else 1) * w q
-- END SPEC

theorem s_mul_s : s * s = 1 / 2 := by
  rw [s, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem key (χ : Fin 2 × R → ℂ) (m₀ m₁ c : Fin 2) (r : R) :
    bob (h0 (cnot01 (init χ))) m₀ m₁ (c, r)
      = (if m₀ = 1 ∧ c + m₁ = 1 then -1 else 1) * ((1 / 2 : ℂ) * χ (c + m₁, r)) := by
  have h := s_mul_s
  fin_cases m₀ <;> fin_cases m₁ <;> fin_cases c <;> simp [bob, h0, cnot01, init] <;> ring_nf <;>
    simp [sq, h] <;> ring

/- SKELETON · teleport
  0. Milestone first, as its own lemma above this theorem (`key` below uses it too):
       s_mul_s : s * s = 1 / 2                    proof: R1 → R2 → R3 → R4 → R5
  1. Function equation → its value at Bob's point `(c, r)`:                 R6
  2. Bring the milestone in (`have h := s_mul_s`):                          R7
  3. Split the three bits `m₀`, `m₁`, `c` (8 goals):                        R8
  4. In every goal, evaluate: `simp` with all six gate names                R9–R12
  5. Collect the two factors `s` into `s ^ 2`:                              R13
  6. `s ^ 2` back to `s * s`, then substitute the milestone (`simp [sq, h]`): R14
  7. Finish the reordering:                                                 R15
-/
-- BEGIN SPEC
theorem teleport (χ : Fin 2 × R → ℂ) (m₀ m₁ : Fin 2) :
    fixZ m₀ (fixX m₁ (bob (h0 (cnot01 (init χ))) m₀ m₁)) = fun q => (1 / 2 : ℂ) * χ q :=
-- END SPEC
  by
    funext ⟨c, r⟩
    have h := s_mul_s
    fin_cases m₀ <;> fin_cases m₁ <;> fin_cases c <;>
      simp [fixZ, fixX, bob, h0, cnot01, init] <;> ring_nf <;> simp [sq, h] <;> ring

/- SKELETON · teleport_prob
  0. Milestone first, as its own lemma (exact statement in H3): the closed form
       key : bob (h0 (cnot01 (init χ))) m₀ m₁ (c, r) = ±(1 / 2) * χ (c + m₁, r),
             sign -1 exactly when `m₀ = 1 ∧ c + m₁ = 1`.
     proof: like `teleport` without its step 1:          R7, R8 (on m₀ m₁ c), R9–R12, R13, R14, R15
  1. One `simp only`: sum over pairs → double sum, every amplitude → `key`,
     `normSq` of the products split:                                        R16, R17, R18
  2. Two facts for step 3:
       hs : ∀ P : Prop, [Decidable P] → Complex.normSq (if P then -1 else 1) = 1
                                                  proof: R19 → R20 → R21
       h4 : Complex.normSq (1 / 2) = 1 / 4        proof: R22
  3. One `simp only` with `hs`, R23, `h4`, R24, R25, `← R26`: each side is one sum over `r : R`
  4. Compare the two sums term by term:                                     R27
  5. Split `m₁`, compute `0 + m₁`, `1 + m₁`, finish:                        R8, R11, R15
-/
-- BEGIN SPEC
theorem teleport_prob [Fintype R] (χ : Fin 2 × R → ℂ) (m₀ m₁ : Fin 2) :
    ∑ q, Complex.normSq (bob (h0 (cnot01 (init χ))) m₀ m₁ q)
      = (1 / 4) * ∑ q, Complex.normSq (χ q) :=
-- END SPEC
  by
    simp only [Fintype.sum_prod_type, key, Complex.normSq_mul]
    have hs : ∀ P : Prop, [Decidable P] → Complex.normSq (if P then -1 else 1) = 1 := by
      intro P _; split_ifs <;> simp
    have h4 : Complex.normSq (1 / 2) = 1 / 4 := by norm_num
    simp only [hs, one_mul, h4, Fin.sum_univ_two, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    -- WHY: `c + m₁` permutes Bob's bit, so the two terms swap when `m₁ = 1`.
    fin_cases m₁ <;> simp <;> ring

end M132

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything is a finite computation. The only irrational number is `s = (√2)⁻¹`, and it always
    appears twice: prove `s * s = 1 / 2` first (R1–R5). Then split every `Fin 2` variable (`m₀`, `m₁`,
    Bob's bit `c`) and let `simp` evaluate the gates.
H2. `teleport`: reduce to Bob's point with `funext ⟨c, r⟩`, split `m₀ m₁ c`, evaluate with `simp` and
    all six gate names, then collect `s * (… * s)` into `s ^ 2` (`ring_nf`) and substitute the milestone.
    `teleport_prob`: first prove a closed form `key` for each amplitude of `bob …` the same way; then
    the sum is bookkeeping (R16–R27).
H3. `theorem key (χ : Fin 2 × R → ℂ) (m₀ m₁ c : Fin 2) (r : R) : bob (h0 (cnot01 (init χ))) m₀ m₁ (c, r)
      = (if m₀ = 1 ∧ c + m₁ = 1 then -1 else 1) * ((1 / 2 : ℂ) * χ (c + m₁, r))`; then
    `simp only [Fintype.sum_prod_type, key, Complex.normSq_mul]`, the sign has `normSq = 1`
    (`intro P _; split_ifs <;> simp`), merge the sums (R23–R26), go term by term (R27), and finish
    per `r` with `fin_cases m₁ <;> simp <;> ring`.
-/
