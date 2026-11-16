/- M132 | Quantum teleportation | 15-20 min | state vectors, Fin 2 indices, corrections, normSq, mathlib
GOAL
  Teleport the state `χ : Fin 2 × R → ℂ` of qubit q₀ and a reference system `R` to Bob's qubit q₂:
  after CNOT, H and outcomes `(m₀, m₁)`, applying `X^m₁` then `Z^m₀` leaves `½ χ` (now on q₂ and `R`);
  each outcome has probability ¼.

REFERENCE
  -- a state of q₀ q₁ q₂ and R is `v : Fin 2 × Fin 2 × Fin 2 × R → ℂ`; for `p = (a, b, c, r)`:
  -- `p.1 = a` (q₀), `p.2.1 = b` (q₁), `p.2.2.1 = c` (q₂, Bob), `p.2.2.2 = r`;  `p.2.2 = (c, r)`
  example : (1 : Fin 2) + 1 = 0 := rfl                -- `+` on `Fin 2` is XOR (bit flip)
  example (f : Fin 2 × ℕ → ℂ) : f = fun q => f q := by funext ⟨c, r⟩; rfl   -- funext + pattern
  example (m : Fin 2) (P : Fin 2 → Prop) (h0 : P 0) (h1 : P 1) : P m := by fin_cases m <;> assumption
  example : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  #check Fintype.sum_prod_type  -- ∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)
  #check Complex.normSq_mul     -- normSq (z * w) = normSq z * normSq w   (normSq z = |z|²)
  #check Fin.sum_univ_two       -- ∑ i : Fin 2, f i = f 0 + f 1
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

-- BEGIN SPEC
theorem teleport (χ : Fin 2 × R → ℂ) (m₀ m₁ : Fin 2) :
    fixZ m₀ (fixX m₁ (bob (h0 (cnot01 (init χ))) m₀ m₁)) = fun q => (1 / 2 : ℂ) * χ q :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem teleport_prob [Fintype R] (χ : Fin 2 × R → ℂ) (m₀ m₁ : Fin 2) :
    ∑ q, Complex.normSq (bob (h0 (cnot01 (init χ))) m₀ m₁ q)
      = (1 / 4) * ∑ q, Complex.normSq (χ q) :=
-- END SPEC
  sorry

end M132

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything is a finite computation: prove `s * s = 1 / 2` first, then split every `Fin 2`
    variable (`m₀`, `m₁`, Bob's bit `c`) and let `simp` unfold the definitions.
H2. `teleport`: `funext ⟨c, r⟩`, then `fin_cases` on `m₀`, `m₁`, `c`, then `simp [defs]`, `ring_nf`,
    and finish with your `s * s` lemma. `teleport_prob`: first prove a closed form for each amplitude
    of `bob …`, then the sum is bookkeeping.
H3. `have key : ∀ c r, bob (h0 (cnot01 (init χ))) m₀ m₁ (c, r)
      = (if m₀ = 1 ∧ c + m₁ = 1 then -1 else 1) * ((1 / 2 : ℂ) * χ (c + m₁, r))`; then
    `simp only [Fintype.sum_prod_type, key, Complex.normSq_mul]`, the sign has `normSq = 1`
    (`split_ifs <;> simp`), and finish per `r` with `fin_cases m₁ <;> simp <;> ring`.
-/
