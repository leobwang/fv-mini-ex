/- M138 | Reduced Bell state is maximally mixed | 15-20 min | MState, partial trace, maximally entangled state, HermitianMat unwrapping, physlib
GOAL
  Let `Φ = Σᵢ |i⟩|i⟩ / √d` be the maximally entangled state on `d × d` (`Ket.MES d`). Tracing out the
  left half of `|Φ⟩⟨Φ|` leaves the maximally mixed state `I / d` (`MState.uniform`).

REFERENCE
  -- `MState d`: density matrix on `d`; `ρ.M : HermitianMat d ℂ` (a subtype), `ρ.m = ρ.M.mat : Matrix d d ℂ`.
  #check @MState.ext_m             -- ρ₁.m = ρ₂.m → ρ₁ = ρ₂   (then `ext i j` for entries)
  -- `show ρ.M.mat i j = σ.M.mat i j` restates a goal `ρ.m i j = σ.m i j` (definitionally equal).
  #check @MState.traceLeft_M        -- ↑ρ.traceLeft = (↑ρ).traceLeft   (HermitianMat level; ↑ = `.M`)
  #check @HermitianMat.traceLeft_mat -- ↑A.traceLeft = (↑A).traceLeft  (raw matrix level; ↑ = `.mat`)
  #check @MState.mat_M              -- ↑↑ρ = ρ.m
  #check @Matrix.traceLeft          -- A.traceLeft i j = ∑ k, A (k, i) (k, j)   (unfold it with simp)
  #check @MState.pure_apply         -- (pure ψ).m i j = ψ i * conj (ψ j)
  #check @MState.coe_ofClassical    -- ↑(ofClassical p) = HermitianMat.diagonal ℂ (p ·); `uniform = ofClassical uniform`
  #check @HermitianMat.diagonal_mat -- ↑(HermitianMat.diagonal ℂ f) = Matrix.diagonal (fun x => ↑(f x))
  #check @Real.mul_self_sqrt        -- 0 ≤ x → √x * √x = x
BANNED: traceRight_pure_MES
-/
import QuantumInfo.States.Mixed.MState

open Matrix

namespace M138

-- BEGIN SPEC
theorem traceLeft_MES {d : Type} [Fintype d] [DecidableEq d] [Nonempty d] :
    (MState.pure (Ket.MES d)).traceLeft = MState.uniform :=
-- END SPEC
  sorry

end M138

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Reduce to an entrywise statement about plain matrices: `apply MState.ext_m; ext i j`, then `show` the
    goal with `.M.mat` on both sides so the `traceLeft_M` / `traceLeft_mat` / `coe_ofClassical` lemmas can fire.
H2. After unwrapping, the left side is `∑ k, Φ(k, i) * conj Φ(k, j)` and the right side is `if i = j then 1/d else 0`.
    Split on `i = j`; `simp [Ket.MES, Ket.apply]` collapses the sum (only `k = i` survives) and kills the off-diagonal case.
H3. `rw [MState.traceLeft_M, HermitianMat.traceLeft_mat, MState.mat_M, MState.uniform, MState.coe_ofClassical,
    HermitianMat.diagonal_mat, Matrix.diagonal_apply]`; the diagonal case ends at `(√n)⁻¹ * (√n)⁻¹ = n⁻¹`:
    `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]`, then `simp`.
-/
