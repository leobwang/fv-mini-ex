/- M146 | The dephasing channel | 15 min | CPTPMap, Kraus form, MState, fin_cases, physlib
GOAL
  Build the qubit dephasing channel `ρ ↦ ∑ k, |k⟩⟨k| ρ |k⟩⟨k|` as a bundled channel from its Kraus
  operators: check `∑ k, (P k)ᴴ * P k = 1`, show the output is the diagonal of `ρ` (coherences erased,
  populations kept), and that dephasing twice is the same as dephasing once.

REFERENCE
  -- `ρ : MState d` is a density matrix; `ρ.m : Matrix d d ℂ` is its matrix. `Aᴴ` is the conjugate transpose.
  -- `CPTPMap dIn dOut ℂ` is a quantum channel; it coerces to a function, so `Λ ρ : MState dOut`.
  #check CPTPMap.of_kraus_CPTPMap     -- (M : κ → Matrix dOut dIn 𝕜) (∑ k, (M k)ᴴ * M k = 1) : CPTPMap dIn dOut 𝕜
  #check CPTPMap.mat_coe_eq_apply_mat -- (Λ ρ).m = (… Λ …).map ρ.m
  -- for a channel built by `of_kraus_CPTPMap M _`, that `map ρ.m` is `∑ k, M k * ρ.m * (M k)ᴴ` by definition (`rfl`)
  #check MState.ext_m                 -- ρ₁.m = ρ₂.m → ρ₁ = ρ₂
  #check Matrix.diagonal_apply        -- diagonal v i j = if i = j then v i else 0
  #check Pi.single_apply              -- Pi.single i x i' = if i' = i then x else 0
  #check Matrix.mul_apply             -- (M * N) i k = ∑ j, M i j * N j k
  #check Fin.sum_univ_two             -- ∑ i : Fin 2, f i = f 0 + f 1
  example (A : Matrix (Fin 2) (Fin 2) ℂ) : A = A := by ext i j; fin_cases i <;> fin_cases j <;> rfl  -- entry by entry
-/
import QuantumInfo.Channels.CPTP

open Matrix

namespace M146

-- BEGIN SPEC
/-- Kraus operators `P 0 = |0⟩⟨0|` and `P 1 = |1⟩⟨1|` -/
def P (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (Pi.single i 1)

theorem dephase_tp : ∑ k, (P k)ᴴ * P k = 1 :=
-- END SPEC
  by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Fin.sum_univ_two, Pi.single_apply]

-- BEGIN SPEC
noncomputable def dephase : CPTPMap (Fin 2) (Fin 2) ℂ := CPTPMap.of_kraus_CPTPMap P dephase_tp
-- END SPEC

/-- bridge: the bundled channel acts on the matrix as its Kraus sum -/
theorem dephase_mat (ρ : MState (Fin 2)) : (dephase ρ).m = ∑ k, P k * ρ.m * (P k)ᴴ := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  -- WHY: `of_kraus_CPTPMap` stores `MatrixMap.of_kraus P P`, which unfolds to this sum
  rfl

-- BEGIN SPEC
theorem dephase_apply (ρ : MState (Fin 2)) :
    (dephase ρ).m = Matrix.diagonal (fun i => ρ.m i i) :=
-- END SPEC
  by
    rw [dephase_mat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Fin.sum_univ_two, Matrix.mul_apply]

-- BEGIN SPEC
theorem dephase_idem (ρ : MState (Fin 2)) : dephase (dephase ρ) = dephase ρ :=
-- END SPEC
  by
    apply MState.ext_m
    rw [dephase_apply, dephase_apply]
    ext i j
    by_cases h : i = j <;> simp [h]

end M146

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything goes through the raw matrix `(dephase ρ).m`. First prove a bridge lemma that writes it as
    the Kraus sum `∑ k, P k * ρ.m * (P k)ᴴ`; after that it is 2×2 matrix arithmetic.
H2. `dephase_tp` and `dephase_apply` (after the bridge): `ext i j; fin_cases i <;> fin_cases j <;> simp [...]`
    with `P`, `Fin.sum_univ_two`, `Matrix.mul_apply`, `Pi.single_apply`. For `dephase_idem`, use `MState.ext_m`
    and `dephase_apply` twice: dephasing a diagonal matrix changes nothing.
H3. Bridge: `theorem dephase_mat (ρ : MState (Fin 2)) : (dephase ρ).m = ∑ k, P k * ρ.m * (P k)ᴴ`; its key step is
    `rw [CPTPMap.mat_coe_eq_apply_mat]; rfl`. `dephase_idem`: use `MState.ext_m`, then `dephase_apply` twice;
    go entrywise and split on `i = j`.
-/
