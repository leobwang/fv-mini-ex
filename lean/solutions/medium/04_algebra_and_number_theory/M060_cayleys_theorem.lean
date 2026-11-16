/- M060 | Cayley's theorem | 15 min | Equiv, Equiv.Perm, MonoidHom, structure instance, ext, mathlib
GOAL
  Build by hand the homomorphism `G →* Equiv.Perm G` sending `g` to the permutation `x ↦ g * x`,
  then prove it injective: every group embeds in a group of permutations (Cayley's theorem).

REFERENCE
  -- `Equiv.Perm G` is `G ≃ G`: `toFun`, `invFun`, `left_inv : ∀ x, invFun (toFun x) = x`, `right_inv`
  example : ℤ ≃ ℤ := { toFun := fun x => x + 1, invFun := fun x => x - 1, left_inv := fun x => by simp, right_inv := fun x => by simp }
  -- `G →* M` is a structure too: `{ toFun := _, map_one' := _, map_mul' := _ }`
  example (σ τ : Equiv.Perm ℕ) (h : ∀ x, σ x = τ x) : σ = τ := Equiv.ext h   -- tactic form: `ext x`
  example (σ τ : Equiv.Perm ℕ) (x : ℕ) : (σ * τ) x = σ (τ x) := rfl   -- `*` is composition, `1` is id
  #check inv_mul_cancel_left   -- a⁻¹ * (a * b) = b     (mul_inv_cancel_left : a * (a⁻¹ * b) = b)
  #check mul_assoc             -- a * b * c = a * (b * c)
  example (f g : ℕ → ℕ) (h : f = g) : f 1 = g 1 := congrArg (fun φ => φ 1) h   -- apply both sides
BANNED: MulAction.toPermHom, MulAction.toPerm, Equiv.mulLeft, Equiv.mulRight, Equiv.mulLeft₀, Equiv.constSMulHom, Equiv.constSMul, MonoidHom.toHomPerm, MulAction.toEndHom, exact?, apply?, rw?, hint, try?
NOTE: search tactics (`exact?`, `try?`, ...) are fine for exploring, but they close goals with banned terms, so they cannot stay.
-/
import Mathlib

namespace M060

-- BEGIN SPEC
def leftMul {G : Type*} [Group G] : G →* Equiv.Perm G :=
-- END SPEC
  { toFun := fun g =>
      { toFun := fun x => g * x
        invFun := fun x => g⁻¹ * x
        left_inv := fun x => inv_mul_cancel_left g x
        right_inv := fun x => mul_inv_cancel_left g x }
    map_one' := by ext x; simp
    map_mul' := fun a b => by ext x; simp [mul_assoc] }

-- BEGIN SPEC
theorem leftMul_apply {G : Type*} [Group G] (g x : G) : leftMul g x = g * x :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem cayley {G : Type*} [Group G] : Function.Injective (leftMul (G := G)) :=
-- END SPEC
  by
    intro a b h
    have := congrArg (fun σ : Equiv.Perm G => σ 1) h
    simpa [leftMul_apply] using this

end M060

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two nested structures: the outer `MonoidHom`'s `toFun g` is itself an `Equiv`. The inverse of
    "multiply by `g` on the left" is "multiply by `g⁻¹` on the left". `leftMul_apply` is then `rfl`.
H2. `map_one'` and `map_mul'` are equalities of permutations: prove them with `ext x` and `simp`
    (add `mul_assoc` for `map_mul'`). For `cayley`, evaluate both permutations at `1`.
H3. The inner permutation: `{ toFun := fun x => g * x, invFun := fun x => g⁻¹ * x, left_inv := ?_, right_inv := ?_ }`.
    `cayley`: `intro a b h; have := congrArg (fun σ : Equiv.Perm G => σ 1) h`, then simplify `this` with `leftMul_apply`.
-/
