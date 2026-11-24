/- M060 | Cayley's theorem | 15 min | Equiv, Equiv.Perm, MonoidHom, structure instance, ext, mathlib
GOAL
  Build by hand the homomorphism `G →* Equiv.Perm G` sending `g` to the permutation `x ↦ g * x`,
  then prove it injective: every group embeds in a group of permutations (Cayley's theorem).

BANNED: MulAction.toPermHom, MulAction.toPerm, Equiv.mulLeft, Equiv.mulRight, Equiv.mulLeft₀, Equiv.constSMulHom, Equiv.constSMul, MonoidHom.toHomPerm, MulAction.toEndHom, exact?, apply?, rw?, hint, try?

GUIDE
  Entries R1–R16: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M060

/- SKELETON · leftMul
  1. The outer structure, a homomorphism; its `toFun g` is the inner one:   R5
  2. The inner structure, the permutation x ↦ g * x with inverse x ↦ g⁻¹ * x:   R1
       left_inv:  R2, then `exact` with R3 applied to g and x   (or the term `fun x => …` with R3)
       right_inv: R2, then `exact` with R4 likewise
       (not `rw`: after R2 the goal is still `(fun x => g⁻¹ * x) ((fun x => g * x) x) = x`)
     One `refine` with all four `?_` gives the goals in the order of steps 2–4.
  3. map_one': an equation of permutations. Pointwise, then evaluate:      R6, then `simp` (R7, R8, R9)
  4. map_mul': introduce the two factors, pointwise, evaluate, reassociate:
       intro a b (or `fun a b => by …`), R6, then `simp` with R11 named (R7, R10, R11)
-/
-- BEGIN SPEC
def leftMul {G : Type*} [Group G] : G →* Equiv.Perm G :=
-- END SPEC
  sorry

/- SKELETON · leftMul_apply
  1. Both sides unfold to `g * x` (true only for the structure-instance definition):   R12
-/
-- BEGIN SPEC
theorem leftMul_apply {G : Type*} [Group G] (g x : G) : leftMul g x = g * x :=
-- END SPEC
  sorry

/- SKELETON · cayley
  1. Open the injectivity statement: a b, h : leftMul a = leftMul b, goal a = b:   R13
  2. Evaluate the permutation equation h at the point 1:                           R14
  3. Simplify `this` with leftMul_apply (Part 2) and mul_one, and close:           R15 inside R16
-/
-- BEGIN SPEC
theorem cayley {G : Type*} [Group G] : Function.Injective (leftMul (G := G)) :=
-- END SPEC
  sorry

end M060

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two nested structures: the outer `MonoidHom`'s `toFun g` is itself an `Equiv`. The inverse of
    "multiply by `g` on the left" is "multiply by `g⁻¹` on the left". `leftMul_apply` is then `rfl`.
    For `cayley`, two permutations that are equal agree at every point, in particular at `1`.
H2. The inverse laws are R3 and R4 applied to `g` and `x`. `map_one'` and `map_mul'` are equations of
    permutations: `ext x` and `simp` (add `mul_assoc` for `map_mul'`). For `cayley`, `intro a b h`,
    evaluate `h` at `1` with `congrArg`, and simplify with `leftMul_apply`.
H3. The inner permutation: `{ toFun := fun x => g * x, invFun := fun x => g⁻¹ * x, left_inv := fun x => inv_mul_cancel_left g x, right_inv := ?_ }`.
    `cayley`: `intro a b h; have := congrArg (fun σ : Equiv.Perm G => σ 1) h`, then `simpa [leftMul_apply] using this`.
-/
