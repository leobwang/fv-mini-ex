/- M059 | The kernel of a homomorphism | 10-15 min | Subgroup, MonoidHom, structure instance, map_mul, mathlib
GOAL
  Build the kernel `{g | f g = 1}` of a group homomorphism `f : G →* H` as a `Subgroup G` (the set
  plus three closure proofs), then show `f` is injective iff its kernel contains only `1`.

REFERENCE
  -- `G →* H` is a monoid hom (here between groups); `f g` applies it.
  -- A `Subgroup G` is a structure; build one as `{ carrier := _, one_mem' := _, ... }`:
  --   carrier := (s : Set G),  one_mem' : 1 ∈ s,  mul_mem' : a ∈ s → b ∈ s → a * b ∈ s,
  --   inv_mem' : x ∈ s → x⁻¹ ∈ s   (a, b, x are implicit: start the proof with `intro a b ha hb`)
  example {G : Type} (P : G → Prop) (g : G) (h : P g) : g ∈ {x | P x} := h  -- set-builder membership is defeq
  #check map_mul          -- f (x * y) = f x * f y      (also `map_one f : f 1 = 1`)
  #check map_inv          -- f a⁻¹ = (f a)⁻¹
  #check mul_inv_eq_one   -- a * b⁻¹ = 1 ↔ a = b
  #check mul_inv_cancel   -- a * a⁻¹ = 1
  -- `show f (a * b) = 1` or `simp only [Set.mem_setOf_eq] at *` turns `_ ∈ {g | ...}` into the predicate.
BANNED: MonoidHom.ker, MonoidHom.mem_ker, injective_iff_map_eq_one, injective_iff_map_eq_one', MonoidHom.ker_eq_bot_iff, Subgroup.comap, Submonoid.comap, MonoidHom.eqLocus, MonoidHom.eqLocusM, MonoidHom.mker, exact?, apply?, rw?, hint, try?
NOTE: search tactics (`exact?`, `try?`, ...) are fine for exploring, but they close goals with banned lemmas, so they cannot stay.
-/
import Mathlib

namespace M059

-- BEGIN SPEC
def kernel {G H : Type*} [Group G] [Group H] (f : G →* H) : Subgroup G :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mem_kernel {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ kernel f ↔ f g = 1 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem injective_iff {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective f ↔ ∀ g ∈ kernel f, g = 1 :=
-- END SPEC
  sorry

end M059

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Replace the `sorry` of `kernel` by a structure instance `{ carrier := {g | f g = 1}, ... }`.
    Once `carrier` is that set, `mem_kernel` holds by definition (`Iff.rfl`).
H2. Closure: rewrite `f (a * b)` with `map_mul`, then use `f a = 1` and `f b = 1`; inverses likewise
    with `map_inv` and `inv_one`. Injectivity (←): if `f a = f b`, then `a * b⁻¹` is in the kernel.
H3. `mul_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb, one_mul]`;
    (←): `have : a * b⁻¹ ∈ kernel f := by rw [mem_kernel, map_mul, map_inv, hab, mul_inv_cancel]`,
    then `mul_inv_eq_one.mp (h _ this)`. (→): `hf (((mem_kernel f g).mp hg).trans (map_one f).symm)`.
-/
