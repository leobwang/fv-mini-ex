/- M059 | The kernel of a homomorphism | 10-15 min | Subgroup, MonoidHom, structure instance, map_mul, mathlib
GOAL
  Build the kernel `{g | f g = 1}` of a group homomorphism `f : G →* H` as a `Subgroup G` (the set
  plus three closure proofs), then show `f` is injective iff its kernel contains only `1`.
BANNED: MonoidHom.ker, MonoidHom.mem_ker, injective_iff_map_eq_one, injective_iff_map_eq_one', MonoidHom.ker_eq_bot_iff, Subgroup.comap, Submonoid.comap, MonoidHom.eqLocus, MonoidHom.eqLocusM, MonoidHom.mker, exact?, apply?, rw?, hint, try?

GUIDE
  Entries R1–R19: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M059

/- SKELETON · kernel   (a def: replace `sorry` by a structure instance)
  1. Give all four fields in braces, carrier `{g | f g = 1}`:                 R1
  2. one_mem': the goal `1 ∈ {g | f g = 1}` is `f 1 = 1` by definition:       R2, R3
  3. mul_mem': name the two elements and their memberships:                   R4
       turn every `_ ∈ {g | f g = 1}` into `f _ = 1`:                         R5
       push `f` through `*`, substitute `ha`, `hb`, cancel `1 * 1`:           R6, rw [ha, hb], R7
  4. inv_mem': the same with one element:                                     R4, R5, R8, rw [ha], R9
-/
-- BEGIN SPEC
def kernel {G H : Type*} [Group G] [Group H] (f : G →* H) : Subgroup G :=
-- END SPEC
  sorry

/- SKELETON · mem_kernel
  1. Both sides are `f g = 1` once `kernel` and set-builder membership
     unfold; this needs the carrier of `kernel` to be exactly `{g | f g = 1}`: R10
-/
-- BEGIN SPEC
theorem mem_kernel {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ kernel f ↔ f g = 1 :=
-- END SPEC
  sorry

/- SKELETON · injective_iff
  1. Split the `↔`:                                                           R11
  (→)
  2. Name `hf`, then `g` and `hg : g ∈ kernel f`:                             intro hf, R12
  3. `hg` read through `mem_kernel` gives `f g = 1`:                          R13
  4. Chain with `map_one f` reversed to get `f g = f 1`:                      R14 (with R3)
  5. Injectivity turns that into `g = 1`:                                     R15
  (←)
  6. Name `h`, then `a b` and `hab : f a = f b`:                              intro h, R16
  7. Fact `this : a * b⁻¹ ∈ kernel f`, by rewriting: membership → equation,
     `f` through `*` and `⁻¹`, `hab`, then `f b * (f b)⁻¹ = 1`:              R17 → R6 → R8 → rw [hab] → R18
  8. `h _ this : a * b⁻¹ = 1`, then turn it into `a = b`:                     R19
-/
-- BEGIN SPEC
theorem injective_iff {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective f ↔ ∀ g ∈ kernel f, g = 1 :=
-- END SPEC
  sorry

end M059

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `kernel` is a structure instance `{ carrier := {g | f g = 1}, one_mem' := …, mul_mem' := …,
    inv_mem' := … }`; each closure field is one hom law: `f 1 = 1`, `f (a * b) = f a * f b`,
    `f a⁻¹ = (f a)⁻¹`. With that carrier, `mem_kernel` holds by definition.
H2. Closure fields: `intro`, `simp only [Set.mem_setOf_eq] at *`, then `rw` with `map_mul` / `map_inv`
    and the hypotheses. `mem_kernel := Iff.rfl`. `injective_iff`: `constructor`; (→) `f g = 1 = f 1`,
    so `g = 1` by injectivity; (←) if `f a = f b`, then `a * b⁻¹` is in the kernel, so `a * b⁻¹ = 1`.
H3. `mul_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb, one_mul]`;
    (→): `hf (((mem_kernel f g).mp hg).trans (map_one f).symm)`;
    (←): `have : a * b⁻¹ ∈ kernel f := by rw [mem_kernel, map_mul, map_inv, hab, mul_inv_cancel]`,
    then `mul_inv_eq_one.mp (h _ this)`.
-/
