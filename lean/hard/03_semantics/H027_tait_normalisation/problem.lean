/- H027 | Typed combinators are normalising (Tait) | 45-75 min | logical relations, reducibility, weak normalisation, combinatory logic, structural recursion on types
GOAL
  SK combinators: `K x y ⟶ x`, `S x y z ⟶ x z (y z)` (`⟶` is one `Step`, allowed anywhere in a term).
  Prove every simply typed term is weakly normalising (`WN t`: it reduces to a normal form) by Tait's
  method: `Red A t` by recursion on `A`, closed under backward steps, holds for every typed term.

GUIDE
  Entries R1–R17: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H027

-- BEGIN SPEC
inductive Ty where
  | base
  | arr (A B : Ty)

inductive Tm where
  | S
  | K
  | app (t u : Tm)

inductive HasTy : Tm → Ty → Prop
  | K {A B : Ty} : HasTy .K (.arr A (.arr B A))
  | S {A B C : Ty} : HasTy .S (.arr (.arr A (.arr B C)) (.arr (.arr A B) (.arr A C)))
  | app {t u : Tm} {A B : Ty} : HasTy t (.arr A B) → HasTy u A → HasTy (.app t u) B

inductive Step : Tm → Tm → Prop
  | K {x y : Tm} : Step (.app (.app .K x) y) x
  | S {x y z : Tm} : Step (.app (.app (.app .S x) y) z) (.app (.app x z) (.app y z))
  | appL {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} : Step u u' → Step (.app t u) (.app t u')

inductive Star : Tm → Tm → Prop
  | refl (t : Tm) : Star t t
  | step {t u v : Tm} : Step t u → Star u v → Star t v

def Normal (t : Tm) : Prop := ∀ t', ¬ Step t t'

def WN (t : Tm) : Prop := ∃ v, Star t v ∧ Normal v
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- Reducibility (the logical relation): `WN` at the base type; at `A → B`, also maps
    reducible arguments to reducible results. -/
def Red : Ty → Tm → Prop
  | .base, t => WN t
  | .arr A B, t => WN t ∧ ∀ u, Red A u → Red B (.app t u)

-- MILESTONE (optional: change or delete)
/- SKELETON · red_back
  1. Induction on the type, generalizing both terms (the arrow case needs the IH at `.app t u`):  R10
  2. base: `h` is `WN t'`: take it apart, rebuild it with the step `s` in front          R11 → R13
  3. arr A B: take `h` apart into its `WN` half and its clause `hf`                     R12
     rebuild: the `WN` half as in 2; the clause as `fun u hu => …` from `ihB`, the step
     `.appL s : Step (.app t u) (.app t' u)` and `hf u hu`                            R14, R3
-/
theorem red_back {A : Ty} {t t' : Tm} (s : Step t t') (h : Red A t') : Red A t := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · red_K
  Uses the helpers `normal_K`, `normal_Kx`, `star_appR`, `red_wn` (see SKELETON · weak_normalization)
  and the milestone `red_back`.
  1. `WN .K` with zero steps; open the clause for `x`, `hx : Red A x`:                 R15
  2. `WN (.app .K x)`: `x ⟶* x'` normal from `red_wn hx`, lifted by `star_appR`        R11, R13
  3. the clause for `y`: `K x y ⟶ x`, so `red_back` with the step `.K` and `hx`        R14, R16 (as a term)
-/
theorem red_K {A B : Ty} : Red (.arr A (.arr B A)) .K := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · red_S
  Uses `normal_S`, `normal_Sx`, `normal_Sxy`, `star_trans`, `star_appL`, `star_appR`, `red_wn`, `red_back`.
  Peel the three arrows one argument at a time, as in `red_K`:
  1. `WN .S`; open the clause for `x`, `hx`:                                           R15
  2. `WN (S x)` from `red_wn hx` and `star_appR`; open the clause for `y`, `hy`         R11, R15
  3. `WN (S x y)`: from `red_wn hy`; the sequence `S x y ⟶* S x' y ⟶* S x' y'` is
     `star_trans` of `star_appL (star_appR _)` and `star_appR _`; open the clause for `z`, `hz`   R11, R15
  4. `S x y z` is not normal: step back once with `red_back` and the step `.S`          R16
     then `x z (y z)` is reducible: the arrow clauses of `hx` and `hy`, nested          R9
-/
theorem red_S {A B C : Ty} : Red (.arr (.arr A (.arr B C)) (.arr (.arr A B) (.arr A C))) .S := by
  sorry

/- SKELETON · weak_normalization
  Prove first (helpers you add yourself; where they are used on the right). Place the `star_` and
  `normal_` helpers right after the first `-- END SPEC`, `red_wn` right after `def Red`:
    star_trans : Star a b → Star b c → Star a c                     R1 → R2       red_S
    star_appL  : Star t t' → Star (.app t u) (.app t' u)            R1 → R2, R3   red_S
    star_appR  : Star u u' → Star (.app t u) (.app t u')            R1 → R2, R3   red_K, red_S
    normal_K, normal_S : Normal .K, Normal .S                       R4 → R5       red_K, red_S
    normal_Kx, normal_Sx : Normal x → Normal (.app .K x), (.app .S x)
                                                                    R4 → R6 → R5 / R7
    normal_Sxy : Normal x → Normal y → Normal (.app (.app .S x) y)  R4 → R6 → R7  red_S
    red_wn : Red A t → WN t                                         R8            red_K, red_S, step 2
  Then the milestones, in this order: red_back (used by red_K, red_S), red_K, red_S.
  1. State `fundamental : HasTy t A → Red A t` after red_S, above this SKELETON;
     induction on the typing:                                                       R17
       K, S cases: the milestones red_K, red_S;  app case: the arrow clause of ih1    R9
  2. The theorem is `red_wn` applied to `fundamental h` (a term, no tactics).
-/
-- BEGIN SPEC
theorem weak_normalization {t : Tm} {A : Ty} (h : HasTy t A) : WN t :=
-- END SPEC
  sorry

end H027

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induction on typing fails directly: `WN t` and `WN u` say nothing about `WN (.app t u)`. `Red` strengthens the induction hypothesis so that the `app` case is just the arrow clause of `Red` (R9). Every `Red A t` gives `WN t` by `cases A` (R8).
H2. Helpers first (SKELETON · weak_normalization): `Star` is transitive and a congruence on both sides of `app` (induction on `Star`, R1–R3); `K`, `S`, `K x`, `S x`, `S x y` are normal when `x`, `y` are (`intro t' h; cases h`, R4–R7). `red_back`: `induction A generalizing t t'`, the arrow case steps with `.appL s` (R10–R14). `red_K`/`red_S`: one `refine ⟨⟨_, …, …⟩, fun x hx => ?_⟩` per arrow (R15); only the fully applied case needs `red_back .K` / `red_back .S` (R16).
H3. Saturated `S` case: `apply red_back .S; exact (hx.2 z hz).2 _ (hy.2 z hz)`. Then `theorem fundamental (h : HasTy t A) : Red A t` by `induction h` (R17); the `app` case is `ih1.2 _ ih2`, and `weak_normalization` is `red_wn (fundamental h)`.
-/
