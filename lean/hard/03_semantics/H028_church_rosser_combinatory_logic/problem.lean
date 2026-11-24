/- H028 | Church-Rosser for combinatory logic | 1.5-2 h | confluence, parallel reduction, diamond property, inversion lemmas, strip lemma, combinatory logic
GOAL
  Weak reduction of SK combinators (`⟶` is one `Step`: `K x y ⟶ x`, `S x y z ⟶ x z (y z)`,
  allowed anywhere inside a term; informal notation, not Lean syntax) is confluent: two reduction
  sequences (`Star`) from `a` can always be joined at a common `d`. Prove it with
  Tait–Martin-Löf parallel reduction `Par`: it has the diamond property and `Step ⊆ Par ⊆ Star`.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H028

-- BEGIN SPEC
/-- Untyped combinatory logic. -/
inductive Tm where
  | S
  | K
  | app (t u : Tm)

/-- Weak reduction: `K x y ⟶ x`, `S x y z ⟶ x z (y z)`, in any context. -/
inductive Step : Tm → Tm → Prop
  | K {x y : Tm} : Step (.app (.app .K x) y) x
  | S {x y z : Tm} : Step (.app (.app (.app .S x) y) z) (.app (.app x z) (.app y z))
  | appL {t t' u : Tm} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Tm} : Step u u' → Step (.app t u) (.app t u')

/-- Zero or more steps. -/
inductive Star : Tm → Tm → Prop
  | refl (t : Tm) : Star t t
  | step {a b c : Tm} : Step a b → Star b c → Star a c
-- END SPEC

-- MILESTONE (optional: change or delete)
/-- Parallel reduction: contract any set of redexes present in the term at once. -/
inductive Par : Tm → Tm → Prop
  | refl (t : Tm) : Par t t
  | app {t t' u u' : Tm} : Par t t' → Par u u' → Par (.app t u) (.app t' u')
  | K {x x' y : Tm} : Par x x' → Par (.app (.app .K x) y) x'
  | S {x x' y y' z z' : Tm} : Par x x' → Par y y' → Par z z' →
      Par (.app (.app (.app .S x) y) z) (.app (.app x' z') (.app y' z'))

-- MILESTONE (optional: change or delete): inversion lemmas for the overlap cases
/- SKELETON · par_Kx
  0. First, a helper above this lemma: `par_K : Par .K t → t = .K`        R3, then rfl
  1. Case split on `h`: only `refl` and `app` can have `K x` on the left    R4
  2. refl: the witness is `x` itself                                        R2 with R1 (`.refl x`)
  3. app h1 h2: `h1 : Par Tm.K t'✝`; turn `t'✝` into `K`, then the witness  rw [par_K h1], R2
-/
theorem par_Kx {x t : Tm} (h : Par (.app .K x) t) : ∃ x', t = .app .K x' ∧ Par x x' := by
  sorry

/- SKELETON · par_Sxy
  0. Helpers first: `par_S : Par .S t → t = .S` (R3) and
     `par_Sx : Par (.app .S x) t → ∃ x', t = .app .S x' ∧ Par x x'`        as par_Kx: R4, R2, rw
  1. Case split on `h`                                                      R4
  2. refl: witnesses `x`, `y`                                               R2 with R1
  3. app h1 h2: `h1 : Par (Tm.S.app x) t'✝`; unpack `par_Sx h1`            R5 (pattern `rfl`), R2
-/
theorem par_Sxy {x y t : Tm} (h : Par (.app (.app .S x) y) t) :
    ∃ x' y', t = .app (.app .S x') y' ∧ Par x x' ∧ Par y y' := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · par_diamond   (uses par_Kx, par_Sxy)
  1. Induction on `hb`, keeping `c` general; case names after R8          R9, R8
  2. refl: no split needed, `c` is the join (`hc` and `.refl c`)          R2, R1
  3. In each of the other 3 cases, split `hc` the same way                R4
     `refl` there: the join is `hb`'s right side, rebuilt by hb's rule    R2, R1
  4. same rule on both sides: apply each IH to the matching premise, unpack  R5
       app vs app: rebuild both sides with `Par.app`                      R1, R2
       K vs K: the IH applied to the premise is already the goal          exact
       S vs S: three IHs; rebuild both `x z (y z)` shapes with `Par.app`  R1, R2
  5. app vs K (and app vs S): `cases hc` made the head `K x` (or `S x y`):
       invert `ht` with par_Kx / par_Sxy                                  R5
       feed the head IH a Par of the head, e.g. `.app (.refl .K) hx2`     R1, R5
       invert both results with par_Kx / par_Sxy; equate the two          R5, R6
       (S only: the third argument with `ihu`)                            R5
       close: the `app` side with the K / S rule (S: the other with `Par.app`)  R2, R1
  6. K vs app, S vs app: invert the `app` side's head `h1` with
     par_Kx / par_Sxy (pattern `rfl`), then the IHs                       R5
     close: the `app` side with the K / S rule (S: the other with `Par.app`)  R2, R1
-/
theorem par_diamond {a b c : Tm} (hb : Par a b) (hc : Par a c) : ∃ d, Par b d ∧ Par c d := by
  sorry

-- MILESTONE (optional: change or delete): `Step ⊆ Par ⊆ Star`
/- SKELETON · par_of_step
  1. Induction on the step: `| K | S | appL _ ih | appR _ ih`             R8
  2. Each case is one `Par` rule; parts that do not move use `.refl _`    R1
-/
theorem par_of_step {a b : Tm} (h : Step a b) : Par a b := by
  sorry

/- SKELETON · star_trans
  1. Induction on `h1` (`h2` mentions `b` and is carried along)           R7
  2. refl: `h2` is the goal; step: one `Star.step`, then the IH on `h2`   R1
-/
theorem star_trans {a b c : Tm} (h1 : Star a b) (h2 : Star b c) : Star a c := by
  sorry

/- SKELETON · star_of_par   (uses star_trans)
  0. Helpers first (guide W2 is the general form):
       star_appL : Star t t' → Star (.app t u) (.app t' u)               R7, R1
       star_appR : Star u u' → Star (.app t u) (.app t u')               R7, R1
  1. Induction on `h`, one IH per `Par` premise                           R8
  2. app: star_trans of the two helpers on the IHs                        R1
     K: one `Step.K`, then the IH                                         R1
     S: one `Step.S`, then rebuild `x z (y z)` → `x' z' (y' z')`
        with the helpers and star_trans                                   R1
-/
theorem star_of_par {a b : Tm} (h : Par a b) : Star a b := by
  sorry

-- MILESTONE (optional: change or delete)
/- SKELETON · strip   (uses par_diamond, par_of_step, star_of_par, star_trans)
  1. Induction on `hc`, keeping `b` general                               R9, R7
  2. refl: `b` itself                                                      R2, R1
  3. step s _ ih: diamond of `hb` against `par_of_step s`, unpack          R5
     the IH at the new Par, unpack                                         R9, R5
     join: star_trans (star_of_par _) _                                    R2
-/
theorem strip {a b c : Tm} (hb : Par a b) (hc : Star a c) : ∃ d, Star b d ∧ Par c d := by
  sorry

/- SKELETON · church_rosser   (prove the MILESTONES above first, in file order;
  this proof uses strip, par_of_step, star_of_par, star_trans)
  1. Induction on `hb`, keeping `c` general                               R9, R7
  2. refl: `c` itself                                                      R2, R1
  3. step s _ ih: `strip (par_of_step s) hc`, unpack                      R5
     the IH at the new Star, unpack                                        R9, R5
     join: on the `c` side star_trans (star_of_par _) _                    R2
-/
-- BEGIN SPEC
theorem church_rosser {a b c : Tm} (hb : Star a b) (hc : Star a c) :
    ∃ d, Star b d ∧ Star c d :=
-- END SPEC
  sorry

end H028

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Tile the square: the one-step diamond for `Par` (`par_diamond`) gives a strip (one `Par` against a
    `Star`), and strips stacked along the first `Star` give confluence. `Step ⊆ Par` (`par_of_step`) and
    `Par ⊆ Star` (`star_of_par`, after `star_trans` and the congruences `star_appL`, `star_appR`) move
    between the relations. `Step` alone has no diamond: `S x y z` copies `z`.
H2. `par_diamond`, `strip`, `church_rosser`: `induction … generalizing …` (R9) on one derivation, and in
    `par_diamond` also `cases` (R4) on the other; the rest are plain `induction` (R7, R8). The hard cases are `app` on one side against a `K`/`S`
    contraction on the other: invert the head with `par_Kx` / `par_Sxy`, then apply the head's IH.
    The inversions themselves: `cases h`, and invert the shorter head (`par_K`, `par_S`, `par_Sx`).
H3. `app` vs `K hx2`: `obtain ⟨x1, rfl, hx1⟩ := par_Kx ht; obtain ⟨d', hd1, hd2⟩ := iht (.app (.refl .K) hx2)`,
    invert `hd1`, `hd2` with `par_Kx`, `cases` the equation, witness `⟨e1, .K he1, he2⟩`.
    `church_rosser`, step case: `obtain ⟨d, h1, h2⟩ := strip (par_of_step s) hc`, then `ih h1`, then
    `star_trans (star_of_par h2) _`.
-/
