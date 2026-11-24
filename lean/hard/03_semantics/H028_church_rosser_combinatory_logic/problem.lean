/- H028 | Church-Rosser for combinatory logic | 1.5-2 h | confluence, parallel reduction, diamond property, inversion lemmas, strip lemma, combinatory logic
GOAL
  Weak reduction of SK combinators (`⟶` is one `Step`: `K x y ⟶ x`, `S x y z ⟶ x z (y z)`,
  allowed anywhere inside a term; informal notation, not Lean syntax) is confluent: two reduction
  sequences (`Star`) from `a` can always be joined at a common `d`. Prove it with
  Tait–Martin-Löf parallel reduction `Par`: it has the diamond property and `Step ⊆ Par ⊆ Star`.

REFERENCE
  example : H028.Step (.app (.app .K .S) .K) .S := .K               -- `K S K ⟶ S`
  example (t : H028.Tm) : H028.Par t t := .refl t                    -- build proofs with `.ctor`
  -- `cases h` on `h : Par .K t` leaves only the `refl` case (no other rule has `.K` on the left).
  -- `obtain ⟨x', rfl, hx⟩ := h` on `h : ∃ x', t = .app .K x' ∧ ..` also substitutes `t` away.
  -- `cases he` on `he : Tm.app .K u = Tm.app .K v` unifies `u` and `v` (constructors are injective).
  -- `induction hb generalizing c with | refl t => .. | app ht hu iht ihu => .. | K hx ihx => ..`
  -- `induction h with | refl => .. | step s _ ih => ..` on `h : Star a b`.
NOTE: `Step` alone has no diamond (`S x y z` copies `z`), hence `Par`. Leave no `exact?`/`apply?`/`try?`.
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
theorem par_Kx {x t : Tm} (h : Par (.app .K x) t) : ∃ x', t = .app .K x' ∧ Par x x' := by
  sorry

theorem par_Sxy {x y t : Tm} (h : Par (.app (.app .S x) y) t) :
    ∃ x' y', t = .app (.app .S x') y' ∧ Par x x' ∧ Par y y' := by
  sorry

-- MILESTONE (optional: change or delete)
theorem par_diamond {a b c : Tm} (hb : Par a b) (hc : Par a c) : ∃ d, Par b d ∧ Par c d := by
  sorry

-- MILESTONE (optional: change or delete): `Step ⊆ Par ⊆ Star`
theorem par_of_step {a b : Tm} (h : Step a b) : Par a b := by
  sorry

theorem star_trans {a b c : Tm} (h1 : Star a b) (h2 : Star b c) : Star a c := by
  sorry

theorem star_of_par {a b : Tm} (h : Par a b) : Star a b := by
  sorry

-- MILESTONE (optional: change or delete)
theorem strip {a b c : Tm} (hb : Par a b) (hc : Star a c) : ∃ d, Star b d ∧ Par c d := by
  sorry

-- BEGIN SPEC
theorem church_rosser {a b c : Tm} (hb : Star a b) (hc : Star a c) :
    ∃ d, Star b d ∧ Star c d :=
-- END SPEC
  sorry

end H028

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Tile the square: a diamond for one-step `Par` gives a "strip" (one `Par` against a `Star`), and strips stacked along the first `Star` give confluence. Every `Step` is a `Par`, and every `Par` is a `Star` (for `star_of_par`, first prove `Star` is a congruence on each side of `app`: `Star t t' → Star (.app t u) (.app t' u)` and the same for `u`).
H2. `par_diamond`: `induction hb generalizing c`, then `cases hc` in each case. The hard cases are an `app` congruence on one side against a `K`/`S` contraction on the other: invert the head with `par_Kx` / `par_Sxy`, then use the IH on the head. To prove those, `cases h` and invert the shorter head again (`Par .K t` forces `t = .K`; `par_Sxy` needs a `par_Sx` for `Par (.app .S x) t`). `strip`: induction on `hc` generalizing `b`.
H3. `app` vs `K hx2` case: `obtain ⟨x1, rfl, hx1⟩ := par_Kx ht; obtain ⟨d', hd1, hd2⟩ := iht (.app (.refl .K) hx2)`; invert `hd1` and `hd2` with `par_Kx`, `cases` the equation, and the witness is the `K`-argument (`.K he1`). `church_rosser`: `induction hb generalizing c`; in the step case use `strip (par_of_step s) hc`, then the IH, then `star_trans` and `star_of_par`.
-/
