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

-- Inversion lemmas: what can `K`, `S`, `K x`, `S x` reduce to in parallel?
theorem par_K {t : Tm} (h : Par .K t) : t = .K := by cases h; rfl

theorem par_S {t : Tm} (h : Par .S t) : t = .S := by cases h; rfl

theorem par_Sx {x t : Tm} (h : Par (.app .S x) t) : ∃ x', t = .app .S x' ∧ Par x x' := by
  cases h with
  | refl => exact ⟨x, rfl, .refl x⟩
  | app h1 h2 => rw [par_S h1]; exact ⟨_, rfl, h2⟩

-- MILESTONE (optional: change or delete): inversion lemmas for the overlap cases
theorem par_Kx {x t : Tm} (h : Par (.app .K x) t) : ∃ x', t = .app .K x' ∧ Par x x' := by
  cases h with
  | refl => exact ⟨x, rfl, .refl x⟩
  | app h1 h2 => rw [par_K h1]; exact ⟨_, rfl, h2⟩

theorem par_Sxy {x y t : Tm} (h : Par (.app (.app .S x) y) t) :
    ∃ x' y', t = .app (.app .S x') y' ∧ Par x x' ∧ Par y y' := by
  cases h with
  | refl => exact ⟨x, y, rfl, .refl x, .refl y⟩
  | app h1 h2 =>
    obtain ⟨x', rfl, hx⟩ := par_Sx h1
    exact ⟨x', _, rfl, hx, h2⟩

-- MILESTONE (optional: change or delete)
theorem par_diamond {a b c : Tm} (hb : Par a b) (hc : Par a c) : ∃ d, Par b d ∧ Par c d := by
  induction hb generalizing c with
  | refl t => exact ⟨c, hc, .refl c⟩
  | app ht hu iht ihu =>
    cases hc with
    | refl => exact ⟨_, .refl _, .app ht hu⟩
    | app ht2 hu2 =>
      obtain ⟨d1, h1, h1'⟩ := iht ht2
      obtain ⟨d2, h2, h2'⟩ := ihu hu2
      exact ⟨_, .app h1 h2, .app h1' h2'⟩
    | K hx2 =>
      -- WHY: the IH is about the head `K x`, so feed it a `Par` of the head and invert both results.
      obtain ⟨x1, rfl, hx1⟩ := par_Kx ht
      obtain ⟨d', hd1, hd2⟩ := iht (.app (.refl .K) hx2)
      obtain ⟨e1, rfl, he1⟩ := par_Kx hd1
      obtain ⟨e2, he, he2⟩ := par_Kx hd2
      cases he
      exact ⟨e1, .K he1, he2⟩
    | S hx2 hy2 hz2 =>
      obtain ⟨x1, y1, rfl, hx1, hy1⟩ := par_Sxy ht
      obtain ⟨d', hd1, hd2⟩ := iht (.app (.app (.refl .S) hx2) hy2)
      obtain ⟨ex, ey, rfl, hex1, hey1⟩ := par_Sxy hd1
      obtain ⟨ex', ey', he, hex2, hey2⟩ := par_Sxy hd2
      cases he
      obtain ⟨dz, hz1, hz2⟩ := ihu hz2
      exact ⟨_, .S hex1 hey1 hz1, .app (.app hex2 hz2) (.app hey2 hz2)⟩
  | K hx ihx =>
    cases hc with
    | refl => exact ⟨_, .refl _, .K hx⟩
    | app h1 _ =>
      obtain ⟨x2, rfl, hx2⟩ := par_Kx h1
      obtain ⟨d, hd1, hd2⟩ := ihx hx2
      exact ⟨d, hd1, .K hd2⟩
    | K hx2 => exact ihx hx2
  | S hx hy hz ihx ihy ihz =>
    cases hc with
    | refl => exact ⟨_, .refl _, .S hx hy hz⟩
    | app h1 h3 =>
      obtain ⟨x2, y2, rfl, hx2, hy2⟩ := par_Sxy h1
      obtain ⟨dx, hx1', hx2'⟩ := ihx hx2
      obtain ⟨dy, hy1', hy2'⟩ := ihy hy2
      obtain ⟨dz, hz1', hz2'⟩ := ihz h3
      exact ⟨_, .app (.app hx1' hz1') (.app hy1' hz1'), .S hx2' hy2' hz2'⟩
    | S hx2 hy2 hz2 =>
      obtain ⟨dx, hx1', hx2'⟩ := ihx hx2
      obtain ⟨dy, hy1', hy2'⟩ := ihy hy2
      obtain ⟨dz, hz1', hz2'⟩ := ihz hz2
      exact ⟨_, .app (.app hx1' hz1') (.app hy1' hz1'), .app (.app hx2' hz2') (.app hy2' hz2')⟩

-- MILESTONE (optional: change or delete): `Step ⊆ Par ⊆ Star`
theorem par_of_step {a b : Tm} (h : Step a b) : Par a b := by
  induction h with
  | K => exact .K (.refl _)
  | S => exact .S (.refl _) (.refl _) (.refl _)
  | appL _ ih => exact .app ih (.refl _)
  | appR _ ih => exact .app (.refl _) ih

theorem star_trans {a b c : Tm} (h1 : Star a b) (h2 : Star b c) : Star a c := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

theorem star_appL {t t' u : Tm} (h : Star t t') : Star (.app t u) (.app t' u) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appL s) ih

theorem star_appR {t u u' : Tm} (h : Star u u') : Star (.app t u) (.app t u') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.appR s) ih

theorem star_of_par {a b : Tm} (h : Par a b) : Star a b := by
  induction h with
  | refl => exact .refl _
  | app _ _ ih1 ih2 => exact star_trans (star_appL ih1) (star_appR ih2)
  | K _ ih => exact .step .K ih
  | S _ _ _ ih1 ih2 ih3 =>
    exact .step .S (star_trans (star_appL (star_trans (star_appL ih1) (star_appR ih3)))
      (star_appR (star_trans (star_appL ih2) (star_appR ih3))))

-- MILESTONE (optional: change or delete)
theorem strip {a b c : Tm} (hb : Par a b) (hc : Star a c) : ∃ d, Star b d ∧ Par c d := by
  induction hc generalizing b with
  | refl => exact ⟨b, .refl _, hb⟩
  | step s _ ih =>
    obtain ⟨d, h1, h2⟩ := par_diamond hb (par_of_step s)
    obtain ⟨e, h3, h4⟩ := ih h2
    exact ⟨e, star_trans (star_of_par h1) h3, h4⟩

-- BEGIN SPEC
theorem church_rosser {a b c : Tm} (hb : Star a b) (hc : Star a c) :
    ∃ d, Star b d ∧ Star c d :=
-- END SPEC
  by
    induction hb generalizing c with
    | refl => exact ⟨c, hc, .refl _⟩
    | step s _ ih =>
      obtain ⟨d, h1, h2⟩ := strip (par_of_step s) hc
      obtain ⟨e, h3, h4⟩ := ih h1
      exact ⟨e, h3, star_trans (star_of_par h2) h4⟩

end H028

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Tile the square: a diamond for one-step `Par` gives a "strip" (one `Par` against a `Star`), and strips stacked along the first `Star` give confluence. Every `Step` is a `Par`, and every `Par` is a `Star` (for `star_of_par`, first prove `Star` is a congruence on each side of `app`: `Star t t' → Star (.app t u) (.app t' u)` and the same for `u`).
H2. `par_diamond`: `induction hb generalizing c`, then `cases hc` in each case. The hard cases are an `app` congruence on one side against a `K`/`S` contraction on the other: invert the head with `par_Kx` / `par_Sxy`, then use the IH on the head. To prove those, `cases h` and invert the shorter head again (`Par .K t` forces `t = .K`; `par_Sxy` needs a `par_Sx` for `Par (.app .S x) t`). `strip`: induction on `hc` generalizing `b`.
H3. `app` vs `K hx2` case: `obtain ⟨x1, rfl, hx1⟩ := par_Kx ht; obtain ⟨d', hd1, hd2⟩ := iht (.app (.refl .K) hx2)`; invert `hd1` and `hd2` with `par_Kx`, `cases` the equation, and the witness is the `K`-argument (`.K he1`). `church_rosser`: `induction hb generalizing c`; in the step case use `strip (par_of_step s) hc`, then the IH, then `star_trans` and `star_of_par`.
-/
