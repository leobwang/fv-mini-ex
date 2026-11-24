/- E017 | Structures | 2-3 min | structure, fields, projections
GOAL
  Define `origin` and `Point.swap` for a 2D point structure, and prove they behave.

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
structure Point where
  x : Nat
  y : Nat
-- END SPEC

/- SKELETON · origin (definition body)
  1. Both fields must be `0` (origin_spec). Write the value, fields by name:          R1
     (or by position, `x` first:                                                     R2)
-/
-- BEGIN SPEC
def origin : Point :=
-- END SPEC
  { x := 0, y := 0 }

/- SKELETON · Point.swap (definition body)
  1. Read the old fields of `p` with projections:                                    R3
  2. Build the new point: the new `x` is the old `y`, the new `y` the old `x`
     (swap_fields). By name or by position (positions follow field order):           R1 or R2
-/
-- BEGIN SPEC
def Point.swap (p : Point) : Point :=
-- END SPEC
  ⟨p.y, p.x⟩

/- SKELETON · origin_spec
  1. Split the `∧`:                                                                  R4
  2. Each half: unfold `origin`, reduce the projection, then the sides agree:        R5 → R6
     Steps 1–2 in one term: the pair form of R4, with R7 in each slot:               R4, R7
-/
-- BEGIN SPEC
theorem origin_spec : origin.x = 0 ∧ origin.y = 0 :=
-- END SPEC
  ⟨rfl, rfl⟩

/- SKELETON · swap_fields
  1. Split the `∧`:                                                                  R4
  2. Each half: unfold `Point.swap`, reduce the projection (`p` stays a variable):   R5 → R6
     or in one go:                                                                   R7
-/
-- BEGIN SPEC
theorem swap_fields (p : Point) : p.swap.x = p.y ∧ p.swap.y = p.x :=
-- END SPEC
  ⟨rfl, rfl⟩

/- SKELETON · swap_swap
  1. Unfold `Point.swap`: the left side becomes                                      R5
     `{ x := { x := p.y, y := p.x }.y, y := { x := p.y, y := p.x }.x }`.
  2. Reduce the projections: the fields become `p.x` and `p.y`, i.e. `p` rebuilt from
     its own fields, which is `p` by structure eta (no `cases p` needed). `dsimp only`
     does both at once and CLOSES the goal, so there is no separate eta step to run:  R6 + R8
     Steps 1–2 in one go:                                                            R7 (+ R8)
-/
-- BEGIN SPEC
theorem swap_swap (p : Point) : p.swap.swap = p :=
-- END SPEC
  rfl

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `origin_spec` and `swap_fields` say exactly what each field of `origin` and `p.swap` must be. Every
    theorem then follows by computing projections of constructor values.
H2. Build values with `{ x := _, y := _ }` (R1) or `⟨_, _⟩` (R2; positions follow the field order `x, y`).
    Prove each `∧` as a pair (R4) whose halves hold by unfolding and reducing (R5, R6), i.e. by `rfl` (R7).
    `swap_swap` additionally needs structure eta (R8), which `rfl` also knows.
H3. `def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩`; proofs `⟨rfl, rfl⟩`, `⟨rfl, rfl⟩`, `rfl`.
-/
