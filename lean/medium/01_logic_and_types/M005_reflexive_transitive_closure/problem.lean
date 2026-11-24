/- M005 | Reflexive-transitive closure | 15-20 min | inductive Prop, parameters, induction on derivations
GOAL
  `Star R a b` means b is reachable from a in zero or more `R`-steps. Prove it is transitive,
  and that for the successor relation on Nat it is exactly `≤`.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M005

-- BEGIN SPEC
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star R a a
  | step {a b c : α} : R a b → Star R b c → Star R a c
-- END SPEC

/- SKELETON · star_single
  1. One `step` whose premise is `h`, in front of the empty path at `b`.
     Write it as a single term: the `step` constructor, its last argument `refl`:    R2 → R1
-/
-- BEGIN SPEC
theorem star_single {α : Type} {R : α → α → Prop} {a b : α} (h : R a b) : Star R a b :=
-- END SPEC
  sorry

/- SKELETON · star_trans   (milestone: used in `star_succ_iff`, direction ←)
  1. Induct on the FIRST derivation `h1`, naming the parts. `h2 : Star R b c` mentions
     the index `b`, so it is generalized: it reappears in each case and in the IH:   R3, R4
  2. `refl`: `h2` now has exactly the goal's type:                                   exact h2
  3. `step hab _ ih` (`hab : R a✝¹ b✝`, `ih : Star R c✝ c → Star R b✝ c`,
     `h2 : Star R c✝ c`, goal `Star R a✝¹ c`): put `hab` in front of
     the path the IH builds from `h2`:                                               R2, R5
-/
-- BEGIN SPEC
theorem star_trans {α : Type} {R : α → α → Prop} {a b c : α}
    (h1 : Star R a b) (h2 : Star R b c) : Star R a c :=
-- END SPEC
  sorry

/- SKELETON · star_succ_iff   (prove `star_single` and `star_trans` first)
  1. Split the `↔`:                                                                  R6
  2. → (`intro h`): induct on the derivation `h`:                                    R4
       `refl`: `a✝ ≤ a✝`; `step hab _ ih` (`hab : b✝ = a✝¹ + 1`, `ih : b✝ ≤ c✝`,
       goal `a✝¹ ≤ c✝`): arithmetic in both cases:                                   R7
  3. ← (`intro h`): there is no derivation yet; induct on the NUMBER `b`.
     `h : a ≤ b` mentions `b`, so it moves into the IH:                              R8
       `zero` (`h : a ≤ 0`): fact `a = 0` (R7), substitute it, empty path:           R7 → R9 → R1
       `succ b ih` (`ih : a ≤ b → Star … a b`, `h : a ≤ b + 1`):
         split on `a = b + 1`:                                                       R10
         `a = b + 1`: substitute, empty path:                                        R9 → R1
         `¬a = b + 1`: milestone `star_trans` applied to
           (a) `ih` fed `a ≤ b`, proved inline from `h` and the negation,            R5, R12
           (b) the one-step path `b → b + 1`: milestone `star_single`; its premise
               `(fun n m => m = n + 1) b (b + 1)` is `b + 1 = b + 1`:                R11
-/
-- BEGIN SPEC
theorem star_succ_iff (a b : Nat) : Star (fun n m => m = n + 1) a b ↔ a ≤ b :=
-- END SPEC
  sorry

end M005

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Constructors are functions: `.step h p` puts one step `h : R a b` in front of `p : Star R b c`.
    A hypothesis `h1 : Star R a b` is a derivation: induct on it, one case per constructor. For
    `a ≤ b → Star …` you have no derivation yet, so induct on the number `b` instead.
H2. `star_single`: one `step`, then `refl`. `star_trans`: `induction h1`; `h2` rides along into the IH.
    `star_succ_iff`: `constructor`. → : induction on the derivation, `omega` in both cases.
    ← : `induction b`; in `succ`, `by_cases hab : a = b + 1` and finish with the two milestones.
H3. `star_trans` step case: `exact .step hab (ih h2)`. ← zero case:
    `have : a = 0 := by omega`, `subst this`, `exact .refl 0`.
    ← succ case, `¬a = b + 1`: `exact star_trans (ih (by omega)) (star_single rfl)`.
-/
