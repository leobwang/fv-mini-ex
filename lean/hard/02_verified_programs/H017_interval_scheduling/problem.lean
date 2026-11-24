/- H017 | Greedy interval scheduling is optimal | 1-1.5 h | greedy algorithm, exchange argument, List.Sublist, List.Pairwise, induction generalizing
GOAL
  On intervals sorted by finish time, "take the next interval that starts at or after the last one
  taken finishes" yields a longest compatible chain (each interval starts at or after the previous
  one's finish `f`; disjoint when every `s ≤ f`): a subsequence of the input, and none is longer.

GUIDE
  Entries R1–R25: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace H017

-- BEGIN SPEC
/-- A half-open interval [s, f) of time. -/
structure Iv where
  s : Nat
  f : Nat

/-- Greedy: scan intervals sorted by finish time; take one whenever it starts at or after
    `t`, the finish time of the last interval taken. -/
def greedy : Nat → List Iv → List Iv
  | _, [] => []
  | t, i :: is => if t ≤ i.s then i :: greedy i.f is else greedy t is

/-- A list of intervals, in order, each starting at or after the previous one finishes
    (the first starting at or after `t`). -/
def Compatible : Nat → List Iv → Prop
  | _, [] => True
  | t, i :: is => t ≤ i.s ∧ Compatible i.f is

def SortedByFinish (xs : List Iv) : Prop := xs.Pairwise (fun a b => a.f ≤ b.f)

/-- `S` is a compatible selection from `xs` (kept in input order) and no such selection is longer. -/
def IsOptimal (xs S : List Iv) : Prop :=
  S.Sublist xs ∧ Compatible 0 S ∧
    ∀ S' : List Iv, S'.Sublist xs → Compatible 0 S' → S'.length ≤ S.length
-- END SPEC

/- SKELETON · greedy_sublist   (MILESTONE 1: prove it first; part 1 of greedy_optimal)
  1. Induction on the list; greedy's threshold moves from `t` to `x.f`, so generalize it:
       induction xs generalizing t with | nil => … | cons x xs ih => …           R1
  2. nil: unfold greedy at [] and close `[] <+ []`                               R2
  3. cons x xs: open greedy's cons clause, then split its `if`:                  R3, R4
       taken (t ≤ x.s): keep x on both sides; the rest is the IH at x.f          R5
       skipped:         skip x on the right; the rest is the IH at t             R6
-/
-- MILESTONE (optional: change or delete)
theorem greedy_sublist (t : Nat) (xs : List Iv) : (greedy t xs).Sublist xs := by
  sorry

/- SKELETON · greedy_compatible   (MILESTONE 2: part 2 of greedy_optimal)
  1. Induction on xs generalizing t, as in MILESTONE 1                            R1
  2. nil: the goal `Compatible t (greedy t [])` unfolds to `True`                R7
  3. cons x xs: open greedy, split its `if`:                                      R3, R4
       taken: the goal `Compatible t (x :: greedy x.f xs)` is a pair;
              first half is the condition `h✝ : t ≤ x.s`, second the IH at x.f   R8, R9
       skipped: the IH at t
-/
-- MILESTONE (optional: change or delete)
theorem greedy_compatible (t : Nat) (xs : List Iv) : Compatible t (greedy t xs) := by
  sorry

/- SKELETON · compatible_mono   (MILESTONE 3: used in MILESTONE 4's exchange case)
  1. No induction: case on S, so that `Compatible` unfolds                        R10
  2. nil: True                                                                    R7
  3. cons i is: rebuild the pair from the halves of h;
       first half chains t ≤ t' and t' ≤ i.s                                      R8, R11, R12
-/
-- MILESTONE (optional: change or delete)
theorem compatible_mono {t t' : Nat} {S : List Iv} (h : Compatible t' S) (ht : t ≤ t') :
    Compatible t S := by
  sorry

/- SKELETON · greedy_stays_ahead   (MILESTONE 4, the exchange argument; uses MILESTONE 3;
                                    part 3 of greedy_optimal)
  1. Induction on xs generalizing BOTH t and S (the competitor shrinks too):      R1
  2. nil: hsub forces S = []; then `[].length ≤ …`                                R13, R14
  3. cons x xs: record both halves of sortedness first                            R15
       hs' : SortedByFinish xs         hfx : ∀ y ∈ xs, x.f ≤ y.f
     then open greedy and split its `if`                                          R3, R4
  4. greedy takes x (h✝ : t ≤ x.s); case on how S uses x (goals in this order):   R16
       S skips x (hsub' : S <+ xs): case on S                                     R10
         S = []:       R14
         S = y :: S' (the exchange: swap y for x, which finishes no later):
           hy : y ∈ xs                                                            R17, R18
           h1 : Compatible x.f S'      MILESTONE 3 from hc.2 and hfx y hy         R11
           the IH at x.f for S', with S' <+ xs                                    R19, R20
           lengths and arithmetic                                                 R21, R22
       S keeps x (S = x :: l₁✝): IH at x.f with hc.2 (write `_` for l₁✝),
                                 then lengths and arithmetic                      R11, R20, R21, R22
  5. greedy skips x: name the condition htx : ¬t ≤ x.s, then case on hsub:        R23, R16
       S skips x: the IH at t
       S keeps x: hc.1 : t ≤ x.s contradicts htx                                  R11, R24
-/
-- MILESTONE (optional: change or delete)
theorem greedy_stays_ahead (t : Nat) (xs S : List Iv) (hs : SortedByFinish xs)
    (hsub : S.Sublist xs) (hc : Compatible t S) : S.length ≤ (greedy t xs).length := by
  sorry

/- SKELETON · greedy_optimal   (uses MILESTONES 1, 2, 4; prove them first)
  1. `IsOptimal` is a three-part conjunction: look at it, then split it           R25, refine ⟨?_, ?_, ?_⟩
  2. part 1: MILESTONE 1 at t := 0;  part 2: MILESTONE 2 at t := 0
  3. part 3: intro S' hsub hc, then MILESTONE 4 at t := 0
-/
-- BEGIN SPEC
theorem greedy_optimal (xs : List Iv) (hs : SortedByFinish xs) : IsOptimal xs (greedy 0 xs) :=
-- END SPEC
  sorry

end H017

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones first, each for an arbitrary threshold `t` (greedy calls itself at `x.f`, not at
    `0`); greedy_optimal is MILESTONES 1, 2 and 4 at `t := 0`. MILESTONES 1, 2 and 4 are inductions on `xs`
    that open greedy with `simp only [greedy]` and case on its `if` with `split`.
H2. MILESTONE 4: `induction xs generalizing t S`, head `x`, and `cases hsub` for how `S` uses `x`.
    greedy skips `x` (`¬ t ≤ x.s`): `S` cannot keep `x` (`hc.1`), so it skips it: the IH at `t`.
    greedy takes `x`, `S` keeps `x`: the IH at `x.f` with `hc.2`. greedy takes `x`, `S = y :: S'` skips it:
    sortedness gives `x.f ≤ y.f`, so `S'` is compatible after `x.f` (MILESTONE 3) and the IH bounds `S'`,
    which is one shorter than `S`.
H3. In that last case (`hsub' : (y :: S').Sublist xs`, `hfx := (List.pairwise_cons.mp hs).1`,
    `hs' := (List.pairwise_cons.mp hs).2`):
    `have hy : y ∈ xs := hsub'.subset List.mem_cons_self`,
    `have h1 : Compatible x.f S' := compatible_mono hc.2 (hfx y hy)`,
    `have := ih x.f S' hs' (List.sublist_of_cons_sublist hsub') h1`, then `simp only [List.length_cons]; omega`.
-/
