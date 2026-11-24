/- H017 | Greedy interval scheduling is optimal | 1-1.5 h | greedy algorithm, exchange argument, List.Sublist, List.Pairwise, induction generalizing
GOAL
  On intervals sorted by finish time, "take the next interval that starts at or after the last one
  taken finishes" yields a longest compatible chain (each interval starts at or after the previous
  one's finish `f`; disjoint when every `s ≤ f`): a subsequence of the input, and none is longer.

REFERENCE
  #check List.pairwise_cons    -- Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l
  #check List.Sublist.subset   -- l₁ <+ l₂ → l₁ ⊆ l₂     (`<+` is List.Sublist: delete some entries)
  #check List.sublist_of_cons_sublist  -- a :: l₁ <+ l₂ → l₁ <+ l₂
  #check List.Sublist.cons     -- (a : α) : l₁ <+ l₂ → l₁ <+ a :: l₂
  #check List.Sublist.cons_cons  -- (a : α) : l₁ <+ l₂ → a :: l₁ <+ a :: l₂
  #check List.mem_cons_self    -- a ∈ a :: l
  -- `cases hsub with | cons _ h => _ | cons_cons _ h => _` : `S` skips the head / `S` keeps the head.
  -- `induction xs generalizing t S with | nil => _ | cons x xs ih => _`
  -- `simp only [greedy]` then `split` cases on the `if` inside `greedy`.
NOTE: the spec starts the greedy at threshold `0`; the induction needs an arbitrary threshold `t`.
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

-- MILESTONE (optional: change or delete)
theorem greedy_sublist (t : Nat) (xs : List Iv) : (greedy t xs).Sublist xs := by
  induction xs generalizing t with
  | nil => simp [greedy]
  | cons x xs ih =>
    simp only [greedy]
    split
    · exact (ih x.f).cons_cons x
    · exact (ih t).cons x

-- MILESTONE (optional: change or delete)
theorem greedy_compatible (t : Nat) (xs : List Iv) : Compatible t (greedy t xs) := by
  induction xs generalizing t with
  | nil => trivial
  | cons x xs ih =>
    simp only [greedy]
    split
    · exact ⟨by assumption, ih x.f⟩
    · exact ih t

-- MILESTONE (optional: change or delete)
theorem compatible_mono {t t' : Nat} {S : List Iv} (h : Compatible t' S) (ht : t ≤ t') :
    Compatible t S := by
  cases S with
  | nil => trivial
  | cons i is => exact ⟨Nat.le_trans ht h.1, h.2⟩

-- MILESTONE (optional: change or delete)
theorem greedy_stays_ahead (t : Nat) (xs S : List Iv) (hs : SortedByFinish xs)
    (hsub : S.Sublist xs) (hc : Compatible t S) : S.length ≤ (greedy t xs).length := by
  induction xs generalizing t S with
  | nil => cases hsub; simp
  | cons x xs ih =>
    have hs' : SortedByFinish xs := (List.pairwise_cons.mp hs).2
    have hfx : ∀ y ∈ xs, x.f ≤ y.f := (List.pairwise_cons.mp hs).1
    simp only [greedy]
    split
    · cases hsub with
      | cons _ hsub' =>
        -- `S` skips `x`: exchange its first interval `y` for `x`, which finishes no later.
        cases S with
        | nil => simp
        | cons y S' =>
          have hy : y ∈ xs := hsub'.subset List.mem_cons_self
          have h1 : Compatible x.f S' := compatible_mono hc.2 (hfx y hy)
          have := ih x.f S' hs' (List.sublist_of_cons_sublist hsub') h1
          simp only [List.length_cons]; omega
      | cons_cons _ hsub' =>
        have := ih x.f _ hs' hsub' hc.2
        simp only [List.length_cons]; omega
    · rename_i htx
      cases hsub with
      | cons _ hsub' => exact ih t S hs' hsub' hc
      | cons_cons _ hsub' => exact absurd hc.1 htx

-- BEGIN SPEC
theorem greedy_optimal (xs : List Iv) (hs : SortedByFinish xs) : IsOptimal xs (greedy 0 xs) :=
-- END SPEC
  ⟨greedy_sublist 0 xs, greedy_compatible 0 xs,
    fun _ hsub hc => greedy_stays_ahead 0 xs _ hs hsub hc⟩

end H017

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the three parts of `IsOptimal` separately, each for an arbitrary threshold `t`, then
    instantiate `t := 0`. The first two are inductions on `xs` with `split` on greedy's `if`.
H2. Optimality, induction on `xs` generalizing `t S`, head `x`. If greedy skips `x` (`¬ t ≤ x.s`),
    `S` cannot keep `x` either. If greedy takes `x` and `S` keeps `x`, use the IH at threshold `x.f`.
    If greedy takes `x` but `S = y :: S'` skips it: sortedness gives `x.f ≤ y.f`, so `S'` is still
    compatible after `x.f` and the IH bounds `S'`, which is one shorter than `S`.
H3. In that last case (`hsub' : y :: S' <+ xs` from `cases hsub`, `hs' := (List.pairwise_cons.mp hs).2`):
    `have hy : y ∈ xs := hsub'.subset List.mem_cons_self`,
    `have h1 : Compatible x.f S' := compatible_mono hc.2 ((List.pairwise_cons.mp hs).1 y hy)`,
    `have := ih x.f S' hs' (List.sublist_of_cons_sublist hsub') h1`, then `simp only [List.length_cons]; omega`.
-/
