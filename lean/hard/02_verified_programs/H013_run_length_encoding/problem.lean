/- H013 | Run-length encoding, both directions | 1-1.5 h | write the function, canonical forms, List.replicate, round trip, split
GOAL
  Write `encode` (run-length encoding, e.g. `[a,a,b] ↦ [(a,2),(b,1)]`) and prove: decoding undoes it,
  it always produces a canonical run list, and it undoes decoding on canonical run lists. Together the
  three theorems pin `encode` down uniquely.

REFERENCE
  example : List.replicate 3 'a' = ['a', 'a', 'a'] := rfl     -- `replicate n a`: n copies of a
  #check @List.replicate_succ  -- replicate (n + 1) a = a :: replicate n a
  #check @List.cons_append     -- (a :: as) ++ bs = a :: (as ++ bs)
  example : (fun | [] => 0 | _ :: _ => 1 : List Nat → Nat) [5] = 1 := rfl  -- `fun` with match arms
  -- `def g : List α → β := fun | [] => .. | x :: xs => .. g xs ..` recurses structurally like equations.
  -- `simp only [encode]` unfolds one step; `split` cases on a `match`/`if` in the goal,
  -- `rename_i y n r heq` names the anonymous hypotheses it made (heq : encode xs = (y, n) :: r).
  example (a b : Nat) (n m : Nat) (h : (a, n) = (b, m)) : a = b := by injection h  -- pair equality
  example (n : Nat) (h : 0 < n) : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩  -- then `obtain ⟨k, rfl⟩ := ...`
BANNED: grind, fun_induction, try?, exact?, apply?, import
NOTE: The `:=` of `encode` is frozen, so write its body as `fun | ... => ...` (or any term).
NOTE: Do not add imports or leave search tactics (`exact?`, `apply?`, `try?`) in the file. No `grind`: use `split`.
-/

namespace H013

-- BEGIN SPEC
def decode {α : Type} : List (α × Nat) → List α
  | [] => []
  | (a, n) :: r => List.replicate n a ++ decode r

/-- Canonical run lists: every count is positive and neighbouring runs have different symbols. -/
def Canonical {α : Type} : List (α × Nat) → Prop
  | [] => True
  | [(_, n)] => 0 < n
  | (a, n) :: (b, m) :: r => 0 < n ∧ a ≠ b ∧ Canonical ((b, m) :: r)
-- END SPEC

-- BEGIN SPEC
def encode {α : Type} [DecidableEq α] : List α → List (α × Nat) :=
-- END SPEC
  sorry

-- MILESTONE (optional: change or delete)
theorem canonical_bump {α : Type} (y : α) (n : Nat) (r : List (α × Nat))
    (h : Canonical ((y, n) :: r)) : Canonical ((y, n + 1) :: r) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem canonical_push {α : Type} (x y : α) (n : Nat) (r : List (α × Nat)) (hxy : x ≠ y)
    (h : Canonical ((y, n) :: r)) : Canonical ((x, 1) :: (y, n) :: r) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem encode_replicate_append {α : Type} [DecidableEq α] (a : α) (n : Nat) (ys : List α)
    (hy : ∀ m r, encode ys ≠ (a, m) :: r) :
    encode (List.replicate (n + 1) a ++ ys) = (a, n + 1) :: encode ys := by
  sorry

-- BEGIN SPEC
theorem decode_encode {α : Type} [DecidableEq α] (xs : List α) : decode (encode xs) = xs :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem encode_canonical {α : Type} [DecidableEq α] (xs : List α) : Canonical (encode xs) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem encode_decode {α : Type} [DecidableEq α] (l : List (α × Nat)) (h : Canonical l) :
    encode (decode l) = l :=
-- END SPEC
  sorry

end H013

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Encode from the right: encode the tail first, then either extend its first run or start a new one.
    Every proof then follows that recursion: `induction xs`, `simp only [encode]`, `split`.
H2. `encode_decode` goes by induction on the run list. Decoding `(a, n) :: rest` gives
    `replicate n a ++ decode rest`; the milestone `encode_replicate_append` re-encodes it, and its
    hypothesis holds because `encode (decode rest) = rest` (IH) starts with a symbol `b ≠ a`.
H3. `encode := fun | [] => [] | x :: xs => match encode xs with
       | (y, n) :: r => if x = y then (y, n + 1) :: r else (x, 1) :: (y, n) :: r | [] => [(x, 1)]`.
    `encode_replicate_append`: `induction n`; the succ case is `rw [List.replicate_succ, List.cons_append, encode, ih]; simp`.
-/
