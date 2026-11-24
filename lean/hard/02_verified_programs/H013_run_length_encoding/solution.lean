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
  fun
  | [] => []
  | x :: xs =>
    match encode xs with
    | (y, n) :: r => if x = y then (y, n + 1) :: r else (x, 1) :: (y, n) :: r
    | [] => [(x, 1)]

-- MILESTONE (optional: change or delete)
theorem canonical_bump {α : Type} (y : α) (n : Nat) (r : List (α × Nat))
    (h : Canonical ((y, n) :: r)) : Canonical ((y, n + 1) :: r) := by
  cases r with
  | nil => simp [Canonical]
  | cons q r => obtain ⟨b, m⟩ := q; simp only [Canonical] at h ⊢; exact ⟨by omega, h.2⟩

-- MILESTONE (optional: change or delete)
theorem canonical_push {α : Type} (x y : α) (n : Nat) (r : List (α × Nat)) (hxy : x ≠ y)
    (h : Canonical ((y, n) :: r)) : Canonical ((x, 1) :: (y, n) :: r) := by
  cases r with
  | nil => simp only [Canonical] at h ⊢; exact ⟨by omega, hxy, h⟩
  | cons q r => obtain ⟨b, m⟩ := q; simp only [Canonical] at h ⊢; exact ⟨by omega, hxy, h⟩

-- MILESTONE (optional: change or delete)
theorem encode_replicate_append {α : Type} [DecidableEq α] (a : α) (n : Nat) (ys : List α)
    (hy : ∀ m r, encode ys ≠ (a, m) :: r) :
    encode (List.replicate (n + 1) a ++ ys) = (a, n + 1) :: encode ys := by
  induction n with
  | zero =>
    simp only [List.replicate, List.singleton_append, encode]
    split
    · rename_i y m r heq
      split
      · subst_vars; exact absurd heq (hy _ _)
      · rw [heq]
    · rename_i heq; rw [heq]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, encode, ih]
    simp

-- BEGIN SPEC
theorem decode_encode {α : Type} [DecidableEq α] (xs : List α) : decode (encode xs) = xs :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [encode]
      split <;> (try split) <;> simp_all [decode, List.replicate_succ]

-- BEGIN SPEC
theorem encode_canonical {α : Type} [DecidableEq α] (xs : List α) : Canonical (encode xs) :=
-- END SPEC
  by
    induction xs with
    | nil => trivial
    | cons x xs ih =>
      simp only [encode]
      split
      · rename_i y n r heq
        rw [heq] at ih
        split
        · exact canonical_bump _ _ _ ih
        · rename_i hne; exact canonical_push _ _ _ _ hne ih
      · simp [Canonical]

-- BEGIN SPEC
theorem encode_decode {α : Type} [DecidableEq α] (l : List (α × Nat)) (h : Canonical l) :
    encode (decode l) = l :=
-- END SPEC
  by
    induction l with
    | nil => rfl
    | cons p r ih =>
      obtain ⟨a, n⟩ := p
      cases r with
      | nil =>
        simp only [Canonical] at h
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        simpa [decode, encode] using encode_replicate_append a k [] (by simp [encode])
      | cons q r =>
        obtain ⟨b, m⟩ := q
        simp only [Canonical] at h
        obtain ⟨hn, hab, hr⟩ := h
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have ih' := ih hr
        simp only [decode] at ih' ⊢
        -- WHY: the IH says the rest re-encodes to `(b, m) :: r`, whose head symbol differs from `a`.
        rw [encode_replicate_append a k _ (by rw [ih']; intro m r h; injection h with h; injection h with h; exact hab h.symm), ih']

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
