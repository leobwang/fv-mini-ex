/- H013 | Run-length encoding, both directions | 1-1.5 h | write the function, canonical forms, List.replicate, round trip, split
GOAL
  Write `encode` (run-length encoding, e.g. `[a,a,b] ↦ [(a,2),(b,1)]`) and prove: decoding undoes it,
  it always produces a canonical run list, and it undoes decoding on canonical run lists. Together the
  three theorems pin `encode` down uniquely.

BANNED: grind, fun_induction, try?, exact?, apply?, import

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · encode
  1. The `:=` is frozen: the body is one term, a `fun` with two arms `[]` and `x :: xs`   R1
  2. In the `x :: xs` arm, `match` on the recursive result `encode xs`, and in its cons arm
     compare `x` with the first run's symbol by `if x = y`                              R2
     (empty encoding → one new run; same symbol → bump the count; else → push `(x, 1)`)
  3. Test it: `example : encode [1, 1, 2] = [(1, 2), (2, 1)] := rfl`
-/
-- BEGIN SPEC
def encode {α : Type} [DecidableEq α] : List α → List (α × Nat) :=
-- END SPEC
  fun
  | [] => []
  | x :: xs =>
    match encode xs with
    | (y, n) :: r => if x = y then (y, n + 1) :: r else (x, 1) :: (y, n) :: r
    | [] => [(x, 1)]

/- SKELETON · the three MILESTONES (prove these FIRST)
  canonical_bump and canonical_push are used in encode_canonical (bump in the `x = y` branch,
  push in the `x ≠ y` branch); encode_replicate_append is used in encode_decode, once per case.
  canonical_bump, canonical_push, each:
    1. `Canonical` looks two runs ahead: case on `r`                                 R3
    2. in the cons case, take the head pair apart                                    R4
    3. unfold `Canonical` in `h` and in the goal                                     R5
    4. close: `⟨…, …⟩` from `h`'s parts, counts by `omega`                           R7, R6
    nil case: bump's is `simp [Canonical]`; push's needs R5, then R7 with `hxy` and `h`
       (`simp [Canonical]` alone leaves `¬x = y ∧ 0 < n` there)
  encode_replicate_append:
    1. `induction n`                                                                R8
    2. zero: make the argument a cons, unfold `encode` once                          R9, R10, R11
       split the `match`, name the hypotheses, split the `if`                       R12, R13, R14
         `a = y` branch: impossible by `hy`                                          R15, R16
         other branches: `rw [heq]`
    3. succ: make the argument a cons, unfold once, use `ih`, compute               R17, R18, R11 (rw), rw [ih], R19
-/
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

/- SKELETON · decode_encode
  1. `induction xs`; the `nil` case is `rfl`                                         R8 (on a list)
  2. cons: unfold `encode (x :: xs)` once                                            R11
  3. all three arms in one line: split the `match`, then (where there is one) the `if`,
     and simplify with `decode`, `List.replicate_succ` and the hypotheses           R12 <;> R20 (R14) <;> R21
-/
-- BEGIN SPEC
theorem decode_encode {α : Type} [DecidableEq α] (xs : List α) : decode (encode xs) = xs :=
-- END SPEC
  by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [encode]
      split <;> (try split) <;> simp_all [decode, List.replicate_succ]

/- SKELETON · encode_canonical  (uses canonical_bump, canonical_push)
  1. `induction xs`; the `nil` goal `Canonical (encode [])` computes to `True`       R8, R22
  2. cons: unfold `encode (x :: xs)` once, split the `match`                         R11, R12
  3. cons arm: name `y n r heq`, rewrite `heq` into `ih`, split the `if`             R13, R23, R14
       `x = y`  → canonical_bump applied to `ih`
       `x ≠ y`  → name the `¬x = y` hypothesis, canonical_push applied to it and `ih` R13
  4. empty arm: `Canonical [(x, 1)]`                                                 simp [Canonical]
-/
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

/- SKELETON · encode_decode  (uses encode_replicate_append)
  1. `induction l`; the `nil` case is `rfl`.
     cons: split the head pair `(a, n)`, case on the rest                             R8, R4, R3
  2. one-run case `[(a, n)]`: unfold `Canonical` in `h` (gives `0 < n`), write
     `n = k + 1`, then the milestone with `ys := []`, finished by simplification      R5, R25, R26
     (its `hy` argument: `encode [] = []` is not a cons, `simp [encode]`)
  3. two-run case `(a, n) :: (b, m) :: r`: unfold `Canonical` in `h`, take it apart,
     `n = k + 1`                                                                       R5, R24, R25
  4. the IH on the rest, `have ih' := ih hr`: `encode (decode ((b, m) :: r)) = (b, m) :: r`;
     unfold `decode` in `ih'` and the goal                                            R5
  5. `rw` with the milestone (`encode_replicate_append a k`), then `ih'`. Left out, its
     `hy` argument becomes a second goal `case hy`. There: `rw [ih']`, then an equation
     `(b, m) :: r = (a, m_1) :: r_1` gives `b = a`, contradicting `hab`               R27, R28
-/
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
H1. Encode from the right: encode the tail, then extend its first run or push a new one. Every proof
    follows that recursion: `induction`, unfold `encode` once (`simp only [encode]`), `split` the
    `match` and the `if`. Prove the three MILESTONES first.
H2. `encode_canonical`: in the cons arm `rw [heq] at ih`, then `canonical_bump` / `canonical_push`.
    `encode_decode`: induction on the run list, `cases` on the rest, `n = k + 1` by
    `obtain ⟨k, rfl⟩`; re-encode the first run with `encode_replicate_append`, whose `hy` holds
    because the IH says the rest re-encodes to `(b, m) :: r` with `b ≠ a`.
H3. `encode := fun | [] => [] | x :: xs => match encode xs with
       | (y, n) :: r => if x = y then (y, n + 1) :: r else (x, 1) :: (y, n) :: r | [] => [(x, 1)]`.
    `decode_encode` cons case: `simp only [encode]; split <;> (try split) <;> simp_all [decode, List.replicate_succ]`.
    `encode_replicate_append` succ case: `rw [List.replicate_succ, List.cons_append, encode, ih]; simp`.
-/
