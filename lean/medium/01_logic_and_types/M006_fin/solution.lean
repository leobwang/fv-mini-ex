/- M006 | Fin n | 10-15 min | Fin, dependent types, Fin.ext, Fin.last, castSucc
GOAL
  `Fin n` is a number with a proof that it is `< n`. Build one (`flip`), prove it is an
  involution, and prove a sum over `Fin n` is additive.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M006

/- SKELETON · flip
  1. Return a pair ⟨value, proof of value < n⟩; the value is the mirror image `n - 1 - i.val`:   R1
  2. The proof `n - 1 - ↑i < n` needs `n ≥ 1`, which follows from `↑i < n`:   R3 (R2 shows the bound)
-/
-- BEGIN SPEC
def flip {n : Nat} (i : Fin n) : Fin n :=
-- END SPEC
  ⟨n - 1 - i.val, by omega⟩

/- SKELETON · flip_val
  1. Unfold `flip` and take the value of the pair: both sides compute to the same term:   R4
-/
-- BEGIN SPEC
theorem flip_val {n : Nat} (i : Fin n) : (flip i).val = n - 1 - i.val :=
-- END SPEC
  rfl

/- SKELETON · flip_flip
  1. Equality in `Fin n` → equality of values:  goal `↑(flip (flip i)) = ↑i`   R5
  2. Unfold both `flip`s and take values:  goal `n - 1 - (n - 1 - ↑i) = ↑i`   R6
  3. Truncated subtraction, using the bound `↑i < n`:   R7 (R3)
-/
-- BEGIN SPEC
theorem flip_flip {n : Nat} (i : Fin n) : flip (flip i) = i :=
-- END SPEC
  by
    apply Fin.ext
    simp [flip]
    omega

-- BEGIN SPEC
def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f (Fin.last n) + sumFin n (fun i => f i.castSucc)
-- END SPEC

/- SKELETON · sumFin_const
  1. Induct on `n` (`c` does not mention `n`, so `ih` is about the same `c`):   R8
  2. zero: unfold `sumFin 0 _` and tidy `0 * c`:   R9 (`simp [sumFin]`)
  3. succ: unfold one equation and use `ih` in the same pass:   R9, R10 (`simp [sumFin, ih]`)
       goal `c + n * c = (n + 1) * c`
  4. Multiply out `(n + 1) * c`:   R11
  5. Finish: `n * c` is one unknown on both sides:   R12
-/
-- BEGIN SPEC
theorem sumFin_const (n c : Nat) : sumFin n (fun _ => c) = n * c :=
-- END SPEC
  by
    induction n with
    | zero => simp [sumFin]
    | succ n ih => simp [sumFin, ih, Nat.add_mul]; omega

/- SKELETON · sumFin_add
  1. Induct on `n`; `f g : Fin n → Nat` are generalized, so
       ih : ∀ (f g : Fin n → Nat), (sumFin n fun i => f i + g i) = sumFin n f + sumFin n g   R8, R13
  2. zero: unfold and close:   R9 (`simp [sumFin]`)
  3. succ: unfold the three `sumFin (n + 1) _`:   R9 (`simp only [sumFin]`)
  4. Rewrite the sum of `fun i => f i.castSucc + g i.castSucc` with `ih` at those two functions:   R10
  5. Rearrange: the sums and `f (Fin.last n)`, `g (Fin.last n)` are unknowns:   R12
-/
-- BEGIN SPEC
theorem sumFin_add (n : Nat) (f g : Fin n → Nat) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g :=
-- END SPEC
  by
    induction n with
    | zero => simp [sumFin]
    | succ n ih =>
      simp only [sumFin]
      rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]
      omega

end M006

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `flip i` is a pair: a value and a proof that it is `< n` (R1). Equalities of `Fin`s are equalities of
    values (`Fin.ext`, R5). The sums follow `sumFin`'s two equations: induct on `n` (R8).
H2. `flip_flip`: go to values, unfold `flip`, and let `omega` handle the truncated subtraction with the bound
    `↑i < n` it finds itself. Sums: after unfolding one equation the inner sums are over
    `fun i => f i.castSucc`, so the IH must hold for every function; it does, because `f g` have types that
    mention `n` (R13). `omega` treats sums and `n * c` as unknowns but never multiplies out `(n + 1) * c` (R11).
H3. `⟨n - 1 - i.val, by omega⟩`; `apply Fin.ext; simp [flip]; omega`. `sumFin_const` succ case:
    `simp [sumFin, ih, Nat.add_mul]; omega`. `sumFin_add` succ case:
    `simp only [sumFin]; rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]; omega`.
-/
