/- M006 | Fin n | 10-15 min | Fin, dependent types, Fin.ext, Fin.last, castSucc
GOAL
  `Fin n` is a number with a proof that it is `< n`. Build one (`flip`), prove it is an
  involution, and prove a sum over `Fin n` is additive.

REFERENCE
  example : Fin 5 := ⟨3, by decide⟩           -- value + proof of `3 < 5`
  example (n : Nat) (i : Fin n) : i.val < n := i.isLt   -- `i.val` (or `↑i`) and its bound
  example (n : Nat) (i j : Fin n) (h : i.val = j.val) : i = j := Fin.ext h
  example (n : Nat) (i : Fin n) : i.val < n + 1 := by omega   -- omega knows `i.val < n`
  #check Fin.last       -- (n : Nat) : Fin (n + 1), the value n
  #check Fin.castSucc   -- Fin n → Fin (n + 1), same value
-/

namespace M006

-- BEGIN SPEC
def flip {n : Nat} (i : Fin n) : Fin n :=
-- END SPEC
  ⟨n - 1 - i.val, by omega⟩

-- BEGIN SPEC
theorem flip_val {n : Nat} (i : Fin n) : (flip i).val = n - 1 - i.val :=
-- END SPEC
  rfl

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

-- BEGIN SPEC
theorem sumFin_const (n c : Nat) : sumFin n (fun _ => c) = n * c :=
-- END SPEC
  by
    induction n with
    | zero => simp [sumFin]
    | succ n ih => simp [sumFin, ih, Nat.add_mul]; omega

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
H1. `flip i` needs a value and a proof that it is `< n`; `omega` can prove it from `i.isLt`.
H2. Equality of `Fin`s reduces to equality of values (`Fin.ext`). For sums, induct on `n`; the IH must be usable at a different `f`.
H3. `⟨n - 1 - i.val, by omega⟩`; `apply Fin.ext; simp [flip]; omega`. In `sumFin_add` the IH is `∀ f g, ...` (Lean generalises it since `f g` come after `n`): `rw [ih (fun i => f i.castSucc) (fun i => g i.castSucc)]`.
-/
