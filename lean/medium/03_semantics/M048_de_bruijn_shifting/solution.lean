/- M048 | de Bruijn shifting | 15-20 min | de Bruijn indices, binders, cutoff, induction generalizing, if-splitting
GOAL
  In de Bruijn notation a variable is a number: `var k` points to the `k`-th enclosing `lam`.
  `shift d c t` adds `d` to every variable of `t` that is free at cutoff `c` (index `≥ c`).
  Prove: shifting by 0 is the identity, shifts at one cutoff add up, and unit shifts at
  cutoffs `c ≤ c'` commute (the cutoff `c'` moves to `c' + 1`).

BANNED: try?, grind
GUIDE
  Entries R1–R14: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M048

-- BEGIN SPEC
/-- Untyped lambda terms with de Bruijn indices: `var 0` is the nearest enclosing binder. -/
inductive Tm where
  | var (n : Nat)
  | lam (t : Tm)
  | app (t u : Tm)

/-- `shift d c t` adds `d` to every variable of `t` that is free at cutoff `c`. -/
def shift (d c : Nat) : Tm → Tm
  | .var n => if n < c then .var n else .var (n + d)
  | .lam t => .lam (shift d (c + 1) t)
  | .app t u => .app (shift d c t) (shift d c u)
-- END SPEC

/- SKELETON · shift_zero  (the warm-up)
  1. Induction on `t`, generalizing the cutoff: `lam` recurses at `c + 1`:   R1, R2
  2. `var n`: unfold `shift` to an `if`, split it; both goals are `rfl`
     (`n + 0` reduces to `n`):                                              R3 → R4, rfl
  3. `lam`, `app`: unfold and rewrite with the generalized IH(s):           R5
-/
-- BEGIN SPEC
theorem shift_zero (c : Nat) (t : Tm) : shift 0 c t = t :=
-- END SPEC
  by
    induction t generalizing c with
    | var n => simp only [shift]; split <;> rfl
    | lam t ih => simp [shift, ih]
    | app t u iht ihu => simp [shift, iht, ihu]

/- SKELETON · shift_shift
  1. Induction on `t` generalizing `c`, as in `shift_zero`:                  R1, R2
  2. `var n`: split on `n < c`:                                              R6
       `n < c`:  both inner and outer `if` are decided by `h`:               R7
       `¬n < c`: the inner `if` by `h`; the outer one asks `n + d' < c`,
                 decide it with a fact proved by omega; `simp` strips
                 `Tm.var`; finish the sum (or close it with omega):          R7, R9 (R8), R10, R11, R12
  3. `lam`, `app`:                                                           R5
-/
-- BEGIN SPEC
theorem shift_shift (d d' c : Nat) (t : Tm) : shift d c (shift d' c t) = shift (d + d') c t :=
-- END SPEC
  by
    induction t generalizing c with
    | var n =>
      by_cases h : n < c
      · simp [shift, h]
      · simp [shift, h, show ¬ n + d' < c by omega, Nat.add_assoc, Nat.add_comm d d']
    | lam t ih => simp [shift, ih]
    | app t u iht ihu => simp [shift, iht, ihu]

/- SKELETON · shift_comm  (the real work)
  1. Induction on `t` generalizing BOTH cutoffs; `h : c ≤ c'` is carried
     along and becomes a premise of the IH:                                  R1, R13
  2. `var n`: unfold the inner `shift`s, then split on `n < c'`:             R3, R6
       `n < c'`:  split again on `n < c`; in both branches decide every
                  `if` with `h1`, `h2` and facts such as `n < c' + 1`:       R6, R7, R9 (R8)
       `¬n < c'`: no second split; `¬n < c` and the outer conditions
                  follow from `h1`, `h` by omega:                            R7, R9 (R8)
  3. `lam`: the IH at `c + 1`, `c' + 1`, its premise by omega, inside simp:  R14 (R8), R5
  4. `app`: both IHs at `c`, `c'` with the same `h`, inside simp:            R14, R5
-/
-- BEGIN SPEC
theorem shift_comm (c c' : Nat) (t : Tm) (h : c ≤ c') :
    shift 1 c (shift 1 c' t) = shift 1 (c' + 1) (shift 1 c t) :=
-- END SPEC
  by
    -- WHY: the cutoffs grow under `lam`, so both (and `h`) must stay general in the IH.
    induction t generalizing c c' with
    | var n =>
      simp only [shift]
      by_cases h1 : n < c'
      · by_cases h2 : n < c
        · simp [shift, h1, h2, show n < c' + 1 by omega]
        · simp [shift, h1, h2, show n + 1 < c' + 1 by omega]
      · simp [shift, h1, show ¬ n < c by omega, show ¬ n + 1 < c by omega,
          show ¬ n + 1 < c' + 1 by omega]
    | lam t ih => simp [shift, ih (c + 1) (c' + 1) (by omega)]
    | app t u iht ihu => simp [shift, iht c c' h, ihu c c' h]

end M048

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. All three are inductions on `t` (R1). The interesting case is `var`: unfold `shift` and decide each
    `if` by comparing indices. `lam` is the IH at the bigger cutoff(s), so the cutoffs must be generalized.
H2. `induction t generalizing c with` (R2), and `generalizing c c'` for `shift_comm`, which also carries
    `h` into the IH (R13). `var` case: `split <;> rfl` for `shift_zero` (R4); `by_cases` on `n < c`
    (and on `n < c'`) elsewhere (R6), then `simp [shift, h, show … by omega]` (R7, R9).
    `lam`/`app`: `simp [shift, ih]` (R5), except in `shift_comm`, where the IH needs its premise (R14).
H3. `shift_shift`, `¬n < c`: `simp [shift, h, show ¬ n + d' < c by omega, Nat.add_assoc, Nat.add_comm d d']`.
    `shift_comm`: `lam t ih => simp [shift, ih (c + 1) (c' + 1) (by omega)]`; `app`: `iht c c' h`, `ihu c c' h`;
    `var n`: `simp only [shift]`, `by_cases h1 : n < c'`, inside `by_cases h2 : n < c`, then e.g.
    `simp [shift, h1, h2, show n < c' + 1 by omega]`.
-/
