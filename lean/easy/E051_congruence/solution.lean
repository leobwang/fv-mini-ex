/- E051 | Congruence | 2-3 min | congrArg, congrFun, congr
GOAL
  Push equalities through functions (`congrArg`), evaluate a function equality at a point
  (`congrFun`), and split `f a c = f b d` into argument equalities (`congr`).

BANNED: rw, subst, simp, simpa, simp_all, grind, cases, rcases, obtain, match, ▸, Eq.subst, Eq.mpr, Eq.mp, Eq.rec, Eq.ndrec, Eq.recOn, solve_by_elim, exact?, apply?, try?

GUIDE
  Entries R1–R7: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E051

/- SKELETON · congr_arg_ex
  1. The two sides differ only where `a` becomes `b`; write the function
     "everything around that spot" as a lambda:                            R2
  2. Apply `congrArg` to that lambda and `h` (one term, no `by`):          R1
-/
-- BEGIN SPEC
theorem congr_arg_ex (f g : Nat → Nat) (a b : Nat) (h : a = b) : f (g a) = f (g b) :=
-- END SPEC
  congrArg (fun x => f (g x)) h

/- SKELETON · congr_fun_ex
  1. Evaluate `h : f = g` at `x`, giving `f x = g x`:                       R4
  2. Push that equation through "add one", written with `·`:               R3 → R1
     (step 1 is the argument of step 2: one term)
-/
-- BEGIN SPEC
theorem congr_fun_ex (f g : Nat → Nat) (h : f = g) (x : Nat) : f x + 1 = g x + 1 :=
-- END SPEC
  congrArg (· + 1) (congrFun h x)

/- SKELETON · succ_ne_id
  1. `≠` is a function into `False`: assume the two functions are equal:    R5
  2. Evaluate that equation at `0`; it reads `0 + 1 = 0` after computing:   R4
  3. Feed it to the lemma that says `n.succ ≠ n` (with `n = 0`):            R6
-/
-- BEGIN SPEC
theorem succ_ne_id : (fun n : Nat => n + 1) ≠ (fun n => n) :=
-- END SPEC
  fun h => Nat.succ_ne_self 0 (congrFun h 0)

/- SKELETON · congr_two
  1. Split the equation into one equation per argument; both new goals are
     closed by `h1`, `h2` automatically:                                   R7
-/
-- BEGIN SPEC
theorem congr_two (f : Nat → Nat → Nat) (a b c d : Nat) (h1 : a = b) (h2 : c = d) :
    f a c = f b d :=
-- END SPEC
  by congr

end E051

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every part but the last is one term. `congrArg F h : F a = F b` needs the function `F` around
    the part that changes (R1, R2); `congrFun h x : f x = g x` evaluates a function equality (R4).
H2. `congr_arg_ex`: `F` is a lambda covering both `f` and `g`. `congr_fun_ex`: first `congrFun h x`,
    then `congrArg` with `(· + 1)` (R3). `succ_ne_id`: `fun h => …` assumes the functions are equal
    (R5); evaluate `h` at `0` and apply `Nat.succ_ne_self 0` to it (R6). `congr_two`: `by congr` (R7).
H3. `congr_arg_ex`: `congrArg (fun x => f (g x)) h`; `congr_fun_ex`: `congrArg (· + 1) (congrFun h x)`;
    `succ_ne_id`: `fun h => Nat.succ_ne_self 0 (congrFun h 0)`; `congr_two`: `by congr`.
-/
