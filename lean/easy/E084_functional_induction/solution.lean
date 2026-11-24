/- E084 | Functional induction | 2-3 min | fun_induction, fun_cases, with case names
GOAL
  Prove facts about recursive functions by induction that follows the function's own recursion:
  `fun_induction f x y` makes one goal per equation of `f`, with one induction hypothesis per recursive call.

BANNED: induction, grind, try?, exact?

GUIDE
  Entries R1–R8: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E084

-- BEGIN SPEC
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def pred2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => n
-- END SPEC

/- SKELETON · lt_ack
  1. Split along `ack`'s three equations, giving every argument; name each case's
     variables and IHs (`case1 n`, `case2 m ih`, `case3 m n ih1 ih2`):             R1, R2
  2. case1 (`ack 0 n = n + 1`): no IH, plain arithmetic:                           R7
  3. case2 (`ack (m + 1) 0 = ack m 1`): one IH, about `ack m 1`:                    R7
  4. case3 (two nested calls): two IHs, the inner call's first; chain them:        R3, R7
-/
-- BEGIN SPEC
theorem lt_ack (m n : Nat) : n < ack m n :=
-- END SPEC
  by
  fun_induction ack m n with
  | case1 n => omega
  | case2 m ih => omega
  | case3 m n ih1 ih2 => omega  -- WHY: `n < ack (m + 1) n < ack m (ack (m + 1) n)`, i.e. ih1 then ih2

/- SKELETON · fib_pos
  1. Split along `fib`'s three equations; `h : 0 < n` is carried into every case
     and becomes a premise of each IH:                                             R1, R4 (names: R2)
  2. case1: `h : 0 < 0` is impossible:                                             R6
  3. case2: a closed numeral goal:                                                 `decide` (TACTIC_STATES)
  4. case3: two IHs `0 < _ → 0 < fib _`; the one for `n + 1` always applies:       R8
-/
-- BEGIN SPEC
theorem fib_pos (n : Nat) (h : 0 < n) : 0 < fib n :=
-- END SPEC
  by
  fun_induction fib n with
  | case1 => omega         -- `h : 0 < 0` is absurd
  | case2 => decide
  | case3 n ih1 ih2 => omega  -- the IH for `fib (n + 1)` applies since `0 < n + 1`

/- SKELETON · le_pred2_add
  1. `pred2` is not recursive: split along its three equations, no IHs:           R5
  2. Each case is arithmetic on the pattern (`n✝.succ.succ` is `n✝ + 2`), the same
     tactic in every case (`<;>`):                                                 R7
-/
-- BEGIN SPEC
theorem le_pred2_add (n : Nat) : n ≤ pred2 n + 2 :=
-- END SPEC
  by fun_cases pred2 n <;> omega

end E084

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each proof follows one function's equations: `ack`, `fib` and `pred2` have three each. A recursive
    call on an equation's right-hand side is exactly where you need an induction hypothesis; `pred2`
    has none.
H2. `fun_induction ack m n` (R1–R3) and `fun_induction fib n` (R4: `h` is carried into every case),
    `fun_cases pred2 n` (R5). Every case is then linear arithmetic over the IHs: `omega` (R6–R8),
    or `decide` for `0 < 1`.
H3. `ack`, case3: the IHs `n < ack (m + 1) n` and `ack (m + 1) n < ack m (ack (m + 1) n)` chain by
    `omega`. `fib`, case3: the second IH `0 < n + 1 → 0 < fib (n + 1)` is enough for `omega`.
    In all three: `fun_induction ack m n <;> omega`, the same for `fib n`, `fun_cases pred2 n <;> omega`.
-/
