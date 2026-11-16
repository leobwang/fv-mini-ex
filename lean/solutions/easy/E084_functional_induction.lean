/- E084 | Functional induction | 2-3 min | fun_induction, fun_cases, with case names
GOAL
  Prove facts about recursive functions by induction that follows the function's own recursion:
  `fun_induction f x y` makes one goal per equation of `f`, with one induction hypothesis per recursive call.

REFERENCE
  def half : Nat → Nat | 0 => 0 | 1 => 0 | n + 2 => half n + 1
  #check @half.induct   -- motive 0 → motive 1 → (∀ n, motive n → motive (n + 2)) → ∀ a, motive a
  example (n : Nat) : half n ≤ n := by fun_induction half n <;> omega
    -- in each goal `half n` is already replaced by that equation's right-hand side
  example (n : Nat) : half n ≤ n := by fun_induction half n with | case1 => omega | case2 => omega | case3 n ih => omega
    -- name the cases `case1, case2, …` in equation order; `ih : half n ≤ n` in case3
  `fun_cases f x` makes the same split without induction hypotheses (works for non-recursive `f` too)
  A hypothesis about `n` (such as `h : 0 < n`) is carried into every case and into each IH.
BANNED: induction, grind, try?, exact?
NOTE: plain `induction` is banned to steer you to `fun_induction`/`fun_cases` (a recursive theorem as in E048
  also works, but is longer).
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

-- BEGIN SPEC
theorem lt_ack (m n : Nat) : n < ack m n :=
-- END SPEC
  by
  fun_induction ack m n with
  | case1 n => omega
  | case2 m ih => omega
  | case3 m n ih1 ih2 => omega  -- WHY: `n < ack (m + 1) n < ack m (ack (m + 1) n)`, i.e. ih1 then ih2

-- BEGIN SPEC
theorem fib_pos (n : Nat) (h : 0 < n) : 0 < fib n :=
-- END SPEC
  by
  fun_induction fib n with
  | case1 => omega         -- `h : 0 < 0` is absurd
  | case2 => decide
  | case3 n ih1 ih2 => omega  -- the IH for `fib (n + 1)` applies since `0 < n + 1`

-- BEGIN SPEC
theorem le_pred2_add (n : Nat) : n ≤ pred2 n + 2 :=
-- END SPEC
  by fun_cases pred2 n <;> omega

end E084

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `lt_ack` by plain induction needs an induction on `n` nested inside one on `m`; `fun_induction ack m n`
    gives exactly the three cases of `ack`, and in the third one IHs for both nested calls.
H2. In `ack`'s third case, `ih1 : n < ack (m + 1) n` and `ih2 : ack (m + 1) n < ack m (ack (m + 1) n)`;
    chain them. In `fib`'s third case the IH for `fib (n + 1)` gives positivity. `pred2` is not recursive,
    so use `fun_cases` there.
H3. `fun_induction ack m n <;> omega`, the same shape for `fib n`, and `fun_cases pred2 n <;> omega`.
-/
