/- Guide for M012 (Depth-indexed stack code).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` in an entry is only there to finish the example; it shows what the goal became.
Part W: worked combinations on objects that are NOT the exercise's (a Boolean stack machine).
Assumed: Lean basics (E001–E033). Everything here is core Lean: no imports.
-/

namespace M012Guide

/-! ## The guide's own objects: a Boolean stack machine (not the exercise's)
`Stack n` is a stack of `n` Booleans; `Op n m` turns depth `n` into depth `m`; `Prog n m` chains ops
whose depths match. The depth lives in the type, so `Op.exec` has no error case. -/

inductive Stack : Nat → Type where
  | bot : Stack 0
  | top {n : Nat} (b : Bool) (rest : Stack n) : Stack (n + 1)

inductive Op : Nat → Nat → Type where
  | lit {n : Nat} (b : Bool) : Op n (n + 1)
  | neg {n : Nat} : Op (n + 1) (n + 1)
  | both {n : Nat} : Op (n + 2) (n + 1)

inductive Prog : Nat → Nat → Type where
  | stop {n : Nat} : Prog n n
  | seq {n m k : Nat} (o : Op n m) (p : Prog m k) : Prog n k

/-- `both` only accepts a stack whose type says it has two elements on top. -/
def Op.exec : {n m : Nat} → Op n m → Stack n → Stack m
  | _, _, .lit b, st => .top b st
  | _, _, .neg, .top b st => .top (!b) st
  | _, _, .both, .top y (.top x st) => .top (x && y) st

def Prog.exec : {n m : Nat} → Prog n m → Stack n → Stack m
  | _, _, .stop, st => st
  | _, _, .seq o p, st => p.exec (o.exec st)

def Prog.size : {n m : Nat} → Prog n m → Nat
  | _, _, .stop => 0
  | _, _, .seq _ p => p.size + 1

def Prog.cat : {n m k : Nat} → Prog n m → Prog m k → Prog n k
  | _, _, _, .stop, q => q
  | _, _, _, .seq o p, q => .seq o (p.cat q)

/-- Peephole pass with overlapping arms: `lit x; lit y; both` becomes `lit (x && y)`.
The second arm also matches everything the first one matches; the first arm wins. -/
def simpl : {n m : Nat} → Prog n m → Prog n m
  | _, _, .seq (.lit x) (.seq (.lit y) (.seq .both p)) => .seq (.lit (x && y)) (simpl p)
  | _, _, .seq o p => .seq o (simpl p)
  | _, _, .stop => .stop

/-! # Part R · Reference entries -/

/-! ## Induction on an indexed family -/

/-! ### R1. `induction p with | stop => ?_ | seq o p ih => ?_` · goal list: one goal per constructor
`p : Prog n m` has indices `n m`. Lean also generalizes every hypothesis whose type mentions them
(here `s : Stack n`), so `ih` holds for every stack. `?_` leaves each case open as a named goal. -/
example (P : {n m : Nat} → Prog n m → Stack n → Prop)
    (h0 : ∀ {n : Nat} (s : Stack n), P Prog.stop s)
    (h1 : ∀ {n m k : Nat} (o : Op n m) (p : Prog m k) (s : Stack n),
      (∀ (s : Stack m), P p s) → P (Prog.seq o p) s)
    {n m : Nat} (p : Prog n m) (s : Stack n) : P p s := by
  induction p with
    | stop => ?_
    | seq o p ih => ?_
  · exact h0 s
  · exact h1 o p s ih

/-! ### R2. `simp only [f]` on a constructor · goal: one defining equation of `f` fires
A function defined by pattern matching unfolds only where its argument is a constructor
(`Prog.seq o p`), never on a variable `p`. When both sides then agree, `rfl` would also close it. -/
example {n m k : Nat} (o : Op n m) (p : Prog m k) (P : Nat → Prop) (h : P (p.size + 1)) :
    P (Prog.seq o p).size := by
  simp only [Prog.size]
  exact h

/-! ### R3. `simp only [ih]` with `ih : ∀ x, f x = g x` · goal: `f t` → `g t`, then closed by `rfl`
`simp` instantiates the `∀` by itself (`x := t s`), wherever `f _` occurs. -/
example {n m : Nat} (f g : Stack n → Stack m) (t : Stack n → Stack n)
    (ih : ∀ (s : Stack n), f s = g s) (s : Stack n) : f (t s) = g (t s) := by
  simp only [ih]

/-! ### R4. `simp only [Op.exec]` on a forced stack shape · goal: a dependent match fires
`Op.both` matches `.top y (.top x st)`; the equation fires once the stack is written with two `top`s
(as it is after two pushes). -/
example {n : Nat} (x y : Bool) (st : Stack n) (P : Stack (n + 1) → Prop) (h : P (.top (x && y) st)) :
    P (Op.both.exec (.top y (.top x st))) := by
  simp only [Op.exec]
  exact h

/-! ## Induction that follows a function -/

/-! ### R5. `fun_induction simpl p` · goal list: one goal per arm of `simpl`, IH per recursive call
The catch-all arm also gets hypotheses saying the earlier arms did not match (`≍` is `HEq`). -/
example (P : {n m : Nat} → Prog n m → Prop) (h : ∀ {n m : Nat} (q : Prog n m), P q)
    {n m : Nat} (p : Prog n m) : P (simpl p) := by
  fun_induction simpl p
  all_goals exact h _

/-! ### R6. `simp_all` · goal and context simplified with each other; uses unnamed hypotheses
After `intros` (or `fun_induction`) the hypotheses are inaccessible (`a✝`); `simp_all` still uses them.
Pass definitions to unfold as in `simp_all [Prog.size]`. -/
example (f g : Nat → Nat) (P : Nat → Prop) : (∀ x, f x = g x) → P (g 3) → P (f 3) := by
  intros
  simp_all

/-! ### R7. `omega` · closes linear arithmetic over `Nat`/`Int`, using the hypotheses -/
example (x y : Nat) (h : x ≤ y) : x ≤ y + 2 := by
  omega

/-! ## Induction at every depth -/

/-! ### R8. `induction l generalizing n` · context: the IH quantifies over `n` (and what depends on it)
Without `generalizing n` the IH holds only at the goal's own `n` (second example). -/
example (P : {n : Nat} → List Bool → Stack n → Prop)
    (h0 : ∀ {n : Nat} (s : Stack n), P [] s)
    (h1 : ∀ {n : Nat} (b : Bool) (bs : List Bool) (s : Stack n),
      (∀ {n : Nat} (s : Stack n), P bs s) → P (b :: bs) s)
    {n : Nat} (l : List Bool) (s : Stack n) : P l s := by
  induction l generalizing n with
    | nil => ?_
    | cons b bs ih => ?_
  · exact h0 s
  · exact h1 b bs s ih

example (P : {n : Nat} → List Bool → Stack n → Prop) (h : ∀ {n : Nat} (l : List Bool) (s : Stack n), P l s)
    {n : Nat} (l : List Bool) (s : Stack n) : P l s := by
  induction l with
    | nil => ?_
    | cons b bs ih => ?_
  · exact h [] s
  · exact h (b :: bs) s

/-! ### R9. `rw [ih]` with `ih : ∀ {n} (s : Stack n), f s = g s` · goal: the IH used at depth `n + 1`
The implicit `n` is found by unification with the term in the goal. -/
example {n : Nat} (f g : {n : Nat} → Stack n → Stack (n + 1))
    (ih : ∀ {n : Nat} (s : Stack n), f s = g s) (s : Stack (n + 1)) (P : Stack (n + 2) → Prop)
    (h : P (g s)) : P (f s) := by
  rw [ih]
  exact h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. Structural induction on `Prog`, unfold, use the IH: R1 → R2 → R3 → R7 -/
example {n m k : Nat} (p : Prog n m) (q : Prog m k) : (p.cat q).size = p.size + q.size := by
  induction p with
    | stop => ?_
    | seq o p ih => ?_
  · simp only [Prog.cat, Prog.size]
    omega
  · simp only [Prog.cat, Prog.size]
    simp only [ih]
    omega

/-! ### W2. Follow the peephole pass: R5, then R6 and R7 in every arm -/
example {n m : Nat} (p : Prog n m) : (simpl p).size ≤ p.size := by
  fun_induction simpl p
  all_goals simp_all [Prog.size]
  all_goals omega

/-! ### W3. Run a concrete program: R2 for `Prog.exec`, then R4 for `Op.exec` -/
example {n : Nat} (x y : Bool) (st : Stack n) :
    (Prog.seq (.lit x) (.seq (.lit y) (.seq .both .stop))).exec st = .top (x && y) st := by
  simp only [Prog.exec]
  simp only [Op.exec]

end M012Guide
