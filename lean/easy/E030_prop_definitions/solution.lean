/- E030 | Prop-valued definitions | 3 min | def Prop, unfold, show
GOAL
  Prove facts about predicates defined with `def … : Prop`.

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

-- BEGIN SPEC
def Divides (d n : Nat) : Prop := ∃ k, n = d * k

def UpperBound (b : Nat) (xs : List Nat) : Prop := ∀ x ∈ xs, x ≤ b
-- END SPEC

/- SKELETON · divides_refl
  1. (optional) See the body: the goal is `∃ k, n = n * k`:                      R1 or R2
  2. Give the witness `1` and a proof of `n = n * 1`; the anonymous constructor
     sees through `Divides`, so one term does it:                                  R3
  3. The equation is `n * 1 = n` turned around:                                    R4 → R5
-/
-- BEGIN SPEC
theorem divides_refl (n : Nat) : Divides n n :=
-- END SPEC
  ⟨1, (Nat.mul_one n).symm⟩

/- SKELETON · divides_trans
  1. Unpack `h1`, substituting `b` (the `rfl` pattern):                            R6 → R7
  2. Unpack `h2` the same way, substituting `c`:                                   R7
     The goal is now `Divides a (a * k * m)`.
  3. Witness `k * m`; the equation `a * k * m = a * (k * m)`:                      R3 with R8
-/
-- BEGIN SPEC
theorem divides_trans (a b c : Nat) (h1 : Divides a b) (h2 : Divides b c) : Divides a c :=
-- END SPEC
  by
    obtain ⟨k, rfl⟩ := h1
    obtain ⟨m, rfl⟩ := h2
    exact ⟨k * m, Nat.mul_assoc a k m⟩

/- SKELETON · upperBound_cons
  1. Expose both bounded `∀`s, in `h` and in the goal:                             R9
  2. Take an element `y` and `hy : y ∈ x :: xs`:                                   R10
  3. Membership in a cons → an `∨`:                                                R11
  4. Split it, substituting the equation on the left:                              R12
       left case:  `y` and `x` are now one variable; `hx` is the goal             exact hx
       right case: apply `h` to `y` and `hy`                                       R13
-/
-- BEGIN SPEC
theorem upperBound_cons (b x : Nat) (xs : List Nat) (hx : x ≤ b) (h : UpperBound b xs) :
    UpperBound b (x :: xs) :=
-- END SPEC
  by
    unfold UpperBound at *
    intro y hy
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact h y hy

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `Divides a b` is an `∃` and `UpperBound b xs` is a bounded `∀`, hidden behind a name. Anonymous
    constructors, `obtain`, `rcases` and `intro` see through the name; `rw`, `simp` and `omega` need
    `unfold` first.
H2. `divides_refl`: witness `1`. `divides_trans`: unpack both hypotheses with the `rfl` pattern so `b` and
    `c` become products, then the witness is a product. `upperBound_cons`: unfold, introduce `y`, split
    `y ∈ x :: xs` into `y = x ∨ y ∈ xs`.
H3. `divides_refl`: the equation is `(Nat.mul_one n).symm : n = n * 1`. `divides_trans`: finish with
    `exact ⟨k * m, Nat.mul_assoc a k m⟩`. `upperBound_cons`:
    `unfold UpperBound at *; intro y hy; rw [List.mem_cons] at hy; rcases hy with rfl | hy`.
-/
