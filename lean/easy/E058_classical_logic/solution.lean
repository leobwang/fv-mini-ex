/- E058 | Classical logic | 2-3 min | Classical.em, Classical.byContradiction, by_cases, absurd
GOAL
  Prove four tautologies that need the excluded middle (`P ∨ ¬P` for every `P`): double negation,
  Peirce's law, contraposition, and De Morgan for `∧`. Do the case splits yourself.
BANNED: Classical.not_not, Decidable.of_not_not, Decidable.peirce, peirce', Decidable.not_imp_not, Decidable.not_imp_symm, Decidable.not_imp_comm, Classical.not_and_iff_not_or_not, Decidable.not_and_iff_not_or_not', Decidable.not_and_iff_or_not, simp, simp_all, simpa, grind, exact?, try?

GUIDE
  Entries R1–R11: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E058

/- SKELETON · dne
  1. Assume `¬P` and aim for `False`:                                             R1
  2. `h : ¬¬P` is a function `¬P → False`: apply it:                              R2
     (R1's lemma as a term takes exactly such a function: one term does both steps.)
-/
-- BEGIN SPEC
theorem dne (P : Prop) (h : ¬¬P) : P :=
-- END SPEC
  Classical.byContradiction h

/- SKELETON · peirce
  1. Introduce `h : (P → Q) → P`:                                                 R3
  2. Split on `P`:                                                                R4
  3. Case `hp : P`: the goal is `P`:                                              exact hp
  4. Case `hp : ¬P`: `h` still yields `P` from a function `P → Q`:                R5
       goal `P → Q`: introduce `hp' : P`                                          R3
       goal `Q`: `hp'` and `hp` contradict                                        R6
     (Step 4 as one term: `exact h (fun … => …)`.)
-/
-- BEGIN SPEC
theorem peirce (P Q : Prop) : ((P → Q) → P) → P :=
-- END SPEC
  by
    intro h
    by_cases hp : P
    · exact hp
    · exact h (fun hp' => absurd hp' hp)

/- SKELETON · contrapos
  1. Introduce `hp : P`:                                                          R3
  2. Split on `Q ∨ ¬Q`:                                                           R7
  3. Case `hq : Q`:                                                               exact hq
  4. Case `hnq : ¬Q`: `h hnq : ¬P` contradicts `hp`:                              R6
-/
-- BEGIN SPEC
theorem contrapos (P Q : Prop) (h : ¬Q → ¬P) : P → Q :=
-- END SPEC
  by
    intro hp
    rcases Classical.em Q with hq | hnq
    · exact hq
    · exact absurd hp (h hnq)

/- SKELETON · not_and_split
  1. Split on `P`:                                                                R4
  2. Case `hp : P`: prove the right side `¬Q`:                                    R8
       introduce `hq : Q`, goal `False`                                           R9
       `h` refutes the pair `⟨hp, hq⟩`                                             R10
  3. Case `hp : ¬P`: prove the left side:                                         R11, exact hp
-/
-- BEGIN SPEC
theorem not_and_split (P Q : Prop) (h : ¬(P ∧ Q)) : ¬P ∨ ¬Q :=
-- END SPEC
  by
    by_cases hp : P
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp

end E058

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `¬P` is `P → False`, so `h : ¬¬P` is a function that turns a proof of `¬P` into `False` (R2, R9).
    Only `dne` needs proof by contradiction (R1); the other three are case splits (R4 or R7).
H2. `dne`: compare `h` with the argument `Classical.byContradiction` expects. `peirce`, `not_and_split`: split
    on `P` with `by_cases`; `contrapos`: split on `Q` with `Classical.em`. In the "wrong" branch close the goal
    with `absurd` (R6) or by applying `h` (R5, R10).
H3. `dne`: `h : ¬¬P` has type `¬P → False`, exactly the argument `Classical.byContradiction` takes.
    `peirce`, case `hp : ¬P`: `exact h (fun hp' => absurd hp' hp)`. `contrapos`, case `hnq : ¬Q`:
    `exact absurd hp (h hnq)`. `not_and_split`, case `hp : P`: after `right; intro hq`, `exact h ⟨hp, hq⟩`.
-/
