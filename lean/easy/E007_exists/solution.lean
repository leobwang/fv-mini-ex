/- E007 | Exists | 2-3 min | Exists, exists, obtain, anonymous constructor
GOAL
  Prove existential statements by giving witnesses, and use existential hypotheses.
BANNED: simp, simp_all, grind

GUIDE
  Entries R1–R10: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · exists_square
  1. Pick the witness: the number whose square is 144. Either build the pair at
     once, or fix the witness first and prove the body next:                   R1  (or R2 / R3)
  2. The body with the witness substituted is closed arithmetic on `Nat`:       R4
-/
-- BEGIN SPEC
theorem exists_square : ∃ n : Nat, n * n = 144 :=
-- END SPEC
  ⟨12, rfl⟩

/- SKELETON · exists_weaken
  1. Move the `∃` hypothesis into the context:                                  intro (E003)
  2. Take it apart into the witness and the two proofs; discard the one you
     do not need with `_`:                                                     R6
  3. Rebuild a pair: the same witness, the proof the goal asks for:             R1
-/
-- BEGIN SPEC
theorem exists_weaken (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x :=
-- END SPEC
  by
    intro h
    obtain ⟨x, _, hq⟩ := h
    exact ⟨x, hq⟩

/- SKELETON · exists_map
  1. Introduce and unpack the `∃` in one step:                                   R7
  2. Push the unpacked proof through `h` to get the `q`-fact:                    R8
  3. Pair it with the same witness:                                             R1
-/
-- BEGIN SPEC
theorem exists_map (p q : Nat → Prop) (h : ∀ x, p x → q x) : (∃ x, p x) → ∃ x, q x :=
-- END SPEC
  by
    rintro ⟨x, hx⟩
    exact ⟨x, h x hx⟩

/- SKELETON · exists_shift
  1. Unpack `h` into a number and a proof about its successor:                  R5
  2. Choose the witness for `m`: read the TYPE of the proof you now hold;
     the witness is an expression in the unpacked name, not the name itself.
  3. Give the witness and two proofs flat, `⟨witness, proof₁, proof₂⟩`:        R10
       proof₁ : witness ≠ 0                                                    R9
       proof₂ : already in the context
-/
-- BEGIN SPEC
theorem exists_shift (p : Nat → Prop) (h : ∃ n, p (n + 1)) : ∃ m, m ≠ 0 ∧ p m :=
-- END SPEC
  by
    obtain ⟨n, hn⟩ := h
    exact ⟨n + 1, Nat.succ_ne_zero n, hn⟩

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. To prove `∃`, give the witness first and then the proof (`⟨w, hw⟩`); to use an `∃`
    hypothesis, unpack it with `obtain ⟨x, hx⟩ := h` (or `rintro ⟨x, hx⟩` straight from the goal).
H2. `exists_square`: the witness is 12 and the body is closed arithmetic. `exists_weaken`: `intro`,
    then one flat `obtain` that keeps only the `q`-proof. `exists_map`: `rintro`, then apply `h` to the
    witness and its proof. `exists_shift`: the proof you unpack is about `n + 1`, so that is the witness.
H3. `exists_square`: `⟨12, rfl⟩`. `exists_map`: `exact ⟨x, h x hx⟩`. `exists_shift`:
    `obtain ⟨n, hn⟩ := h` then `exact ⟨n + 1, Nat.succ_ne_zero n, hn⟩`.
-/
