/- E046 | Term-mode sugar | 2-3 min | term mode, dot notation, anonymous hypothesis, ▸, let pattern, show from
GOAL
  Write each proof as a term (no `by`), using the shorthand that tactic proofs usually hide:
  dot notation, `‹P›`, `h ▸ e`, `let ⟨..⟩ := h`, and `have` / `show … from` inside a term.

BANNED: by

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E046

/- SKELETON · or_mp
  1. Split on `h : P ∨ Q` with dot notation; its two arguments are
     functions `P → R` and `Q → R`:                                        R1
  2. First argument: the `↔` read left to right is already a function
     `P → R` (no `fun` needed):                                            R2
  3. Second argument: a hypothesis already has type `Q → R`.
-/
-- BEGIN SPEC
theorem or_mp (P Q R : Prop) (h : P ∨ Q) (hpr : P ↔ R) (hqr : Q → R) : R :=
-- END SPEC
  h.elim hpr.mp hqr

/- SKELETON · anon_hyp
  1. Apply `h` to two arguments, a proof of `P` and a proof of `Q`.
  2. Name each argument by its type, not by its name:                     R3, R3
-/
-- BEGIN SPEC
theorem anon_hyp (P Q R : Prop) (hp : P) (hq : Q) (h : P → Q → R) : R :=
-- END SPEC
  h ‹P› ‹Q›

/- SKELETON · iff_chain
  1. Chain the two `↔` with dot notation on the first one:                R4
-/
-- BEGIN SPEC
theorem iff_chain (P Q R : Prop) (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R :=
-- END SPEC
  h1.trans h2

/- SKELETON · subst_term
  1. Outer term: rewrite the expected type along `h`, so `n` becomes `2`;
     its argument must then prove `2 + 2 = 4`:                             R6
  2. That argument: `2 + 2 = 4` computes, so it holds by:                  R5
-/
-- BEGIN SPEC
theorem subst_term (n : Nat) (h : n = 2) : n + n = 4 :=
-- END SPEC
  h ▸ rfl

/- SKELETON · exists_let
  1. Take `h` apart into the witness, the `p n` part (unused: `_`) and the
     `q n` part, in one nested pattern:                                    R7
  2. Build the new `∃` from the same witness and the `q n` part:          R8
-/
-- BEGIN SPEC
theorem exists_let (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, q n :=
-- END SPEC
  let ⟨n, _, hq⟩ := h
  ⟨n, hq⟩

/- SKELETON · have_show
  1. Name the intermediate fact `hac : a ≤ c`, proved from `h1` and `h2`:   R9, R10
  2. State the final type, then prove it from `hac` one step up:            R11, R12
-/
-- BEGIN SPEC
theorem have_show (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c + 1 :=
-- END SPEC
  have hac : a ≤ c := Nat.le_trans h1 h2
  show a ≤ c + 1 from Nat.le_succ_of_le hac

end E046

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Every proof is one term. Dot notation looks at the head of a hypothesis's type: `h : P ∨ Q`
    gives `h.elim` (R1), `hpr : P ↔ R` gives `hpr.mp` (R2), `h1 : P ↔ Q` gives `h1.trans` (R4).
    To see what a spot expects, write `_` there and read the error (then remove the `_`).
H2. `or_mp`: one function per case of the `∨`, and `hpr.mp` already is one. `anon_hyp`: `h` takes
    two arguments; name each by its type (R3). `subst_term`: `2 + 2 = 4` holds by `rfl`; rewrite it
    with `h` (R6). `exists_let`: take the witness and the `q n` part apart with `let` (R7), then
    build a new pair (R8). `have_show`: prove `a ≤ c` first (R10), then go one step up (R12).
H3. `or_mp`: `h.elim hpr.mp hqr`; `subst_term`: `h ▸ rfl`;
    `have_show`: `have hac : a ≤ c := Nat.le_trans h1 h2` on one line, then `show a ≤ c + 1 from …`.
-/
