/- E046 | Term-mode sugar | 2-3 min | term mode, dot notation, anonymous hypothesis, ▸, let pattern, show from
GOAL
  Write each proof as a term (no `by`), using the shorthand that tactic proofs usually hide:
  dot notation, `‹P›`, `h ▸ e`, `let ⟨..⟩ := h`, and `have` / `show … from` inside a term.

REFERENCE
  example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := h.mpr hq  -- dot notation: `h.mpr` = `Iff.mpr h`
  #check @Or.elim     -- (h : a ∨ b) → (a → c) → (b → c) → c      (so `h.elim f g`)
  #check @Iff.trans   -- (a ↔ b) → (b ↔ c) → (a ↔ c)               (so `h1.trans h2`)
  example (P : Prop) (hp : P) : P ∧ P := ⟨‹P›, ‹P›⟩   -- `‹T›` = "the hypothesis of type T"
  example (a b : Nat) (h : a = b) (hb : 0 < b) : 0 < a := h ▸ hb  -- rewrite a term's type by h
  example (h : ∃ n : Nat, n > 3) : ∃ n : Nat, n > 2 :=
    let ⟨n, hn⟩ := h; ⟨n, Nat.lt_of_succ_lt hn⟩    -- destructure inside a term
  example (a : Nat) (h : 1 ≤ a) : 0 < a := have h' : 0 < a := h; show 0 < a from h'
  #check @Nat.le_trans      -- n ≤ m → m ≤ k → n ≤ k     (and Nat.le_succ_of_le : n ≤ m → n ≤ m + 1)
BANNED: by
NOTE: `by` is banned on purpose. Each theorem targets one shorthand: dot notation (or_mp, iff_chain), `‹P›`, `▸`, `let`, `have`/`show`.
-/

namespace E046

-- BEGIN SPEC
theorem or_mp (P Q R : Prop) (h : P ∨ Q) (hpr : P ↔ R) (hqr : Q → R) : R :=
-- END SPEC
  h.elim hpr.mp hqr

-- BEGIN SPEC
theorem anon_hyp (P Q R : Prop) (hp : P) (hq : Q) (h : P → Q → R) : R :=
-- END SPEC
  h ‹P› ‹Q›

-- BEGIN SPEC
theorem iff_chain (P Q R : Prop) (h1 : P ↔ Q) (h2 : Q ↔ R) : P ↔ R :=
-- END SPEC
  h1.trans h2

-- BEGIN SPEC
theorem subst_term (n : Nat) (h : n = 2) : n + n = 4 :=
-- END SPEC
  h ▸ rfl

-- BEGIN SPEC
theorem exists_let (p q : Nat → Prop) (h : ∃ n, p n ∧ q n) : ∃ n, q n :=
-- END SPEC
  let ⟨n, _, hq⟩ := h
  ⟨n, hq⟩

-- BEGIN SPEC
theorem have_show (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c + 1 :=
-- END SPEC
  have hac : a ≤ c := Nat.le_trans h1 h2
  show a ≤ c + 1 from Nat.le_succ_of_le hac

end E046

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Dot notation looks at the head of the type: `h : P ∨ Q` gives `h.elim`, `hpr : P ↔ R` gives
    `hpr.mp`, `h1 : P ↔ Q` gives `h1.trans`.
H2. `or_mp`: one function per case of the `∨`. `subst_term`: `2 + 2 = 4` holds by `rfl`; rewrite it
    with `h`. `exists_let`: take the witness and the `q n` part apart, then build a new pair.
H3. `or_mp`: `h.elim hpr.mp hqr`; `subst_term`: `h ▸ rfl`;
    `have_show`: `have hac : a ≤ c := Nat.le_trans h1 h2` on one line, then `show a ≤ c + 1 from …`.
-/
