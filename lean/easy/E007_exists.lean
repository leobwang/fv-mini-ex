/- E007 | Exists | 2-3 min | Exists, exists, obtain, anonymous constructor
GOAL
  Prove existential statements by giving witnesses, and use existential hypotheses.

REFERENCE
  example : ∃ n : Nat, n + 2 = 5 := ⟨3, rfl⟩          -- ⟨witness, proof⟩
  example : ∃ n : Nat, n + 2 = 5 := by exists 3        -- `exists w` then tries `rfl`/`trivial`
  example (p : Nat → Prop) (h : ∃ n, p n ∧ n > 0) : ∃ n, p n := by
    obtain ⟨n, hpn, _⟩ := h; exact ⟨n, hpn⟩           -- unpack the witness and its proof
  #check Nat.succ_ne_zero   -- (n : Nat) : n + 1 ≠ 0
BANNED: simp, simp_all, grind
-/

-- BEGIN SPEC
theorem exists_square : ∃ n : Nat, n * n = 144 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem exists_weaken (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem exists_map (p q : Nat → Prop) (h : ∀ x, p x → q x) : (∃ x, p x) → ∃ x, q x :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem exists_shift (p : Nat → Prop) (h : ∃ n, p (n + 1)) : ∃ m, m ≠ 0 ∧ p m :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. To prove `∃`, name the witness; to use `∃`, unpack it with `obtain`.
H2. `exists_shift`: the witness for `m` is not `n` itself.
H3. `obtain ⟨n, hn⟩ := h` then `exact ⟨n + 1, Nat.succ_ne_zero n, hn⟩`.
-/
