/- E021 | have, show, suffices | 3 min | have, show, suffices
GOAL
  Structure proofs with intermediate facts (`have`), a restated goal (`show`), and backward steps (`suffices`).

REFERENCE
  example (f : Nat → Nat) (h : ∀ n, f n ≤ f (n + 1)) : f 0 ≤ f 2 := by
    have h0 : f 0 ≤ f 1 := h 0    -- state the type: plain `h 0` gives `f 0 ≤ f (0 + 1)`
    have h1 : f 1 ≤ f 2 := h 1
    omega
  example (n : Nat) (h : 2 * n = 6) : n = 3 := by
    suffices hs : n + n = 6 by omega   -- prove the goal from `hs`, then prove `hs`
    omega
  example (xs : List Nat) : xs ++ [] = xs := by show xs ++ [] = xs; simp  -- `show` restates
-/

-- BEGIN SPEC
theorem have_chain (f : Nat → Nat) (h : ∀ n, f n < f (n + 1)) : f 0 + 3 ≤ f 3 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem suffices_mono (f : Nat → Nat) (mono : ∀ a b, a ≤ b → f a ≤ f b) (n : Nat) :
    f n ≤ f (n * 2) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem show_ne (xs : List Nat) (h : xs.length = 3) : xs ≠ [] :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `have_chain`: instantiate `h` at 0, 1 and 2 (with the type written out), then it is linear arithmetic.
H2. `suffices_mono`: the goal is `mono` applied to an inequality that `omega` proves.
H3. `suffices hs : n ≤ n * 2 by exact mono n (n * 2) hs`, then `omega`. `show_ne`: `intro hx; rw [hx] at h; simp at h`.
-/
