/- M27 | GCD by Euclid | 10-15 min | well-founded recursion, fun_induction, divisibility [R13]
GOAL
  Prove Euclid's algorithm computes a greatest common divisor: it divides both inputs, and
  every common divisor divides it.

REFERENCE
  #check Nat.dvd_mod_iff   -- k ∣ n → (k ∣ m % n ↔ k ∣ m)
  example (a : Nat) : a ∣ a ∧ a ∣ 0 := ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
  -- fun_induction euclid a b : case1 (b = 0, already substituted) and case2 (b ≠ 0, with IH
  -- for `euclid b (a % b)`). Hypotheses mentioning a, b are generalised automatically.
  example (p q : Prop) (h : p ∧ q) : q := h.2
BANNED: Nat.gcd, Nat.gcd_rec
-/

namespace M27

-- BEGIN SPEC
def euclid (a b : Nat) : Nat := if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)
-- END SPEC

-- BEGIN SPEC
theorem euclid_dvd (a b : Nat) : euclid a b ∣ a ∧ euclid a b ∣ b :=
-- END SPEC
  by
    fun_induction euclid a b with
    | case1 a => exact ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
    | case2 a b h ih => exact ⟨(Nat.dvd_mod_iff ih.1).mp ih.2, ih.1⟩

-- BEGIN SPEC
theorem dvd_euclid (a b d : Nat) (ha : d ∣ a) (hb : d ∣ b) : d ∣ euclid a b :=
-- END SPEC
  by
    fun_induction euclid a b with
    | case1 a => exact ha
    | case2 a b h ih => exact ih hb ((Nat.dvd_mod_iff hb).mpr ha)

end M27

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Follow the recursion: `euclid a b = euclid b (a % b)` when `b ≠ 0`.
H2. Key fact: if `d ∣ b`, then `d ∣ a % b ↔ d ∣ a` (`Nat.dvd_mod_iff`).
H3. `euclid_dvd` case2: `⟨(Nat.dvd_mod_iff ih.1).mp ih.2, ih.1⟩`; `dvd_euclid` case2: `ih hb ((Nat.dvd_mod_iff hb).mpr ha)`.
-/
