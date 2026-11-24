/- M029 | GCD by Euclid | 10-15 min | well-founded recursion, fun_induction, divisibility [R13]
GOAL
  Prove Euclid's algorithm computes a greatest common divisor: it divides both inputs, and
  every common divisor divides it.

BANNED: Nat.gcd, Nat.gcd_rec

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M029

-- BEGIN SPEC
def euclid (a b : Nat) : Nat := if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)
-- END SPEC

/- SKELETON · euclid_dvd
  1. `fun_induction euclid a b with`, naming the arms `case1 a` and `case2 a b h ih`:
       two cases, `b = 0` (case1) and `b ≠ 0` (case2)                                       R1
  2. case1 `a ∣ a ∧ a ∣ 0`: build the pair from two library facts                            R2, R4, R5
  3. case2, with `ih : euclid b (a % b) ∣ b ∧ euclid b (a % b) ∣ a % b`:
       build the pair                                                                         R2
       second half `… ∣ b`: one half of `ih`                                                  R3
       first half `… ∣ a`: from `… ∣ a % b`, with `hk` the other half of `ih`                 R3 → R6
-/
-- BEGIN SPEC
theorem euclid_dvd (a b : Nat) : euclid a b ∣ a ∧ euclid a b ∣ b :=
-- END SPEC
  by
    fun_induction euclid a b with
    | case1 a => exact ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
    | case2 a b h ih => exact ⟨(Nat.dvd_mod_iff ih.1).mp ih.2, ih.1⟩

/- SKELETON · dvd_euclid
  1. `fun_induction euclid a b with` (arms as in euclid_dvd), leaving `ha hb` in context
       (no revert): in case2 the IH is
       `ih : d ∣ b → d ∣ a % b → d ∣ euclid b (a % b)`                                         R8
  2. case1: the goal is `d ∣ a`, already a hypothesis
  3. case2: feed `ih` its two premises                                                        R9
       `d ∣ b`: a hypothesis
       `d ∣ a % b`: from `ha`, with `hb` as `hk`                                              R7
-/
-- BEGIN SPEC
theorem dvd_euclid (a b d : Nat) (ha : d ∣ a) (hb : d ∣ b) : d ∣ euclid a b :=
-- END SPEC
  by
    fun_induction euclid a b with
    | case1 a => exact ha
    | case2 a b h ih => exact ih hb ((Nat.dvd_mod_iff hb).mpr ha)

end M029

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Induct along the recursion, not on `b`: `fun_induction euclid a b` (R1, R8). In case2 the IH
    is about `euclid b (a % b)`, and the goal is already rewritten to that call.
H2. The only arithmetic fact: if `k ∣ n`, then `k ∣ m % n ↔ k ∣ m` (`Nat.dvd_mod_iff`, R6, R7).
    euclid_dvd case1: `Nat.dvd_refl`, `Nat.dvd_zero`; case2: the halves `ih.1`, `ih.2` (R3).
    dvd_euclid: `ha hb` are carried into each case, so `ih` takes two premises (R8, R9).
H3. euclid_dvd case2: `⟨(Nat.dvd_mod_iff ih.1).mp ih.2, ih.1⟩`;
    dvd_euclid case2: `ih hb ((Nat.dvd_mod_iff hb).mpr ha)`.
-/
