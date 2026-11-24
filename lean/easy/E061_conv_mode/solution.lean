/- E061 | conv mode | 2-3 min | conv, lhs, arg, intro, conv at, conv in, rw occs
GOAL
  Rewrite `0 + x` to `x` under a binder (inside a `fun`, inside `List.map`'s function, inside a hypothesis),
  where plain `rw` fails because the subterm mentions the bound variable `x`.

BANNED: simp, simp_all, simpa, grind, funext, funext_iff, ext, induction, ac_rfl, List.map_id'', List.map_congr_left, List.map_inj_left, List.map_eq_map_iff, exact?, try?

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace E061

/- SKELETON · under_binder
  1. Enter conv mode on the goal:                                           R1
  2. Focus the left side `fun x => f (0 + x)`:                              R2
  3. Step under the binder, so `x` is a local:  x : Nat | f (0 + x)         R3
  4. Rewrite `0 + x` in the focus:                                          R4
  5. The block ends: Lean eta-reduces `fun x => f x` to `f`, so the goal is
     `f = f`, and the `rfl` tried at the end closes it:                     R5
-/
-- BEGIN SPEC
theorem under_binder (f : Nat → Nat) : (fun x => f (0 + x)) = f :=
-- END SPEC
  by conv => lhs; intro x; rw [Nat.zero_add]

/- SKELETON · map_under
  1. Enter conv, focus the left side `List.map (fun x => 0 + x) xs`:        R1, R2
  2. Focus `List.map`'s function (its first explicit argument):             R6
  3. Step under the binder, rewrite `0 + x`:                                R3 → R4
  4. The block leaves `List.map (fun x => x) xs = xs` (not closed by rfl):
     close it with the identity-map lemma:                                  R7
-/
-- BEGIN SPEC
theorem map_under (xs : List Nat) : List.map (fun x => 0 + x) xs = xs :=
-- END SPEC
  by
    conv => lhs; arg 1; intro x; rw [Nat.zero_add]
    exact List.map_id' xs

/- SKELETON · at_h
  1. Rewrite inside `h`, not the goal:                                      R8
  2. In `h`, the same path as `under_binder`:                               R2 → R3 → R4
     when the block ends `fun x => f x` is eta-reduced:  h : f = g
  3. `h` is now the goal:                                                   exact h
-/
-- BEGIN SPEC
theorem at_h (f g : Nat → Nat) (h : (fun x => f (0 + x)) = g) : f = g :=
-- END SPEC
  by
    conv at h => lhs; intro x; rw [Nat.zero_add]
    exact h

/- SKELETON · pattern_bind
  1. Jump straight to the subterm `0 + x` by a pattern with a hole `_`:     R9
  2. Rewrite it:                                                            R4
  3. The block ends at `(fun x => f x + 1) = fun x => f x + 1`; `rfl` closes it:  R5
-/
-- BEGIN SPEC
theorem pattern_bind (f : Nat → Nat) : (fun x => f (0 + x) + 1) = fun x => f x + 1 :=
-- END SPEC
  by conv in 0 + _ => rw [Nat.zero_add]

end E061

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try `rw [Nat.zero_add]` first and read the error: the `0 + x` sits under `fun x =>`, where `rw`
    cannot reach. `conv` moves a focus to it (R1), and `intro x` (R3) makes `x` a local `rw` can use.
H2. Walk down with `lhs` (R2), `arg 1` (R6, for `List.map`'s function), `intro x` (R3), then
    `rw [Nat.zero_add]` (R4). The block's final `rfl` (R5) finishes `under_binder` and `pattern_bind`;
    `map_under` still needs `List.map_id'` (R7); `at_h` uses `conv at h` (R8), then `exact h`.
H3. `map_under`: `conv => lhs; arg 1; intro x; rw [Nat.zero_add]`, then `exact List.map_id' xs`.
    `at_h`: `conv at h => lhs; intro x; rw [Nat.zero_add]`. `pattern_bind`: `conv in 0 + _ => …`.
-/
