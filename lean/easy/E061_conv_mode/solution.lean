/- E061 | conv mode | 2-3 min | conv, lhs, arg, intro, conv at, conv in, rw occs
GOAL
  Rewrite `0 + x` to `x` under a binder (inside a `fun`, inside `List.map`'s function, inside a hypothesis),
  where plain `rw` fails because the subterm mentions the bound variable `x`.

REFERENCE
  example (g : Nat → Nat) : (fun x => g (x * 1)) = g := by
    conv => lhs; intro x; rw [Nat.mul_one]       -- `lhs`: left side; `intro x`: step under `fun x =>`
  example (a b c : Nat) (h : a = b * (c * 1)) : a = b * c := by
    conv at h => rhs; arg 2; rw [Nat.mul_one]    -- `arg i`: i-th explicit argument; `at h`: in a hypothesis
    exact h
  example (g : Nat → Nat) : (fun x => g (x * 1) + 2) = fun x => g x + 2 := by
    conv in _ * 1 => rw [Nat.mul_one]            -- `conv in pat`: go to the first match, even under a binder
  example (a b : Nat) : a + b + (a + b) = b + a + (a + b) := by rw (occs := [1]) [Nat.add_comm a b]  -- 1st match only
  #check @List.map_id'   -- (l : List α) : List.map (fun a => a) l = l
BANNED: simp, simp_all, simpa, grind, funext, funext_iff, ext, induction, ac_rfl, List.map_id'', List.map_congr_left, List.map_inj_left, List.map_eq_map_iff, exact?, try?
NOTE: a `conv` block closes the goal by `rfl` when it ends; `conv_lhs` and `nth_rw` are Mathlib only.
-/

namespace E061

-- BEGIN SPEC
theorem under_binder (f : Nat → Nat) : (fun x => f (0 + x)) = f :=
-- END SPEC
  by conv => lhs; intro x; rw [Nat.zero_add]

-- BEGIN SPEC
theorem map_under (xs : List Nat) : List.map (fun x => 0 + x) xs = xs :=
-- END SPEC
  by
    conv => lhs; arg 1; intro x; rw [Nat.zero_add]
    exact List.map_id' xs

-- BEGIN SPEC
theorem at_h (f g : Nat → Nat) (h : (fun x => f (0 + x)) = g) : f = g :=
-- END SPEC
  by
    conv at h => lhs; intro x; rw [Nat.zero_add]
    exact h

-- BEGIN SPEC
theorem pattern_bind (f : Nat → Nat) : (fun x => f (0 + x) + 1) = fun x => f x + 1 :=
-- END SPEC
  by conv in 0 + _ => rw [Nat.zero_add]

end E061

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try `rw [Nat.zero_add]` first and read the error: the `0 + x` sits under `fun x =>`. `conv` lets you walk there.
H2. Navigate: `lhs` (left side), `arg i` (into an argument), `intro x` (under the binder), then `rw [Nat.zero_add]`.
    After `under_binder`'s conv, `fun x => f x` is `f` by eta, so the goal closes by itself.
H3. `map_under`: `conv => lhs; arg 1; intro x; rw [Nat.zero_add]` then `exact List.map_id' xs`;
    `at_h`: `conv at h => lhs; intro x; rw [Nat.zero_add]` then `exact h`; `pattern_bind`: `conv in 0 + _ => …`.
-/
