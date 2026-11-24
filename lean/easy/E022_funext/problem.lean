/- E022 | funext | 2-3 min | funext, Function.comp
GOAL
  Prove equalities between functions by proving they agree on every input.

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · add_zero_fun
  1. Function equality → one input `n`; the left side is a `fun`, so it
     becomes `n + 0`:                                                            R1, R2
  2. Both sides of `n + 0 = id n` compute to `n`:                                R3, R4
-/
-- BEGIN SPEC
theorem add_zero_fun : (fun n : Nat => n + 0) = id :=
-- END SPEC
  sorry

/- SKELETON · comp_twice
  1. Function equality → one input `x`; `(· + 2)` becomes `x + 2`, the left
     side stays `(f ∘ f) x`:                                                     R1, R5
  2. Unfold the composition to `f (f x)`:                                        R6
  3. Use `hf` on the outer call, then on the inner one:                          R7, R7
     (or steps 2–4 in one call:                                                  R8)
  4. The leftover `x + 1 + 1 = x + 2` closes by computation: the last `rw`'s
     own `rfl` (E009 R3) does it, so no further step is needed
-/
-- BEGIN SPEC
theorem comp_twice (f : Nat → Nat) (hf : ∀ x, f x = x + 1) : f ∘ f = (· + 2) :=
-- END SPEC
  sorry

/- SKELETON · map_comp_fun
  1. Both sides are functions `List Nat → List Nat`: reduce to one list `xs`:    R1
  2. Unfold the composition on the left to `List.map f (List.map g xs)`:         R6
  3. Fuse the two maps; the two sides are then identical:                        R9
     (steps 2–3 in one call: `simp` with R9 named                                R6, R9)
-/
-- BEGIN SPEC
theorem map_comp_fun (f g : Nat → Nat) : List.map f ∘ List.map g = List.map (f ∘ g) :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two functions are equal when they agree at every input: start each proof with `funext` (R1).
    After it, a `fun` or `(· + 2)` side is already applied (R2, R5), but `(f ∘ g) x` is not (R6).
H2. `add_zero_fun`: after `funext n`, both sides compute to `n` (R4).
    `comp_twice`: unfold `∘`, then use `hf` twice (R6, R7), or let `simp` do all of it with `hf` (R8).
    `map_comp_fun`: unfold `∘`, then `List.map_map` (R6, R9).
H3. `funext n; rfl`, `funext x; simp [hf]` and `funext xs; simp [List.map_map]`.
-/
