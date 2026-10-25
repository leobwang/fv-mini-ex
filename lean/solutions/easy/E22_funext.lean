/- E22 | funext | 2-3 min | funext, Function.comp
GOAL
  Prove equalities between functions by proving they agree on every input.

REFERENCE
  example : (fun n : Nat => 0 + n) = id := by funext n; simp   -- goal becomes 0 + n = id n
  example (f g : Nat → Nat) (x : Nat) : (f ∘ g) x = f (g x) := rfl   -- `∘` is composition
  #check Function.comp_apply   -- (f ∘ g) x = f (g x)  (useful in `simp [..]`)
  #check List.map_map          -- List.map g (List.map f l) = List.map (g ∘ f) l
  `(· + 2)` is shorthand for `fun x => x + 2`.
-/

-- BEGIN SPEC
theorem add_zero_fun : (fun n : Nat => n + 0) = id :=
-- END SPEC
  by
    funext n
    rfl

-- BEGIN SPEC
theorem comp_twice (f : Nat → Nat) (hf : ∀ x, f x = x + 1) : f ∘ f = (· + 2) :=
-- END SPEC
  by
    funext x
    simp [hf]

-- BEGIN SPEC
theorem map_comp_fun (f g : Nat → Nat) : List.map f ∘ List.map g = List.map (f ∘ g) :=
-- END SPEC
  by
    funext xs
    simp [List.map_map]

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `funext x` turns `F = G` into `F x = G x`.
H2. After `funext`, unfold composition (`Function.comp_apply`) and use the hypotheses or `List.map_map`.
H3. `funext x; simp [hf]` and `funext xs; simp [List.map_map]`.
-/
