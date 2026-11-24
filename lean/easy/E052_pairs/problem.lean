/- E052 | Pairs | 2 min | Prod, .1, .2, Prod.ext, pattern lambda
GOAL
  Work with pairs `α × β`: projections, eta (rebuilding a pair gives it back), extensionality,
  and a function defined by a pattern-matching lambda.

REFERENCE
  example : (3, "a").1 = 3 := rfl                     -- `.1`/`.fst` and `.2`/`.snd` project
  example (p : Nat × Nat) : (p.1, p.2) = p := rfl     -- eta: holds by definition
  #check @Prod.ext      -- x.fst = y.fst → x.snd = y.snd → x = y
  example : Nat × Nat → Nat := fun (a, b) => a * b    -- pattern-matching lambda
  example (p : Nat × Nat) : p.1 + p.2 = p.2 + p.1 := by
    obtain ⟨a, b⟩ := p; exact Nat.add_comm a b        -- split a pair variable into components
BANNED: grind
-/

namespace E052

-- BEGIN SPEC
def swap {α β : Type} (p : α × β) : β × α := (p.2, p.1)
def addPair : Nat × Nat → Nat := fun (a, b) => a + b
-- END SPEC

-- BEGIN SPEC
theorem swap_swap {α β : Type} (p : α × β) : swap (swap p) = p :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem pair_ext (p q : Nat × Nat) (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem addPair_swap (p : Nat × Nat) : addPair (swap p) = addPair p :=
-- END SPEC
  sorry

end E052

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold `swap (swap p)` by hand: what pair do you get, and what does eta say about it?
H2. `pair_ext` is extensionality for `×`. For `addPair_swap`, split `p` into `(a, b)` so that both
    sides compute to plain sums.
H3. `pair_ext`: `Prod.ext h1 h2`; `addPair_swap`: `obtain ⟨a, b⟩ := p` then `exact Nat.add_comm b a`.
-/
