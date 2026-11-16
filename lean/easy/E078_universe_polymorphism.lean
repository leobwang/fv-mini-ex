/- E078 | Universe polymorphism | 2-3 min | universe, Type u, Sort u
GOAL
  Implement the universe-polymorphic `mapFst` (apply `f` to the first component of a pair) and
  `pick` (return the first argument), then use them on types themselves, such as `List` and `Nat`.

REFERENCE
  universe u                                -- declare a universe variable `u`
  def idU {α : Sort u} (a : α) : α := a     -- `Sort u` ranges over Prop (= Sort 0) and every Type
  #check (Nat : Type)                       -- Type = Type 0 = Sort 1
  #check (Type : Type 1)                    -- Type 0 : Type 1 : Type 2 : ...  (Type u = Sort (u+1))
  #check ((List Nat, 3) : Type × Nat)       -- a pair whose first component is a type lives in Type 1
  example : idU Nat = Nat := rfl            -- α := Type here, so idU is used at Sort 2
  example : idU (rfl : 1 = 1) = rfl := rfl  -- ... and at Sort 0: the argument is a proof
  example : (ULift.up 3 : ULift.{1} Nat).down = 3 := rfl   -- ULift: copy a type one universe up
NOTE: with `{α : Type}` in place of `{α : Sort u}`, `idU Nat` fails: it needs `α := Type`, and `Type : Type 1`, not `Type`.
-/

namespace E078

-- BEGIN SPEC
universe u v w

def mapFst {α : Type u} {β : Type v} {γ : Type w} (f : α → γ) (p : α × β) : γ × β :=
-- END SPEC
  sorry

-- BEGIN SPEC
def pick {α : Sort u} (a _b : α) : α :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mapFst_id {α : Type u} {β : Type v} (p : α × β) : mapFst id p = p :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mapFst_comp {α : Type u} {β : Type v} {γ δ : Type w} (f : α → γ) (g : γ → δ) (p : α × β) :
    mapFst g (mapFst f p) = mapFst (g ∘ f) p :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem mapFst_types : mapFst List (Nat, 3) = (List Nat, 3) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem pick_type : pick Nat Bool = Nat :=
-- END SPEC
  sorry

end E078

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The signatures already carry all the universe bookkeeping; the bodies are ordinary one-liners.
H2. `mapFst` builds a new pair from `f p.1` and `p.2`; `pick` ignores `_b`. Once the bodies are right,
    every theorem holds by unfolding, i.e. `rfl`.
H3. `(f p.1, p.2)` and `a`; then `rfl` four times. In `mapFst_types`, `α := Type`, `γ := Type`, `β := Nat`,
    so `u = w = 1` and `v = 0`.
-/
