/- M011 | Lawvere's fixed-point theorem | 15-20 min | diagonal argument, congrFun, funext, propext, cast
GOAL
  Lawvere: if `f : α → α → β` reaches every function `α → β`, then every `t : β → β` has a fixed
  point. Then derive two diagonal arguments from it: no `Nat`-indexed list of Bool sequences is
  complete, and naive set comprehension is inconsistent (Russell). (M071 did Cantor for `Set α`.)

REFERENCE
  example (f g : Nat → Bool) (h : f = g) (x : Nat) : f x = g x := congrFun h x  -- apply an equation of functions
  example (f g : Nat → Bool) (h : ∀ x, f x = g x) : f = g := funext h           -- pointwise equal → equal
  example (P Q : Prop) (h : P ↔ Q) : P = Q := propext h                        -- equivalent props are equal
  example (P Q : Prop) (h : P = Q) (hp : P) : Q := cast h hp                    -- transport along `P = Q`
  example (f : Nat → Nat → Bool) : Nat → Bool := fun n => !f n n                 -- a diagonal
  example (b : Bool) (h : (!b) = b) : False := by cases b <;> simp at h
BANNED: Function.exists_fixed_point_of_surjective, import, exact?, apply?, try?
NOTE: Core only: do not add imports or leave search tactics (`exact?`, `apply?`, `try?`) in the file.
-/

namespace M011

-- BEGIN SPEC
theorem lawvere {α β : Type} (f : α → α → β) (hf : ∀ g : α → β, ∃ a, f a = g)
    (t : β → β) : ∃ b, t b = b :=
-- END SPEC
  by
    obtain ⟨a0, h⟩ := hf (fun a => t (f a a))
    exact ⟨f a0 a0, (congrFun h a0).symm⟩

-- BEGIN SPEC
theorem bool_sequences (f : Nat → Nat → Bool) : ∃ g : Nat → Bool, ∀ n, f n ≠ g :=
-- END SPEC
  by
    refine ⟨fun n => !f n n, fun n h => ?_⟩
    have h' := congrFun h n
    cases hfn : f n n <;> simp [hfn] at h'

-- BEGIN SPEC
theorem russell (V : Type) (mem : V → V → Prop) :
    ¬ ∀ P : V → Prop, ∃ x, ∀ y, mem y x ↔ P y :=
-- END SPEC
  by
    intro hc
    have hf : ∀ P : V → Prop, ∃ x, (fun y => mem y x) = P := by
      intro P
      obtain ⟨x, hx⟩ := hc P
      exact ⟨x, funext fun y => propext (hx y)⟩
    obtain ⟨b, hb⟩ := lawvere (fun x y => mem y x) hf Not
    -- WHY: `hb : (¬ b) = b` is a proposition equal to its own negation; refute it in both directions.
    have hnb : ¬ b := fun h => (cast hb.symm h) h
    exact hnb (cast hb hnb)

end M011

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Lawvere: diagonalise. Ask `hf` for an `a0` with `f a0 = fun a => t (f a a)` and look at `f a0 a0`.
H2. Russell is Lawvere with `β := Prop`, `f := fun x y => mem y x` and `t := Not`: turn comprehension into
    `∃ x, (fun y => mem y x) = P` with `funext`/`propext`, get `b` with `(¬ b) = b`, then refute that.
H3. Lawvere: `congrFun h a0 : f a0 a0 = t (f a0 a0)`. Bool: `g := fun n => !f n n`, then `congrFun h n` and
    `cases f n n`. Russell, from `h : (¬ b) = b`: first `¬ b` (given `hb : b`, `cast h.symm hb : ¬ b`), then `b`.
-/
