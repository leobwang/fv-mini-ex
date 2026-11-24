/- M011 | Lawvere's fixed-point theorem | 15-20 min | diagonal argument, congrFun, funext, propext, cast
GOAL
  Lawvere: if `f : α → α → β` reaches every function `α → β`, then every `t : β → β` has a fixed
  point. Then derive two diagonal arguments from it: no `Nat`-indexed list of Bool sequences is
  complete, and naive set comprehension is inconsistent (Russell). (M071 did Cantor for `Set α`.)

BANNED: Function.exists_fixed_point_of_surjective, import, exact?, apply?, try?

GUIDE
  Entries R1–R13: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

namespace M011

/- SKELETON · lawvere
  1. Ask `hf` for a row equal to the diagonal `fun a => t (f a a)`;
     open the `∃`: witness `a0`, `h : f a0 = fun a => t (f a a)`:            R1
  2. Evaluate `h` at the witness `a0` itself:
       `f a0 a0 = t (f a0 a0)`                                                R2
  3. The fixed point is `b := f a0 a0`; flip the equation of step 2:          R3, R4
-/
-- BEGIN SPEC
theorem lawvere {α β : Type} (f : α → α → β) (hf : ∀ g : α → β, ∃ a, f a = g)
    (t : β → β) : ∃ b, t b = b :=
-- END SPEC
  by
    obtain ⟨a0, h⟩ := hf (fun a => t (f a a))
    exact ⟨f a0 a0, (congrFun h a0).symm⟩

/- SKELETON · bool_sequences
  1. Witness: the flipped diagonal `fun n => !f n n`; the `≠` part is a
     function of `n` and `h : f n = fun n => !f n n`, goal `False`:          R5
  2. Evaluate `h` at `n`:  `h' : f n n = !f n n`                              R2
  3. Split on the Bool value of `f n n`, keeping its equation `hfn`:          R6
  4. In both goals, rewrite `h'` with `hfn`; it becomes `False`:             R7
-/
-- BEGIN SPEC
theorem bool_sequences (f : Nat → Nat → Bool) : ∃ g : Nat → Bool, ∀ n, f n ≠ g :=
-- END SPEC
  by
    refine ⟨fun n => !f n n, fun n h => ?_⟩
    have h' := congrFun h n
    cases hfn : f n n <;> simp [hfn] at h'

/- SKELETON · russell
  1. Assume comprehension `hc`; the goal becomes `False`:                     R8
  2. Prove first, as a `have`, comprehension in `lawvere`'s shape:
       hf : ∀ P : V → Prop, ∃ x, (fun y => mem y x) = P
     proof: fix `P`, open `hc P` (R1), give the same `x` (R4) with
     an equation of predicates (R9) built from each `↔` (R10)
  3. Apply `lawvere` with `f := fun x y => mem y x`, `hf`, `t := Not`;
     open the `∃`:  `hb : (¬b) = b`                                           R11
  4. Prove `hnb : ¬b`: assume `b` (R8), transport it to `¬b` along `hb` flipped
     (R12, R3), apply it to the assumption                                    R13
  5. Transport `hnb` along `hb` to get `b` (R12); apply `hnb` to it            R13
-/
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
H1. All three are diagonal arguments: build a function from the "diagonal" `f a a` and compare it with
    the row it is equal to, AT that row's own index. For Russell, reuse `lawvere` with `β := Prop`.
H2. Lawvere: `obtain` a row `a0` for `fun a => t (f a a)`, then `congrFun` at `a0` (R1, R2).
    Bool: the witness `fun n => !f n n`; `congrFun h n`, then `cases hfn : f n n` and `simp [hfn] at h'`.
    Russell: `intro hc`, rewrite comprehension as `∀ P, ∃ x, (fun y => mem y x) = P` with `funext`/`propext`,
    feed it to `lawvere` with `t := Not`, and refute the resulting `hb : (¬b) = b` with `cast`.
H3. Lawvere: `congrFun h a0 : f a0 a0 = t (f a0 a0)`; its `.symm` is the fixed-point equation for `f a0 a0`.
    Russell: the `have` is `⟨x, funext fun y => propext (hx y)⟩`; then `lawvere (fun x y => mem y x) hf Not`.
    From `hb : (¬b) = b`: first `¬b` (given `h : b`, `cast hb.symm h : ¬b`), then `b` (`cast hb`).
-/
