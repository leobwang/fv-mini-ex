/- H022 | Regex matcher | 1.5-2 h | inductive semantics, Brzozowski derivatives, inversion lemmas
GOAL
  `rmatch` decides regular-expression matching with Brzozowski derivatives. Prove it agrees with
  the inductive matching relation `Matches` on every regex and every word.

REFERENCE
  -- deriv c r matches w  iff  r matches c :: w.  nullable r  iff  r matches [].
  example : H022.Matches (.cat (.chr 'a') (.chr 'b')) ['a', 'b'] := .cat (u := ['a']) (.chr 'a') (.chr 'b')
  #check List.append_eq_nil_iff    -- p ++ q = [] ↔ p = [] ∧ q = []
  #check List.append_eq_cons_iff   -- as ++ bs = x :: c ↔ (as = [] ∧ bs = x :: c) ∨ ∃ as', as = x :: as' ∧ c = as' ++ bs
  -- `cases h` cannot invert `h : Matches (.cat r s) w'` when w' is not a variable; state inversion
  -- lemmas with a variable word (`cases` then works), or `generalize` the index first.
  -- Star with a non-empty word needs its own lemma: the first chunk may be [] (skip it by induction).
-/

namespace H022

-- BEGIN SPEC
inductive Re where
  | empty
  | eps
  | chr (c : Char)
  | alt (r s : Re)
  | cat (r s : Re)
  | star (r : Re)

inductive Matches : Re → List Char → Prop
  | eps : Matches .eps []
  | chr (c : Char) : Matches (.chr c) [c]
  | altL {r s : Re} {w : List Char} : Matches r w → Matches (.alt r s) w
  | altR {r s : Re} {w : List Char} : Matches s w → Matches (.alt r s) w
  | cat {r s : Re} {u v : List Char} : Matches r u → Matches s v → Matches (.cat r s) (u ++ v)
  | starNil {r : Re} : Matches (.star r) []
  | starCons {r : Re} {u v : List Char} :
      Matches r u → Matches (.star r) v → Matches (.star r) (u ++ v)

def nullable : Re → Bool
  | .empty => false
  | .eps => true
  | .chr _ => false
  | .alt r s => nullable r || nullable s
  | .cat r s => nullable r && nullable s
  | .star _ => true

def deriv (c : Char) : Re → Re
  | .empty => .empty
  | .eps => .empty
  | .chr d => if c = d then .eps else .empty
  | .alt r s => .alt (deriv c r) (deriv c s)
  | .cat r s => if nullable r then .alt (.cat (deriv c r) s) (deriv c s) else .cat (deriv c r) s
  | .star r => .cat (deriv c r) (.star r)

def rmatch (r : Re) : List Char → Bool
  | [] => nullable r
  | c :: w => rmatch (deriv c r) w
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem cat_inv {r s : Re} {w : List Char} (h : Matches (.cat r s) w) :
    ∃ u v, w = u ++ v ∧ Matches r u ∧ Matches s v := by
  sorry

-- MILESTONE (optional: change or delete)
theorem nullable_iff (r : Re) : nullable r = true ↔ Matches r [] := by
  sorry

-- MILESTONE (optional: change or delete)
theorem star_cons_inv {r : Re} {c : Char} {w : List Char} (h : Matches (.star r) (c :: w)) :
    ∃ u v, w = u ++ v ∧ Matches r (c :: u) ∧ Matches (.star r) v := by
  sorry

-- MILESTONE (optional: change or delete)
theorem deriv_iff (c : Char) (r : Re) (w : List Char) :
    Matches (deriv c r) w ↔ Matches r (c :: w) := by
  sorry

-- BEGIN SPEC
theorem rmatch_iff (r : Re) (w : List Char) : rmatch r w = true ↔ Matches r w :=
-- END SPEC
  sorry

end H022

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The main theorem is an induction on the word once you know `nullable_iff` and `deriv_iff`.
H2. `deriv_iff` is an induction on `r` generalising `w`. The `cat` case splits `c :: w = u ++ v` into `u = []` or `u = c :: u'`; the `star` case needs `star_cons_inv`.
H3. `star_cons_inv`: `generalize hR : Re.star r = R at h; generalize hx : c :: w = x at h; induction h generalizing w`; in `starCons` with `u = []` use the IH, with `u = c' :: u'` you are done.
-/
