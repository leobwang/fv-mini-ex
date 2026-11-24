/- H022 | Regex matcher | 1.5-2 h | inductive semantics, Brzozowski derivatives, inversion lemmas
GOAL
  `rmatch` decides regular-expression matching with Brzozowski derivatives. Prove it agrees with
  the inductive matching relation `Matches` on every regex and every word.

GUIDE
  Entries R1–R28: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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
/- SKELETON · cat_inv          (used in nullable_iff and deriv_iff)
  1. Invert `h`: only the rule `cat` concludes `Matches (.cat _ _) _`, and `w` is a
     variable, so `w` becomes `u ++ v`. Name the premises:                    R1, R2
     (or `cases h with | cat hu hv => …`)
  2. Give the witnesses; `rfl` proves `u ++ v = ?u ++ ?v`:                     R3
-/
theorem cat_inv {r s : Re} {w : List Char} (h : Matches (.cat r s) w) :
    ∃ u v, w = u ++ v ∧ Matches r u ∧ Matches s v := by
  cases h with
  | cat hu hv => exact ⟨_, _, rfl, hu, hv⟩

-- MILESTONE (optional: change or delete)
/- SKELETON · nullable_iff     (used in deriv_iff, case cat, and in rmatch_iff, case nil)
  1. Induction on `r`, one goal per constructor:                              R4
  2. `empty`, `chr c`: unfold `nullable`, leaves `¬Matches … []`;
     `intro h`, then no rule fits:                                            R5, R6
     `eps`, `star r`: unfold, leaves `Matches … []`; give `.eps` / `.starNil`:  R5, R10
  3. `alt r s ihr ihs`: unfold, `||` → `∨`, rewrite with both IHs:            R28, R7, R9
     `constructor`;  →  `rintro (h | h)`, then `.altL h` / `.altR h`           R10
                     ←  invert `h` (two rules fit: altL, altR), then
                        `Or.inl h` / `Or.inr h`                               R1
  4. `cat r s ihr ihs`: unfold, `&&` → `∧`, both IHs:                          R28, R8, R9
     `constructor`;  →  `.cat (u := []) (v := []) h1 h2`                      R10
                     ←  `obtain ⟨u, v, huv, hu, hv⟩ := cat_inv h`, so
                        `huv : [] = u ++ v`; split it and substitute:         R12, R11
-/
theorem nullable_iff (r : Re) : nullable r = true ↔ Matches r [] := by
  induction r with
  | empty => simp [nullable]; intro h; cases h
  | eps => simp [nullable]; exact .eps
  | chr c => simp [nullable]; intro h; cases h
  | alt r s ihr ihs =>
    simp only [nullable, Bool.or_eq_true, ihr, ihs]
    constructor
    · rintro (h | h)
      · exact .altL h
      · exact .altR h
    · intro h
      cases h with
      | altL h => exact Or.inl h
      | altR h => exact Or.inr h
  | cat r s ihr ihs =>
    simp only [nullable, Bool.and_eq_true, ihr, ihs]
    constructor
    · rintro ⟨h1, h2⟩
      exact .cat (u := []) (v := []) h1 h2
    · intro h
      obtain ⟨u, v, huv, hu, hv⟩ := cat_inv h
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv.symm
      exact ⟨hu, hv⟩
  | star r _ => simp [nullable]; exact .starNil

-- MILESTONE (optional: change or delete)
/- SKELETON · star_cons_inv    (used in deriv_iff, case star, direction ←)
  1. Make both indices of `h` variables:
       hR : Re.star r = R      and      hx : c :: w = x                       R13, R13
  2. Rule induction on `h`, generalizing `w`; hR and hx become
     premises of every IH:                                                    R14
  3. `starNil`: `hx : c :: w = []` is impossible:                             R16
  4. `@starCons r' u v hu hv _ ihv`:
       `cases hR` turns `r'` into `r`:                                        R15
       `cases u`:
         nil:  the first chunk is empty, `hx : c :: w = [] ++ v`
               (= `c :: w = v`), so the IH finishes: `ihv rfl hx`
         cons c' u':  `hx : c :: w = c' :: u' ++ v` → `c = c' ∧ w = u' ++ v`,
               substitute, then witnesses `u'`, `v`:                          R18, R19, R11, R3
  5. Every other rule: `hR` equates different constructors:                   R17, R16
-/
theorem star_cons_inv {r : Re} {c : Char} {w : List Char} (h : Matches (.star r) (c :: w)) :
    ∃ u v, w = u ++ v ∧ Matches r (c :: u) ∧ Matches (.star r) v := by
  generalize hR : Re.star r = R at h
  generalize hx : c :: w = x at h
  induction h generalizing w with
  | starNil => cases hx
  | @starCons r' u v hu hv _ ihv =>
    cases hR
    cases u with
    | nil => exact ihv rfl hx
    | cons c' u' =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨u', v, rfl, hu, hv⟩
  | _ => cases hR

-- MILESTONE (optional: change or delete)
/- SKELETON · deriv_iff        (needs cat_inv, nullable_iff, star_cons_inv; used in rmatch_iff)
  1. Induction on `r` generalizing `w` (IHs are used at shorter words);
     in each case unfold `deriv` with `simp only [deriv]`:                    R20, R28
  2. `empty`, `eps`: no derivation on either side:
     `constructor <;> intro h <;> cases h`                                    R6
  3. `chr d`: `split` on `c = d`, name the hypothesis:                         R21, R2
       c = d:   substitute; each direction: invert, give the other rule       R23, R1, R10
       ¬c = d:  → no rule fits;  ← invert, which leaves `¬c = c`              R6, R1, R24
  4. `alt`: each direction: invert, then `.altL`/`.altR` of the IH at `w`      R1, R10, R25
  5. `cat`:  →  `split at h` on `nullable r`, name it:                         R22, R2
                nullable: invert `h` (two rules fit: altL, altR)              R1
                nullable, `.altL`: `cat_inv` on the inner `.cat`, then
                  `.cat (u := c :: u)` with the IH of `r` at `u`              R11, R10, R25
                nullable, `.altR`: `.cat (u := [])` from `nullable_iff`
                  and the IH of `s` at `w`                                    R10, R25
                not nullable: as the `.altL` sub-case                         R11, R10, R25
             ←  `cat_inv h` gives `huv : c :: w = u ++ v`; split it:          R26
                u = []:      `nullable r = true` from `nullable_iff`; pick the
                             `if` branch, then `.altR` of the IH of `s`        R25, R27, R10
                u = c :: u': `split`, then `.altL (.cat …)` / `.cat …`
                             with the IH of `r` at `u'`                       R21, R10, R25
  6. `star`: →  `cat_inv h`, then `.starCons (u := c :: u)` with the IH        R11, R10, R25
             ←  `star_cons_inv h`, then `.cat` with the IH                     R11, R10, R25
-/
theorem deriv_iff (c : Char) (r : Re) (w : List Char) :
    Matches (deriv c r) w ↔ Matches r (c :: w) := by
  induction r generalizing w with
  | empty => simp only [deriv]; constructor <;> intro h <;> cases h
  | eps => simp only [deriv]; constructor <;> intro h <;> cases h
  | chr d =>
    simp only [deriv]
    split
    · rename_i hcd
      subst hcd
      constructor
      · intro h; cases h; exact .chr c
      · intro h; cases h; exact .eps
    · rename_i hcd
      constructor
      · intro h; cases h
      · intro h; cases h; exact absurd rfl hcd
  | alt r s ihr ihs =>
    simp only [deriv]
    constructor
    · intro h
      cases h with
      | altL h => exact .altL ((ihr w).mp h)
      | altR h => exact .altR ((ihs w).mp h)
    · intro h
      cases h with
      | altL h => exact .altL ((ihr w).mpr h)
      | altR h => exact .altR ((ihs w).mpr h)
  | cat r s ihr ihs =>
    simp only [deriv]
    constructor
    · intro h
      split at h
      · rename_i hn
        cases h with
        | altL h =>
          obtain ⟨u, v, rfl, hu, hv⟩ := cat_inv h
          exact .cat (u := c :: u) ((ihr u).mp hu) hv
        | altR h =>
          exact .cat (u := []) ((nullable_iff r).mp hn) ((ihs w).mp h)
      · obtain ⟨u, v, rfl, hu, hv⟩ := cat_inv h
        exact .cat (u := c :: u) ((ihr u).mp hu) hv
    · intro h
      obtain ⟨u, v, huv, hu, hv⟩ := cat_inv h
      rcases List.append_eq_cons_iff.mp huv.symm with ⟨rfl, rfl⟩ | ⟨u', rfl, rfl⟩
      · have hn : nullable r = true := (nullable_iff r).mpr hu
        simp only [hn, if_true]
        exact .altR ((ihs w).mpr hv)
      · split
        · exact .altL (.cat ((ihr u').mpr hu) hv)
        · exact .cat ((ihr u').mpr hu) hv
  | star r ihr =>
    simp only [deriv]
    constructor
    · intro h
      obtain ⟨u, v, rfl, hu, hv⟩ := cat_inv h
      exact .starCons (u := c :: u) ((ihr u).mp hu) hv
    · intro h
      obtain ⟨u, v, rfl, hu, hv⟩ := star_cons_inv h
      exact .cat ((ihr u).mpr hu) hv

/- SKELETON · rmatch_iff
  Prove the milestones first, in order: cat_inv → nullable_iff → star_cons_inv → deriv_iff.
  1. Induction on the word `w`, generalizing `r` (the regex changes to
     `deriv c r` at each step):                                               R20 (on a list)
  2. nil:  exactly `nullable_iff r`
  3. cons c w ih: unfold one step of `rmatch`, rewrite with `ih`,
     then with `deriv_iff`; `simp only` closes the `A ↔ A` left:              R28, R9, R9
-/
-- BEGIN SPEC
theorem rmatch_iff (r : Re) (w : List Char) : rmatch r w = true ↔ Matches r w :=
-- END SPEC
  by
    induction w generalizing r with
    | nil => exact nullable_iff r
    | cons c w ih => simp only [rmatch, ih, deriv_iff]

end H022

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Prove the milestones in order: `cat_inv` → `nullable_iff` → `star_cons_inv` → `deriv_iff`. The main
    theorem is then an induction on the word, generalizing `r`: `nullable_iff` at `[]`, `deriv_iff` at `c :: w`.
H2. `nullable_iff` and `deriv_iff` are inductions on `r` (`deriv_iff` generalizing `w`); invert derivations
    with `cases` (variable word) or `cat_inv`. In `deriv_iff`'s `cat` case split `c :: w = u ++ v` with
    `List.append_eq_cons_iff` (`u = []` or `u = c :: u'`); its `star` case (←) uses `star_cons_inv`, a rule
    induction on `h` after generalizing both indices.
H3. `star_cons_inv`: `generalize hR : Re.star r = R at h; generalize hx : c :: w = x at h;
    induction h generalizing w with | starNil => cases hx | @starCons r' u v hu hv _ ihv => … | _ => cases hR`;
    in `starCons`: `cases hR; cases u`, with `u = []` use `ihv rfl hx`, with `u = c' :: u'`
    `simp only [List.cons_append, List.cons.injEq] at hx` and give `⟨u', v, rfl, hu, hv⟩`.
-/
