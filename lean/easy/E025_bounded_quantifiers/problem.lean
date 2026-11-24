/- E025 | Bounded quantifiers | 3 min | ∀ x ∈ xs, List.mem_map, List.mem_append
GOAL
  Work with `∀ x ∈ xs, P x` and `∃ x ∈ xs, P x` over lists.

GUIDE
  Entries R1–R12: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/

/- SKELETON · all_map_double
  1. Introduce the element and its membership (two names):                  R1
       hy : y ∈ List.map (fun x => x * 2) xs
  2. Read membership in the `map`:                                           R2
       hy : ∃ a, a ∈ xs ∧ a * 2 = y
  3. Unpack it with the `rfl` pattern (names `x hx`), so `y` becomes `x * 2`: R3
       left over: `x * 2 > 1`, with `hx : x ∈ xs`
  4. `omega` cannot use the `∀` in `h`: put `x > 0` in the context first:     R4
  5. Finish the arithmetic:                                                  R5
-/
-- BEGIN SPEC
theorem all_map_double (xs : List Nat) (h : ∀ x ∈ xs, x > 0) : ∀ y ∈ xs.map (· * 2), y > 1 :=
-- END SPEC
  sorry

/- SKELETON · all_append
  1. Introduce the element and its membership:                              R1
  2. Read membership in `xs ++ ys`:                                          R6
       hz : z ∈ xs ∨ z ∈ ys
  3. Split the `∨` into two goals:                                           R7
  4. Each goal is `p z`: the hypothesis for that side, applied to `z`:       R8
-/
-- BEGIN SPEC
theorem all_append (p : Nat → Prop) (xs ys : List Nat) (h1 : ∀ x ∈ xs, p x) (h2 : ∀ y ∈ ys, p y) :
    ∀ z ∈ xs ++ ys, p z :=
-- END SPEC
  sorry

/- SKELETON · exists_big
  One anonymous constructor ⟨witness, membership, property⟩ (term or refine): R9
  1. Witness: `3` (it is in the tail `xs` of `0 :: xs`, not the head).
  2. Membership `3 ∈ 0 :: xs`: head-or-tail, then the tail side from `h`:   R10 → R11
  3. Property `3 > 2`: compute it (`by decide` inside a term):              R12
-/
-- BEGIN SPEC
theorem exists_big (xs : List Nat) (h : 3 ∈ xs) : ∃ x ∈ 0 :: xs, x > 2 :=
-- END SPEC
  sorry

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A `∀ y ∈ L, …` goal starts with `intro y hy` (R1). Then say what `y ∈ L` means for the list `L` you
    have: `List.mem_map` for a `map`, `List.mem_append` for `++` (R2, R6), used with `rw [..] at hy`.
    An `∃ x ∈ L, …` goal needs a witness, a membership proof and a proof of the property (R9).
H2. `all_map_double`: unpack `hy` with the `rfl` pattern (R3), get `x > 0` from `h` (R4), then `omega`.
    `all_append`: split the `∨` with `rcases` (R7) and close each side with `h1` or `h2` (R8).
    `exists_big`: the witness is `3`, which sits in the tail of `0 :: xs` (R10, then `Or.inr`).
H3. `all_map_double`: `obtain ⟨x, hx, rfl⟩ := hy; have := h x hx; omega`.
    `exists_big`: `⟨3, List.mem_cons.mpr (Or.inr h), by decide⟩`.
-/
