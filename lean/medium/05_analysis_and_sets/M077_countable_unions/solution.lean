/- M077 | Countable unions of countable sets | 10-15 min | choose, Nat.pair, iUnion, Set.range, computable def, mathlib
GOAL
  Call `s` enumerable if some sequence `f : ℕ → α` lists every element of `s` (`s ⊆ Set.range f`);
  for nonempty `α` this is Mathlib's `Set.Countable`. Show `ℕ × ℕ` is enumerable. Then write
  `interleave f`: one sequence that lists every `f n m`, i.e. the sequences `f 0, f 1, …` merged.
  Use it to show a union `⋃ n, A n` of enumerable sets is enumerable.
BANNED: Countable, countable, Encodable, Denumerable, Cardinal, exists_injective_nat, countable_range, countable_iUnion, countable_iff_exists_subset_range, exists_surjective_nat, exists_eq_range, exists_surjective, countable_iUnion_iff, countable_univ, to_countable, countable_coe_iff, enumerateCountable, subset_range_enumerate, range_enumerateCountable_subset, countable_iff_exists_surjective, countable_iff_exists_injective, countable_iff_exists_injOn, countable_iff_nonempty_encodable, nonempty_encodable, exists_seq_cover_iff_countable, toEncodable, ofCountable, to_subtype, countable_union, biUnion, sUnion, noncomputable

GUIDE
  Entries R1–R9: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M077

-- BEGIN SPEC
def Enumerable {α : Type*} (s : Set α) : Prop := ∃ f : ℕ → α, s ⊆ Set.range f
-- END SPEC

/- SKELETON · enumerable_prod
  1. Name the sequence: `Nat.unpair : ℕ → ℕ × ℕ` (`Enumerable` unfolds by itself):   R1
  2. Take a pair `p` (its membership in `Set.univ` is useless):                    R2
  3. Give the index of `p`: the code of its two coordinates, `Nat.pair p.1 p.2`:    R3
  4. Close `Nat.unpair (Nat.pair p.1 p.2) = p` with the decoding lemma:             R4
-/
-- BEGIN SPEC
theorem enumerable_prod : Enumerable (Set.univ : Set (ℕ × ℕ)) :=
-- END SPEC
  ⟨Nat.unpair, fun p _ => ⟨Nat.pair p.1 p.2, Nat.unpair_pair p.1 p.2⟩⟩

/- SKELETON · interleave
  1. A `fun k => …`; decode `k` into the pair `(k.unpair.1, k.unpair.2)`:           R5
  2. Return entry `k.unpair.2` of sequence `k.unpair.1`. No `Classical.choose`.
-/
-- BEGIN SPEC
def interleave {α : Type*} (f : ℕ → ℕ → α) : ℕ → α :=
-- END SPEC
  fun k => f k.unpair.1 k.unpair.2

/- SKELETON · iUnion_subset_interleave
  1. Take `x` and `hx : x ∈ ⋃ n, A n`:                                              R2
  2. Find its piece: `n` and `hn : x ∈ A n`:                                         R6
  3. Push `hn` through `hf n` to get `x ∈ Set.range (f n)`:                          R7
  4. Replace `x` by `f n m`:                                                         R8
  5. Give the index of `f n m` in `interleave f` (the code of `(n, m)`):             R3
  6. Evaluate: unfold `interleave`, then decode (one `simp` with both names):      R5, R4
-/
-- BEGIN SPEC
theorem iUnion_subset_interleave {α : Type*} (A : ℕ → Set α) (f : ℕ → ℕ → α)
    (hf : ∀ n, A n ⊆ Set.range (f n)) : ⋃ n, A n ⊆ Set.range (interleave f) :=
-- END SPEC
  by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, rfl⟩ := hf n hn
    exact ⟨Nat.pair n m, by simp [interleave, Nat.unpair_pair]⟩

/- SKELETON · enumerable_iUnion
  1. One sequence per piece: `f : ℕ → ℕ → α`, `hf : ∀ n, A n ⊆ Set.range (f n)`:     R9
  2. The sequence is `interleave f`; its property is your Part 3 theorem
     applied to `A f hf`:                                                            R1
-/
-- BEGIN SPEC
theorem enumerable_iUnion {α : Type*} (A : ℕ → Set α) (h : ∀ n, Enumerable (A n)) :
    Enumerable (⋃ n, A n) :=
-- END SPEC
  by
    choose f hf using h
    exact ⟨interleave f, iUnion_subset_interleave A f hf⟩

end M077

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each part is a membership chase: a `⊆` goal is `intro`, an `x ∈ Set.range f` goal is "give the index",
    and the index of a pair `(n, m)` is the number `Nat.pair n m`, decoded back by `Nat.unpair`.
H2. `enumerable_prod`: the sequence is `Nat.unpair`, the index of `p` is `Nat.pair p.1 p.2`.
    `interleave f` reads `k` as the pair `k.unpair` and returns entry `k.unpair.2` of sequence `k.unpair.1`.
    `iUnion_subset_interleave`: `intro`, `Set.mem_iUnion.mp`, `hf n hn`, `obtain ⟨m, rfl⟩`, index `Nat.pair n m`.
    `enumerable_iUnion`: `choose` the sequences, then use `iUnion_subset_interleave`.
H3. `interleave f := fun k => f k.unpair.1 k.unpair.2`; the last goal of Part 3 closes by
    `simp [interleave, Nat.unpair_pair]`; Part 4 is `choose f hf using h` then
    `exact ⟨interleave f, iUnion_subset_interleave A f hf⟩`.
-/
