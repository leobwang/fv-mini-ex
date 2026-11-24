/- M077 | Countable unions of countable sets | 10-15 min | choose, Nat.pair, iUnion, Set.range, computable def, mathlib
GOAL
  Call `s` enumerable if some sequence `f : ℕ → α` lists every element of `s` (`s ⊆ Set.range f`);
  for nonempty `α` this is Mathlib's `Set.Countable`. Show `ℕ × ℕ` is enumerable. Then write
  `interleave f`: one sequence that lists every `f n m`, i.e. the sequences `f 0, f 1, …` merged.
  Use it to show a union `⋃ n, A n` of enumerable sets is enumerable.

REFERENCE
  example (a b : ℕ) : Nat.unpair (Nat.pair a b) = (a, b) := Nat.unpair_pair a b  -- pairing ℕ × ℕ ≃ ℕ
  example (k : ℕ) : ℕ × ℕ := k.unpair     -- `k.unpair.1`, `k.unpair.2` are its two coordinates
  example (g : ℕ → ℕ → ℕ) : ℕ → ℕ := fun k => g k 0   -- a sequence written as a `fun`
  #check Set.mem_range    -- x ∈ Set.range f ↔ ∃ y, f y = x     (`Set.range f` = {f y | y})
  #check Set.mem_iUnion   -- x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i
  example (s t : Set ℕ) (h : ∀ x, x ∈ s → x ∈ t) : s ⊆ t := h  -- `⊆` is `∀ x, x ∈ s → x ∈ t`
  example (h : ∀ n : ℕ, ∃ m : ℕ, n < m) : True := by choose f hf using h; trivial  -- f : ℕ → ℕ, hf : ∀ n, n < f n
  -- `obtain ⟨m, rfl⟩ := hx` on `hx : x ∈ Set.range f` replaces `x` by `f m` everywhere
  -- `simp [interleave]` unfolds your own definition inside a goal
BANNED: Countable, countable, Encodable, Denumerable, Cardinal, exists_injective_nat, countable_range, countable_iUnion, countable_iff_exists_subset_range, exists_surjective_nat, exists_eq_range, exists_surjective, countable_iUnion_iff, countable_univ, to_countable, countable_coe_iff, enumerateCountable, subset_range_enumerate, range_enumerateCountable_subset, countable_iff_exists_surjective, countable_iff_exists_injective, countable_iff_exists_injOn, countable_iff_nonempty_encodable, nonempty_encodable, exists_seq_cover_iff_countable, toEncodable, ofCountable, to_subtype, countable_union, biUnion, sUnion, noncomputable
NOTE: The point is to build the enumerations yourself, so Mathlib's `Set.Countable` API is banned.
  `interleave` must be computable (`noncomputable` is banned), so it cannot be picked by choice:
  write the actual formula.
-/
import Mathlib

namespace M077

-- BEGIN SPEC
def Enumerable {α : Type*} (s : Set α) : Prop := ∃ f : ℕ → α, s ⊆ Set.range f
-- END SPEC

-- BEGIN SPEC
theorem enumerable_prod : Enumerable (Set.univ : Set (ℕ × ℕ)) :=
-- END SPEC
  sorry

-- BEGIN SPEC
def interleave {α : Type*} (f : ℕ → ℕ → α) : ℕ → α :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem iUnion_subset_interleave {α : Type*} (A : ℕ → Set α) (f : ℕ → ℕ → α)
    (hf : ∀ n, A n ⊆ Set.range (f n)) : ⋃ n, A n ⊆ Set.range (interleave f) :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem enumerable_iUnion {α : Type*} (A : ℕ → Set α) (h : ∀ n, Enumerable (A n)) :
    Enumerable (⋃ n, A n) :=
-- END SPEC
  sorry

end M077

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `ℕ × ℕ`: the sequence is `Nat.unpair`. For `interleave`, read the index `k` as a pair `(n, m)` with
    `Nat.unpair` and return entry `m` of sequence `n`.
H2. `interleave f := fun k => f k.unpair.1 k.unpair.2`. In `iUnion_subset_interleave`, for `x ∈ A n` get `m`
    with `f n m = x`; the witness index is `Nat.pair n m`, closed by `simp [interleave, Nat.unpair_pair]`.
H3. `enumerable_iUnion`: `choose f hf using h` gives `f : ℕ → ℕ → α` with `hf : ∀ n, A n ⊆ Set.range (f n)`;
    finish with `⟨interleave f, iUnion_subset_interleave A f hf⟩`.
-/
