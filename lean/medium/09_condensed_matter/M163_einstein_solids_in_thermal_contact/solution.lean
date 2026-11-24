/- M163 | Einstein solids in thermal contact | 15-20 min | Nat.card, stars and bars, Fin.append, fiberwise counting, card_nbij', mathlib
GOAL
  A microstate of `n` oscillators is `f : Fin n → ℕ` (quanta per site); `Ω_n(k)` counts those with `k`
  quanta in total. (a) `Ω_N(q) = C(N + q - 1, q)`. (b) Solids `A` (`a` sites) and `B` (`b` sites) sharing
  `q` quanta: `Ω_{a+b}(q) = ∑_{k ≤ q} Ω_a(k) · Ω_b(q - k)`. Two MILESTONEs split (b).

REFERENCE
  #check Sym.equivNatSumOfFintype  -- Sym α n ≃ {P : α → ℕ // ∑ i, P i = n}  (multisets of size n)
  #check Sym.card_sym_eq_choose    -- Fintype.card (Sym α k) = (Fintype.card α + k - 1).choose k
  #check Nat.card_congr            -- α ≃ β → Nat.card α = Nat.card β;  also Nat.card_eq_fintype_card
  #check Finset.Nat.mem_antidiagonalTuple  -- x ∈ antidiagonalTuple k n ↔ ∑ i, x i = n
  #check Nat.card_eq_finsetCard    -- Nat.card ↥s = s.card;  Equiv.subtypeEquivRight changes the predicate
  #check Finset.card_eq_sum_card_fiberwise  -- MapsTo f s t → s.card = ∑ b ∈ t, {a ∈ s | f a = b}.card
  #check Finset.card_nbij'   -- i, j, maps-to both ways, j ∘ i = id, i ∘ j = id → s.card = t.card
  #check Finset.card_product -- (s ×ˢ t).card = s.card * t.card
  #check Fin.sum_univ_add    -- ∑ over Fin (a + b) = ∑ over castAdd part + ∑ over natAdd part
  #check Fin.append_left     -- Fin.append u v (Fin.castAdd n i) = u i   (and Fin.append_right)
  #check Fin.append_castAdd_natAdd  -- Fin.append (f ∘ castAdd) (f ∘ natAdd) = f
NOTE: `Set.MapsTo f ↑s ↑t` goals show `x ∈ ↑s`; `simp only [Finset.mem_coe, ...]` turns them into `x ∈ s`.
-/
import Mathlib

namespace M163

-- BEGIN SPEC
theorem einstein_solid (N q : ℕ) :
    Nat.card {f : Fin N → ℕ // ∑ i, f i = q} = (N + q - 1).choose q :=
-- END SPEC
  by
    rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin N) q), Nat.card_eq_fintype_card,
      Sym.card_sym_eq_choose, Fintype.card_fin]

-- MILESTONE (optional: change or delete)
-- `Ω_n(k)` as the size of a `Finset` of tuples, so Finset counting lemmas apply
theorem card_eq (n k : ℕ) :
    Nat.card {f : Fin n → ℕ // ∑ i, f i = k} = (Finset.Nat.antidiagonalTuple n k).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun f => Finset.Nat.mem_antidiagonalTuple.symm)

-- MILESTONE (optional: change or delete)
-- fibre `k`: joint states where `A` holds exactly `k` quanta ≃ (states of A with k) × (states of B with q - k)
theorem fibre_card (a b q k : ℕ) (hk : k ≤ q) :
    {x ∈ Finset.Nat.antidiagonalTuple (a + b) q | ∑ i : Fin a, x (Fin.castAdd b i) = k}.card =
      (Finset.Nat.antidiagonalTuple a k).card * (Finset.Nat.antidiagonalTuple b (q - k)).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij'
    (fun x => (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j)))
    (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.Nat.mem_antidiagonalTuple, Set.mem_setOf_eq,
      Fin.sum_univ_add] at hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.Nat.mem_antidiagonalTuple]
    omega
  · intro p hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.Nat.mem_antidiagonalTuple] at hp
    simp only [Finset.coe_filter, Finset.Nat.mem_antidiagonalTuple, Set.mem_setOf_eq,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    omega
  · intro x _
    exact Fin.append_castAdd_natAdd
  · intro p _
    exact Prod.ext (funext (Fin.append_left _ _)) (funext (Fin.append_right _ _))

-- BEGIN SPEC
theorem thermal_contact (a b q : ℕ) :
    Nat.card {f : Fin (a + b) → ℕ // ∑ i, f i = q} =
      ∑ k ∈ Finset.range (q + 1),
        Nat.card {f : Fin a → ℕ // ∑ i, f i = k} * Nat.card {f : Fin b → ℕ // ∑ i, f i = q - k} :=
-- END SPEC
  by
    simp only [card_eq]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => ∑ i : Fin a, x (Fin.castAdd b i))
      (t := Finset.range (q + 1))]
    · exact Finset.sum_congr rfl fun k hk =>
        fibre_card a b q k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    · intro x hx
      simp only [Finset.mem_coe, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_add] at hx
      simp only [Finset.mem_coe, Finset.mem_range]
      omega

end M163

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (a) is a rewrite chain: turn the subtype into `Sym (Fin N) q`, then count multisets.
    (b) does not need (a). Move every `Nat.card {f // ∑ f = k}` to `(antidiagonalTuple n k).card`.
H2. (b): `simp only [card_eq]`, then split `antidiagonalTuple (a + b) q` into fibres by the quanta
    held by `A`, `x ↦ ∑ i : Fin a, x (Fin.castAdd b i)`; each fibre is counted by `fibre_card`.
    `fibre_card`: build the bijection `x ↦ (x on A's sites, x on B's sites)`, inverse `Fin.append`.
H3. Main: `rw [Finset.card_eq_sum_card_fiberwise (f := fun x => ∑ i : Fin a, x (Fin.castAdd b i))
    (t := Finset.range (q + 1))]`, then `Finset.sum_congr rfl` with `fibre_card`. `fibre_card`:
    `rw [← Finset.card_product]` and `Finset.card_nbij' (fun x => (fun i => x (Fin.castAdd b i),
    fun j => x (Fin.natAdd a j))) (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_`; membership goals close
    with `Fin.sum_univ_add` and `omega`.
-/
