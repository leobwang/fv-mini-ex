/- M163 | Einstein solids in thermal contact | 15-20 min | Nat.card, stars and bars, Fin.append, fiberwise counting, card_nbij', mathlib
GOAL
  A microstate of `n` oscillators is `f : Fin n → ℕ` (quanta per site); `Ω_n(k)` counts those with `k`
  quanta in total. (a) `Ω_N(q) = C(N + q - 1, q)`. (b) Solids `A` (`a` sites) and `B` (`b` sites) sharing
  `q` quanta: `Ω_{a+b}(q) = ∑_{k ≤ q} Ω_a(k) · Ω_b(q - k)`. Two MILESTONEs split (b).

GUIDE
  Entries R1–R26: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
-/
import Mathlib

namespace M163

/- SKELETON · einstein_solid
  One `rw [...]` chain; the last rewrite leaves `C(N + q - 1, q) = C(N + q - 1, q)`, which `rw` closes.
  1. The subtype of multiplicity functions → multisets `Sym (Fin N) q`:
       the equivalence R2, used right to left through R1                    R2 → R1
  2. `Nat.card` → `Fintype.card`:                                            R3
  3. Stars and bars:                                                         R4
  4. `Fintype.card (Fin N)` → `N`:                                           R5
-/
-- BEGIN SPEC
theorem einstein_solid (N q : ℕ) :
    Nat.card {f : Fin N → ℕ // ∑ i, f i = q} = (N + q - 1).choose q :=
-- END SPEC
  sorry

/- SKELETON · card_eq   (MILESTONE, used in step 1 of thermal_contact)
  1. Right side `(antidiagonalTuple n k).card` → `Nat.card ↥(antidiagonalTuple n k)`:  R6
  2. Both sides are now `Nat.card` of a subtype of `Fin n → ℕ`. The two predicates
     `∑ i, f i = k` and `f ∈ antidiagonalTuple n k` agree by R7 (flip it with `.symm`);
     close the goal with R1 applied to R8.                                    R7, R8 → R1
-/
-- MILESTONE (optional: change or delete)
-- `Ω_n(k)` as the size of a `Finset` of tuples, so Finset counting lemmas apply
theorem card_eq (n k : ℕ) :
    Nat.card {f : Fin n → ℕ // ∑ i, f i = k} = (Finset.Nat.antidiagonalTuple n k).card := by
  sorry

/- SKELETON · fibre_card   (MILESTONE, used in step 3 of thermal_contact)
  1. Product of two cards → card of a product Finset:                        R9
  2. A bijection `fibre → product`: R10 with
       i x = (A's sites of x, B's sites of x)    (`Fin.castAdd`, `Fin.natAdd`: R15)
       j p = Fin.append p.1 p.2                  (R16)
     Four goals, in this order:
  3. `i` lands in the product: R11; at `hx` R12 with R7, R15; goal R14 with R7; then R17
  4. `j` lands in the fibre:   R11; at `hp` R14 with R7; goal R12 with R7, R15, R16; then R17
  5. `j (i x) = x`:            R18, R19
  6. `i (j p) = p`:            R18, R20; each component by R21 with R16
-/
-- MILESTONE (optional: change or delete)
-- fibre `k`: joint states where `A` holds exactly `k` quanta ≃ (states of A with k) × (states of B with q - k)
theorem fibre_card (a b q k : ℕ) (hk : k ≤ q) :
    {x ∈ Finset.Nat.antidiagonalTuple (a + b) q | ∑ i : Fin a, x (Fin.castAdd b i) = k}.card =
      (Finset.Nat.antidiagonalTuple a k).card * (Finset.Nat.antidiagonalTuple b (q - k)).card := by
  sorry

/- SKELETON · thermal_contact
  Prove the MILESTONEs first: `card_eq` (step 1) and `fibre_card` (step 3). Part (a) is not used.
  1. Every `Nat.card {f // …}` → `(antidiagonalTuple n k).card`, also those under `∑ k`:
       `card_eq` as a rewrite rule                                           R22
  2. Split `antidiagonalTuple (a + b) q` into fibres by A's quanta
       f x = ∑ i : Fin a, x (Fin.castAdd b i),   t = Finset.range (q + 1):   R23
     This leaves the sum goal and the side goal `Set.MapsTo f ↑s ↑t`.
  3. Sum goal, term by term: R24, then `intro k hk`; the term at `k` is
     `fibre_card a b q k _`, with `k ≤ q` from `hk : k ∈ range (q + 1)`:     R25 → R26
  4. Side goal: R11; at `hx` R13, R7, R15; goal R13, R25; then R17
-/
-- BEGIN SPEC
theorem thermal_contact (a b q : ℕ) :
    Nat.card {f : Fin (a + b) → ℕ // ∑ i, f i = q} =
      ∑ k ∈ Finset.range (q + 1),
        Nat.card {f : Fin a → ℕ // ∑ i, f i = k} * Nat.card {f : Fin b → ℕ // ∑ i, f i = q - k} :=
-- END SPEC
  sorry

end M163

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. (a) needs no induction: it is one rewrite chain through multisets (`Sym (Fin N) q`), then stars and
    bars. (b) does not use (a). First turn every `Nat.card {f // ∑ i, f i = k}` into the size of a
    Finset (`card_eq`), so that Finset counting lemmas apply.
H2. (b): split `antidiagonalTuple (a + b) q` into fibres by the quanta held by `A`,
    `x ↦ ∑ i : Fin a, x (Fin.castAdd b i)`; each fibre is counted by `fibre_card`. `fibre_card`: write
    the product of cards as the card of a product, then give the bijection `x ↦ (x on A's sites, x on
    B's sites)` with inverse `Fin.append`. Its membership goals close with `Fin.sum_univ_add` and
    `omega`; its inverse goals with `Fin.append_castAdd_natAdd` and `Fin.append_left/right`.
H3. (a): `rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin N) q)]`, then R3, R4, R5.
    Main: `simp only [card_eq]`, then `rw [Finset.card_eq_sum_card_fiberwise (f := fun x => ∑ i : Fin a,
    x (Fin.castAdd b i)) (t := Finset.range (q + 1))]`, then `Finset.sum_congr rfl` with `fibre_card`.
    `fibre_card`: `rw [← Finset.card_product]` and `refine Finset.card_nbij' (fun x => (fun i => x
    (Fin.castAdd b i), fun j => x (Fin.natAdd a j))) (fun p => Fin.append p.1 p.2) ?_ ?_ ?_ ?_`.
-/
