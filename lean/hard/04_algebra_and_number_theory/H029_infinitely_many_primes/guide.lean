/- Guide for H029 (Infinitely many primes).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`G : Prop` is an arbitrary goal and `P`/`Q` are arbitrary predicates. A hypothesis `g` or `h` in an
entry is only there to finish the example; it shows what the step produced.
Part W: worked combinations on facts that are NOT the exercise's.
Assumed: Lean basics (E001–E033).
-/
import Mathlib

namespace H029Guide

/-! # Part R · Reference entries -/

/-! ## Strong induction and case splits -/

/-! ### R1. `induction n using Nat.strong_induction_on` · goal `Q n` → `Q n` with the IH for every `m < n`
`Nat.strong_induction_on : (∀ n, (∀ m < n, Q m) → Q n) → Q n`. A hypothesis that mentions `n`
(here `hn : 2 ≤ n`) is put back after the induction and also enters the IH (`2 ≤ m → Q m`).
Without `with` Lean invents the names `n✝ a✝`; `rename_i k ih` names them. The usual form names them at
once: `induction n using Nat.strong_induction_on with | _ k ih => …` (see W1). -/
example (Q : ℕ → Prop) (step : ∀ n, (∀ m < n, 2 ≤ m → Q m) → 2 ≤ n → Q n) (n : ℕ) (hn : 2 ≤ n) :
    Q n := by
  induction n using Nat.strong_induction_on
  rename_i k ih
  exact step k ih hn

/-! ### R2. `by_cases hA : A` · goal list: one goal → two, with `hA : A` and with `hA : ¬A` -/
example (A G : Prop) (h1 : A → G) (h2 : ¬A → G) : G := by
  by_cases hA : A
  exact h1 hA
  exact h2 hA

/-! ### R3. `exact ⟨x, ha, hb⟩` · closes `∃ y, A y ∧ B y`: witness first, then one proof per conjunct -/
example {α : Type} (A B : α → Prop) (x : α) (ha : A x) (hb : B x) : ∃ y, A y ∧ B y := by
  exact ⟨x, ha, hb⟩

/-! ### R4. `dvd_refl a : a ∣ a` · context gains `a ∣ a` (every number divides itself) -/
example {α : Type} [Monoid α] (a : α) (G : Prop) (g : a ∣ a → G) : G := by
  have h := dvd_refl a
  exact g h

/-! ## Getting a divisor out of `¬ Nat.Prime n` -/

/-! ### R5. `obtain ⟨x, ha, hb, hc⟩ : T := e` · context gains `x` and one hypothesis per conjunct of `T`
You state `T` yourself; `e` (often `by …`) proves it. -/
example {α : Type} (A B C : α → Prop) (G : Prop) (e : ∃ x, A x ∧ B x ∧ C x)
    (g : ∀ x, A x → B x → C x → G) : G := by
  obtain ⟨x, ha, hb, hc⟩ : ∃ x, A x ∧ B x ∧ C x := e
  exact g x ha hb hc

/-! ### R6. `rw [Nat.prime_def] at hp` · context: `Nat.Prime n` → `2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n` -/
example (n : ℕ) (hp : ¬Nat.Prime n) (G : Prop)
    (g : ¬(2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n) → G) : G := by
  rw [Nat.prime_def] at hp
  exact g hp

/-! ### R7. `push Not at h` · context: pushes `¬` inward (`¬(A ∧ B)` → `A → ¬B`, `¬∀` → `∃ ¬`, `¬ a ≤ b` → `b < a`) -/
example (n : ℕ) (hp : ¬(2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n)) (G : Prop)
    (g : (2 ≤ n → ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n) → G) : G := by
  push Not at hp
  exact g hp

example (a b : ℕ) (h : ¬a ≤ b) (G : Prop) (g : b < a → G) : G := by
  push Not at h
  exact g h

/-! ### R8. `rintro rfl` · goal `m ≠ 0` (that is `m = 0 → False`) → `False`, with `m` replaced by `0` everywhere -/
example (m : ℕ) (Q : ℕ → Prop) (hm : Q m) (h0 : ¬Q 0) : m ≠ 0 := by
  rintro rfl
  exact h0 hm

/-! ### R9. `simp at h` · context: `h : 0 ∣ n` → `h : n = 0` (lemma `zero_dvd_iff`) -/
example (n : ℕ) (h : 0 ∣ n) (G : Prop) (g : n = 0 → G) : G := by
  simp at h
  exact g h

/-! ### R10. `omega` · closes linear arithmetic over `ℕ`/`ℤ` (`+`, `-`, `≤`, `<`, `=`, `≠`, numerals), using the hypotheses -/
example (n : ℕ) (h : n = 0) (hn : 2 ≤ n) : False := by
  omega

example (n m : ℕ) (hn : 2 ≤ n) (hm : m ≠ 0) (hm1 : m ≠ 1) : 0 < n ∧ 2 ≤ m := by
  omega

/-! ## From a divisor to a smaller number -/

/-! ### R11. `Nat.le_of_dvd : 0 < n → m ∣ n → m ≤ n` · context gains `m ≤ n` -/
example (m n : ℕ) (hn : 0 < n) (h : m ∣ n) (G : Prop) (g : m ≤ n → G) : G := by
  have hle := Nat.le_of_dvd hn h
  exact g hle

/-! ### R12. `Nat.lt_of_le_of_ne : m ≤ n → ¬m = n → m < n` · context gains `m < n` (`m ≠ n` is `¬m = n`) -/
example (m n : ℕ) (h1 : m ≤ n) (h2 : m ≠ n) (G : Prop) (g : m < n → G) : G := by
  have hlt := Nat.lt_of_le_of_ne h1 h2
  exact g hlt

/-! ### R13. Use the IH: `ih m hlt h2` · context gains `Q m` (give the smaller number, then each premise) -/
example (Q : ℕ → Prop) (n m : ℕ) (ih : ∀ k < n, 2 ≤ k → Q k) (hlt : m < n) (h2 : 2 ≤ m)
    (G : Prop) (g : Q m → G) : G := by
  have hm := ih m hlt h2
  exact g hm

/-! ### R14. `dvd_trans : a ∣ b → b ∣ c → a ∣ c` · context gains `a ∣ c` -/
example {α : Type} [Semigroup α] (a b c : α) (h1 : a ∣ b) (h2 : b ∣ c) (G : Prop)
    (g : a ∣ c → G) : G := by
  have h := dvd_trans h1 h2
  exact g h

/-! ## Euclid's argument -/

/-! ### R15. `Nat.factorial_pos n : 0 < n.factorial` · context gains `0 < n !`
`n.factorial` is `n !`; Lean prints `n.factorial` unless `open Nat` is active. -/
example (n : ℕ) (G : Prop) (g : 0 < n.factorial → G) : G := by
  have hf := Nat.factorial_pos n
  exact g hf

/-! ### R16. `refine ⟨x, ?_, hb⟩` · goal `∃ y, A y ∧ B y` → `A x` (witness and `B x` given now) -/
example {α : Type} (A B : α → Prop) (x : α) (ha : A x) (hb : B x) : ∃ y, A y ∧ B y := by
  refine ⟨x, ?_, hb⟩
  exact ha

/-! ### R17. `by_contra hA` · goal `A` → `False`, context gains `hA : ¬A` -/
example (A : Prop) (h : ¬A → False) : A := by
  by_contra hA
  exact h hA

/-! ### R18. `Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n !` · context gains `m ∣ n.factorial` -/
example (m n : ℕ) (hm : 0 < m) (hle : m ≤ n) (G : Prop) (g : m ∣ n.factorial → G) : G := by
  have h := Nat.dvd_factorial hm hle
  exact g h

/-! ### R19. `hp.pos` (`Nat.Prime.pos : Nat.Prime p → 0 < p`) · context gains `0 < p`
`hp.pos` is dot notation: `hp : Nat.Prime p`, so it means `Nat.Prime.pos hp`. -/
example (p : ℕ) (hp : Nat.Prime p) (G : Prop) (g : 0 < p → G) : G := by
  have h := hp.pos
  exact g h

/-! ### R20. `hlt.le` (`LT.lt.le : a < b → a ≤ b`) · context gains `a ≤ b` -/
example (a b : ℕ) (hlt : a < b) (G : Prop) (g : a ≤ b → G) : G := by
  have h := hlt.le
  exact g h

/-! ### R21. `(Nat.dvd_add_right h).mp` · `Nat.dvd_add_right : k ∣ m → (k ∣ m + n ↔ k ∣ n)` · context gains `k ∣ n`
`.mp` uses an `↔` left to right. -/
example (k m n : ℕ) (h : k ∣ m) (hs : k ∣ m + n) (G : Prop) (g : k ∣ n → G) : G := by
  have h' := (Nat.dvd_add_right h).mp hs
  exact g h'

/-! ### R22. `hp.one_lt` (`Nat.Prime.one_lt : Nat.Prime p → 1 < p`) · context gains `1 < p` -/
example (p : ℕ) (hp : Nat.Prime p) (G : Prop) (g : 1 < p → G) : G := by
  have h := hp.one_lt
  exact g h

/-! ### R23. `h.ne'` (`LT.lt.ne' : a < b → b ≠ a`) · context gains `b ≠ a` -/
example (a b : ℕ) (h : a < b) (G : Prop) (g : b ≠ a → G) : G := by
  have h' := h.ne'
  exact g h'

/-! ### R24. `Nat.dvd_one.mp` · `Nat.dvd_one : n ∣ 1 ↔ n = 1` · context gains `n = 1` -/
example (n : ℕ) (h : n ∣ 1) (G : Prop) (g : n = 1 → G) : G := by
  have h' := Nat.dvd_one.mp h
  exact g h'

/-! # Part W · Worked combinations (not the exercise's facts) -/

/-! ### W1. Strong induction stepping down by 2 (R1, R2, R5, R10, R13) -/
example (Q : ℕ → Prop) (h0 : Q 0) (h1 : Q 1) (step : ∀ k, Q k → Q (k + 2)) (n : ℕ) : Q n := by
  induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : 2 ≤ n
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        exact step k (ih k (by omega))
      · by_cases hz : n = 0
        · rw [hz]
          exact h0
        · have h1' : n = 1 := by omega
          rw [h1']
          exact h1

/-! ### W2. A divisor of `n + 1` other than `n + 1` is at most `n` (R11, R12, R10) -/
example (d n : ℕ) (h : d ∣ n + 1) (hne : d ≠ n + 1) : d ≤ n := by
  have hlt := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) h) hne
  omega

/-! ### W3. A prime cannot divide two consecutive numbers `a` and `a + 1` (R21, R24, R22, R23) -/
example (p a : ℕ) (hp : Nat.Prime p) (h : p ∣ a) (h' : p ∣ a + 1) : False := by
  have h1 : p ∣ 1 := (Nat.dvd_add_right h).mp h'
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

end H029Guide
