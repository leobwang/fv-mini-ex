/- Guide for H042 (Cauchy ⇔ convergent in ℝ).
Part R: one reference entry per tactic or library lemma the exercise needs, stated with typed
placeholders. Put the cursor before and after the step to see the proof state change in the infoview.
`P` stands for "the rest of your goal": the step changes only the part shown inside `P (…)`. A
hypothesis `h` or `k` in an entry is only there to finish the example; it shows what the goal became.
`G : Prop` is an arbitrary goal; `k : … → G` consumes a fact that the step added to the context.
Part W: worked combinations on objects that are NOT the exercise's (sums of limits, an interval).
Assumed: Lean basics (E001–E033). New: Mathlib's real numbers `ℝ`, absolute value `|x|`, sets
`{x | Q x}`, `BddAbove`, `Set.Nonempty`, `sSup`, and the tactics `obtain`, `rintro`, `set`, `calc`,
`positivity`, `linarith`, `ring_nf`.
The import lines are the exercise's frozen imports; its BANNED line forbids adding more.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace H042Guide

/-! # Part R · Reference entries -/

/-! ## ε–N statements: taking them apart and building them -/

/-- A toy definition whose body is an `∀ ε > 0, …`, like the exercise's two definitions. -/
def ForallPos (Q : ℝ → Prop) : Prop := ∀ ε > 0, Q ε

/-! ### R1. `intro ε hε` · goal `∀ ε > 0, Q ε` (even behind a `def`) → context gains `ε`, `hε` -/
example (Q : ℝ → Prop) (h : ∀ e : ℝ, 0 < e → Q e) : ForallPos Q := by
  intro ε hε
  exact h ε hε

/-- A toy definition with the shape "for every `ε > 0` there is an `N`". -/
def SomeIndex (Q : ℝ → ℕ → Prop) : Prop := ∀ ε > 0, ∃ N : ℕ, Q ε N

/-! ### R2. `obtain ⟨N, hN⟩ := h x hx` · apply `h` (a `def` unfolds when applied), split the `∃`
· context gains `N`, `hN` -/
example (Q : ℝ → ℕ → Prop) (h : SomeIndex Q) (x : ℝ) (hx : x > 0) (G : Prop)
    (k : ∀ N, Q x N → G) : G := by
  obtain ⟨N, hN⟩ := h x hx
  exact k N hN

/-! ### R3. `positivity` · closes `0 < e` (or `e > 0`) for `e` built from positive pieces -/
example (x : ℝ) (hx : x > 0) : x / 3 > 0 := by
  positivity

/-! ### R4. `refine ⟨K, fun m hm n hn => ?_⟩` · goal `∃ N, ∀ m ≥ N, ∀ n ≥ N, P m n`
→ witness `K` given, context gains `m hm n hn`, goal is the body -/
example (P : ℕ → ℕ → Prop) (K : ℕ) (h : ∀ m n, P m n) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, P m n := by
  refine ⟨K, fun m hm n hn => ?_⟩
  exact h m n

/-! ### R5. `have h1 := hK m hm` · instantiate a `∀ n ≥ K, …` hypothesis · context gains `h1` -/
example (Q : ℕ → Prop) (K m : ℕ) (hK : ∀ n ≥ K, Q n) (hm : m ≥ K) : Q m := by
  have h1 := hK m hm
  exact h1

/-! ## Chains of (in)equalities and the triangle inequality -/

/-! ### R6. `calc` · goal `a < d` closed by a chain `a = b`, `b ≤ c`, `c < d` -/
example (a b c d : ℝ) (h1 : a = b) (h2 : b ≤ c) (h3 : c < d) : a < d := by
  calc a = b := h1
    _ ≤ c := h2
    _ < d := h3

/-! ### R7. `ring_nf` · closes `f (x - y) = f (x - z + (z - y))`: it normalises ring expressions
even inside a function such as `|·|` -/
example (f : ℝ → ℝ) (x y z : ℝ) : f (x - y) = f (x - z + (z - y)) := by
  ring_nf

/-! ### R8. `abs_add_le` · `|a + b| ≤ |a| + |b|` (triangle inequality) · context gains it -/
example (x y : ℝ) (G : Prop) (k : |x + y| ≤ |x| + |y| → G) : G := by
  have h := abs_add_le x y
  exact k h

/-! ### R9. `abs_sub_comm` · `|a - b| = |b - a|`; `rw [abs_sub_comm x]` flips only `|x - _|` · goal -/
example (x y : ℝ) (P : ℝ → Prop) (h : P |y - x|) : P |x - y| := by
  rw [abs_sub_comm x]
  exact h

/-! ### R10. `add_lt_add` · `a < b → c < d → a + c < b + d` · closes the goal -/
example (a b c d : ℝ) (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  exact add_lt_add h1 h2

/-! ## Sets given by a property -/

/-! ### R11. `Set.mem_setOf_eq` · `x ∈ {y | Q y}` is by definition `Q x` · goal -/
example (Q : ℝ → Prop) (x : ℝ) (h : Q x) : x ∈ {y : ℝ | Q y} := by
  rw [Set.mem_setOf_eq]
  exact h

/-! ### R12. `le_rfl` · `a ≤ a`; it proves `K ≥ K` when you instantiate at `n := K` · context -/
example (Q : ℕ → Prop) (K : ℕ) (hK : ∀ n ≥ K, Q n) (G : Prop) (k : Q K → G) : G := by
  have h := hK K le_rfl
  exact k h

/-! ### R13. `abs_lt` · `|a| < b ↔ -b < a ∧ a < b`; `rw [abs_lt] at h ⊢` · context and goal -/
example (x b y c : ℝ) (h : |x| < b) (k : -b < x ∧ x < b → -c < y ∧ y < c) : |y| < c := by
  rw [abs_lt] at h ⊢
  exact k h

/-! ### R14. `linarith` · closes a linear (in)equality from hypotheses, `∧`-hypotheses included -/
example (x y z : ℝ) (h1 : -1 < x - y ∧ x - y < 1) (h2 : y ≤ z) : x < z + 1 := by
  linarith

/-! ### R15. `rintro x ⟨M, hM⟩` · goal `∀ x ∈ {x | ∃ M, Q x M}, G x` → context gains `x M hM` -/
example (Q : ℝ → ℕ → Prop) (G : ℝ → Prop) (k : ∀ x M, Q x M → G x) :
    ∀ x ∈ {x : ℝ | ∃ M : ℕ, Q x M}, G x := by
  rintro x ⟨M, hM⟩
  exact k x M hM

/-! ### R16. `le_max_left`, `le_max_right` · `a ≤ max a b`, `b ≤ max a b` · context -/
example (M N : ℕ) (Q R : ℕ → Prop) (hM : ∀ n ≥ M, Q n) (hN : ∀ n ≥ N, R n) (G : Prop)
    (k : Q (max M N) → R (max M N) → G) : G := by
  have h1 := hM (max M N) (le_max_left M N)
  have h2 := hN (max M N) (le_max_right M N)
  exact k h1 h2

/-! ## Iff, local definitions, least upper bounds -/

/-! ### R17. `constructor` on `A ↔ B` · goal list: `A → B`, then `B → A` -/
example (A B : Prop) (hab : A → B) (hba : B → A) : A ↔ B := by
  constructor
  exacts [hab, hba]

/-! ### R18. `set S : Set ℝ := e` · context gains `S : Set ℝ := e`; every `e` in the goal → `S` -/
example (Q : ℝ → Prop) (G : Set ℝ → Prop) (k : ∀ T, G T) : G {x | Q x} := by
  set S : Set ℝ := {x | Q x}
  exact k S

/-! ### R19. `one_pos` · `0 < 1`; it proves `1 > 0` when you instantiate at `ε := 1` · context -/
example (Q : ℝ → Prop) (h : ∀ e : ℝ, e > 0 → Q e) (G : Prop) (k : Q 1 → G) : G := by
  have h1 := h 1 one_pos
  exact k h1

/-! ### R20. `Set.Nonempty` · `s.Nonempty` is `∃ x, x ∈ s`: prove it with `⟨_, hx⟩` -/
example (s : Set ℝ) (x : ℝ) (hx : x ∈ s) : s.Nonempty := by
  exact ⟨_, hx⟩

/-! ### R21. `BddAbove` · `BddAbove s` is "some `b` is ≥ every element": prove it with `⟨b, hb⟩` -/
example (s : Set ℝ) (b : ℝ) (hb : ∀ x ∈ s, x ≤ b) : BddAbove s := by
  exact ⟨b, hb⟩

/-! ### R22. `le_csSup` · `BddAbove s → a ∈ s → a ≤ sSup s` · context gains it -/
example (s : Set ℝ) (x : ℝ) (hb : BddAbove s) (hx : x ∈ s) (G : Prop)
    (k : x ≤ sSup s → G) : G := by
  have h := le_csSup hb hx
  exact k h

/-! ### R23. `csSup_le` · `s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a` · context gains it -/
example (s : Set ℝ) (b : ℝ) (hne : s.Nonempty) (hb : ∀ x ∈ s, x ≤ b) (G : Prop)
    (k : sSup s ≤ b → G) : G := by
  have h := csSup_le hne hb
  exact k h

/-! # Part W · Worked combinations (not the exercise's objects) -/

/-! ### W1. The ε/2 split for a sum: R6 with R7, R8, R10 and `ring` -/
example (x y p q e : ℝ) (hx : |x - p| < e / 2) (hy : |y - q| < e / 2) :
    |(x + y) - (p + q)| < e := by
  calc |(x + y) - (p + q)| = |(x - p) + (y - q)| := by ring_nf
    _ ≤ |x - p| + |y - q| := abs_add_le _ _
    _ < e / 2 + e / 2 := add_lt_add hx hy
    _ = e := by ring

/-! ### W2. A sandwich turned into an absolute value: R13, then `constructor <;> linarith` (R14) -/
example (c t y e : ℝ) (h1 : c - e ≤ t) (h2 : t ≤ c + e) (hy : |y - c| < e) : |y - t| < 2 * e := by
  rw [abs_lt] at hy ⊢
  constructor <;> linarith

/-! ### W3. `sSup` of `{x | x < 1}` is at most `1` and at least `0`: R11, R20, R21, R22, R23 -/
example : sSup {x : ℝ | x < 1} ≤ 1 ∧ 0 ≤ sSup {x : ℝ | x < 1} := by
  set T : Set ℝ := {x | x < 1}
  have hne : T.Nonempty := ⟨0, by rw [Set.mem_setOf_eq]; norm_num⟩
  -- `le_of_lt : a < b → a ≤ b`; `hx : x ∈ T` is by definition `x < 1` (R11)
  have hub : ∀ x ∈ T, x ≤ 1 := fun x hx => le_of_lt hx
  have hbdd : BddAbove T := ⟨1, hub⟩
  exact ⟨csSup_le hne hub, le_csSup hbdd (by rw [Set.mem_setOf_eq]; norm_num)⟩

end H042Guide
