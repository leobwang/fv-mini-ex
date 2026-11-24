/- E064 | simp_rw | 2 min | simp_rw, rewriting under binders, mathlib
GOAL
  Rewrite inside binders (`fun n => …`, `∀ n, …`, `∑ i ∈ s, …`), where `rw` cannot reach
  because the term mentions the bound variable.

REFERENCE
  example (f : ℕ → ℕ) (h : ∀ n, f n = n) : (fun n => f n + 1) = fun n => n + 1 := by simp_rw [h]
  example (n : ℕ) : ∑ i ∈ Finset.range n, (i + 0) = ∑ i ∈ Finset.range n, i := by simp_rw [add_zero]
  #check two_mul    -- 2 * a = a + a
  #check zero_add   -- 0 + a = a
  #check mul_add    -- a * (b + c) = a * b + a * c
  #check mul_one    -- a * 1 = a
  `simp_rw [h₁, ← h₂]` = `simp only [h₁]` then `simp only [← h₂]`: each rule rewrites everywhere, under binders too.
BANNED: simp, simp_all, simpa, norm_num, ring, ring_nf, abel, abel_nf, noncomm_ring, push_cast, norm_cast, aesop, grind, funext, ext, congr, conv, forall_congr', Finset.sum_congr, Finset.sum_add_distrib, Finset.mul_sum, fun, intro, intros, rintro, constructor, exact?, apply?, try?
NOTE: `fun`, `intro`, `funext`, `constructor` are banned so you rewrite under the binder instead of opening it.
  `ring`, `abel`, `push_cast` are banned too: they also normalize under binders, which would skip the lesson.
-/
import Mathlib

namespace E064

-- BEGIN SPEC
theorem fun_rw (f : ℕ → ℕ) (h : ∀ n, f n = n + 1) :
    (fun n => f n + f n) = fun n => 2 * n + 2 :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem forall_rw (p : ℕ → Prop) : (∀ n, p (0 + n)) ↔ ∀ n, p n :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem sum_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 * i = ∑ i ∈ Finset.range n, (i + i) :=
-- END SPEC
  sorry

end E064

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Try `rw [h]` on `fun_rw` and read the error: `n` is bound by the `fun`. `simp_rw` gets under it.
H2. `fun_rw`: after `h` the body is `n + 1 + (n + 1)`; turn it into `2 * n + 2` with more rules in the same
    `simp_rw`, using `two_mul` right-to-left. The other two need one rule each.
H3. `fun_rw`: `simp_rw [h, ← two_mul, ?, ?]`, where the two holes are REFERENCE rules that turn `2 * (n + 1)`
    into `2 * n + 2`. `sum_two`: `simp_rw [two_mul]`.
-/
