# Lean 4 reference (fv-mini-ex)

Lean 4.32.0 + Mathlib v4.32.0. Cumulative cheat sheet for the Lean track, grouped by topic.
Numbers in the last column are the problems that introduce or lean on an entry. Every name below
was `#check`ed at the pinned versions or is used in a passing reference solution.

Run one problem: `./check lean E07` (add `-v` for Lean's full output). In the editor, put the
cursor after a tactic to see the goal. `sorry` is a hole; the file compiles but the check says TODO.

## 1. Commands and files

| Syntax | Meaning | IDs |
|---|---|---|
| `def f (n : Nat) : Nat := n + 1` | definition | E01 |
| `theorem t : P := proof` / `example : P := proof` | named / anonymous proof | E01 |
| `#eval f 3`, `#check Nat.add_comm`, `#check @Nat.le_trans` | run, show a type (`@`: with implicit args) | E01, E23 |
| `by tac₁; tac₂` or one tactic per line | tactic block | E03 |
| `namespace X … end X` | scope names (`X.foo`) | E15 |
| `open Finset` / `open Function` | drop the prefix | E42, M37 |
| `import Mathlib` (first command of the file) | Mathlib problems only | E34 |
| `exact?`, `apply?` | library search; paste the suggestion | E33 |

## 2. Definitions and data

| Syntax | Meaning | IDs |
|---|---|---|
| `def f : Nat → Nat \| 0 => 1 \| n + 1 => (n + 1) * f n` | equations by pattern matching | E02 |
| `match n with \| 0 => a \| k + 1 => b` | match on an argument; `match xs, ys with` for two | E02, M28 |
| `fun \| [] => none \| x :: _ => some x` | pattern-matching lambda | E32 |
| `if h : c then a else b` / `if c then a else b` | conditionals (c decidable) | E12, E32 |
| `termination_by n` (after the body) | well-founded recursion on a measure | E26 |
| `decreasing_by` + one goal per recursive call | prove the measure decreases yourself | M06 |
| `structure P where x : Nat  y : Nat`; `⟨1, 2⟩`, `{ x := 1, y := 2 }`, `{ p with x := 0 }`, `p.x` | records | E17 |
| `@[ext] structure V2 …` → `V2.ext : p.x = q.x → p.y = q.y → p = q` | extensionality lemma | E19 |
| `inductive Color where \| red \| green deriving DecidableEq` | enumerations, trees, ASTs | E18, M15, M16 |
| `inductive Vec (α : Type) : Nat → Type \| nil : Vec α 0 \| cons … : Vec α (n+1)` | indexed families | M11 |
| `inductive Ev : Nat → Prop \| zero : Ev 0 \| step n : Ev n → Ev (n+2)` | inductive predicates / relations | M07, M08, H03, H04, H05 |
| `instance instAddV2 : Add V2 := ⟨fun p q => …⟩` | type-class instance (`p + q`) | E19 |
| `class C (α : Type) where op : α → α → α; law : ∀ a, …` | class with proof fields | M12 |
| `instance : DecidablePred P := fun n => decidable_of_iff Q proof` | make `decide` work on `P` | M13 |
| `abbrev EvenNat := {n : Nat // n % 2 = 0}`; `⟨v, proof⟩`, `x.val`, `x.property`, `Subtype.ext` | subtypes | M10 |
| `Fin n`: `⟨v, proof⟩`, `i.val`, `i.isLt`, `Fin.ext`, `Fin.last n`, `i.castSucc` | bounded naturals | M09 |
| `Id.run do let mut s := 0; for x in xs do s := s + x; return s` | imperative loop (simp turns it into `List.foldl`) | M14 |
| `Except String Int`: `pure`, `throw e`, `let x ← e`; values `.ok v` / `.error e` | error monad | M19 |
| `Option`: `some`, `none`, `o.map f`, `o.getD d`, `xs[i]?` | partial results, safe indexing | E16, E32, M20 |
| `Array`: `a[i]` (bound by omega), `a[i]?`, `a.size`, `a.swap i j` | arrays | M23, H06 |
| `Set α`: `{x \| p x}`, `A ∩ B`, `A ∪ B`, `Aᶜ`, `f '' A`, `f ⁻¹' B`, `⋂₀ S`, `⋃₀ S` | sets (Mathlib) | E40, M38, H09 |
| `∑ i ∈ Finset.range n, f i`; `(s.filter p).card` | finite sums and counts (Mathlib) | E42, M32, M44 |

## 3. Logic: core tactics

| Goal / hypothesis | Tactic or term | IDs |
|---|---|---|
| `P → Q` | `intro h` / `fun h => …` | E03, E04 |
| goal matches hyp's conclusion | `apply h` (goals for premises), `exact h a` | E03 |
| `P ∧ Q` | `constructor`, `⟨hp, hq⟩`; use: `h.1`, `obtain ⟨hp, hq⟩ := h` | E04, E05 |
| `P ↔ Q` | `constructor`; use: `h.mp`, `h.mpr` | E05 |
| `P ∨ Q` | `left`/`right`, `Or.inl`; use: `cases h with \| inl h => … \| inr h => …`, `rcases h with h \| h` | E06 |
| `∃ x, P x` | `⟨w, proof⟩`, `exists w` (core), `use w` (Mathlib); use: `obtain ⟨x, hx⟩ := h` | E07, E41 |
| `¬P` (= `P → False`) | `intro h`; use: `h hp : False`, `absurd hp h`, `contradiction`, `exfalso` | E08 |
| intro + destructure | `rintro ⟨x, hx, rfl⟩` (`rfl` pattern substitutes) | E05, E25 |
| case split on a Prop | `by_cases h : a ≤ b` | E13 |
| intermediate facts | `have h : T := …`, `suffices h : T by …`, `show T` | E21 |
| chains | `calc a < b := h₁` / `_ ≤ c := h₂` | E20 |
| function equality | `funext x` | E22 |
| implicit args | `f (n := 3)`, `@f 3`, `@h 3` for `h : ∀ {n}, …` | E23 |
| several goals | `refine ⟨?_, ?_⟩`, `t <;> s`, `all_goals s`, `first \| t₁ \| t₂`, `assumption` | E31 |
| constructors | `injection h with h₁ h₂`, `nofun`, `intro h; nomatch h` | E29 |
| unfold a `def` | `unfold f` (also `at h`), `simp only [f]`, `rw [f]` | E12, E26, E30 |

## 4. Rewriting and simplification

| Syntax | Meaning | IDs |
|---|---|---|
| `rw [h]`, `rw [← h]`, `rw [h] at h'`, `rw [h₁, h₂]` | rewrite left→right / right→left / in a hypothesis | E09 |
| `rw [show a = b by omega]` | rewrite with a one-off fact | M01 |
| `simp`, `simp only [l₁, l₂]`, `simp [f, h]`, `simp at h`, `simp_all` | simplifier | E10, E16 |
| `@[simp] theorem …`, `attribute [simp] foo`, `simp [-foo]` | manage the simp set | E27 |
| `split` (goal has `if`/`match`), `split at h`; `rename_i h` | case on a conditional | E12, M15, M26 |
| `if_pos h`, `if_neg h` | pick an `if` branch with `rw` | E26 |
| `conv => lhs; rw [h]` | rewrite only one side | M30 |
| `congr 1` | `f a = f b` from `a = b` | M24, M25 |

## 5. Decision procedures and automation

| Tactic | Proves | IDs |
|---|---|---|
| `rfl` | both sides compute to the same value | E01 |
| `decide` | closed decidable statements (incl. bounded `∀ n < 10`, `ZMod n`) | E01, M13, M41 |
| `omega` | linear arithmetic over `Nat`/`Int` (`+`, `-`, literal `*`, `/`, `%`, `min`, `max`, casts); `x*y` is an atom | E11, E14 |
| `grind` | congruence + linear arithmetic + ring normalisation + case splits; mixes Prop atoms (`x ∈ l`) with arithmetic | E28, M16, M21 |
| `ring` (Mathlib) | commutative-ring identities (ignores hypotheses) | E34 |
| `linarith [extra facts]` | linear consequences over ordered fields | E35 |
| `nlinarith [sq_nonneg (a - b)]` | linarith + products of hypotheses | M34, M40 |
| `norm_num` | numeric facts, `Nat.Prime 97` | E36, E43 |
| `positivity` | `0 < e`, `0 ≤ e`, `e ≠ 0` | E37 |
| `gcongr` | `f a ≤ f b` from `a ≤ b` (same shape) | E44 |
| `field_simp` (`at h`) | clear denominators (needs `≠ 0` facts) | E45 |
| `push Not` (`at h`) | move `¬` inward (`push_neg` is the deprecated name) | E41 |
| `push_cast`, `exact_mod_cast h` | move casts inward / prove modulo casts | M34, M35, M41 |

## 6. Induction and recursion

| Syntax | Use | IDs |
|---|---|---|
| `induction n with \| zero => … \| succ n ih => …` | Nat | E14 |
| `induction xs with \| nil => … \| cons x xs ih => …` | List | E15 |
| `induction n generalizing xs` | IH for every `xs` (accumulators, two-argument recursion) | M01, M02, M03 |
| `induction n using Nat.strongRecOn with \| _ n ih => …` (core), `Nat.strong_induction_on` (Mathlib) | strong induction | M05, H07, H08 |
| `induction h with …` on `h : Ev n` | induction on a derivation | M07, M08 |
| `cases h` on `h : Ev (n + 2)` | inversion (impossible rules disappear) | M07, H03 |
| `generalize hw : Com.while .tt c = w at h` then `induction h` | index is not a variable | H04, H05 |
| `fun_induction f x y with \| case1 … \| case2 … ih => …` | follow `f`'s recursion (wf defs, `if`s, matches) | M06, M22, M23, M25, M27 |

## 7. Library names by area

| Area | Names | IDs |
|---|---|---|
| Nat arithmetic | `Nat.add_comm`, `Nat.add_zero`, `Nat.mul_one`, `Nat.add_mul`, `Nat.mul_add`, `Nat.le_trans`, `Nat.succ_ne_zero`, `Nat.le_of_dvd`, `Nat.mod_lt`, `Nat.div_mul_le_self`, `Nat.le_mul_self`, `Nat.dvd_mod_iff`, `Nat.dvd_refl`, `Nat.dvd_zero` | E09–M27 |
| Nat powers | `Nat.pow_two`, `Nat.pow_mul`, `Nat.pow_succ'` | M25 |
| Int | `Int.add_comm` | E19 |
| Lists | `List.length_append`, `List.length_map`, `List.length_reverse`, `List.append_nil`, `List.append_assoc`, `List.reverse_cons`, `List.reverse_append`, `List.map_map`, `List.filter_map`, `List.filter_cons`, `List.length_filter_le`, `List.foldl_cons`, `List.foldl_append`, `List.take_append_drop`, `List.take_succ_cons`, `List.sum_cons` | E24, M03, M31, H02 |
| List membership | `List.mem_cons`, `List.mem_append`, `List.mem_map`, `List.mem_cons_self`, `List.mem_cons_of_mem` | E25, M21 |
| List indexing | `List.getElem?_reverse`, `List.ext_getElem?`, `List.getElem?_eq_none`, `List.getElem?_map`, `List.append_eq_nil_iff`, `List.append_eq_cons_iff` | M03, M30, M31, H05 |
| Permutations | `List.Perm.refl`, `.cons`, `.trans`, `.swap`, `.append`, `.mem_iff`, `.length_eq`, `List.perm_middle`, `List.filter_append_perm` | M17, M18, M28, H02 |
| Pairwise / sorted | `List.Pairwise.cons`, `List.Pairwise.of_cons`, `List.rel_of_pairwise_cons`, `List.pairwise_cons`, `List.pairwise_singleton` | M22, M28, M29 |
| Option / Bool | `Option.map_eq_some_iff`, `Bool.and_eq_true`, `beq_iff_eq`, `decide_eq_true_eq` | M20, M22, M30 |
| Arrays | `Array.getElem?_eq_getElem`, `Array.swap_perm`, `Array.getElem_swap`, `Array.Perm.trans`, `Array.Perm.refl` | M23, H06 |
| Finset (Mathlib) | `Finset.sum_range_succ`, `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.range_add_one`, `Finset.filter_insert`, `Finset.card_insert_of_notMem` | E42, M32, M44 |
| Parity, divisibility, primes | `Even`, `Odd`, `even_iff_two_dvd`, `even_two_mul`, `dvd_add`, `dvd_sub`, `dvd_mul_of_dvd_right`, `mul_dvd_mul`, `Nat.Prime.two_le`, `Nat.Prime.odd_of_ne_two`, `Nat.Prime.eq_one_or_self_of_dvd`, `Nat.Prime.dvd_mul`, `Nat.Prime.dvd_of_dvd_pow`, `Nat.prime_def`, `Nat.prime_two`, `Nat.dvd_factorial`, `Nat.factorial_pos`, `Nat.dvd_add_right` | E38–E43, M43, H07, H08 |
| Sets and functions | `Set.mem_inter_iff`, `Set.mem_union`, `Set.mem_setOf_eq`, `Set.mem_image`, `Set.mem_preimage`, `Set.image_mono`, `Set.compl_subset_compl`, `Set.sInter_subset_of_mem`, `Set.subset_sInter`, `Set.subset_sUnion_of_mem`, `Set.sUnion_subset`, `subset_antisymm`, `Function.Injective`, `Function.Surjective`, `Function.invFun`, `Function.leftInverse_invFun` | E40, M37–M39, H09, H10 |
| Real analysis | `sq_nonneg`, `abs_of_pos`, `abs_add_le`, `exists_nat_gt`, `div_lt_iff₀`, `le_of_max_le_left`, `add_lt_add`, `mul_le_mul_of_nonneg_right`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.sq_sqrt`, `irrational_iff_ne_rational`, `sub_ne_zero`, `mul_eq_zero`, `pow_succ`, `pow_two` | E35–E45, M34–M36, M40, M45, H08 |
| Groups, ZMod | `mul_inv_rev`, `inv_eq_of_mul_eq_one_right`, `mul_inv_cancel`, `ZMod.intCast_mod`, `Int.natAbs_pow` | M41, M42, H08 |

## 8. Traps

- Nat subtraction truncates: `3 - 5 = 0`. State `… + 1 = 2 ^ n` instead of `… = 2 ^ n - 1`. (E11, M33)
- `have h := f 0` for `f : ∀ n, P n (n + 1)` gives `P 0 (0 + 1)`; write the type: `have h : P 0 1 := f 0`. (E21)
- `omega` treats `x * y` as an opaque atom: expand products first (`Nat.add_mul`, `Nat.mul_add`). It cannot use facts like `x ∈ l`; use `grind`. (E14, M16, M21)
- Well-founded definitions (`termination_by`) do not compute by `rfl`/`decide`; unfold with `rw [f]` / `simp [f]`. (E26)
- `rw [ih]` before unfolding helper definitions, or the IH no longer matches. (M06)
- `ring` ignores hypotheses (substitute first); `field_simp` needs `x ≠ 0` in context. (E34, E45)
- An accumulator or a fixed second argument makes the plain IH too weak: `generalizing`. (M01–M03)
- `cases h` cannot invert `Matches r (u ++ v)`-style indices: state inversion lemmas over a variable, or `generalize` first. (H04, H05)
- A `let x := …` inside a definition shows up as a local definition in `fun_induction` cases; use `show` to unfold it. (M25)

## Cheatsheet

| Need | Write |
|---|---|
| prove an implication | `intro h` |
| close with a term | `exact h` |
| work backwards | `apply h` |
| split `∧` / `↔` | `constructor` |
| use `∧` / `∃` | `obtain ⟨a, b⟩ := h` |
| intro + unpack | `rintro ⟨x, hx, rfl⟩` |
| use `∨` | `rcases h with h \| h` |
| prove `∨` | `left` / `right` |
| prove `∃` | `exact ⟨w, h⟩` / `exists w` / `use w` |
| contradiction | `exact absurd hp hnp` / `contradiction` / `exfalso` |
| case on a Prop | `by_cases h : p` |
| case on data | `cases x with \| c₁ => … \| c₂ a => …` |
| case on `if` in goal | `split` |
| rewrite | `rw [h]`, `rw [← h] at h'` |
| simplify | `simp`, `simp only [l]`, `simp [f] at h`, `simp_all` |
| linear arithmetic (ℕ, ℤ) | `omega` |
| everything-mixed | `grind` |
| closed computation | `rfl`, `decide` |
| function equality | `funext x` |
| intermediate fact | `have h : T := by …` |
| backwards step | `suffices h : T by …` |
| chain | `calc a = b := … _ ≤ c := …` |
| induction (Nat/List) | `induction n with \| zero => … \| succ n ih => …` |
| stronger IH | `induction xs generalizing acc` |
| strong induction | `induction n using Nat.strongRecOn with \| _ n ih => …` |
| follow a function | `fun_induction f x` |
| inversion | `cases h` |
| injectivity / clash | `injection h with h₁`, `nofun` |
| several goals | `refine ⟨?_, ?_⟩ <;> simp` |
| unfold | `unfold f at h ⊢` |
| measure | `termination_by xs.length`, `decreasing_by omega` |
| Fin / Subtype value | `⟨v, by omega⟩`, ext: `Fin.ext`, `Subtype.ext` |
| ring identity | `ring` |
| linear (ℝ) | `linarith [sq_nonneg (a - b)]` |
| nonlinear (ℝ) | `nlinarith [mul_nonneg ha hb]` |
| numbers, primes | `norm_num` |
| `0 < e` | `positivity` |
| monotonicity | `gcongr` |
| denominators | `field_simp` |
| negations | `push Not at h` |
| casts | `push_cast`, `exact_mod_cast h` |
| sets | `ext x`, `Set.mem_inter_iff`, `rintro x ⟨ha, hb⟩` |
| sums | `Finset.sum_range_succ` |
| perm | `List.Perm.cons`, `.trans`, `List.perm_middle` |
| sorted | `List.Pairwise.cons`, `List.rel_of_pairwise_cons` |
| find a lemma | `exact?` |
