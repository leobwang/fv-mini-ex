# Lean 4 syllabus (author's plan and progress tracker)

Easy E01–E33 tour core Lean in order (one new construct each); E34–E45 meet the Mathlib
tactics. Medium M01–M31 are core, M32–M45 use Mathlib. Hard H01–H06 are core, H07–H10 Mathlib.
`[Rnn]` = shared problem (DESIGN.md §7). Status: `done` = stub fails, solution passes.

Mathlib count: 12 easy + 14 medium + 4 hard = 30.

## Easy (45)

| ID | Title | New construct(s) | Tags | R | Status |
|---|---|---|---|---|---|
| E01 | rfl, decide, #eval | `rfl`, `decide`, `#eval`, `def` | | | done |
| E02 | Factorial by pattern matching | `match n with`, structural recursion | | | done |
| E03 | intro, exact, apply | `intro`, `exact`, `apply` | | | done |
| E04 | Term-mode proofs | `fun h => …`, `⟨_, _⟩`, `.1`/`.2` | | | done |
| E05 | And and Iff | `constructor`, `obtain ⟨_, _⟩`, `Iff.intro`, `.mp` | | | done |
| E06 | Or | `cases h with`, `rcases h with h \| h`, `left`/`right` | | | done |
| E07 | Exists | `⟨w, h⟩`, `exists w`, `obtain ⟨x, hx⟩` | | | done |
| E08 | Not and False | `intro h` on `¬`, `absurd`, `contradiction`, `exfalso` | | | done |
| E09 | Rewriting | `rw [h]`, `rw [← h]`, `rw [h] at h'` | | | done |
| E10 | simp | `simp`, `simp only [..]`, `simp at h`, `simp [f]` | | | done |
| E11 | omega | `omega` on Nat subtraction, `Int`, casts `(n : Int)` | | | done |
| E12 | Absolute value | `if … then … else`, `split` | | R01 | done |
| E13 | Max of two | `by_cases h : p` | | R02 | done |
| E14 | Induction on Nat | `induction n with \| zero \| succ n ih` | | | done |
| E15 | Induction on lists | `induction xs with \| nil \| cons x xs ih` | | | done |
| E16 | Bool and Option cases | `cases b`, `cases o`, `<;>` first sight | | | done |
| E17 | Structures | `structure`, `{ x := .. }`, `⟨..⟩`, `p.x` | | | done |
| E18 | Inductive types | `inductive`, `match`, `cases c <;> rfl` | | | done |
| E19 | Add instance | `instance : Add V where add := …` | | | done |
| E20 | calc | `calc a < b := h … _ ≤ c := …` | | | done |
| E21 | have, show, suffices | `have`, `show`, `suffices` | | | done |
| E22 | funext | `funext x`, `Function.comp` | | | done |
| E23 | Implicit arguments | `{x}`, `@f`, `f (x := v)` | | | done |
| E24 | List library facts | `List.length_map`, `List.map_map`, `List.filter`, `List.foldl` | | | done |
| E25 | Bounded quantifiers | `∀ x ∈ xs`, `List.mem_map`, `List.mem_append` | | | done |
| E26 | termination_by | well-founded `def`, `termination_by`, `rw [f]` unfold | | | done |
| E27 | simp lemmas | `@[simp] theorem` | | | done |
| E28 | grind | `grind` | | | done |
| E29 | Constructor injectivity | `injection`, `nomatch`, `simp at h` on constructors | | | done |
| E30 | Prop-valued definitions | `def P : Prop`, `unfold`, `show` | | | done |
| E31 | Tactic combinators | `<;>`, `all_goals`, `refine ⟨?_, ?_⟩`, `first` | | | done |
| E32 | Option-returning functions | `if h : p then … else …`, `some`/`none` | | | done |
| E33 | Library search | `exact?`, `List.length_reverse` | | | done |
| E34 | ring | `ring` | mathlib | | done |
| E35 | linarith | `linarith` | mathlib | | done |
| E36 | norm_num | `norm_num` | mathlib | | done |
| E37 | positivity | `positivity` | mathlib | | done |
| E38 | Even and Odd | `Even`, `Odd`, `obtain ⟨k, rfl⟩` | mathlib | | done |
| E39 | Divisibility | `∣`, `Dvd.intro`, `dvd_add` | mathlib | | done |
| E40 | Set extensionality | `Set`, `ext x`, `Set.mem_inter_iff`, `Set.subset_def` | mathlib | | done |
| E41 | use and push Not | `use`, `push Not` (`push_neg` is deprecated in this Mathlib) | mathlib | | done |
| E42 | Finset sums | `∑ i ∈ Finset.range n, f i`, `Finset.sum_range_succ` | mathlib | | done |
| E43 | Primes by norm_num | `Nat.Prime`, `norm_num` | mathlib | | done |
| E44 | gcongr | `gcongr` | mathlib | | done |
| E45 | field_simp | `field_simp` | mathlib | | done |

## Medium (45)

| ID | Title | New construct(s) | Tags | R | Status |
|---|---|---|---|---|---|
| M01 | take and drop | `induction … generalizing` | | | done |
| M02 | Sum by accumulator | accumulator invariant lemma | | R03 | done |
| M03 | Reverse with an accumulator | accumulator ⇔ spec | | R07 | done |
| M04 | Peano addition is commutative | own `inductive`, helper lemmas | | | done |
| M05 | Postage stamps | strong induction `Nat.strongRecOn` | | | done |
| M06 | Quicksort terminates | `decreasing_by`, `fun_induction` | | | done |
| M07 | Even as an inductive predicate | inductive `Prop`, induction on derivations, `cases h` | | | done |
| M08 | Reflexive-transitive closure | parameterised inductive predicate | | | done |
| M09 | Fin n | `Fin n`, `⟨v, proof⟩`, `Fin.ext` | | | done |
| M10 | Subtypes | `{x // p x}`, `.val`, `.property` | | | done |
| M11 | Length-indexed vectors | indexed `inductive Vec α n` | | | done |
| M12 | A monoid class with laws | `class` with proof fields, `instance` | | | done |
| M13 | Decidable instance | `Decidable`, `decidable_of_iff`, `decide` | | | done |
| M14 | Count with a for loop | `Id.run do`, `let mut`, `for` | | R06 | done |
| M15 | Constant folding | evaluator, optimisation preserves semantics | | | done |
| M16 | BST insert | tree `inductive`, inductive `BST` invariant, `grind` for Prop atoms | | | done |
| M17 | Insertion sort | inductive `Sorted`, `List.Perm` | | R14 | done |
| M18 | Partition is a permutation | `List.Perm` lemmas | | | done |
| M19 | Except evaluator | `Except`, `do`, `throw` | | | done |
| M20 | Linear search | `xs[i]?`, `Option` result | | R04 | done |
| M21 | Max of a non-empty list | head + tail non-emptiness | | R05 | done |
| M22 | Is sorted | `List.Pairwise`, Bool ⇔ Prop | | R08 | done |
| M23 | Binary search | `termination_by hi - lo`, invariant over a range | | R09 | done |
| M24 | Fibonacci, iterative | pair accumulator | | R10 | done |
| M25 | Fast exponentiation | `Nat.pow` lemmas, `fun_induction` | | R11 | done |
| M26 | Integer square root | nonlinear Nat facts via `Nat.add_mul` + `omega` atoms | | R12 | done |
| M27 | GCD by Euclid | `fun_induction` on wf def, `Nat.dvd_mod_iff` | | R13 | done |
| M28 | Merge sorted lists | lexicographic termination, `List.Perm` | | R15 | done |
| M29 | Dedup a sorted list | `List.Pairwise (· < ·)` | | R16 | done |
| M30 | Palindrome | `List.getElem?_reverse`, `List.ext_getElem?` | | R17 | done |
| M31 | Prefix sums | `List.take`, `getElem?` | | R18 | done |
| M32 | Gauss sum | Finset induction | mathlib | | done |
| M33 | Geometric sum | `Finset.sum_range_succ`, `ring` | mathlib | | done |
| M34 | Bernoulli's inequality | induction + `nlinarith` | mathlib | | done |
| M35 | 1/(n+1) tends to 0 | ε-N with own definition, `exists_nat_gt`, `div_lt_iff₀` | mathlib | | done |
| M36 | Limit of a sum | ε/2 argument | mathlib | | done |
| M37 | Injective and surjective | `Function.Injective`, `Function.Surjective` | mathlib | | done |
| M38 | Image and preimage | `Set.image`, `Set.preimage` | mathlib | | done |
| M39 | Cantor's theorem | diagonal argument | mathlib | | done |
| M40 | AM-GM for two reals | `nlinarith [sq_nonneg _]` | mathlib | | done |
| M41 | Sums of two squares mod 4 | `ZMod`, `decide`, casts | mathlib | | done |
| M42 | Exponent-2 groups are abelian | `Group`, `mul_assoc`, `mul_left_cancel` | mathlib | | done |
| M43 | Primes and products | `Nat.Prime.dvd_mul` | mathlib | | done |
| M44 | Counting with Finset.filter | `Finset.filter`, `Finset.card` | mathlib | | done |
| M45 | Solving x² = 4 | `mul_eq_zero`, `sub_eq_zero` | mathlib | | done |

## Hard (10)

| ID | Title | Topic | Tags | R | Status |
|---|---|---|---|---|---|
| H01 | Compiling expressions to a stack machine | compiler correctness | | | done |
| H02 | Merge sort | sorted + perm, wf recursion | | R20 | done |
| H03 | Type safety | progress + preservation | | | done |
| H04 | IMP big-step semantics | determinism, non-termination | | | done |
| H05 | Regex matcher | matcher ⇔ inductive semantics | | | done |
| H06 | Dutch national flag | 3-way partition | | R19 | done |
| H07 | Infinitely many primes | Euclid's argument | mathlib | | done |
| H08 | √2 is irrational | parity / descent | mathlib | | done |
| H09 | Knaster–Tarski | fixed points on `Set α` | mathlib | | done |
| H10 | Schröder–Bernstein | Set-level construction | mathlib | | done |

## Coverage check against DESIGN.md §8

- Every easy core item: E01–E33 (`grind` E28, `@[simp]` E27, `termination_by` E26, `@` E23).
- Mathlib easy: ring E34, linarith E35, norm_num E36, positivity E37, Even/Odd E38, ∣ E39,
  Set ext E40, Finset.sum_range_succ E42, Nat.Prime E43 (+ use/push Not E41, gcongr E44, field_simp E45).
- Medium core items: generalizing M01, accumulators M02/M03, strong induction M05, decreasing_by
  M06, inductive predicates M07/M08/M17, Fin/Subtype/Vec M09–M11, law fields M12, Decidable M13,
  Id.run M14, constant folding M15, BST M16, insertion sort M17, Perm M18, Except M19, R02–R18.
- Mathlib medium: Gauss M32, geometric M33, induction inequality M34, ε-N M35/M36, Inj/Surj M37,
  image/preimage M38, Cantor M39, AM-GM M40, ZMod M41.
- Shared: R01 E12, R02 E13, R03 M02, R04 M20, R05 M21, R06 M14, R07 M03, R08 M22, R09 M23,
  R10 M24, R11 M25, R12 M26, R13 M27, R14 M17, R15 M28, R16 M29, R17 M30, R18 M31, R19 H06, R20 H02.
