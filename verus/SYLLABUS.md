# Verus syllabus (author plan + progress tracker)

Verus 0.2026.09.27.3cf1832. Status column: `-` planned, `S` stub written, `OK` stub + solution pass.

## Conventions (all problems)

- Header `// ID | Title | time | tags [Rnn]`, then `// GOAL`, `// REFERENCE` (<= 12 lines), optional
  `// BANNED:` / `// NOTE:`; body; hints banner copied from E01.
- `use vstd::prelude::*;` then `verus! { ... } // verus!`. Extra `use` lines (e.g. `vstd::arithmetic::...`)
  go before `verus!`.
- Spec regions hold signatures + contracts + the spec fns / types they mention. Bodies follow `END SPEC`.
- Spec fns are plain `spec fn` (crate-private, body visible everywhere in the file). `pub open spec fn`
  appears only where `open` is the lesson (E03). Structs used by spec fns are private; a `View` impl uses
  `closed spec fn view` (open would require `pub` on struct + fields).
- `&mut` params, new mut-ref style: `requires` may say `v` or `old(v)`; `ensures` must say `old(v)` (entry)
  or `final(v)` (exit). Inside the body/invariants, `old(v)` is the entry value and `v` the current one.
- Stub holes: exec body `0 // TODO`, `false // TODO`, `Vec::new() // TODO`, `None // TODO`, `()`-returning
  exec bodies `{ }` (must still fail); proof fn bodies `{ }`; learner-written spec fn bodies `0 // TODO`.
- Facts learned while probing this version (cards must match):
  - `==` on Seq/Set/Map in `ensures`/`assert`/invariants is proved extensionally automatically;
    `=~=` is still needed when the equality is *inside* a function argument (e.g. `sum(s.push(x).drop_last())`).
  - Nonlinear facts (`a*(i+1) == a*i + a`, `x*x*x > 0`) need `by (nonlinear_arith)` or vstd lemmas.
    Constant multiplication (`3 * q`) and `/ c`, `% c` for literal `c` are linear and automatic.
  - Commutativity is not automatic either: `lemma_fundamental_div_mod(x, d)` gives `x == d * (x / d) + x % d`.
  - Recursive spec fns have fuel 1: `pow2(3) == 8` needs a chain of asserts, `reveal_with_fuel`, or `by (compute)`.
  - `vstd::set::Set` is finite-only; `Set::new` returns `Option<Set>`. Use `set![..]`, `.insert`, `.filter`.
    `Map::new(dom_set, |k| v)`; `map![k => v]`.
  - `choose|x| P(x)` needs a trigger (wrap `P` in a spec fn or mention `s[x]`).
  - `pow` in `vstd::arithmetic::power` is opaque; problems define their own `pow2`/`pow` spec fns instead.
  - A narrowing exec cast `x as u8` is accepted but its value is unknown unless `x` fits: reduce first.
  - A loop `decreases` measure must stay >= 0 after the last iteration too (`2*n - p`, not `n - p`).
  - Auto-trigger quirks: `forall|j| .. s[j] == s[0]` and `.. r.0 <= v[i] <= r.1` fail to infer a trigger;
    write `s[0] == s[j]`, split chains, or annotate `#[trigger]`.
  - Never write the two spec-marker words in comments: the checker matches them anywhere.

## Easy (45)

| ID | Title | New construct(s) | R | St |
|---|---|---|---|---|
| E01 | Absolute value | `verus!`, `fn`, `requires`/`ensures`, overflow | R01 | OK |
| E02 | Max of two | `\|\|` in ensures, if-else expression | R02 || OK |
| E03 | Clamp | `pub open spec fn`, calling spec fns in ensures | || OK |
| E04 | Average without overflow | `int`, `as int`, spec arithmetic is unbounded | || OK |
| E05 | Saturating add | `u64::MAX`, overflow-safe comparison | || OK |
| E06 | Sign | `match` + guards, `==>` | || OK |
| E07 | Cube is positive | `proof fn`, calling a lemma | || OK |
| E08 | Powers of two | recursive `spec fn`, `decreases`, `(n - 1) as nat` | || OK |
| E09 | Unfold pow2 by hand | `assert`, fuel 1 (BANNED compute, reveal_with_fuel) | || OK |
| E10 | pow2 beats n | induction in a `proof fn` (recursive call) | || OK |
| E11 | Remainder by subtraction | `while` + `invariant` + `decreases` | || OK |
| E12 | Last element | `Vec`, `v.len()`, `v[i]`, `v@`, `v@[i]` | || OK |
| E13 | All below a bound | `for i in 0..n` + invariant, `forall\|i: int\|` | || OK |
| E14 | Has a negative | `exists\|i: int\|`, witnesses | || OK |
| E15 | Range vector | `Vec::new()`, `push` in a loop | || OK |
| E16 | Square of a u32 | `by (nonlinear_arith)` | || OK |
| E17 | Triangular closed form | `proof { }` block in exec code | || OK |
| E18 | A power of two above n | `assert(..) by { }`, proving `exists` | || OK |
| E19 | Prepend by copying | `Seq`: `seq![]`, `+`, `.subrange` in invariants | || OK |
| E20 | Checked double subtraction | `Option<T>` return, `is`, `->` | || OK |
| E21 | Distinct among three | `Set`: `set![]`, `.len()`, `.contains` | || OK |
| E22 | Two-entry lookup | `Map`: `map![]`, `.dom()`, `m[k]` | || OK |
| E23 | Accumulator commands | `struct`/`enum` + `match` in spec | || OK |
| E24 | Swap two cells | `&mut` params, `old(x)`, `final(x)` | || OK |
| E25 | Clamp all in place | `v.set(i, x)`, `old(v)` in loop invariants | || OK |
| E26 | Next power of two | `let ghost mut`, ghost updates in `proof { }` | || OK |
| E27 | Make the trigger fire | `#[trigger]`, trigger terms | || OK |
| E28 | Choose a witness | `choose\|x\|` | || OK |
| E29 | Bit tricks as arithmetic | `by (bit_vector)` | || OK |
| E30 | Division with remainder | calling a vstd lemma (`vstd::arithmetic::div_mod`), tuple return | || OK |
| E31 | Swap keeps the multiset | `broadcast use`, `to_multiset` | || OK |
| E32 | All equal slice | `&[T]` slices, two-variable `forall`, `<==>` | || OK |
| E33 | Generic swap | generics `<T: Copy>` | || OK |
| E34 | Sum after push | `.drop_last()`/`.last()`, `=~=` inside arguments | || OK |
| E35 | Evaluate by computation | `by (compute)` | || OK |
| E36 | Interval intersection | `impl` blocks, `&self` methods, spec methods | || OK |
| E37 | Floor division of signed ints | exec `/` truncates, spec `/` floors | || OK |
| E38 | Powers of three, recursively | recursive exec `fn` + `decreases` | || OK |
| E39 | Double every element | spec closures, `.map_values` | || OK |
| E40 | Ghost argument | `Ghost(x): Ghost<T>` parameter | || OK |
| E41 | Rotate last to front | `pop`, `insert`, `unwrap` specs | || OK |
| E42 | ASCII upper case | `u8`, byte literals `b'a'` | || OK |
| E43 | Wrapping hash step | `wrapping_mul`/`wrapping_add` | || OK |
| E44 | Narrowing casts | exec `as u8` known only when the value fits | || OK |
| E45 | Ends of a sorted Vec | spec predicate in `requires`, `Seq::contains` | || OK |

## Medium (45)

| ID | Title | Constructs | R | St |
|---|---|---|---|---|
| M01 | Sum 0..n by a loop | loop invariant with `2*s == i*(i+1)`, nonlinear steps | R03 || OK |
| M02 | Linear search | `Option<usize>`, first occurrence, not-found => key not in v | R04 || OK |
| M03 | Max element | forall + exists postcondition | R05 || OK |
| M04 | Count occurrences | recursive count spec on `drop_last`, subrange invariant | R06 || OK |
| M05 | Reverse in place | two-index swap loop, `old(v)` | R07 || OK |
| M06 | Is sorted | pairwise sortedness from adjacent checks | R08 || OK |
| M07 | Binary search | sorted `Vec<u64>`, overflow-safe midpoint | R09 || OK |
| M08 | Fibonacci, iterative | requires `fib(n) <= u64::MAX`, monotonicity lemma | R10 || OK |
| M09 | Fast modular exponentiation | O(log e) squaring, own `pow` spec, `pow(b, e) % m` with `1 < m <= 0xFFFF_FFFF` so products fit in u64 (Verus adaptation of R11) | R11 || OK |
| M10 | Integer square root | `n: u32`, squares computed in u64, `r*r <= n < (r+1)*(r+1)`, nonlinear | R12 || OK |
| M11 | GCD by Euclid | `r == gcd(a, b)` (recursive spec) + `r` divides a and b, via div_mod lemmas | R13 || OK |
| M12 | Merge two sorted Vecs | sorted + `to_multiset` of subranges | R15 || OK |
| M13 | Dedup a sorted Vec | strictly increasing + same element set (`contains`) | R16 || OK |
| M14 | Palindrome check | two pointers, `<==>` | R17 || OK |
| M15 | Prefix sums | sum spec, `r[i] == sum(v@.subrange(0, i))`, overflow bound | R18 || OK |
| M16 | Stack with a Seq view | `impl View`, `&mut self` methods | || OK |
| M17 | Opaque sortedness | `#[verifier::opaque]`, `reveal` | || OK |
| M18 | Closed spec behind a module | `mod`, `pub closed spec fn`, exported lemmas | || OK |
| M19 | Fuel | `reveal_with_fuel` | || OK |
| M20 | First zero with loop/break | `loop`, `break`, `invariant_except_break`, loop `ensures` | || OK |
| M21 | Loop isolation | `#[verifier::loop_isolation(false)]` | || OK |
| M22 | Tracked permission token | `tracked struct`, `Tracked<T>`, `Ghost<T>` | || OK |
| M23 | Pointwise lemma over a Seq | `assert forall .. implies .. by { }` | || OK |
| M24 | Powers-of-two table | lemma call in a loop body via `proof { }` | || OK |
| M25 | Ackermann grows | lexicographic `decreases m, n` | || OK |
| M26 | Counter trait | trait with `spec fn` + method contracts, two impls | || OK |
| M27 | Boxed linked list | `enum` with `Box`, recursive view, recursive exec | || OK |
| M28 | Last occurrence | backward scan, `usize` vs `int` index arithmetic | || OK |
| M29 | Minimum to front | permutation via `to_multiset`, swap | || OK |
| M30 | Running statistics | struct invariant `well_formed`, `Ghost` field, `&mut self` | || OK |
| M31 | Sum distributes over concat | induction on `Seq`, `=~=` | || OK |
| M32 | Reverse is an involution | recursive spec, helper lemma | || OK |
| M33 | All distinct | nested loops, two-index invariant | || OK |
| M34 | Digit sum | `/ 10` recursion, overflow bound by lemma | || OK |
| M35 | Integer log2 | halving loop, nonlinear sandwich invariant `pow2(r)*m <= n < pow2(r)*(m+1)` | || OK |
| M36 | Insert into sorted Vec | sorted + multiset, `Vec::insert` | || OK |
| M37 | Even/odd mutual recursion | mutually recursive spec fns | || OK |
| M38 | Filter evens | `Seq::filter` (opaque), `reveal(Seq::filter)` | || OK |
| M39 | Checked sum of a Vec | `Option`, monotone-sum lemma | || OK |
| M40 | Byte histogram | `vec![0; 256]`, count spec per bucket | || OK |
| M41 | Higher-order all-satisfy | closures, `f.requires`, `f.ensures`, closure contracts (count dropped: `f.ensures` is a relation) | || OK |
| M42 | Rotate by k | `%` indexing, `usize`/`int` | || OK |
| M43 | Bits to number | `Vec<bool>` (MSB first), `pow2` bound, `by (compute)` | || OK |
| M44 | Longest plateau | optimality spec (exists + forall) | || OK |
| M45 | Common element of sorted Vecs | two pointers, exists pair | || OK |

## Hard (10)

| ID | Title | Constructs | R | St |
|---|---|---|---|---|
| H01 | Insertion sort | in-place, sorted + `to_multiset` | R14 || OK |
| H02 | Merge sort | recursion on subranges, merge, multiset | R20 || OK |
| H03 | Dutch national flag | 3-way partition of `Vec<i64>` around a pivot, returns the two boundaries; regions + permutation | R19 || OK |
| H04 | Ring buffer queue | learner writes `well_formed`; `Seq::new` view, `%`-free wrap-around | || OK |
| H05 | Linked stack | `Option<Box<Node>>`, push/pop/reverse, `Seq` view | || OK |
| H06 | BST map | `Box` tree, `Map` view, insert/lookup/delete (`remove_min` milestone) | || OK |
| H07 | Sieve of Eratosthenes | nested loops, `divides` via exists, `n < 1_000_000` | || OK |
| H08 | Popcount (Kernighan) | frozen Kernighan lemma to prove, `popcount_loop`, O(1) `is_pow2` | || OK |
| H09 | Two-sum on a sorted Vec | two pointers, pair-exclusion invariant | || OK |
| H10 | LCS length by DP | rolling rows, table invariant | || OK |

## Coverage check against DESIGN.md §8 (Verus)

Easy: verus!/fn/requires/ensures/overflow E01 · spec fn (open) E03 · proof fn E07 · int/nat, `as int` E04 ·
overflow preconditions E01, E05, E16 · if/match E02, E06 · while+invariant+decreases E11 · for loops E13 ·
Vec, `v@` E12 · forall/exists E13, E14 · assert E09 · assert-by E18 · proof block E17 · recursive spec fn E08 ·
induction E10 · Seq E19 · Set E21 · Map E22 · struct/enum + match E23 · `&mut` + old E24 · push/set E15, E25 ·
nonlinear_arith E16 · bit_vector E29 · Option E20 · let ghost E26 · #[trigger] E27 · choose E28 ·
vstd lemma E30 · broadcast use E31.
Medium: R02 (E02) R03-R13, R15-R18 (M01-M15) · View M16 · closed/opaque/reveal M17, M18 · reveal_with_fuel M19 ·
loop/break M20 · loop_isolation M21 · Ghost/Tracked M22 (+E40) · assert forall M23 · lemma from exec M24 ·
lexicographic decreases M25 · traits M26 · Box list M27 (+H05) · closures M41 · usize/int M28, M42 · to_multiset M29 ·
struct invariants M30.
Hard: R14 H01 · R20 H02 · R19 H03 · ring buffer H04 · linked list H05 · BST H06 · sieve H07 · bit tricks H08 ·
two-sum H09 · DP H10.
