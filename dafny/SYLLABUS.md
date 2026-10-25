# Dafny syllabus (author plan + progress tracker)

Dafny 4.11.0. Each easy problem introduces about one construct, in order. `[Rnn]` = shared problem (DESIGN.md §7).
Status: `-` planned, `S` stub+solution written, `OK` both `--stubs` and `--solutions` pass.

## Easy (E01–E45)

| ID | Title | New construct(s) | R | Status |
|---|---|---|---|---|
| E01 | Absolute value | `method`, `requires`/`ensures`, `if`/`else` | R01 | OK |
| E02 | Max of two | method call `var m := M(..)`; callers see only the contract | R02 | OK |
| E03 | Min as a function | `function`, `if … then … else` expression, function `ensures` | | OK |
| E04 | Leap year | `predicate`, `%`, test lemma | | OK |
| E05 | Sum of a range | recursive function, explicit `decreases` | | OK |
| E06 | Sum 0..n by loop | `while`, `invariant`, `decreases` | R03 | OK |
| E07 | Factorial by for-loop | `for i := lo to hi` | | OK |
| E08 | All positive | `array<int>`, `a.Length`, `forall i :: …` | | OK |
| E09 | Adjacent equal pair | `exists i :: …`, negated-exists invariant | | OK |
| E10 | Array sum | `reads a` for functions over arrays | | OK |
| E11 | Increment all | `modifies a`, `old(a[i])`, frame invariant | | OK |
| E12 | Rotate left | `seq`: `\|s\|`, `s[i]`, `s[..k]`, `s[k..]`, `+`, `[x]` | | OK |
| E13 | Set filter and symmetric difference | `set` ops `+ - *`, `in`, comprehension | | OK |
| E14 | Swap | `multiset`, parallel assignment | | OK |
| E15 | Histogram increment | `map`: `k in m`, `m[k]`, `m[k := v]` | | OK |
| E16 | A square witness | `lemma`, `assert` as a hint/witness | | OK |
| E17 | Sum of odd numbers | lemma by induction (recursive call), `{:induction false}` | | OK |
| E18 | Product of powers | `calc` with `{ lemma(); }` hints | | OK |
| E19 | Shape area | `datatype`, `match`, `.Ctor?`, destructors | | OK |
| E20 | Positive integers | subset type `type T = x: int \| P witness w`, `nat` | | OK |
| E21 | Distance on nat | `nat` subtraction trap | | OK |
| E22 | Division with remainder | multiple returns, `var q, r := M(..)` | | OK |
| E23 | Generic replace | generics `<T(==)>`, recursion on `s[1..]` | | OK |
| E24 | All powers positive | `forall` statement, `assert forall … by` | | OK |
| E25 | Max element value | `ghost var` witness | R05 | OK |
| E26 | Pick from a set | `:|` (assign such that), set cardinality | | OK |
| E27 | Uppercase string | `string` = `seq<char>`, char literals, `as int`/`as char` | | OK |
| E28 | Find with Option | generic `datatype Option<T>`, `Some`/`None` | | OK |
| E29 | Integer list length | recursive datatype, structural recursion | | OK |
| E30 | Length of append | structural induction lemma with `match` | | OK |
| E31 | Move money | datatype update `p.(x := e)` | | OK |
| E32 | Call a lemma | calling a lemma from a method | | OK |
| E33 | Array of squares | `new int[n](i => e)`, `fresh` | | OK |
| E34 | Double in place | aggregate `forall i \| … { a[i] := … }` | | OK |
| E35 | Integer range | `seq(n, i => e)` comprehension | | OK |
| E36 | Mean of two | `real`, `as real`, `2.0` | | OK |
| E37 | Blit | slices of arrays in `ensures`, `old(a[..k])` | | OK |
| E38 | Compose | function types `int -> int`, lambdas | | OK |
| E39 | Count digits | "done + remaining" invariant | | OK |
| E40 | Slice of a slice | seq extensionality `assert s[..i+1][..i] == s[..i]` | | OK |
| E41 | Set image and map comprehension | `set x \| x in s :: f(x)`, `map k \| k in s :: e` | | OK |
| E42 | Even plus even | existential elimination `var k :\| P(k)` in a lemma | | OK |
| E43 | Recursive maximum | recursive function proving its own `ensures`, `var x := e; body` let | | OK |
| E44 | Horner's rule | `for i := hi downto lo` | | OK |
| E45 | Strip factors of two | explicit loop `decreases` | | OK |

## Medium (M01–M45)

| ID | Title | New construct(s) | R | Status |
|---|---|---|---|---|
| M01 | Linear search | first occurrence, `-1` sentinel | R04 | OK |
| M02 | Count occurrences | spec-level `Count`, helper lemma for appending | R06 | OK |
| M03 | Reverse in place | two-index loop, `old(a[..])` | R07 | OK |
| M04 | Is sorted | `forall i, j` pairs vs adjacent check | R08 | OK |
| M05 | Binary search | sorted precondition, half-open `lo..hi` | R09 | OK |
| M06 | Fibonacci | two-variable invariant | R10 | OK |
| M07 | Fast exponentiation | invariant `r * Pow(b, e) == Pow(B, E)`, helper lemma | R11 | OK |
| M08 | Integer square root | nonlinear invariant | R12 | OK |
| M09 | GCD by Euclid | spec gcd function, `%` lemma | R13 | OK |
| M10 | Merge two sorted sequences | `multiset` + sortedness invariants | R15 | OK |
| M11 | Dedup a sorted sequence | strictly increasing, `set` equality | R16 | OK |
| M12 | Palindrome check | two pointers on `string` | R17 | OK |
| M13 | Prefix sums | `new int[n+1]`, sum lemma | R18 | OK |
| M14 | Sum of a concatenation | seq induction with extensionality | | OK |
| M15 | Assert by | `assert P by { … }` | | OK |
| M16 | Lemma for every element | `forall` statement calling a lemma | | OK |
| M17 | Opaque function | `opaque function`, `reveal F();` | | OK |
| M18 | Triggers | `{:trigger}`, why a quantifier never fires | | OK |
| M19 | Ackermann | lexicographic `decreases m, n` | | OK |
| M20 | Mutual recursion | mutually recursive predicates + lemma | | OK |
| M21 | Generic list append | generic `datatype List<T>`, associativity | | OK |
| M22 | List reverse involution | helper lemma `Rev(Append(a,b))` | | OK |
| M23 | Tree mirror | `Tree<T>`, `Size`, `Mirror` lemmas | | OK |
| M24 | Counter class | `class`, fields, `constructor`, `this`, `modifies this`, `fresh` | | OK |
| M25 | Growable stack | `Valid()`, `ghost var Repr`, `ghost var Contents: seq<int>`, `fresh(Repr - old(Repr))` | | OK |
| M26 | Shapes trait | `trait`, `extends`, dynamic dispatch with specs | | OK |
| M27 | Two-state lemma | `twostate lemma`, `old` in lemmas | | OK |
| M28 | Result and :- | failure-compatible `Result`, `:-` | | OK |
| M29 | Byte newtype | `newtype` with a range, saturating add | | OK |
| M30 | Bit tricks | `bv8`, `&`, `\|`, `<<`, `as` | | OK |
| M31 | Modules | `module`, `import`, qualified names | | OK |
| M32 | Function by method | `function … by method` | | OK |
| M33 | Matrix transpose | `array2`, `Length0/Length1`, nested loops | | OK |
| M34 | Map and filter | higher-order functions on `seq`, lemmas | | OK |
| M35 | Run-length encoding | encode/decode round trip | | OK |
| M36 | Two-sum on a sorted array | two pointers, existence spec | | OK |
| M37 | Filter into a fresh array | two passes, `new`, prefix-count lemma | | OK |
| M38 | Partition evens first | in-place swaps + `multiset` invariant | | OK |
| M39 | Elements to set | set accumulation invariant | | OK |
| M40 | Word frequency | `map<string, nat>` + spec count | | OK |
| M41 | Functional queue | two-list queue, abstraction function | | OK |
| M42 | Binary round trip | `seq<bool>`, div/mod induction | | OK |
| M43 | Sum of cubes | nonlinear induction with `calc` | | OK |
| M44 | Reachability | `least predicate`, `least lemma` | | OK |
| M45 | All distinct | nested loops, pair invariants | | OK |

## Hard (H01–H10)

| ID | Title | New construct(s) | R | Status |
|---|---|---|---|---|
| H01 | Insertion sort | nested loop, sorted + permutation | R14 | OK |
| H02 | Merge sort | recursion on `seq`, merge lemma | R20 | OK |
| H03 | Dutch national flag | three-region invariant | R19 | OK |
| H04 | Circular buffer queue | class; learner-designed `Valid()` tying ghost `Contents` to a ring buffer | | OK |
| H05 | Binary search tree | `Contents` set, insert + delete (`RemoveMin`), in-order traversal sorted | | OK |
| H06 | Binary heap insert | sift-up, "heap except at k" invariant, `{:trigger}` against matching loops | | OK |
| H07 | Expression compiler | compile to a stack machine, correctness | | OK |
| H08 | Maximum subarray | Kadane with an optimality spec | | OK |
| H09 | Quicksort | Lomuto partition, recursion on ranges | | OK |
| H10 | Longest common subsequence | DP table in `array2` = recursive spec, loop `modifies`, triggers | | OK |

## Coverage of DESIGN.md §8 (Dafny)

| Syllabus item | Problems |
|---|---|
| `method`/`requires`/`ensures` | E01, E02 |
| `if`/`else` | E01, E02 |
| `function` vs `method` | E03 |
| `predicate` | E04 |
| recursive function + `decreases` | E05, E45 (loop), M19 |
| `while` + `invariant` + `decreases` | E06, E22, E39, E45 |
| `for i := 0 to n` (and `downto`) | E07, E44 |
| arrays: `a.Length`, `a[..]`, `forall`, `exists` | E08, E09, E40 |
| `reads a` | E10 |
| `modifies a` + `old(a[..])` | E11, E37, M03 |
| `seq` ops | E12, E23, E35 |
| `set` ops and comprehension | E13, E41, M39 |
| `multiset` | E14, M10, M38, H01 |
| `map` | E15, E41, M40 |
| `assert` | E16, E40 |
| lemma by induction | E17, E30, M14, M21 |
| `calc` | E18, M43 |
| `datatype` + `match` + `.Ctor?` + destructors | E19, E28, E29 |
| `nat` and subset types with `witness` | E20, E21 |
| tuples, multiple returns | E22, M35, H05 |
| generics `<T>` | E23, E28, M21 |
| `forall` statement / `assert forall … by` | E24, M16 |
| `ghost var` | E25, H06, H09 |
| `:|` | E26, E42 |
| `string` as `seq<char>` | E27, M12 |
| shared R04–R13, R15–R18 | M01–M13 |
| classes: fields, `constructor`, `this`, `modifies this`, `fresh` | M24 |
| `Valid()` + `ghost var Repr` (dynamic frames) | M25, H04 |
| `ghost var Contents: seq<T>` abstraction | M25, H04 |
| `opaque function` + `reveal` | M17 |
| `{:trigger}` | M18, H06, H10 |
| lexicographic `decreases` (Ackermann) | M19 |
| mutual recursion | M20 |
| `assert … by { }` | M15, M09 |
| `forall` statement calling a lemma for all elements | M16, M09 |
| generic `List<T>`/`Tree<T>` with lemmas | M21, M22, M23 |
| `trait` + `extends` | M26 |
| `twostate` / `old` in lemmas | M27 |
| failure-compatible `Result` and `:-` | M28 |
| `newtype` with a range | M29 |
| bit-vectors `bv8` | M30 |
| `module`/`import` | M31 |
| `function … by method` | M32 |
| hard: insertion sort (R14), merge sort (R20), Dutch flag (R19) | H01, H02, H03 |
| hard: circular buffer, BST, heap insert, compiler, Kadane | H04–H08 |
| hard (replacements): quicksort, LCS DP | H09, H10 (instead of union-find and KMP) |
