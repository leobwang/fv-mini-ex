# Verus reference (Verus 0.2026.09.27.3cf1832)

A cumulative cheat sheet for the Verus track, grouped by topic. `→ E07` lists the problems that use
an entry. Everything here compiles at the pinned version. Run `./check verus E07` to check one problem,
or `./check -v verus E07` to see Verus's output.

## 1. File skeleton and modes

```rust
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;      // extra imports go before verus!

verus! {
fn exec_fn(x: u64) -> (r: u64) requires x < 10, ensures r == x + 1, { x + 1 }   // compiled + verified
spec fn f(x: int) -> int { x + 1 }                                             // math only, never runs
proof fn lemma(x: int) requires x > 0, ensures f(x) > 1, { }                   // ghost, erased
} // verus!
```

| Mode | Can call | Arithmetic | Typical use | IDs |
|---|---|---|---|---|
| `fn` (exec) | exec fns; proof fns only inside `proof { }` | machine ints, overflow-checked | the code | E01 |
| `spec fn` | spec fns | `int`/`nat`, never overflows | definitions in contracts | E03, E08 |
| `proof fn` | proof + spec fns | `int`/`nat` | lemmas | E07, E10 |

- `pub open spec fn` exports the body to other modules; inside one file plain `spec fn` is enough → E03.
- `pub closed spec fn` in a `mod` hides the body outside the module; reason through exported lemmas
  (`reveal` on a closed fn is a compile error) → M18.
- `#[verifier::opaque] spec fn f` hides the body everywhere until `reveal(f);` → M17.
- Name the result to use it in `ensures`: `-> (r: u64)`; tuples `-> (r: (u64, u64))`, `r.0` → E30, E45.
- `requires` / `ensures` / `invariant` take comma-separated clauses (all must hold). Multi-line
  conjunctions: `&&& P &&& Q` → H04.

## 2. Integers, overflow, casts

| Item | Meaning | IDs |
|---|---|---|
| `x as int`, `n as nat` | cast to math integers; needed when passing machine ints to `int` params | E03, E04 |
| `a + b` in a spec on `u64`s | an `int`: cannot overflow | E04, E05 |
| `a + b` in exec code | Verus proves it fits; `u64::MAX`, `i64::MIN` are available | E01, E05 |
| `(n - 1) as nat` | nat minus nat is an int; cast back | E08 |
| `x / 2`, `x % 2` | spec: floor division (toward -inf), `%` in `0..d`; exec on `i64`: truncates toward 0 | E37 |
| `y as u8` (exec, narrowing) | allowed, but its value is known only when `y` fits; use `(x % 256) as u8` | E44 |
| `x as u64` (widening) | exact | E16, E23 |
| `a.wrapping_mul(b)`, `a.wrapping_add(b)` | result == (a op b) mod 2^bits | E43 |
| `a.checked_add(b)` | `Option`: `Some(a + b)` if it fits | M39 |
| `b'a'` | byte literal (`u8`), in exec and spec code | E42 |

Overflow-safe idioms: test `a > u64::MAX - b` before `a + b` → E05; midpoint `lo + (hi - lo) / 2` → M07;
`a / 2 + b / 2 + (a % 2 + b % 2) / 2` → E04; check `a >= b && a - b >= c` rather than `a >= b + c` → E20.

## 3. Control flow and loops

```rust
match x { 0 => a, y if y > 0 => b, _ => c }                    // E06
while r >= d
    invariant d > 0, rem(r as nat, d as nat) == rem(n as nat, d as nat),
    decreases r,
{ r = r - d; }                                                   // E11
for i in 0..v.len()
    invariant forall|j: int| 0 <= j < i ==> v[j] < b,           // i in scope, 0 <= i <= len known
{ if v[i] >= b { return false; } }                               // E13
loop
    invariant_except_break i < v.len(), ...                      // holds at the top, not at break
    ensures v[i as int] == 0,                                    // what is known after break
    decreases v.len() - i,
{ if v[i] == 0 { break; } i += 1; }                              // M20
```

- The loop body sees **only** its invariants (not the function's `requires`, not facts proved before
  the loop): restate what you need → E11. `#[verifier::loop_isolation(false)]` on the fn lifts this → M21.
- After the loop Verus knows the invariants plus the negated condition.
- `decreases e`: `e >= 0` and strictly smaller after every iteration, **including the last one** → E26.
- Exec recursion needs `decreases` too → E38, H02, H05. Lexicographic: `decreases m, n` → M25.
  Structural on data: `decreases self` / `decreases l` → H05, H06.
- `unreached()` marks an impossible branch (requires `false`) → H06.

## 4. Quantifiers and triggers

```rust
forall|i: int| 0 <= i < v.len() ==> v[i] >= 0          // `==>` under forall       E13
exists|i: int| 0 <= i < v.len() && v[i] < 0            // `&&` under exists         E14
forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]                       E45
forall|i: int| 0 <= i < n ==> #[trigger] f(s[i])       // explicit trigger          E27
choose|i: int| 0 <= i < s.len() && s[i] == 0           // a witness, if one exists  E28
assert forall|i: int| 0 <= i < s.len() implies P(i) by { lemma(s[i]); }             M23
```

- A quantified fact is used only on terms that match its trigger. If the goal does not mention such
  a term, mention it: `assert(is_pos(s[0]));` → E27.
- To prove `exists|k| P(k)`, make `P(w)` a known fact; the trigger term (`pow2(w)`) must appear → E18, E14.
- Auto-trigger quirks at this version: `forall|j| .. s[j] == s[0]` and chained `a <= v[i] <= b` may fail
  with "Could not automatically infer triggers". Write `s[0] == s[j]`, split the chain, or annotate
  `#[trigger] s@[j]` → E32, E45. Multi-triggers: `#[trigger] s[i] + #[trigger] s[j]` → H09.
- `verus --triggers file.rs` prints the triggers Verus chose.

## 5. Proofs

| Construct | Example | IDs |
|---|---|---|
| assert | `assert(pow2(1) == 2);` then use it below | E09 |
| assert-by | `assert(P) by { lemma(x); }` (facts inside stay local) | E18 |
| proof block in exec | `proof { lemma_tri(n as nat); }` | E17, M24 |
| lemma call | `lemma_mul_pos(x, x * x);` adds its ensures | E07 |
| induction | recursive call on a smaller argument + `decreases n,` | E10, M31, M32 |
| nonlinear | `assert(y * y <= u64::MAX) by (nonlinear_arith) requires y <= u32::MAX;` | E16, E17, M01 |
| bit-vector | `assert(x & 1 == x % 2) by (bit_vector);` (fixed-width operands only) | E29, H08 |
| compute | `assert(pow2(40) == 1099511627776) by (compute);` (closed terms) | E35 |
| fuel | `reveal_with_fuel(pow2, 4);` unfolds a recursive spec fn 4 levels | M19 |
| reveal | `reveal(f);` for `#[verifier::opaque]` fns | M17 |
| extensional eq. | `assert(s.push(x).drop_last() =~= s);` | E34, M31 |
| mutual recursion | `spec fn even(n)` calls `odd(n - 1)` and back; both `decreases n` | M37 |

- Products of variables are not reasoned about by default (`a*(i+1) == a*i + a` fails); multiplication
  by a literal and `/`, `%` by a literal are fine → E07, E11, E16. Commutativity is not automatic either:
  `lemma_fundamental_div_mod(x, d)` gives `x == d * (x / d) + x % d`, so write specs in that order → E30.
- Recursive spec fns unfold one level per occurrence (fuel 1): `pow2(4) == 16` needs the chain
  `pow2(0)`, ..., `pow2(3)` first → E09.
- `==` on `Seq`/`Set`/`Map` in asserts, ensures and invariants is proved element-wise automatically.
  Use `=~=` when the equality is needed *inside* a function argument → E34.

## 6. Collections (spec types)

| Type | Build | Query / update | IDs |
|---|---|---|---|
| `Seq<T>` | `seq![1, 2]`, `Seq::empty()`, `Seq::new(n, \|i: int\| f(i))`, `v@` | `s.len()`, `s[i]`, `s.push(x)`, `s + t`, `s.subrange(lo, hi)`, `s.update(i, x)`, `s.drop_last()`, `s.last()`, `s.drop_first()`, `s.first()`, `s.contains(x)`, `s.map_values(\|x: u32\| ..)`, `s.filter(\|x: u64\| ..)`, `s.reverse()`, `s.insert(i, x)`, `s.remove(i)` | E19, E34, E39, H04 |
| `Set<T>` (finite) | `set![a, b]`, `Set::empty()` | `s.contains(x)`, `s.insert(x)`, `s.remove(x)`, `s.len()`, `s.union(t)`, `s.filter(f)`, `s.subset_of(t)` | E21 |
| `Map<K, V>` | `map![k => v]`, `Map::empty()`, `Map::new(dom_set, \|k\| v)` | `m.dom().contains(k)`, `m[k]`, `m.insert(k, v)`, `m.remove(k)`, `m.union_prefer_right(m2)` | E22, H06 |
| `Multiset<T>` | `s.to_multiset()` | `m.count(x)`, `m.add(m2)`, `m.insert(x)` | E31, M29, H01 |

- `vstd::set::Set` is finite-only at this version; `Set::new(f)` returns `Option<Set<T>>`.
- Permutation lemmas: `broadcast use vstd::seq_lib::group_to_multiset_ensures;` (push, update, remove,
  insert, len, contains) → E31, H01, H03. Put it at file level (outside any fn) when loops need it:
  inside a fn body it did not reach the loop bodies → M12. Multiset equalities between built-up
  sequences sometimes need an explicit `assert(a.to_multiset() =~= b.to_multiset())` → M12. `vstd::seq_lib::lemma_multiset_commutative(a, b)` gives
  `(a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset())` → H02, M12.

## 7. Vec, slices, Option (exec types)

| Item | Spec effect | IDs |
|---|---|---|
| `v.len()`, `v[i]` | `v@.len()`, `v@[i]` (needs `i < v.len()`) | E12 |
| `Vec::new()`, `vec![0u64; n]` | empty; length `n`, all zeros | E15, H04 |
| `v.push(x)` | `v@ == old v@.push(x)` | E15 |
| `v.set(i, x)` | `v@ == old v@.update(i as int, x)` | E25, E33 |
| `v.pop()` | `Some(last)`, `v@ == old v@.drop_last()` | E41 |
| `v.insert(i, x)` | `v@ == old v@.insert(i as int, x)` | E41, M36 |
| `s: &[u64]` | `s@` is a `Seq`; `s.len()`, `s[i]` | E32 |
| `Some(x)`, `None`, `o.unwrap()` | `r is Some`, `r is None`, `r->0` (payload) | E20, E41 |
| `Option::take`, `Box::new`, `*b` | moving out of / into boxes | H05, H06 |
| `v[j as int]` | in spec quantifiers, index with an `int` | H04 |

## 8. Mutable references, structs, enums, traits

```rust
fn swap(a: &mut u64, b: &mut u64)
    ensures *final(a) == *old(b), *final(b) == *old(a),       // E24: old = entry, final = exit
fn clamp_all(v: &mut Vec<u64>, hi: u64)
    ensures final(v).len() == old(v).len(),                   // E25: in the body, old(v) = entry value
```

- `requires` may write `*a`/`v` (entry value) or `old(..)`; `ensures` must say `old(..)` or `final(..)`.
- `enum Cmd { Add(u32), Reset }`, `match c { Cmd::Add(k) => .., Cmd::Reset => .. }` in spec and exec → E23.
  Struct-like variants `Tree::Node { left, key, .. }`, tests `t is Node`, fields `t->key` → H06.
- `impl S { spec fn p(&self) -> bool { .. } fn m(&self) -> (r: S) ensures r.p() { .. } }` → E36.
- `impl View for S { type V = Seq<u64>; closed spec fn view(&self) -> Seq<u64> { self.v@ } }`, then
  `self@`, `old(self)@`, `final(self)@` → M16, H04. (`open` there would need `pub` struct and fields.)
- Struct invariant: `spec fn well_formed(&self) -> bool`, required and ensured by every `&mut self` method → M30, H04, H05.
- Generic exec fns: `fn swap_elems<T: Copy>(v: &mut Vec<T>, ..)` → E33.
- Traits: `trait Counter { spec fn value(&self) -> nat; fn inc(&mut self) requires .. ensures final(self).value() == ..; }`,
  `impl Counter for S { spec fn value(&self) -> nat { .. } fn inc(&mut self) { .. } }`, generic client `fn f<C: Counter>(c: &mut C)` → M26.
- Closures: `fn all<F: Fn(u64) -> bool>(v: &Vec<u64>, f: F) requires forall|x: u64| f.requires((x,))`,
  results via `f.ensures((x,), b)`; a closure with a contract: `|x: u64| -> (r: bool) ensures r == (x < 10) { x < 10 }` → M41.

## 9. Ghost code

| Item | Example | IDs |
|---|---|---|
| ghost local | `let ghost mut k: nat = 0;` then `proof { k = k + 1; }` | E26 |
| ghost parameter | `fn f(x: u64, Ghost(k): Ghost<nat>)`, call `f(7, Ghost(3))` | E40 |
| ghost value | `let g: Ghost<int> = Ghost(5); g@` | E40 |
| ghost struct field | `seen: Ghost<Seq<u64>>`, update `self.seen = Ghost(self.seen@.push(x));` | M30 |
| tracked | `tracked struct Key { pub ghost id: int }`, `fn f(Tracked(k): Tracked<&Key>)`, `let tracked k = ..;` | M22 |
| ghost snapshot | `let ghost r0 = r@;` | H07 |

## 10. vstd lemmas used in this track

| Lemma / group | Gives | IDs |
|---|---|---|
| `vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, d)` | `x == d * (x / d) + x % d` | E30, M11 |
| `vstd::arithmetic::div_mod::lemma_mod_multiples_basic`, `lemma_mod_self_0` | `(x * m) % m == 0`, `m % m == 0` | M11 |
| `vstd::arithmetic::div_mod::lemma_mul_mod_noop_left/right`, `lemma_small_mod` | move `% m` through `*`; `x < m ==> x % m == x` | M09 |
| `vstd::arithmetic::div_mod::lemma_add_mod_noop_right`, `lemma_mod_sub_multiples_vanish`, `lemma_mod_bound` | `%` through `+`/`-`, `0 <= x % m < m` | M42 |
| `vstd::seq_lib::group_seq_properties` | Dafny-style Seq facts (`contains`, take/skip) | M13 |
| `vstd::seq_lib::group_to_multiset_ensures` | multiset of push/update/remove/insert | E31, H01 |
| `vstd::seq_lib::lemma_multiset_commutative(a, b)` | multiset of `a + b` | H02 |
| `reveal(Seq::filter);` | unfold vstd's opaque `filter` | M38 |

## Cheatsheet

| Need | Write |
|---|---|
| file | `use vstd::prelude::*; verus! { .. } // verus!` |
| contract | `fn f(x: u64) -> (r: u64) requires P, ensures Q,` |
| math int | `x as int`, `(n - 1) as nat` |
| spec / proof fn | `spec fn f(n: nat) -> nat decreases n, { .. }`, `proof fn l(n: nat) ensures .., decreases n, { .. }` |
| view | `v@`, `v@.len()`, `v@[i]`, `v[i]` in specs |
| quantifiers | `forall\|i: int\| 0 <= i < n ==> P`, `exists\|i: int\| 0 <= i < n && P` |
| trigger | `#[trigger] f(s[i])`; fire it with `assert(f(s[k]));` |
| witness | `choose\|i: int\| P(i)` |
| while | `while c invariant I, decreases e, { .. }` |
| for | `for i in 0..n invariant I, { .. }` |
| loop/break | `loop invariant_except_break I, ensures E, decreases e, { .. break; }` |
| mut ref | `ensures *final(a) == *old(a) + 1`, `final(v)@ == old(v)@.push(x)` |
| Vec | `Vec::new()`, `v.push(x)`, `v.set(i, x)`, `v.pop()`, `v.insert(i, x)`, `vec![0; n]` |
| Seq | `seq![..]`, `s.push(x)`, `s + t`, `s.subrange(a, b)`, `s.update(i, x)`, `s.drop_last()`, `s.last()` |
| Set / Map | `set![..]`, `s.contains(x)`, `s.len()`; `map![k => v]`, `m.dom().contains(k)`, `m[k]` |
| permutation | `a.to_multiset() == b.to_multiset()`, `broadcast use vstd::seq_lib::group_to_multiset_ensures;` |
| Option | `r is Some`, `r->0`, `match r { Some(x) => .., None => .. }` |
| proof steps | `assert(P);`, `assert(P) by { .. }`, `proof { lemma(..); }` |
| solver modes | `by (nonlinear_arith) requires ..;`, `by (bit_vector);`, `by (compute);` |
| unfolding | `reveal_with_fuel(f, k);`, `reveal(f);` for opaque fns |
| ext. equality | `assert(a =~= b);` when `a`, `b` are arguments of a spec fn |
| ghost | `let ghost mut k: nat = 0;`, `proof { k = k + 1; }`, `Ghost(k): Ghost<nat>`, `g@` |
| overflow idioms | `a > u64::MAX - b`, `lo + (hi - lo) / 2`, widen with `as u64` before `*` |
| loops forget | restate `requires` facts and `v.len() == n` in every invariant |
