# Dafny reference (4.11)

Cumulative cheat sheet for the Dafny track, grouped by topic. Every snippet compiles at Dafny 4.11.
IDs in brackets point to the problems that use the construct. `./check dafny E07` checks one problem.

Warnings are errors here: a bodyless lemma, `assume`, or a quantifier without a trigger fails the check.

## 1. Methods, contracts, control flow

```dafny
method Abs(x: int) returns (y: int)       // out-parameter y is the result      [E01]
  requires P                               // caller proves
  ensures y >= 0 && (y == x || y == -x)    // you prove; may mention x, y, old(...)
{ if x < 0 { y := -x; } else { y := x; } }
```

| Construct | Example | Notes / IDs |
|---|---|---|
| call | `var m := Max(a, b);` `m := Max(t, c);` | callers see only `ensures` [E02] |
| several results | `returns (q: nat, r: nat)` / `var q, r := DivMod(17, 5);` | [E22, M36] |
| simultaneous assignment | `x, y := y, x + y;` | right sides read first [E22, M06] |
| early return | `return false;` `return true, lo, hi;` | [E08, M36] |
| `while` | `while i < n invariant 0 <= i <= n decreases n - i { … }` | decreases is guessed only from guards like `i < n`, `i != n` [E06, E45] |
| `for` | `for i := lo to hi invariant P(i) { … }` | i = lo..hi-1; at the head lo <= i <= hi [E07] |
| `downto` | `for i := hi downto lo invariant P(i) { … }` | i = hi-1..lo; at the head, i = last index processed [E44] |
| loop frame | `for j := 1 to n modifies cur invariant … { }` | otherwise a loop may modify everything the method may [H10] |
| aggregate update | `forall i \| 0 <= i < a.Length { a[i] := 2 * a[i]; }` | all reads before all writes [E34] |
| match statement | `match a[w] case Red => … case White => … case Blue => …` | [H03] |
| conditional expr | `if a <= b then a else b` | both arms required [E03] |
| let expr | `var m := SeqMax(s[1..]); if s[0] >= m then s[0] else m` | [E43] |

## 2. Functions, predicates, termination

```dafny
function Fact(n: nat): nat { if n == 0 then 1 else n * Fact(n - 1) }  // compiled in Dafny 4 [E07]
function Min(a: int, b: int): int ensures Min(a, b) <= a { if a <= b then a else b }      [E03]
predicate IsLeap(y: int) { y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) }                  [E04]
ghost predicate Even(n: int) { exists k :: n == 2 * k }   // ghost: not compilable           [E42]
function G(i: int, n: int): int decreases n - i { if i >= n then 0 else G(i + 1, n) }      [E05]
function Ack(m: nat, n: nat): nat decreases m, n { … }   // lexicographic                   [M19]
function SumUpTo(a: array<int>, n: int): int requires 0 <= n <= a.Length reads a decreases n { … }  [E10]
opaque ghost predicate AllNonNeg(s: seq<int>) { … }   // body hidden; reveal AllNonNeg();     [M17]
function Fib(n: nat): nat { … } by method { … return x; }   // spec body + fast code          [M32]
```

- Default `decreases` for a function is its parameters in order; for `nat`/datatype recursion it is usually right. [E05, M19]
- Mutual recursion just works when a shared measure decreases. [M20]
- A recursive function's `ensures` is assumed for its recursive calls, so it can prove itself. [E23, E43]
- A lemma can be called inside a function body: `RevLength(q.back); Queue(Rev(q.back), [])`. [M41]

## 3. Lemmas and proof statements

```dafny
lemma {:induction false} OddSumIsSquare(n: nat) ensures OddSum(n) == n * n
{ if n > 0 { OddSumIsSquare(n - 1); } }                     // induction = recursive call  [E17]
lemma {:induction false} L(a: IntList) ensures …
{ match a case Nil => case Cons(_, t) => L(t); }            // structural induction        [E30]
```

| Tool | Example | IDs |
|---|---|---|
| assert (hint / witness) | `assert 12 > 0 && 12 * 12 == 144;` | [E16] |
| seq extensionality | `assert s[..i + 1][..i] == s[..i];` `assert a[..a.Length] == a[..];` `assert (a + b)[1..] == a[1..] + b;` | [E40, M14] |
| lemma call in code | `SumToFormula(n);` | [E32] |
| calc | `calc { A; == { L(x); } B; == C; }` | [E18, M43] |
| forall statement | `forall n: nat ensures Pow2(n) > 0 { Pow2Pos(n); }` | [E24] |
| … with range / pairs | `forall i, j \| 0 <= i < j < \|s\| ensures P(i, j) { L(s[i], s[j]); }` | [M16] |
| assert forall | `assert forall i \| 0 <= i < \|s\| :: P(s[i]) by { forall i \| 0 <= i < \|s\| { L(s[i]); } }` | [E24] |
| assert by | `assert k < Pow2(k) by { Pow2Grows(k); }` | facts in the block are then forgotten [M15] |
| exists elimination | `var i :\| a == 2 * i;` | [E42, M09] |
| reveal | `reveal AllNonNeg();` `assert P(3) by { reveal P(); }` | [M17] |
| twostate lemma | `twostate lemma L(a: array<int>, i: int) requires a[i] == old(a[i]) + 1 ensures …` | `old` = caller's entry state [M27] |
| least predicate / lemma | `least predicate Ev(n: int) { n == 0 \|\| Ev(n - 2) }` `least lemma S(n: int) requires Ev(n) ensures … { if n != 0 { S(n - 2); } }` | [M44] |
| `{:induction false}` | in a spec: forces you to write the induction | [E17, E30, M21] |

## 4. Quantifiers and triggers

```dafny
forall i :: 0 <= i < a.Length ==> a[i] > 0          // ==> under forall                [E08]
exists i :: 0 <= i < a.Length && a[i] == 0           // && under exists                [E09]
forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]     // pairs                          [M04]
forall x {:trigger g(x)} :: g(x) > 0                 // explicit trigger               [M18]
```

- A quantified fact is instantiated only for terms matching its trigger. `forall x :: f(x) < f(x + 1)` gets the
  multi-trigger `{f(x), f(x+1)}`: mention the missing term (`assert f(0) < f(1) < f(2);`). [M18]
- `s[i]` together with `s[(i - 1) / 2]` is a matching loop: annotate `{:trigger s[i]}`, also on forall statements
  (`forall i {:trigger t[i]} | … ensures … { }`). [H06]
- "Out of resource" with a recursive spec function inside an invariant: trigger on the table, `{:trigger T[p, q]}`. [H10]
- Keep the index in range on both sides of every `a[k]` inside an invariant. [E09]

## 5. Built-in types

| Type | Syntax | IDs |
|---|---|---|
| `int`, `nat`, `bool` | unbounded; `a - b` on nats is int subtraction (assigning a negative to a nat fails) | [E21] |
| subset type | `type Pos = x: int \| x > 0 witness 1` | [E20] |
| `newtype` | `newtype u8 = x: int \| 0 <= x < 256`; `b as int`, `(n as u8)`; no wrap-around | [M29] |
| `bv8` | `0x0F`, `x & y`, `x \| y`, `x ^ y`, `!x`, `x << 1`, `x >> 1`, `-x`, `x - 1` (wrap), `x as int` | [M30] |
| `real` | `1.5`, `2.0`, `n as real`, `r.Floor` | [E36] |
| `char`, `string` | `'a' <= c <= 'z'`, `c as int`, `(n as char)`, `string == seq<char>`, `"abc"` | [E27, M12] |
| tuples | `(3, 2)`, `p.0`, `p.1`, `seq<(int, nat)>`, `var (m, r') := RemoveMin(r);` | [M35, H05] |
| function types | `f: int -> int`, `x => f(g(x))`, `(x: int) => x + 1` | [E38, M34] |

## 6. Collections

| | seq | set | multiset | map |
|---|---|---|---|---|
| literal | `[1, 2]`, `[]` | `{1, 2}`, `{}` | `multiset{1, 1, 2}` | `map[1 := 10]`, `map[]` |
| size / member | `\|s\|`, `x in s` | `\|s\|`, `x in s` | `multiset(s)[x]` (count) | `k in m`, `m.Keys`, `m.Values` |
| access | `s[i]`, `s[..k]`, `s[k..]`, `s[i..j]` | | | `m[k]` (needs `k in m`) |
| build | `s + t`, `s[i := v]`, `seq(n, i => e)` | `a + b`, `a * b`, `a - b` | `multiset(s)`, `+` | `m[k := v]` |
| comprehension | `seq(\|s\|, i requires 0 <= i < \|s\| => s[i])` | `set x \| x in s && P(x)`, `set x \| x in s :: f(x)` | | `map k \| k in s :: e` |
| IDs | [E12, E35] | [E13, E41, M39] | [E14, M10] | [E15, M40] |

Facts the verifier knows: `multiset(s + t) == multiset(s) + multiset(t)`, `x in multiset(s) <==> x in s`,
`|s - {x}| == |s| - 1` when `x in s`. Equalities of seqs are proved element-wise once you *state* them.

## 7. Arrays

```dafny
method M(a: array<int>, src: array<int>) modifies a      // a is never null (array?<int> is)  [E08, E11]
a[i] := a[i] + 1;  a[i], a[j] := a[j], a[i];  old(a[i])  old(a[..])  old(a[..k])          [E11, E14, E37]
a := new int[n];  a := new int[n](i => i * i);  var b := new int[] [1, 2, 3];  fresh(a)     [E33]
var t := new int[r, c];  t.Length0  t.Length1  t[i, j]                                      [M33, H10]
```

- Loop invariants over arrays need the untouched part too: `forall j :: i <= j < a.Length ==> a[j] == old(a[j])`. [E11]
- Distinct arrays: `requires src != dst`; a `fresh` array cannot alias an argument. [E37, M13]
- Frame for a range: `forall k :: 0 <= k < lo || hi <= k < a.Length ==> a[k] == old(a[k])`. [H09]

## 8. Datatypes

```dafny
datatype Shape = Square(side: nat) | Rect(w: nat, h: nat)                    [E19]
match s case Square(a) => a * a case Rect(w, h) => w * h                     // s.Square?  s.side
datatype Option<T> = None | Some(value: T)                                   [E28]
datatype List<T> = Nil | Cons(head: T, tail: List<T>)                        [M21]
a.(balance := a.balance + amount)                                            // update [E31]
datatype Result<T> = Success(value: T) | Failure(error: string) {            [M28]
  predicate IsFailure() { Failure? }
  function PropagateFailure<U>(): Result<U> requires IsFailure() { Failure(error) }
  function Extract(): T requires !IsFailure() { value }
}
var x :- SafeDiv(a, b);                                                      // propagate failure
```

## 9. Classes, traits, modules

```dafny
class Counter { var count: nat  constructor (s: nat) ensures count == s { count := s; } }     [M24]
method Inc() modifies this ensures count == old(count) + 1
var c := new Counter(5);  fresh(c)  requires from != to  modifies from, to
trait Shape { function Perimeter(): nat reads this  method Grow(d: nat) modifies this ensures … }  [M26]
class Square extends Shape { … }    var shapes: seq<Shape> := [sq as Shape, r as Shape];
module MathLib { export provides Abs, AbsNonNeg  function Abs(x: int): int { … } … }        [M31]
module Client1 { import opened MathLib … }   module Client2 { import M = MathLib … M.Abs(x) }
```

Dynamic frames [M25, H04]:

```dafny
ghost var Contents: seq<int>          // what clients reason about
ghost var Repr: set<object>           // objects owned by this structure
ghost predicate Valid() reads this, Repr ensures Valid() ==> this in Repr { this in Repr && data in Repr && … }
method Push(x: int) requires Valid() modifies Repr
  ensures Valid() && fresh(Repr - old(Repr)) && Contents == old(Contents) + [x]
```

## 10. Common traps

| Symptom | Fix | IDs |
|---|---|---|
| postcondition fails after a loop | add the invariant that says what the loop has done so far; check the exit gives the spec | [E06] |
| "index out of range" in an invariant | bound the index from both sides | [E09, M12] |
| `a[..i+1]` vs `a[..i]` facts don't connect | `assert a[..i + 1] == a[..i] + [a[i]];` or `assert a[..i+1][..i] == a[..i];` | [M02, E40] |
| "cannot prove termination" | `decreases` clause (lexicographic `m, n` if needed) | [E05, E45, M19] |
| "cannot find witness" | `witness w` on the subset type | [E20] |
| "insufficient reads clause" | `reads a` / `reads this, Repr` | [E10] |
| nat subtraction rejected | branch so the larger value comes first | [E21] |
| nonlinear step fails | spell out the product in a `calc` or an `assert` | [M07, M43] |
| lemma "proved by itself" | that's automatic induction; specs here use `{:induction false}` when the induction is the exercise | [E17] |
| "out of resource" | smaller proof units (helper lemmas on seqs), explicit triggers, avoid `%` (see `Wrap` in H04) | [H04, H06, H09, H10] |

## Cheatsheet

| Need | Write |
|---|---|
| contract | `method M(x: int) returns (r: int) requires P ensures Q` |
| function / predicate | `function F(n: nat): nat { … }` · `predicate P(x: int) { … }` · `ghost predicate` |
| conditional expr | `if c then a else b` · `var y := e; body` |
| while loop | `while g invariant I decreases D { … }` |
| for loop | `for i := lo to hi invariant I { … }` · `for i := hi downto lo` |
| array | `a.Length` `a[i]` `a[..]` `a[lo..hi]` `new int[n](i => e)` `fresh(a)` |
| frame | `modifies a` · `reads a` · `old(a[i])` · `old(a[..])` |
| 2-D array | `new int[r, c]` `m.Length0` `m.Length1` `m[i, j]` |
| swap | `a[i], a[j] := a[j], a[i];` |
| quantifiers | `forall i :: R ==> P` · `exists i :: R && P` · `{:trigger t}` |
| seq | `\|s\|` `s[i]` `s[..k]` `s[k..]` `s + t` `[x]` `s[i := v]` `seq(n, i => e)` |
| set | `{}` `x in s` `a + b` `a * b` `a - b` `set x \| x in s :: f(x)` |
| multiset | `multiset(s)` `multiset(s)[x]` `multiset{x}` |
| map | `map[]` `k in m` `m[k]` `m[k := v]` `m.Keys` `map k \| k in s :: e` |
| lemma | `lemma L(n: nat) requires P ensures Q { … }` |
| induction | `{ if n > 0 { L(n - 1); } }` · `match t case Leaf => case Node(l, _, r) => L(l); L(r);` |
| no auto-induction | `lemma {:induction false} L(...)` |
| hint | `assert e;` · `assert e by { L(); }` · `L(x);` |
| seq equality | `assert s[..i+1][..i] == s[..i];` · `assert a[..a.Length] == a[..];` |
| universal | `forall x \| R ensures P { L(x); }` |
| existential | provide: `assert P(w);` · use: `var w :\| P(w);` |
| calc | `calc { A; == { L(); } B; }` |
| subset type | `type Pos = x: int \| x > 0 witness 1` |
| newtype / bv | `newtype u8 = x: int \| 0 <= x < 256` · `x: bv8`, `x & (x - 1)` |
| real / char | `n as real` `r.Floor` · `'a' <= c <= 'z'` `c as int` |
| datatype | `datatype D = A(x: int) \| B` · `d.A?` `d.x` · `d.(x := 1)` |
| match | `match d case A(x) => … case B => …` |
| Option / tuple | `Some(v)` `None` `o.value` · `(a, b)` `p.0` |
| generic | `function F<T(==)>(s: seq<T>, x: T): nat` |
| lambda | `x => x + 1` · `f: int -> int` |
| opaque | `opaque function F…` · `reveal F();` |
| class | `class C { var f: int  constructor () ensures … { … } }` · `new C()` |
| dynamic frames | `ghost var Repr: set<object>` · `modifies Repr` · `fresh(Repr - old(Repr))` |
| trait | `trait T { … }` · `class C extends T { … }` · `x as T` |
| failure / `:-` | `IsFailure()` `PropagateFailure()` `Extract()` · `var x :- M();` |
| by method | `function F(n: nat): nat { spec } by method { code; return r; }` |
| twostate | `twostate lemma L(a: array<int>) requires old(a[0]) < a[0] ensures …` |
| least predicate | `least predicate P(n: int) { … }` · `least lemma L(n: int) requires P(n) ensures …` |
| module | `module M { export provides F … }` · `import opened M` · `import X = M` |
