// M34 | Map and filter | 10-15 min | higher-order functions, seq lemmas
// GOAL
//   Write MapSeq, then prove that Filter keeps only elements of s satisfying p, and that it
//   distributes over concatenation.
//
// REFERENCE
//   function G<T>(p: T -> bool, s: seq<T>): seq<T>     // a function-typed parameter
//   p(x)                                                // apply it
//   seq(|s|, i requires 0 <= i < |s| => f(s[i]))        // comprehension (E35)
//   assert (a + b)[1..] == a[1..] + b;                  // extensionality step (M14)

// BEGIN SPEC
function MapSeq<T, U>(f: T -> U, s: seq<T>): seq<U>
  ensures |MapSeq(f, s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> MapSeq(f, s)[i] == f(s[i])
// END SPEC
{
  [] // TODO
}

// BEGIN SPEC
function Filter<T>(p: T -> bool, s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else if p(s[0]) then [s[0]] + Filter(p, s[1..])
  else Filter(p, s[1..])
}

lemma {:induction false} FilterSound<T>(p: T -> bool, s: seq<T>)
  ensures forall x :: x in Filter(p, s) ==> x in s && p(x)
// END SPEC
{
}

// BEGIN SPEC
lemma {:induction false} FilterConcat<T>(p: T -> bool, a: seq<T>, b: seq<T>)
  ensures Filter(p, a + b) == Filter(p, a) + Filter(p, b)
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. MapSeq is a seq comprehension. Both lemmas: induction on the first seq argument.
H2. FilterSound: recursive call on s[1..] suffices. FilterConcat: when a is non-empty, relate
    (a + b)[1..] to a[1..] + b first; when a is empty, a + b == b.
H3. if |a| == 0 { assert a + b == b; } else { assert (a + b)[1..] == a[1..] + b; FilterConcat(p, a[1..], b); }
*/
