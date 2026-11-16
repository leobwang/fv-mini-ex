// E08 | All positive | 2-3 min | array, Length, forall
// GOAL
//   Return whether every element of the array is positive.
//
// REFERENCE
//   a: array<int>    a.Length    a[i]          // arrays live on the heap; index from 0
//   forall j :: 0 <= j < i ==> a[j] > 0        // bounded universal quantifier
//   invariant 0 <= i <= a.Length               // keep the index in range
//   return false;                              // early return (sets the out-parameters first)
//   // array<int> is never null in Dafny 4 (the nullable type is array?<int>).

// BEGIN SPEC
method AllPositive(a: array<int>) returns (b: bool)
  ensures b <==> forall i :: 0 <= i < a.Length ==> a[i] > 0
// END SPEC
{
  var i := 0;
  for i := 0 to a.Length
  invariant 0 <= i <= a.Length
  invariant forall j :: 0 <= j < i ==> a[j] > 0
  {
    if a[i] <= 0 {return false;}
  }
  return true;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Scan left to right; stop as soon as you see a non-positive element.
H2. The invariant says the prefix a[0..i) is all positive. At exit (i == a.Length) that is the spec.
H3. invariant 0 <= i <= a.Length   invariant forall j :: 0 <= j < i ==> a[j] > 0
*/
