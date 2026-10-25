// H10 | Longest common subsequence | 40-75 min | DP table, array2, nested loop invariants
// GOAL
//   Compute the LCS length of a and b bottom-up in a 2-D table, in O(|a| * |b|) time; prove it
//   equals the (exponential) recursive specification LCS(a, b, |a|, |b|).
//
// REFERENCE
//   var T := new nat[m + 1, n + 1];          // 2-D array (M33); T[i, j] for 0 <= i <= m ...
//   T[i, j] := if a[i - 1] == b[j - 1] then T[i - 1, j - 1] + 1 else Max(T[i - 1, j], T[i, j - 1]);
//   invariant forall p, q :: 0 <= p < i && 0 <= q <= n ==> T[p, q] == LCS(a, b, p, q)
//   for j := 0 to n + 1 { ... }               // inner loop over a whole row
//   // Fill row 0 and column 0 too (or start the loops at 1 after initializing them).
//   for j := 1 to n + 1 modifies cur invariant ... { }   // loop frame: only cur changes
// NOTE: "out of resource"? Give table invariants {:trigger T[p, q]}: if LCS(...) terms trigger
//   them, every unfolding of LCS spawns new instances.

// BEGIN SPEC
function Max(x: nat, y: nat): nat { if x >= y then x else y }

function LCS(a: seq<int>, b: seq<int>, i: nat, j: nat): nat
  requires i <= |a| && j <= |b|
{
  if i == 0 || j == 0 then 0
  else if a[i - 1] == b[j - 1] then LCS(a, b, i - 1, j - 1) + 1
  else Max(LCS(a, b, i - 1, j), LCS(a, b, i, j - 1))
}

method LCSLength(a: seq<int>, b: seq<int>) returns (len: nat)
  ensures len == LCS(a, b, |a|, |b|)
// END SPEC
{
  var m, n := |a|, |b|;
  var T := new nat[m + 1, n + 1];
  for i := 0 to m + 1
    invariant forall p, q {:trigger T[p, q]} :: 0 <= p < i && 0 <= q <= n ==> T[p, q] == LCS(a, b, p, q)
  {
    for j := 0 to n + 1
      invariant forall p, q {:trigger T[p, q]} :: 0 <= p < i && 0 <= q <= n ==> T[p, q] == LCS(a, b, p, q)
      invariant forall q {:trigger T[i, q]} :: 0 <= q < j ==> T[i, q] == LCS(a, b, i, q)
    {
      var v: nat;
      if i == 0 || j == 0 {
        v := 0;
      } else if a[i - 1] == b[j - 1] {
        v := T[i - 1, j - 1] + 1;
      } else {
        v := Max(T[i - 1, j], T[i, j - 1]);
      }
      assert v == LCS(a, b, i, j);
      T[i, j] := v;
    }
  }
  len := T[m, n];
}

// MILESTONE (optional: change or delete)
// The table is correct on all rows above i, and on row i left of column j.
ghost predicate Filled(T: array2<nat>, a: seq<int>, b: seq<int>, i: int, j: int)
  reads T
  requires T.Length0 == |a| + 1 && T.Length1 == |b| + 1
  requires 0 <= i <= |a| && 0 <= j <= |b| + 1
{
  (forall p, q :: 0 <= p < i && 0 <= q <= |b| ==> T[p, q] == LCS(a, b, p, q)) &&
  (forall q :: 0 <= q < j ==> T[i, q] == LCS(a, b, i, q))
}

// MILESTONE (optional: change or delete)
// Space-saving variant: only the previous row is needed. Same answer, O(|b|) memory.
method LCSTwoRows(a: seq<int>, b: seq<int>) returns (len: nat)
  ensures len == LCS(a, b, |a|, |b|)
{
  var n := |b|;
  var prev := new nat[n + 1](_ => 0);
  for i := 1 to |a| + 1
    invariant fresh(prev) && prev.Length == n + 1
    invariant forall q :: 0 <= q <= n ==> prev[q] == LCS(a, b, i - 1, q)
  {
    var cur := new nat[n + 1];
    cur[0] := 0;
    for j := 1 to n + 1
      modifies cur
      invariant forall q :: 0 <= q < j ==> cur[q] == LCS(a, b, i, q)
    {
      if a[i - 1] == b[j - 1] {
        cur[j] := prev[j - 1] + 1;
      } else {
        cur[j] := Max(prev[j], cur[j - 1]);
      }
    }
    prev := cur;
  }
  len := prev[n];
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Fill the table row by row, left to right, so T[i - 1, *] and T[i, j - 1] are ready when you
    compute T[i, j]. The entry T[i, j] mirrors one unfolding of LCS(a, b, i, j).
H2. Outer invariant: rows 0 .. i-1 are correct. Inner invariant: the outer one, plus row i is
    correct left of j. The verifier unfolds LCS once per new cell by itself.
H3. invariant forall p, q {:trigger T[p, q]} :: 0 <= p < i && 0 <= q <= n ==> T[p, q] == LCS(a, b, p, q)
    inner: invariant forall q {:trigger T[i, q]} :: 0 <= q < j ==> T[i, q] == LCS(a, b, i, q)
    (compute the new value into a local v, assert v == LCS(a, b, i, j), then write T[i, j] := v)
*/
