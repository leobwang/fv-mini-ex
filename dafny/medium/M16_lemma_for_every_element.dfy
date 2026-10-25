// M16 | Lemma for every element | 10-15 min | forall statement, pair quantifier, induction
// GOAL
//   Prove Pow2 monotone, then lift it pointwise: mapping Pow2 over a sorted seq keeps it sorted.
//
// REFERENCE
//   forall i, j | 0 <= i < j < |s| ensures P(i, j) { L(s[i], s[j]); }   // lemma for every pair
//   lemma {:induction false} M(m: nat, n: nat) requires m <= n ensures F(m) <= F(n)
//   { if m < n { M(m, n - 1); } }          // induct on the distance by shrinking n

// BEGIN SPEC
function Pow2(n: nat): nat { if n == 0 then 1 else 2 * Pow2(n - 1) }

function MapPow2(s: seq<nat>): seq<nat>
  ensures |MapPow2(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> MapPow2(s)[i] == Pow2(s[i])
{
  seq(|s|, i requires 0 <= i < |s| => Pow2(s[i]))
}

lemma {:induction false} Pow2Mono(m: nat, n: nat)
  requires m <= n
  ensures Pow2(m) <= Pow2(n)
// END SPEC
{
}

// BEGIN SPEC
lemma SortedMap(s: seq<nat>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| ==> MapPow2(s)[i] <= MapPow2(s)[j]
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Pow2Mono: if m < n, compare Pow2(m) with Pow2(n - 1), then Pow2(n - 1) with Pow2(n).
H2. SortedMap: a forall statement over all pairs (i, j), each calling Pow2Mono.
H3. if m < n { Pow2Mono(m, n - 1); }
    forall i, j | 0 <= i < j < |s| ensures MapPow2(s)[i] <= MapPow2(s)[j] { Pow2Mono(s[i], s[j]); }
*/
