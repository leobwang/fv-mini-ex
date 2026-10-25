// M35 | Run-length encoding | 15-20 min | tuples, decode spec, helper lemma
// GOAL
//   Encode s as maximal runs (value, count) so that decoding gives s back.
//
// REFERENCE
//   (3, 2)    p.0    p.1    seq<(int, nat)>      // tuples and projections
//   seq(n, _ => x)                               // n copies of x
//   assert Repeat(x, n + 1) == Repeat(x, n) + [x];
//   invariant Decode(runs) + Repeat(cur, cnt) == s[..i]   // closed runs + the open run
//   // Decode recurses from the front; appending a run at the back needs a lemma.

// BEGIN SPEC
function Repeat(x: int, n: nat): seq<int> { seq(n, _ => x) }

function Decode(runs: seq<(int, nat)>): seq<int>
{
  if |runs| == 0 then [] else Repeat(runs[0].0, runs[0].1) + Decode(runs[1..])
}

method Encode(s: seq<int>) returns (runs: seq<(int, nat)>)
  ensures Decode(runs) == s
  ensures forall i :: 0 <= i < |runs| ==> runs[i].1 > 0
  ensures forall i :: 0 <= i < |runs| - 1 ==> runs[i].0 != runs[i + 1].0
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Keep the closed runs in runs and the run in progress as (cur, cnt). Close it when the value
    changes, and once more at the end.
H2. Needed lemma: Decode(runs + [r]) == Decode(runs) + Repeat(r.0, r.1), by induction on runs.
    Track that the last closed run's value differs from cur.
H3. invariant Decode(runs) + Repeat(cur, cnt) == s[..i]
    invariant |runs| > 0 ==> runs[|runs| - 1].0 != cur
*/
