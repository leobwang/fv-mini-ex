// E34 | Double in place | 1-3 min | aggregate forall statement
// GOAL
//   Implement both methods with a single forall statement each (no loops, no invariants).
//
// REFERENCE
//   forall i | 0 <= i < a.Length { a[i] := 0; }     // update all indices "at once"
//   forall i | 0 <= i < n { a[i] := a[i] + b[i]; }  // right sides read the state *before*
//                                                    // any of the updates happen
//   // The verifier checks that no two iterations write the same location.

// BEGIN SPEC
method DoubleAll(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 2 * old(a[i])
// END SPEC
{
  forall i | 0 <= i < a.Length { a[i] := 2 * a[i]; }
}

// BEGIN SPEC
method ShiftLeft(a: array<int>)
  requires a.Length > 0
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[i + 1])
  ensures a[a.Length - 1] == old(a[a.Length - 1])
// END SPEC
{
  forall i | 0 <= i < a.Length - 1 { a[i] := a[i + 1]; }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Each method is one forall statement; think about which indices it ranges over.
H2. Because all reads happen before all writes, a[i] := a[i + 1] does not "smear" values.
H3. forall i | 0 <= i < a.Length { a[i] := 2 * a[i]; }  and  forall i | 0 <= i < a.Length - 1 { ... }
*/
