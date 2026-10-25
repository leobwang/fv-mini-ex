// M39 | Elements to set | 8-12 min | set accumulation, set comprehension, cardinality
// GOAL
//   Collect the elements of an array into a set, and show the set is no larger than the array.
//
// REFERENCE
//   set i | 0 <= i < n :: a[i]            // the values at indices below n
//   s := s + {a[i]};                       // add one element
//   |s + {x}| <= |s| + 1                   // the verifier knows this cardinality fact
//   invariant s == set k | 0 <= k < i :: a[k]
//   // Set equality is extensional; a membership-style invariant can be easier to maintain.

// BEGIN SPEC
method ToSet(a: array<int>) returns (s: set<int>)
  ensures s == set i | 0 <= i < a.Length :: a[i]
  ensures |s| <= a.Length
// END SPEC
{
  s := {};
  for i := 0 to a.Length
    invariant s == set k | 0 <= k < i :: a[k]
    invariant |s| <= i
  {
    s := s + {a[i]};
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One loop adding a[i] each time.
H2. Two invariants: s equals the comprehension over [0, i), and |s| <= i.
H3. invariant s == set k | 0 <= k < i :: a[k]    invariant |s| <= i
*/
