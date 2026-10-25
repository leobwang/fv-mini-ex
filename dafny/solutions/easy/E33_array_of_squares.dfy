// E33 | Array of squares | 1-2 min | new, fresh, initializer
// GOAL
//   Allocate and return an array holding 0, 1, 4, 9, ..., (n-1)^2.
//
// REFERENCE
//   a := new int[n];                    // allocate (contents unspecified to the verifier)
//   a := new int[n](i => i + 1);        // allocate with an initializer function of the index
//   var b := new int[] [1, 2, 3];       // allocate from a display
//   ensures fresh(a)                    // a was allocated by this method (no aliasing)

// BEGIN SPEC
method Squares(n: nat) returns (a: array<int>)
  ensures fresh(a) && a.Length == n
  ensures forall i :: 0 <= i < n ==> a[i] == i * i
// END SPEC
{
  a := new int[n](i => i * i);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One statement. No loop needed.
H2. The array constructor can take a lambda from index to value.
H3. a := new int[n](i => i * i);
*/
