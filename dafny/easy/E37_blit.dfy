// E37 | Blit | 3 min | array slices, old, aliasing
// GOAL
//   Copy src into dst starting at position at, leaving the rest of dst unchanged.
//
// REFERENCE
//   a[lo..hi]   a[..k]   a[k..]          // slices of an array are seqs (read the heap)
//   old(a[..k])                          // the slice as it was at method entry
//   requires src != dst                  // distinct arrays: writing dst cannot change src
//   for i := 0 to n invariant P(i) { }   // the for-loop from E07
//   // Equalities of slices are often easier to prove from pointwise forall invariants.

// BEGIN SPEC
method Blit(src: array<int>, dst: array<int>, at: nat)
  requires src != dst
  requires at + src.Length <= dst.Length
  modifies dst
  ensures dst[..at] == old(dst[..at])
  ensures dst[at..at + src.Length] == src[..]
  ensures dst[at + src.Length..] == old(dst[at + src.Length..])
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One loop over the indices of src.
H2. Three pointwise invariants: the part before at, the copied part, and everything after.
H3. invariant forall k :: 0 <= k < i ==> dst[at + k] == src[k]
    invariant forall k :: at + i <= k < dst.Length ==> dst[k] == old(dst[k])   (plus the prefix)
*/
