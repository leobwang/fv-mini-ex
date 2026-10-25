// M30 | Bit tricks | 8-12 min | bv8, bitwise operators, conversions
// GOAL
//   Implement classic bit tricks on bytes; the verifier checks them by bit-blasting.
//
// REFERENCE
//   x: bv8    0x0F    1 as bv8         // 8-bit vectors (arithmetic wraps modulo 256)
//   x & y   x | y   x ^ y   !x         // and, or, xor, complement
//   x << 1   x >> 1    -x    x - 1     // shifts; negation and subtraction wrap
//   x as int    (n as bv8)             // conversions (n must be in range)
//   x in {1, 2, 4}                     // set literal of bv8 values

// BEGIN SPEC
method IsPowerOfTwo(x: bv8) returns (r: bool)
  ensures r <==> x in {1, 2, 4, 8, 16, 32, 64, 128}
// END SPEC
{
}

// BEGIN SPEC
function LowestSetBit(x: bv8): bv8
  ensures x == 0 ==> LowestSetBit(x) == 0
  ensures x != 0 ==> LowestSetBit(x) in {1, 2, 4, 8, 16, 32, 64, 128}
  ensures x != 0 ==> x & LowestSetBit(x) == LowestSetBit(x)
  ensures x & (LowestSetBit(x) - 1) == 0
// END SPEC
{
  0 // TODO
}

// BEGIN SPEC
function ClearLowestSetBit(x: bv8): bv8
  ensures ClearLowestSetBit(x) == x ^ LowestSetBit(x)
// END SPEC
{
  0 // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Subtracting 1 flips the lowest set bit and every zero below it.
H2. x & (x - 1) clears the lowest set bit; it is 0 exactly for powers of two (and 0 itself).
    In two's complement, -x keeps the lowest set bit of x and flips everything above it.
H3. x != 0 && x & (x - 1) == 0      x & -x      x & (x - 1)
*/
