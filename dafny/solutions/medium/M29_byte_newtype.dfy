// M29 | Byte newtype | 8-12 min | newtype, range, conversions
// GOAL
//   Implement saturating add/sub and an overflow-free average on an 8-bit newtype.
//
// REFERENCE
//   newtype u8 = x: int | 0 <= x < 256     // a NEW numeric type (not interchangeable with int)
//   var b: u8 := 200;   b as int   (n as u8)   // literals; conversions (n must be in range)
//   a + b                                   // u8 arithmetic: the result must stay in range,
//                                           // or it is a verification error (no wrap-around)
//   if a as int + b as int > 255 then 255 else a + b

// BEGIN SPEC
newtype u8 = x: int | 0 <= x < 256

function SatAdd(a: u8, b: u8): u8
  ensures SatAdd(a, b) as int == if a as int + b as int > 255 then 255 else a as int + b as int
// END SPEC
{
  if a as int + b as int > 255 then 255 else a + b
}

// BEGIN SPEC
function SatSub(a: u8, b: u8): u8
  ensures SatSub(a, b) as int == if a < b then 0 else a as int - b as int
// END SPEC
{
  if a < b then 0 else a - b
}

// BEGIN SPEC
function Avg(a: u8, b: u8): u8
  ensures Avg(a, b) as int == (a as int + b as int) / 2
// END SPEC
{
  ((a as int + b as int) / 2) as u8
}

// BEGIN SPEC
method SumSat(s: seq<u8>) returns (t: u8)
  ensures forall i :: 0 <= i < |s| ==> s[i] <= t
// END SPEC
{
  t := 0;
  for i := 0 to |s|
    invariant forall k :: 0 <= k < i ==> s[k] <= t
  {
    t := SatAdd(t, s[i]);
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Do range decisions in int; only build u8 values that are provably in range.
H2. (a + b) / 2 in u8 may overflow before dividing; convert to int first.
H3. if a as int + b as int > 255 then 255 else a + b      ((a as int + b as int) / 2) as u8
*/
