// M42 | Binary round trip | 15-20 min | seq<bool>, div/mod induction, canonical forms
// GOAL
//   Write ToBin (least significant bit first, no trailing false). Prove both round trips.
//
// REFERENCE
//   [n % 2 == 1] + ToBin(n / 2)         // one bit, then the rest
//   b[|b| - 1]                          // last bit (canonical: true, unless b == [])
//   assert ([x] + s)[1..] == s;         // tail of a cons
//   // (bit + 2 * k) % 2 == bit and (bit + 2 * k) / 2 == k for bit in {0, 1}, k >= 0.

// BEGIN SPEC
function FromBin(b: seq<bool>): nat
{
  if |b| == 0 then 0 else (if b[0] then 1 else 0) + 2 * FromBin(b[1..])
}

predicate Canonical(b: seq<bool>) { |b| == 0 || b[|b| - 1] }

function ToBin(n: nat): seq<bool>
  ensures Canonical(ToBin(n))
// END SPEC
{
  if n == 0 then [] else [n % 2 == 1] + ToBin(n / 2)
}

// BEGIN SPEC
lemma {:induction false} FromTo(n: nat)
  ensures FromBin(ToBin(n)) == n
// END SPEC
{
  if n > 0 {
    assert ToBin(n)[1..] == ToBin(n / 2);
    FromTo(n / 2);
  }
}

// BEGIN SPEC
lemma {:induction false} ToFrom(b: seq<bool>)
  requires Canonical(b)
  ensures ToBin(FromBin(b)) == b
// END SPEC
{
  if |b| > 0 {
    var k := FromBin(b[1..]);
    assert Canonical(b[1..]);
    ToFrom(b[1..]);
    PositiveIfNonEmpty(b);
    assert FromBin(b) / 2 == k;
    assert (FromBin(b) % 2 == 1) == b[0];
    assert b == [b[0]] + b[1..];
  }
}

lemma PositiveIfNonEmpty(b: seq<bool>)
  requires Canonical(b) && |b| > 0
  ensures FromBin(b) > 0
{
  if |b| > 1 { PositiveIfNonEmpty(b[1..]); }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. ToBin(0) is []. Induction for FromTo is on n via n / 2; for ToFrom on b via b[1..].
H2. ToFrom needs FromBin(b) > 0 whenever b is canonical and non-empty (its own small lemma);
    then FromBin(b) % 2 is b[0]'s bit and FromBin(b) / 2 is FromBin(b[1..]).
H3. lemma PositiveIfNonEmpty(b: seq<bool>) requires Canonical(b) && |b| > 0 ensures FromBin(b) > 0
*/
