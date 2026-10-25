// M27 | Two-state lemma | 15-20 min | twostate lemma, old, seq update
// GOAL
//   Bump increments one array element. Prove the array's Sum grows by exactly 1, via a seq lemma
//   and a twostate lemma that relates the method's pre-state (old) and the current state.
//
// REFERENCE
//   twostate lemma L(a: array<int>) requires old(a[0]) < a[0] ensures ...   // sees two heaps
//   L(a);                               // called in a method: old = the method's entry state
//   s[i := v]                           // seq with index i replaced by v
//   assert a[..] == old(a[..])[i := a[i]];
//   lemma U(s: seq<int>, i: int, v: int) requires 0 <= i < |s| ensures F(s[i := v]) == ...

// BEGIN SPEC
function Sum(s: seq<int>): int { if |s| == 0 then 0 else s[0] + Sum(s[1..]) }

twostate lemma SumBumped(a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires a[i] == old(a[i]) + 1
  requires forall j :: 0 <= j < a.Length && j != i ==> a[j] == old(a[j])
  ensures Sum(a[..]) == Sum(old(a[..])) + 1
// END SPEC
{
  assert a[..] == old(a[..])[i := a[i]];
  SumUpdate(old(a[..]), i, a[i]);
}

lemma SumUpdate(s: seq<int>, i: int, v: int)
  requires 0 <= i < |s|
  ensures Sum(s[i := v]) == Sum(s) - s[i] + v
{
  if i > 0 {
    assert s[i := v][1..] == s[1..][i - 1 := v];
    SumUpdate(s[1..], i - 1, v);
  }
}

// BEGIN SPEC
method Bump(a: array<int>, i: int)
  requires 0 <= i < a.Length
  modifies a
  ensures Sum(a[..]) == Sum(old(a[..])) + 1
// END SPEC
{
  a[i] := a[i] + 1;
  SumBumped(a, i);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. First prove how Sum changes when one index of a *seq* is replaced (plain lemma, induction).
H2. In the twostate lemma, express the new contents as old(a[..])[i := a[i]] and apply the seq
    lemma. In Bump, write a[i] then call the twostate lemma.
H3. lemma SumUpdate(s: seq<int>, i: int, v: int) requires 0 <= i < |s|
      ensures Sum(s[i := v]) == Sum(s) - s[i] + v
    (step: assert s[i := v][1..] == s[1..][i - 1 := v]; for i > 0)
*/
