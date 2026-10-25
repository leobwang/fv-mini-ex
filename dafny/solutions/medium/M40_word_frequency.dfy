// M40 | Word frequency | 12-15 min | map<string, nat>, spec count
// GOAL
//   Count how often each word occurs. The keys are exactly the words that occur.
//
// REFERENCE
//   m: map<string, nat>   m[w := m[w] + 1]   w in m      // map update and membership (E15)
//   invariant forall w :: w in m <==> w in words[..i]
//   invariant forall w :: w in m ==> m[w] == Count(words[..i], w)
//   invariant forall w :: w !in m ==> Count(words[..i], w) == 0    // the case for new keys
//   assert words[..i + 1][..i] == words[..i];                      // unfold Count (E40)

// BEGIN SPEC
function Count(s: seq<string>, w: string): nat
{
  if |s| == 0 then 0
  else Count(s[..|s| - 1], w) + (if s[|s| - 1] == w then 1 else 0)
}

method Frequencies(words: seq<string>) returns (m: map<string, nat>)
  ensures forall w :: w in m <==> w in words
  ensures forall w :: w in m ==> m[w] == Count(words, w)
// END SPEC
{
  m := map[];
  for i := 0 to |words|
    invariant forall w :: w in m <==> w in words[..i]
    invariant forall w :: w in m ==> m[w] == Count(words[..i], w)
    invariant forall w :: w !in m ==> Count(words[..i], w) == 0
  {
    assert words[..i + 1][..i] == words[..i];
    assert words[..i + 1] == words[..i] + [words[i]];
    var x := words[i];
    if x in m {
      m := m[x := m[x] + 1];
    } else {
      m := m[x := 1];
    }
  }
  assert words[..|words|] == words;
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. One pass; for each word either bump its count or insert it with count 1.
H2. Besides the two "result" invariants, record that words not in m have count 0 so far.
H3. invariant forall w :: w !in m ==> Count(words[..i], w) == 0
    (plus assert words[..i + 1][..i] == words[..i]; and words[..i + 1] == words[..i] + [words[i]];)
*/
