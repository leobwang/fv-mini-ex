// E28 | Find with Option | 2-3 min | generic datatype, Option
// GOAL
//   Return Some(i) with s[i] == x, or None when x does not occur in s.
//
// REFERENCE
//   datatype Option<T> = None | Some(value: T)       // generic datatype
//   Some(3)   None   o.Some?   o.value               // build, test, project
//   match o case None => 0 case Some(v) => v + 1     // match expression
//   x in s    x !in s                                // seq membership

// BEGIN SPEC
datatype Option<T> = None | Some(value: T)

function Find(s: seq<int>, x: int): Option<nat>
  ensures Find(s, x).Some? ==> Find(s, x).value < |s| && s[Find(s, x).value] == x
  ensures Find(s, x).None? ==> x !in s
// END SPEC
{
  if |s| == 0 then None
  else if s[0] == x then Some(0)
  else match Find(s[1..], x)
    case None => None
    case Some(i) => Some(i + 1)
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Recurse on s[1..]. An index into s[1..] is off by one from an index into s.
H2. Three cases: empty, head matches, otherwise shift the recursive answer.
H3. ... else match Find(s[1..], x) case None => None case Some(i) => Some(i + 1)
*/
