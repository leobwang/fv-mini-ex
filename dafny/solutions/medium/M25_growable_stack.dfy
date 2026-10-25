// M25 | Growable stack | 15-20 min | Valid, Repr, ghost Contents, dynamic frames
// GOAL
//   Implement a stack backed by an array that doubles when full. Clients see only the ghost
//   Contents; Valid() ties it to the array. Keep Valid() and Repr up to date in every method.
//
// REFERENCE
//   ghost var Contents: seq<int>        // abstract state (what clients reason about)
//   ghost var Repr: set<object>         // every object the stack owns (this, data, ...)
//   reads this, Repr    modifies Repr   // frames expressed through Repr
//   ensures fresh(Repr - old(Repr))     // only newly allocated objects were added
//   Contents := Contents + [x];  Repr := Repr + {nd};   // ghost updates are ordinary assignments
//   forall i | 0 <= i < size { nd[i] := data[i]; }      // copy into a fresh array

// BEGIN SPEC
class Stack {
  ghost var Contents: seq<int>
  ghost var Repr: set<object>
  var data: array<int>
  var size: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr && data in Repr &&
    0 < data.Length && size <= data.Length &&
    Contents == data[..size]
  }

  constructor ()
    ensures Valid() && fresh(Repr) && Contents == []
// END SPEC
  {
    data := new int[4];
    size := 0;
    Contents := [];
    Repr := {this, data};
  }

// BEGIN SPEC
  method Push(x: int)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [x]
// END SPEC
  {
    if size == data.Length {
      var nd := new int[2 * data.Length];
      forall i | 0 <= i < size { nd[i] := data[i]; }
      data := nd;
      Repr := Repr + {nd};
    }
    data[size] := x;
    size := size + 1;
    Contents := Contents + [x];
  }

// BEGIN SPEC
  method Pop() returns (x: int)
    requires Valid() && |Contents| > 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures x == old(Contents)[|old(Contents)| - 1]
    ensures Contents == old(Contents)[..|old(Contents)| - 1]
// END SPEC
  {
    size := size - 1;
    x := data[size];
    Contents := Contents[..size];
  }
}

// BEGIN SPEC
method Client()
{
  var s := new Stack();
  s.Push(1); s.Push(2); s.Push(3); s.Push(4); s.Push(5);
  var x := s.Pop();
  assert x == 5 && s.Contents == [1, 2, 3, 4];
}
// END SPEC

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The constructor sets all four fields. Pop is three assignments. Push has a "grow" branch.
H2. In Push, after copying into a fresh array nd, point data at nd and add nd to Repr; then
    write, bump size, extend Contents. The verifier proves Contents == data[..size] from the
    pointwise facts.
H3. if size == data.Length { var nd := new int[2 * data.Length];
      forall i | 0 <= i < size { nd[i] := data[i]; } data := nd; Repr := Repr + {nd}; }
*/
