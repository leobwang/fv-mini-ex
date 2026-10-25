// H04 | Circular buffer queue | 45-90 min | class, Valid, Repr, ghost Contents, modular indices
// GOAL
//   Implement a bounded FIFO queue in a ring buffer. YOU design Valid(): it must tie the ghost
//   Contents to buf, head and count. Front and Dequeue return real data, so a Valid that does
//   not describe the buffer cannot be made to verify.
//
// REFERENCE
//   Wrap(head + i, buf.Length)               // ring-buffer index of the i-th element (below)
//   ghost predicate Valid() reads this, Repr { this in Repr && buf in Repr && ... }
//   // && is short-circuit: put "buf in Repr" before anything that reads buf's elements.
//   Contents := Contents + [x];   Contents := Contents[1..];   // ghost updates
// NOTE: % is expensive for the solver; Wrap (one conditional subtraction) is enough here.
//   // Methods that keep the same objects can still promise fresh(Repr - old(Repr)) (nothing new).

// BEGIN SPEC
function Wrap(k: int, n: int): int { if k < n then k else k - n }

class Queue {
  ghost var Contents: seq<int>
  ghost var Repr: set<object>
  var buf: array<int>
  var head: nat
  var count: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
// END SPEC
  {
    this in Repr && buf in Repr &&
    buf.Length > 0 && head < buf.Length && count <= buf.Length &&
    |Contents| == count &&
    forall i :: 0 <= i < count ==> Contents[i] == buf[Wrap(head + i, buf.Length)]
  }

// BEGIN SPEC
  function Capacity(): nat
    reads this, Repr
    requires Valid()
// END SPEC
  {
    buf.Length
  }

// BEGIN SPEC
  constructor (cap: nat)
    requires cap > 0
    ensures Valid() && fresh(Repr) && Contents == [] && Capacity() == cap
// END SPEC
  {
    buf := new int[cap];
    head, count := 0, 0;
    Contents := [];
    Repr := {this, buf};
  }

// BEGIN SPEC
  method Enqueue(x: int)
    requires Valid() && |Contents| < Capacity()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr)) && Capacity() == old(Capacity())
    ensures Contents == old(Contents) + [x]
// END SPEC
  {
    buf[Wrap(head + count, buf.Length)] := x;
    count := count + 1;
    Contents := Contents + [x];
  }

// BEGIN SPEC
  method Front() returns (x: int)
    requires Valid() && |Contents| > 0
    ensures x == Contents[0]
// END SPEC
  {
    assert Contents[0] == buf[Wrap(head + 0, buf.Length)];
    x := buf[head];
  }

// BEGIN SPEC
  method Dequeue() returns (x: int)
    requires Valid() && |Contents| > 0
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr)) && Capacity() == old(Capacity())
    ensures x == old(Contents)[0] && Contents == old(Contents)[1..]
// END SPEC
  {
    assert Contents[0] == buf[Wrap(head + 0, buf.Length)];
    x := buf[head];
    head := Wrap(head + 1, buf.Length);
    count := count - 1;
    Contents := Contents[1..];
  }
}
// BEGIN SPEC
method Client()
{
  var q := new Queue(2);
  q.Enqueue(1); q.Enqueue(2);
  var a := q.Dequeue();
  q.Enqueue(3);
  var b := q.Dequeue();
  var c := q.Front();
  assert a == 1 && b == 2 && c == 3;
}
// END SPEC

// MILESTONE (optional: change or delete)
// Index arithmetic for Dequeue: advancing head by one shifts every logical index by one.
// (The verifier proves this one by itself; it tells you which fact Dequeue relies on.)
lemma WrapShift(h: int, i: int, n: int)
  requires 0 <= h < n && 0 <= i && h + 1 + i < 2 * n
  ensures Wrap(Wrap(h + 1, n) + i, n) == Wrap(h + 1 + i, n)
{
}

// MILESTONE (optional: change or delete)
// The logical contents of a ring buffer s with head h and c elements. With it, Valid() can
// say Contents == Window(buf[..], head, count).
ghost function Window(s: seq<int>, h: int, c: int): seq<int>
  requires 0 <= h < |s| && 0 <= c <= |s|
  ensures |Window(s, h, c)| == c
  ensures forall i :: 0 <= i < c ==> Window(s, h, c)[i] == s[Wrap(h + i, |s|)]
{
  seq(c, i requires 0 <= i < c => s[Wrap(h + i, |s|)])
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Valid() says: the objects (this, buf) are in Repr; head and count are in range; Contents
    has length count; and element i of Contents sits at buf[Wrap(head + i, buf.Length)].
H2. Enqueue writes at Wrap(head + count, buf.Length). Dequeue reads buf[head], then sets
    head := Wrap(head + 1, buf.Length). With Wrap instead of %, the index facts are linear and
    the verifier handles them (WrapShift is the fact it needs).
H3. forall i :: 0 <= i < count ==> Contents[i] == buf[Wrap(head + i, buf.Length)]
    (plus this in Repr && buf in Repr && buf.Length > 0 && head < buf.Length &&
     count <= buf.Length && |Contents| == count)
*/
