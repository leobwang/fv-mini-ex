// M41 | Functional queue | 12-18 min | abstraction function, data invariant
// GOAL
//   A queue as two seqs: pop from front, push onto back (stored reversed). Implement the
//   operations so they preserve Valid and act on Model like a FIFO queue.
//
// REFERENCE
//   datatype Q = Q(front: seq<int>, back: seq<int>)   // back holds newest element first
//   q.(back := [x] + q.back)                            // datatype update (E31)
//   lemma RevLen(s: seq<int>) ensures |Rev(s)| == |s|  // helper lemmas are fine (auto-induction)
//   // Valid: front is empty only if the whole queue is (so Peek is O(1)).

// BEGIN SPEC
datatype Queue = Queue(front: seq<int>, back: seq<int>)

function Rev(s: seq<int>): seq<int> { if |s| == 0 then [] else Rev(s[1..]) + [s[0]] }

function Model(q: Queue): seq<int> { q.front + Rev(q.back) }

predicate Valid(q: Queue) { q.front == [] ==> q.back == [] }

function Push(q: Queue, x: int): Queue
  requires Valid(q)
  ensures Valid(Push(q, x)) && Model(Push(q, x)) == Model(q) + [x]
// END SPEC
{
  if q.front == [] then Queue([x], [])
  else q.(back := [x] + q.back)
}

// BEGIN SPEC
function Peek(q: Queue): int
  requires Valid(q) && Model(q) != []
  ensures Peek(q) == Model(q)[0]
// END SPEC
{
  q.front[0]
}

// BEGIN SPEC
function Pop(q: Queue): Queue
  requires Valid(q) && Model(q) != []
  ensures Valid(Pop(q)) && Model(Pop(q)) == Model(q)[1..]
// END SPEC
{
  if |q.front| > 1 then q.(front := q.front[1..])
  else
    RevLength(q.back);
    Queue(Rev(q.back), [])
}

lemma RevLength(s: seq<int>)
  ensures |Rev(s)| == |s|
{}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Push: if the queue is empty, the new element must go to front (Valid!). Pop: drop the head
    of front; if front becomes empty, move Rev(back) over.
H2. Pop's second case needs Rev(back) to be non-empty when back is: a length lemma for Rev.
    In a function body you can call a lemma inline: L(x); expr.
H3. if |q.front| > 1 then q.(front := q.front[1..]) else RevLength(q.back); Queue(Rev(q.back), [])
*/
