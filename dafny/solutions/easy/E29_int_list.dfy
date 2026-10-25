// E29 | Integer list length | 2-3 min | recursive datatype
// GOAL
//   Implement Length and Snoc (append one element at the end) on a cons list. The specs relate
//   them to the seq that the list represents.
//
// REFERENCE
//   datatype L = Nil | Cons(head: int, tail: L)     // recursive datatype
//   match l
//   case Nil => 0
//   case Cons(h, t) => h + Sum(t)                   // structural recursion: termination automatic
//   case Cons(_, t) => ...                          // _ ignores a field

// BEGIN SPEC
datatype IntList = Nil | Cons(head: int, tail: IntList)

function ToSeq(l: IntList): seq<int>
{
  match l
  case Nil => []
  case Cons(h, t) => [h] + ToSeq(t)
}

function Length(l: IntList): nat
  ensures Length(l) == |ToSeq(l)|
// END SPEC
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + Length(t)
}

// BEGIN SPEC
function Snoc(l: IntList, x: int): IntList
  ensures ToSeq(Snoc(l, x)) == ToSeq(l) + [x]
// END SPEC
{
  match l
  case Nil => Cons(x, Nil)
  case Cons(h, t) => Cons(h, Snoc(t, x))
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both functions follow the shape of ToSeq.
H2. Snoc walks to the end: it rebuilds each Cons cell around the recursive result.
H3. case Nil => Cons(x, Nil)  case Cons(h, t) => Cons(h, Snoc(t, x))
*/
