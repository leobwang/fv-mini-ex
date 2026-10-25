// E30 | Length of append | 2-3 min | structural induction, match in lemma
// GOAL
//   Prove both lemmas by induction on the first list.
//
// REFERENCE
//   lemma {:induction false} L(a: IntList)
//     ensures P(a)
//   {
//     match a
//     case Nil =>                       // base case (often empty)
//     case Cons(_, t) => L(t);          // induction hypothesis for the tail
//   }

// BEGIN SPEC
datatype IntList = Nil | Cons(head: int, tail: IntList)

function Length(l: IntList): nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + Length(t)
}

function Append(a: IntList, b: IntList): IntList
{
  match a
  case Nil => b
  case Cons(h, t) => Cons(h, Append(t, b))
}

lemma {:induction false} LengthAppend(a: IntList, b: IntList)
  ensures Length(Append(a, b)) == Length(a) + Length(b)
// END SPEC
{
  match a
  case Nil =>
  case Cons(_, t) => LengthAppend(t, b);
}

// BEGIN SPEC
lemma {:induction false} AppendNil(a: IntList)
  ensures Append(a, Nil) == a
// END SPEC
{
  match a
  case Nil =>
  case Cons(_, t) => AppendNil(t);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Append recurses on its first argument, so induct on a.
H2. Match on a; in the Cons case call the lemma on the tail.
H3. match a  case Nil =>  case Cons(_, t) => LengthAppend(t, b);
*/
