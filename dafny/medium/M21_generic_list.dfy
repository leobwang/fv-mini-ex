// M21 | Generic list append | 10-15 min | generic datatype, higher-order map, induction
// GOAL
//   Write Map for a generic list, then prove append is associative and Map distributes over it.
//
// REFERENCE
//   datatype List<T> = Nil | Cons(head: T, tail: List<T>)
//   function F<T, U>(f: T -> U, l: List<T>): List<U>      // two type parameters
//   lemma {:induction false} L<T>(a: List<T>) ensures ... { match a case Nil => case Cons(_, t) => L(t); }
//   // Type arguments of lemma calls are inferred.

// BEGIN SPEC
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Append<T>(a: List<T>, b: List<T>): List<T>
{
  match a
  case Nil => b
  case Cons(h, t) => Cons(h, Append(t, b))
}

function Map<T, U>(f: T -> U, l: List<T>): List<U>
  ensures l.Nil? ==> Map(f, l) == Nil
  ensures l.Cons? ==> Map(f, l) == Cons(f(l.head), Map(f, l.tail))
// END SPEC
{
  Nil // TODO
}

// BEGIN SPEC
lemma {:induction false} AppendAssoc<T>(a: List<T>, b: List<T>, c: List<T>)
  ensures Append(Append(a, b), c) == Append(a, Append(b, c))
// END SPEC
{
}

// BEGIN SPEC
lemma {:induction false} MapAppend<T, U>(f: T -> U, a: List<T>, b: List<T>)
  ensures Map(f, Append(a, b)) == Append(Map(f, a), Map(f, b))
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Map follows the list structure. Both lemmas recurse on a, because Append does.
H2. Match on a; the Cons case calls the same lemma on the tail.
H3. match a  case Nil =>  case Cons(_, t) => AppendAssoc(t, b, c);
*/
