// M22 | List reverse involution | 15-20 min | helper lemmas, induction
// GOAL
//   Prove that reversing twice gives back the list. You will need helper lemmas; state them.
//
// REFERENCE
//   lemma {:induction false} L<T>(a: List<T>, b: List<T>) ensures ... // helper with 2 lists
//   calc { Rev(Append(a, b)); == ...; }                               // optional: show steps
//   // Typical helper chain: Append(a, Nil) == a, associativity, then Rev of an Append.
//   // Your own helper lemmas may rely on automatic induction (no {:induction false} needed).

// BEGIN SPEC
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Append<T>(a: List<T>, b: List<T>): List<T>
{
  match a
  case Nil => b
  case Cons(h, t) => Cons(h, Append(t, b))
}

function Rev<T>(l: List<T>): List<T>
{
  match l
  case Nil => Nil
  case Cons(h, t) => Append(Rev(t), Cons(h, Nil))
}

lemma {:induction false} RevRev<T>(l: List<T>)
  ensures Rev(Rev(l)) == l
// END SPEC
{
  match l
  case Nil =>
  case Cons(h, t) =>
    RevAppend(Rev(t), Cons(h, Nil));
    RevRev(t);
}

lemma AppendNil<T>(a: List<T>)
  ensures Append(a, Nil) == a
{}

lemma AppendAssoc<T>(a: List<T>, b: List<T>, c: List<T>)
  ensures Append(Append(a, b), c) == Append(a, Append(b, c))
{}

lemma RevAppend<T>(a: List<T>, b: List<T>)
  ensures Rev(Append(a, b)) == Append(Rev(b), Rev(a))
{
  match a
  case Nil => AppendNil(Rev(b));
  case Cons(h, t) =>
    RevAppend(t, b);
    AppendAssoc(Rev(b), Rev(t), Cons(h, Nil));
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Unfold Rev(Rev(Cons(h, t))) = Rev(Append(Rev(t), [h])). What do you need to know about
    Rev of an Append?
H2. Helper: Rev(Append(a, b)) == Append(Rev(b), Rev(a)), by induction on a; its cases use
    Append(x, Nil) == x and associativity of Append.
H3. lemma RevAppend<T>(a: List<T>, b: List<T>) ensures Rev(Append(a, b)) == Append(Rev(b), Rev(a))
    then in RevRev's Cons case: RevAppend(Rev(t), Cons(h, Nil)); RevRev(t);
*/
