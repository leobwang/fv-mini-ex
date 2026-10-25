// M23 | Tree mirror | 15-20 min | generic tree, structural induction, seq lemmas
// GOAL
//   Write Mirror (swap children everywhere). Prove it is an involution, preserves Size, and
//   reverses the in-order traversal.
//
// REFERENCE
//   datatype Tree<T> = Leaf | Node(left: Tree<T>, val: T, right: Tree<T>)
//   match t case Leaf => ... case Node(l, x, r) => ...
//   lemma {:induction false} L<T>(t: Tree<T>) ensures ... { match t case Leaf => case Node(l, _, r) => L(l); L(r); }
//   assert (a + b)[1..] == a[1..] + b;           // for a seq helper about RevSeq(a + b)

// BEGIN SPEC
datatype Tree<T> = Leaf | Node(left: Tree<T>, val: T, right: Tree<T>)

function Size<T>(t: Tree<T>): nat
{
  match t
  case Leaf => 0
  case Node(l, _, r) => Size(l) + 1 + Size(r)
}

function Inorder<T>(t: Tree<T>): seq<T>
{
  match t
  case Leaf => []
  case Node(l, x, r) => Inorder(l) + [x] + Inorder(r)
}

function RevSeq<T>(s: seq<T>): seq<T>
{
  if |s| == 0 then [] else RevSeq(s[1..]) + [s[0]]
}

function Mirror<T>(t: Tree<T>): Tree<T>
  ensures t.Leaf? ==> Mirror(t).Leaf?
// END SPEC
{
  t // TODO
}

// BEGIN SPEC
lemma {:induction false} MirrorMirror<T>(t: Tree<T>)
  ensures Mirror(Mirror(t)) == t
// END SPEC
{
}

// BEGIN SPEC
lemma {:induction false} SizeMirror<T>(t: Tree<T>)
  ensures Size(Mirror(t)) == Size(t)
// END SPEC
{
}

// BEGIN SPEC
lemma {:induction false} InorderMirror<T>(t: Tree<T>)
  ensures Inorder(Mirror(t)) == RevSeq(Inorder(t))
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Mirror swaps and recurses. The first two lemmas: match t, recurse on both children.
H2. InorderMirror needs a seq lemma: RevSeq(a + b) == RevSeq(b) + RevSeq(a) (induction on a).
H3. lemma RevConcat<T>(a: seq<T>, b: seq<T>) ensures RevSeq(a + b) == RevSeq(b) + RevSeq(a)
    Node case: InorderMirror(l); InorderMirror(r); RevConcat(Inorder(l) + [x], Inorder(r));
    RevConcat(Inorder(l), [x]);
*/
