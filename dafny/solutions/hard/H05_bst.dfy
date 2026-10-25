// H05 | Binary search tree | 45-90 min | datatype, Contents set, BST invariant, milestones
// GOAL
//   Implement membership, insert and delete on an immutable binary search tree. Each operation
//   must preserve the BST property and change Contents exactly as specified. Finally prove that
//   the in-order traversal of a BST is strictly increasing.
//
// REFERENCE
//   match t case Leaf => ... case Node(l, k, r) => ...
//   if x < k then Node(Insert(l, x), k, r) else ...      // rebuild the path you changed
//   Contents(t) + {x}    Contents(t) - {x}               // set algebra (E13)
//   function F(t: Tree): (int, Tree) requires ... ensures F(t).0 ...   // tuple result
//   // A function's ensures is all callers know: make helper specs strong enough for Delete.
//   (a + [k] + b)[i]   // index into a concatenation: case-split on i < |a|, i == |a|, ...

// BEGIN SPEC
datatype Tree = Leaf | Node(left: Tree, key: int, right: Tree)

function Contents(t: Tree): set<int>
{
  match t
  case Leaf => {}
  case Node(l, k, r) => Contents(l) + {k} + Contents(r)
}

ghost predicate BST(t: Tree)
{
  match t
  case Leaf => true
  case Node(l, k, r) =>
    BST(l) && BST(r) &&
    (forall x :: x in Contents(l) ==> x < k) &&
    (forall x :: x in Contents(r) ==> x > k)
}

function Contains(t: Tree, x: int): bool
  requires BST(t)
  ensures Contains(t, x) <==> x in Contents(t)
// END SPEC
{
  match t
  case Leaf => false
  case Node(l, k, r) =>
    if x < k then Contains(l, x)
    else if x > k then Contains(r, x)
    else true
}

// BEGIN SPEC
function Insert(t: Tree, x: int): Tree
  requires BST(t)
  ensures BST(Insert(t, x))
  ensures Contents(Insert(t, x)) == Contents(t) + {x}
// END SPEC
{
  match t
  case Leaf => Node(Leaf, x, Leaf)
  case Node(l, k, r) =>
    if x < k then Node(Insert(l, x), k, r)
    else if x > k then Node(l, k, Insert(r, x))
    else t
}

// BEGIN SPEC
function Delete(t: Tree, x: int): Tree
  requires BST(t)
  ensures BST(Delete(t, x))
  ensures Contents(Delete(t, x)) == Contents(t) - {x}
// END SPEC
{
  match t
  case Leaf => Leaf
  case Node(l, k, r) =>
    if x < k then Node(Delete(l, x), k, r)
    else if x > k then Node(l, k, Delete(r, x))
    else if r == Leaf then l
    else
      var (m, r') := RemoveMin(r);
      Node(l, m, r')
}

// MILESTONE (optional: change or delete)
// Remove the smallest key of a non-empty tree; return it together with the remaining tree.
function RemoveMin(t: Tree): (int, Tree)
  requires BST(t) && t != Leaf
  ensures BST(RemoveMin(t).1)
  ensures RemoveMin(t).0 in Contents(t)
  ensures Contents(RemoveMin(t).1) == Contents(t) - {RemoveMin(t).0}
  ensures forall y :: y in Contents(RemoveMin(t).1) ==> RemoveMin(t).0 < y
{
  match t
  case Node(l, k, r) =>
    if l == Leaf then (k, r)
    else
      var (m, l') := RemoveMin(l);
      (m, Node(l', k, r))
}

// BEGIN SPEC
function Inorder(t: Tree): seq<int>
{
  match t
  case Leaf => []
  case Node(l, k, r) => Inorder(l) + [k] + Inorder(r)
}

lemma InorderSorted(t: Tree)
  requires BST(t)
  ensures forall i, j :: 0 <= i < j < |Inorder(t)| ==> Inorder(t)[i] < Inorder(t)[j]
// END SPEC
{
  match t
  case Leaf =>
  case Node(l, k, r) =>
    InorderSorted(l);
    InorderSorted(r);
    InorderContents(l);
    InorderContents(r);
    var s := Inorder(t);
    var n := |Inorder(l)|;
    forall i, j | 0 <= i < j < |s| ensures s[i] < s[j] {
      if j < n {
      } else if i < n {
        assert s[i] in Contents(l);
        if j > n { assert s[j] == Inorder(r)[j - n - 1]; assert s[j] in Contents(r); }
      } else if i == n {
        assert s[j] == Inorder(r)[j - n - 1];
        assert s[j] in Contents(r);
      } else {
        assert s[i] == Inorder(r)[i - n - 1] && s[j] == Inorder(r)[j - n - 1];
      }
    }
}

// MILESTONE (optional: change or delete)
lemma InorderContents(t: Tree)
  ensures forall x :: x in Inorder(t) <==> x in Contents(t)
{
  match t
  case Leaf =>
  case Node(l, _, r) => InorderContents(l); InorderContents(r);
}

// BEGIN SPEC
method Client()
{
  var t := Insert(Insert(Insert(Leaf, 5), 2), 8);
  t := Delete(t, 5);
  assert Contents(t) == {2, 8};
  assert Contains(t, 8) && !Contains(t, 5);
}
// END SPEC

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Contains and Insert follow the BST ordering down one path. Delete is the classic three
    cases; the hard one is a node with two children.
H2. For a node with a right subtree, replace its key by the minimum m of the right subtree and
    delete m from there (RemoveMin). Its ensures must say m is smaller than everything left in
    the right subtree, so the new node is still a BST.
H3. else if r == Leaf then l else var (m, r') := RemoveMin(r); Node(l, m, r')
    RemoveMin: if l == Leaf then (k, r) else var (m, l') := RemoveMin(l); (m, Node(l', k, r))
    InorderSorted: induction on both subtrees + InorderContents, then a forall i, j statement
    that splits on where i and j fall: in Inorder(l), at the root (index |Inorder(l)|), or in
    Inorder(r) (index shifted by |Inorder(l)| + 1).
*/
