// M33 | Matrix transpose | 15-20 min | array2, nested loops
// GOAL
//   Transpose into a new matrix, then transpose a square matrix in place.
//
// REFERENCE
//   m: array2<int>   m.Length0   m.Length1   m[i, j]     // 2-D array: rows, columns, element
//   var t := new int[r, c];                               // allocate r x c
//   m[i, j], m[j, i] := m[j, i], m[i, j];                 // swap two cells
//   // Nested loops: the inner invariant must restate what the outer one knows, plus the
//   // partial row; write the inner loop's invariant first.

// BEGIN SPEC
method Transpose(m: array2<int>) returns (t: array2<int>)
  ensures fresh(t) && t.Length0 == m.Length1 && t.Length1 == m.Length0
  ensures forall i, j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> t[j, i] == m[i, j]
// END SPEC
{
  t := new int[m.Length1, m.Length0];
  for i := 0 to m.Length0
    invariant forall p, q :: 0 <= p < i && 0 <= q < m.Length1 ==> t[q, p] == m[p, q]
  {
    for j := 0 to m.Length1
      invariant forall p, q :: 0 <= p < i && 0 <= q < m.Length1 ==> t[q, p] == m[p, q]
      invariant forall q :: 0 <= q < j ==> t[q, i] == m[i, q]
    {
      t[j, i] := m[i, j];
    }
  }
}

// BEGIN SPEC
method TransposeInPlace(m: array2<int>)
  requires m.Length0 == m.Length1
  modifies m
  ensures forall i, j :: 0 <= i < m.Length0 && 0 <= j < m.Length0 ==> m[i, j] == old(m[j, i])
// END SPEC
{
  var n := m.Length0;
  for i := 0 to n
    invariant forall p, q :: 0 <= p < n && 0 <= q < n ==>
      m[p, q] == (if p < i || q < i then old(m[q, p]) else old(m[p, q]))
  {
    for j := i + 1 to n
      invariant forall p, q :: 0 <= p < n && 0 <= q < n ==>
        m[p, q] == (if p < i || q < i || (p == i && i < q < j) || (q == i && i < p < j)
                    then old(m[q, p]) else old(m[p, q]))
    {
      m[i, j], m[j, i] := m[j, i], m[i, j];
    }
  }
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Transpose: copy cell by cell. In place: swap (i, j) with (j, i) only for j > i.
H2. In place, describe every cell at once: a cell is "done" (holds old(m[q, p])) when it lies in
    an already processed row or column; otherwise it still holds its old value.
H3. outer invariant: forall p, q :: 0 <= p < n && 0 <= q < n ==>
      m[p, q] == (if p < i || q < i then old(m[q, p]) else old(m[p, q]))
    (inner: also count p == i && i < q < j and q == i && i < p < j as done)
*/
