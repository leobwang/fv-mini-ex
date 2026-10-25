// M12 | Merge two sorted Vecs | 15-20 min | sorted, to_multiset, subrange, broadcast use [R15]
// GOAL
//   Merge two sorted Vecs into one sorted Vec holding exactly the same elements
//   (multiset of the output = multiset of a + multiset of b).
//
// REFERENCE
//   broadcast use vstd::seq_lib::group_to_multiset_ensures;  // at file level, outside verus fns:
//       // teaches Verus s.push(x).to_multiset() =~= s.to_multiset().insert(x), and more
//   s.to_multiset()  m1.add(m2)  m.insert(x)   // multiset of a Seq; union (counts add); add one
//   assert(m1.add(m2).insert(x) =~= m1.insert(x).add(m2));   // multiset equality: use =~=
//   a@.subrange(0, i + 1) == a@.subrange(0, i as int).push(a[i as int])   // assert to rewrite
//   while i < a.len() || j < b.len() invariant ..., decreases a.len() + b.len() - i - j, { .. }
//   forall|k: int| 0 <= k < r.len() ==> (i < a.len() ==> r[k] <= a[i as int])   // r <= what is left
// NOTE: loops do not see `requires`: restate sorted(a@), sorted(b@) in the invariant.

use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_to_multiset_ensures;

// BEGIN SPEC
spec fn sorted(s: Seq<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

fn merge(a: &Vec<u64>, b: &Vec<u64>) -> (r: Vec<u64>)
    requires sorted(a@), sorted(b@),
    ensures
        sorted(r@),
        r@.to_multiset() == a@.to_multiset().add(b@.to_multiset()),
// END SPEC
{
    let mut r: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            sorted(a@),
            sorted(b@),
            sorted(r@),
            r@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(
                b@.subrange(0, j as int).to_multiset()),
            forall|k: int| 0 <= k < r.len() ==> (i < a.len() ==> r[k] <= a[i as int]) && (j
                < b.len() ==> r[k] <= b[j as int]),
        decreases a.len() + b.len() - i - j,
    {
        let ghost r0 = r@;
        let ghost ma = a@.subrange(0, i as int).to_multiset();
        let ghost mb = b@.subrange(0, j as int).to_multiset();
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            let x = a[i];
            assert(a@.subrange(0, i + 1) == a@.subrange(0, i as int).push(x));
            r.push(x);
            i += 1;
            assert(r@ == r0.push(x));
            assert(ma.add(mb).insert(x) =~= ma.insert(x).add(mb));
        } else {
            let x = b[j];
            assert(b@.subrange(0, j + 1) == b@.subrange(0, j as int).push(x));
            r.push(x);
            j += 1;
            assert(r@ == r0.push(x));
            assert(ma.add(mb).insert(x) =~= ma.add(mb.insert(x)));
        }
    }
    assert(a@.subrange(0, a.len() as int) == a@);
    assert(b@.subrange(0, b.len() as int) == b@);
    r
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Two indices i, j; push the smaller head; stop when both inputs are used up.
H2. Invariant: bounds; sorted inputs (restated) and sorted output; the output's multiset is
    the multiset of the two consumed prefixes; and every output element is <= both
    remaining heads (that is what keeps the output sorted after the next push).
H3. r@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(b@.subrange(0, j as int).to_multiset()),
    forall|k: int| 0 <= k < r.len() ==> (i < a.len() ==> r[k] <= a[i as int]) && (j < b.len() ==> r[k] <= b[j as int]),
    In a branch pushing x = a[i]: with ghost r0 = r@, ma, mb = multisets of the two prefixes,
      assert(a@.subrange(0, i + 1) == a@.subrange(0, i as int).push(x));  (before i += 1)
      assert(r@ == r0.push(x));  assert(ma.add(mb).insert(x) =~= ma.insert(x).add(mb));
*/
