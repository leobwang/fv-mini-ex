// M24 | Counter class | 8-12 min | class, constructor, this, modifies, fresh
// GOAL
//   Implement the Counter class, a transfer between two counters, and a factory.
//
// REFERENCE
//   class C { var f: int  constructor (x: int) ensures f == x { f := x; } }
//   var c := new C(5);            // allocate and run the constructor
//   c.f    this.f    f            // field access (this. optional inside the class)
//   modifies this   modifies a, b // a method that writes fields must say whose
//   old(c.f)    fresh(c)          // field at entry; c allocated by this method
//   // Two references may alias: if a == b, writing a.f also changes b.f.

// BEGIN SPEC
class Counter {
  var count: nat

  constructor (start: nat)
    ensures count == start
// END SPEC
  {
    count := start;
  }

// BEGIN SPEC
  method Inc()
    modifies this
    ensures count == old(count) + 1
// END SPEC
  {
    count := count + 1;
  }

// BEGIN SPEC
  method Dec()
    requires count > 0
    modifies this
    ensures count == old(count) - 1
// END SPEC
  {
    count := count - 1;
  }
}

// BEGIN SPEC
method Transfer(from: Counter, to: Counter)
  requires from != to && from.count > 0
  modifies from, to
  ensures from.count == old(from.count) - 1
  ensures to.count == old(to.count) + 1
// END SPEC
{
  from.Dec();
  to.Inc();
}

// BEGIN SPEC
method MakeTwo() returns (a: Counter, b: Counter)
  ensures fresh(a) && fresh(b) && a != b
  ensures a.count == 0 && b.count == 10
// END SPEC
{
  a := new Counter(0);
  b := new Counter(10);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The class methods are one assignment each. Transfer and MakeTwo only call class members.
H2. Transfer: why would it be wrong without "from != to"? MakeTwo: two "new" expressions; the
    verifier knows separately allocated objects differ.
H3. from.Dec(); to.Inc();      a := new Counter(0); b := new Counter(10);
*/
