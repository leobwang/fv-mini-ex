// M26 | Counter trait | 10-15 min | trait, spec fn in trait, method contracts, generic client
// GOAL
//   A trait describes counters by an abstract spec value. Implement it for two concrete
//   representations, then write a generic client that only knows the trait's contracts.
//
// REFERENCE
//   trait T { spec fn value(&self) -> nat;  fn get(&self) -> (r: u64) ensures r == self.value(); }
//   impl T for S { spec fn value(&self) -> nat { self.n as nat }  fn get(&self) -> (r: u64) { .. } }
//   // impl methods inherit the trait's requires/ensures; don't repeat them.
//   fn client<C: T>(c: &mut C) ...                  // generic: only the trait contracts are known
//   requires self.value() < 1000                    // in requires, `self` is the entry value
//   ensures final(self).value() == old(self).value() + 1   // &mut self: old/final in ensures
// NOTE: Split stores lo in the low 32 bits: value = hi * 2^32 + lo. Carry when lo is u32::MAX.

use vstd::prelude::*;

verus! {

// BEGIN SPEC
trait Counter {
    spec fn value(&self) -> nat;

    fn get(&self) -> (r: u64)
        requires self.value() <= u64::MAX,
        ensures r == self.value();

    fn inc(&mut self)
        requires self.value() < 1000,
        ensures final(self).value() == old(self).value() + 1;
}

struct Simple {
    n: u64,
}

struct Split {
    hi: u32,
    lo: u32,
}
// END SPEC

impl Counter for Simple {
    // BEGIN SPEC
    spec fn value(&self) -> nat {
        self.n as nat
    }
    // END SPEC

    fn get(&self) -> (r: u64) {
        0 // TODO
    }

    fn inc(&mut self) {
    }
}

impl Counter for Split {
    // BEGIN SPEC
    spec fn value(&self) -> nat {
        (self.hi as nat) * 0x1_0000_0000 + self.lo as nat
    }
    // END SPEC

    fn get(&self) -> (r: u64) {
        0 // TODO
    }

    fn inc(&mut self) {
    }
}

// BEGIN SPEC
fn inc_twice<C: Counter>(c: &mut C)
    requires c.value() < 999,
    ensures final(c).value() == old(c).value() + 2,
// END SPEC
{
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Simple is direct. For Split, compute the value with u64 arithmetic: hi * 2^32 + lo fits
    because hi, lo < 2^32.
H2. inc on Split: if lo is u32::MAX, set lo = 0 and bump hi; else bump lo. The precondition
    value < 1000 rules out hi overflow. inc_twice just calls the trait method twice.
H3. Split::get:  (self.hi as u64) * 0x1_0000_0000 + self.lo as u64
    Split::inc:  if self.lo == u32::MAX { self.lo = 0; self.hi = self.hi + 1; } else { self.lo = self.lo + 1; }
*/
