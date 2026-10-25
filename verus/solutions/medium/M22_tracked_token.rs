// M22 | Tracked permission token | 10 min | tracked struct, Tracked<T>, Ghost<T>, let tracked
// GOAL
//   A Vault may only be modified by someone holding the matching Key, a proof-only (tracked)
//   object that costs nothing at run time. Implement vault creation and two deposit functions,
//   threading the key through as a tracked argument.
//
// REFERENCE
//   pub tracked struct Key { pub ghost id: int }  // exists only in proofs; cannot be copied
//   fn f(Tracked(k): Tracked<&Key>)             // take a tracked borrow; k.id usable in specs
//   let tracked k = Key { id: 7 };               // create a tracked value (proof-mode expression)
//   (v, Tracked(k))                              // wrap a tracked value to return it from exec code
//   f(Tracked(&k))   f(Tracked(k))               // pass a tracked borrow / the tracked value itself
//   g: Ghost<int>   g@   Ghost(5)                // ghost wrapper: read with @, build with Ghost(..)

use vstd::prelude::*;

verus! {

// BEGIN SPEC
pub tracked struct Key {
    pub ghost id: int,
}

pub struct Vault {
    pub id: Ghost<int>,
    pub balance: u64,
}

fn new_vault(id: Ghost<int>) -> (r: (Vault, Tracked<Key>))
    ensures r.0.id@ == id@, r.0.balance == 0, r.1@.id == id@,
// END SPEC
{
    let tracked k = Key { id: id@ };
    (Vault { id, balance: 0 }, Tracked(k))
}

// BEGIN SPEC
fn deposit(v: &mut Vault, amount: u64, Tracked(k): Tracked<&Key>)
    requires k.id == v.id@, v.balance + amount <= u64::MAX,
    ensures final(v).id == old(v).id, final(v).balance == old(v).balance + amount,
// END SPEC
{
    v.balance = v.balance + amount;
}

// BEGIN SPEC
fn deposit_twice(v: &mut Vault, a: u64, b: u64, Tracked(k): Tracked<&Key>)
    requires k.id == v.id@, v.balance + a + b <= u64::MAX,
    ensures final(v).id == old(v).id, final(v).balance == old(v).balance + a + b,
// END SPEC
{
    deposit(v, a, Tracked(k));
    deposit(v, b, Tracked(k));
}

// BEGIN SPEC
fn open_and_fund(a: u64) -> (r: Vault)
    ensures r.balance == a, r.id@ == 42,
// END SPEC
{
    let (mut v, Tracked(k)) = new_vault(Ghost(42));
    deposit(&mut v, a, Tracked(&k));
    v
}

} // verus!

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Tracked and ghost values follow the same code shape as exec values, just wrapped.
H2. new_vault builds the key with `let tracked` and returns it wrapped in Tracked(..).
    deposit_twice already holds a tracked borrow `k: &Key`: pass it on as Tracked(k).
    open_and_fund destructures new_vault's result with a `Tracked(k)` pattern.
H3. let tracked k = Key { id: id@ }; (Vault { id, balance: 0 }, Tracked(k))
    let (mut v, Tracked(k)) = new_vault(Ghost(42)); deposit(&mut v, a, Tracked(&k)); v
*/
