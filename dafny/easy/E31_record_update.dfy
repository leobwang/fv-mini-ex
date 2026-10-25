// E31 | Move money | 1-2 min | datatype update
// GOAL
//   Implement Deposit with a datatype update expression (copy with one field changed).
//
// REFERENCE
//   datatype P = P(x: int, y: int)           // one constructor = a record
//   P(1, 2)   p.x                             // construct; read a field
//   p.(x := 5)                                // copy of p with x replaced
//   p.(x := p.x + 1, y := 0)                  // several fields at once

// BEGIN SPEC
datatype Account = Account(owner: string, balance: int, frozen: bool)

function Deposit(a: Account, amount: nat): Account
  requires !a.frozen
  ensures Deposit(a, amount).balance == a.balance + amount
  ensures Deposit(a, amount).owner == a.owner && Deposit(a, amount).frozen == a.frozen
// END SPEC
{
  a // TODO
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Only one field changes.
H2. Use the update syntax rather than rebuilding Account(...) by hand.
H3. a.(balance := a.balance + amount)
*/
