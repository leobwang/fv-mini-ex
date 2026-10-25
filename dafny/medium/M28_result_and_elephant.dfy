// M28 | Result and :- | 10-15 min | failure-compatible type, :- (elephant operator)
// GOAL
//   Make Result failure-compatible (add the three members), implement SafeDiv, then write
//   DivTwice with :- so failures propagate automatically.
//
// REFERENCE
//   datatype R<T> = Ok(v: T) | Err(msg: string) {          // members follow the constructors
//     predicate IsFailure() { Err? }
//     function PropagateFailure<U>(): R<U> requires IsFailure() { Err(msg) }
//     function Extract(): T requires !IsFailure() { v }
//   }
//   var x :- M(..);          // if M(..) failed, return its failure now; else x := Extract()
//   return Success(x);       // methods returning a failure-compatible type

// BEGIN SPEC
datatype Result<T> = Success(value: T) | Failure(error: string)
// END SPEC
  // TODO: a { ... } block with IsFailure, PropagateFailure and Extract

// BEGIN SPEC
method SafeDiv(a: int, b: int) returns (r: Result<int>)
  ensures b == 0 <==> r.Failure?
  ensures r.Success? ==> r.value == a / b
// END SPEC
{
}

// BEGIN SPEC
method DivTwice(a: int, b: int, c: int) returns (r: Result<int>)
  ensures r.Failure? <==> b == 0 || c == 0
  ensures r.Success? ==> r.value == (a / b) / c
// END SPEC
{
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. The member block goes right after the constructors (on the TODO line). Use Failure? and
    the field names value and error.
H2. DivTwice: two :- calls, then return Success of the second result.
H3. var x :- SafeDiv(a, b); var y :- SafeDiv(x, c); return Success(y);
*/
