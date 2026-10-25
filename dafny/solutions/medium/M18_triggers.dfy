// M18 | Triggers | 10-15 min | trigger, quantifier instantiation
// GOAL
//   A quantified fact is used only when terms matching its trigger appear. Make each one fire.
//
// REFERENCE
//   forall x {:trigger g(x)} :: g(x) > 0       // explicit trigger: fires on every term g(t)
//   // Default for "forall x :: f(x) < f(x + 1)" is the multi-trigger {f(x), f(x + 1)}: an
//   // instance x := t needs BOTH f(t) and f(t + 1) to be present already.
//   assert f(1) == f(1);                        // mentions a term (introduces f(1))
//   assert f(0) < f(1) < f(2);                  // chained assertion
//   forall x ensures Q(x) { ... }               // forall statement (E24)

// BEGIN SPEC
ghost function f(x: int): int
ghost predicate Marked(i: int)

lemma Chain()
  requires forall x :: f(x) < f(x + 1)
  ensures f(0) < f(3)
// END SPEC
{
  assert f(0) < f(1) < f(2) < f(3);
}

// BEGIN SPEC
lemma SkipOne()
  requires forall x :: f(x) < f(x + 1)
  ensures forall x :: f(x) < f(x + 2)
// END SPEC
{
  forall x ensures f(x) < f(x + 2) { assert f(x) < f(x + 1) < f(x + 2); }
}

// BEGIN SPEC
lemma UseMarked(s: seq<int>)
  requires forall i {:trigger Marked(i)} :: 0 <= i < |s| ==> s[i] > 0
  requires |s| > 2
  ensures s[2] > 0
// END SPEC
{
  assert Marked(2) || !Marked(2);
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Ask: which terms must appear for each hypothesis to be instantiated where you need it?
H2. Chain: the missing terms are f(1) and f(2). SkipOne: per x, mention f(x + 1). UseMarked: the
    trigger is Marked(i), so some Marked(2) term must appear (any tautology about it will do).
H3. assert f(0) < f(1) < f(2) < f(3);      assert Marked(2) || !Marked(2);
*/
