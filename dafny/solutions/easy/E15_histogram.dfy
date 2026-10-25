// E15 | Histogram increment | 1-3 min | map
// GOAL
//   Return the map m with the count for key k increased by one (absent keys count as 0).
//
// REFERENCE
//   m: map<int, nat>    map[]    map[1 := 10]    // type, empty map, literal
//   k in m    m[k]                                // key membership; lookup (requires k in m)
//   m[k := v]                                     // new map: k now maps to v, others unchanged
//   m.Keys    m.Values                            // key / value sets
//   if k in m then m[k] else 0                    // safe lookup with a default

// BEGIN SPEC
function Inc(m: map<int, nat>, k: int): map<int, nat>
  ensures k in Inc(m, k)
  ensures Inc(m, k)[k] == (if k in m then m[k] else 0) + 1
  ensures forall j :: j != k ==> (j in Inc(m, k) <==> j in m)
  ensures forall j :: j != k && j in m ==> Inc(m, k)[j] == m[j]
// END SPEC
{
  m[k := if k in m then m[k] + 1 else 1]
}

/* ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. A single map update expression.
H2. The new value depends on whether k is already a key; use a conditional expression.
H3. m[k := if k in m then m[k] + 1 else 1]
*/
