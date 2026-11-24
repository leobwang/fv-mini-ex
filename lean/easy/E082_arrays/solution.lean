/- E082 | Arrays | 2-3 min | Array, #[..], push, size, getElem?, unfold, if_neg
GOAL
  Implement `pushTwice a x` (append `x` twice to the array `a`) and prove its size, its list view,
  and that every old index still holds its old element.

REFERENCE
  #eval #[1, 2].push 3                   -- #[1, 2, 3]: `#[..]` is an array literal, `push` appends
  example : (#[10, 20, 30] : Array Nat)[1]? = some 20 := rfl   -- `a[i]?` returns an Option
  #check @Array.size_push                -- (xs.push v).size = xs.size + 1
  #check @Array.toList_push              -- (xs.push x).toList = xs.toList ++ [x]
  #check @Array.getElem?_push            -- (xs.push x)[i]? = if i = xs.size then some x else xs[i]?
  #check @Array.getElem?_eq_getElem      -- (h : i < xs.size) : xs[i]? = some xs[i]
                                         --   `xs[i]` (no ?) needs a proof of `i < xs.size`; Lean finds `h` in context
  #check @if_neg                         -- ¬c → (if c then t else e) = e
  `unfold f` replaces `f` by its body; `simp [f]` also unfolds `f` and uses `@[simp]` lemmas such as `size_push`.
BANNED: grind, try?, exact?
-/

namespace E082

-- BEGIN SPEC
def pushTwice (a : Array Nat) (x : Nat) : Array Nat :=
-- END SPEC
  (a.push x).push x

-- BEGIN SPEC
theorem lit_size : #[1, 2, 3].size = 3 :=
-- END SPEC
  rfl

-- BEGIN SPEC
theorem pushTwice_size (a : Array Nat) (x : Nat) : (pushTwice a x).size = a.size + 2 :=
-- END SPEC
  by simp [pushTwice]

-- BEGIN SPEC
theorem pushTwice_toList (a : Array Nat) (x : Nat) : (pushTwice a x).toList = a.toList ++ [x, x] :=
-- END SPEC
  by simp [pushTwice]

-- BEGIN SPEC
theorem pushTwice_old (a : Array Nat) (x i : Nat) (h : i < a.size) :
    (pushTwice a x)[i]? = some a[i] :=
-- END SPEC
  by
  unfold pushTwice
  -- WHY: the outer `push` sees an array of size `a.size + 1`, so its `if` needs `simp` before `omega`
  rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]
  exact Array.getElem?_eq_getElem h

end E082

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. `pushTwice` is two `push`es. A literal's size is computed by `rfl` (or `decide`).
H2. Size and list view: `simp [pushTwice]` (the `push` lemmas are simp lemmas). For old indices,
    `unfold pushTwice` and rewrite with `Array.getElem?_push` twice; each time the `if` is false.
H3. `rw [Array.getElem?_push, if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]`,
    then `exact Array.getElem?_eq_getElem h`.
-/
