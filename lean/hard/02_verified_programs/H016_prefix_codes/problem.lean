/- H016 | Prefix codes from a code tree | 45-75 min | Huffman-style codes, prefix-free, decoding, List.IsPrefix, Option, split at
GOAL
  A binary code tree gives each leaf symbol a code word (its root-to-leaf path). Prove the code is
  prefix-free, and that decoding `msg.length` symbols from `encode t msg` returns `msg` with no bits left.

REFERENCE
  example (xs ys : List Bool) (h : xs <+: ys) : ∃ rest, xs ++ rest = ys := h  -- `<+:` is List.IsPrefix
  #check List.append_assoc   -- (as bs cs : List α) : as ++ bs ++ cs = as ++ (bs ++ cs)
  #check List.append_nil     -- (as : List α) : as ++ [] = as
  example (a b : Nat) (h : some a = some b) : a = b := by cases h; rfl  -- `cases` on `some _ = some _`
  example (a : Nat) (h : (none : Option Nat) = some a) : False := by cases h  -- impossible equation
  -- `obtain ⟨rest, rfl⟩ := hpre` replaces `cb` by `ca ++ rest` everywhere.
  -- `split at h` cases on the `if`/`match` inside hypothesis `h`; `rename_i c hc` names the new variables.
  -- `induction t generalizing c with | leaf b => _ | node l r ihl ihr => _`
  -- `suffices ∀ rest, P (bs ++ rest) by simpa using this []` strengthens a goal before induction.
NOTE: `codeOf t a = none` when `a` is not in the tree, so `encode` returns `none` on such messages.
-/

namespace H016

-- BEGIN SPEC
/-- A code tree: a symbol's code word is its path from the root (false = left, true = right). -/
inductive CTree (α : Type) where
  | leaf (a : α)
  | node (l r : CTree α)

/-- The code word of `a`: the path to the first (leftmost) leaf labelled `a`, if any. -/
def codeOf {α : Type} [DecidableEq α] : CTree α → α → Option (List Bool)
  | .leaf b, a => if a = b then some [] else none
  | .node l r, a =>
    match codeOf l a with
    | some c => some (false :: c)
    | none =>
      match codeOf r a with
      | some c => some (true :: c)
      | none => none

/-- Concatenate the code words of the message (fails if a symbol has no code). -/
def encode {α : Type} [DecidableEq α] (t : CTree α) : List α → Option (List Bool)
  | [] => some []
  | a :: as =>
    match codeOf t a, encode t as with
    | some c, some cs => some (c ++ cs)
    | _, _ => none

/-- Walk down the tree reading bits until a leaf; return its symbol and the unread bits. -/
def decodeOne {α : Type} : CTree α → List Bool → Option (α × List Bool)
  | .leaf a, bs => some (a, bs)
  | .node _ _, [] => none
  | .node l r, b :: bs => decodeOne (if b then r else l) bs

/-- Decode exactly `n` symbols; return them and the unread bits. -/
def decodeN {α : Type} (t : CTree α) : Nat → List Bool → Option (List α × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match decodeOne t bs with
    | none => none
    | some (a, bs') =>
      match decodeN t n bs' with
      | none => none
      | some (as, rest) => some (a :: as, rest)
-- END SPEC

-- MILESTONE (optional: change or delete)
theorem decodeOne_codeOf {α : Type} [DecidableEq α] (t : CTree α) (a : α) (c rest : List Bool)
    (h : codeOf t a = some c) : decodeOne t (c ++ rest) = some (a, rest) := by
  sorry

-- MILESTONE (optional: change or delete)
theorem decodeN_encode_append {α : Type} [DecidableEq α] (t : CTree α) (msg : List α)
    (bs : List Bool) (h : encode t msg = some bs) :
    ∀ rest, decodeN t msg.length (bs ++ rest) = some (msg, rest) := by
  sorry

-- BEGIN SPEC
theorem prefix_free {α : Type} [DecidableEq α] (t : CTree α) (a b : α) (ca cb : List Bool)
    (ha : codeOf t a = some ca) (hb : codeOf t b = some cb) (hpre : ca <+: cb) : a = b :=
-- END SPEC
  sorry

-- BEGIN SPEC
theorem decode_encode {α : Type} [DecidableEq α] (t : CTree α) (msg : List α) (bs : List Bool)
    (h : encode t msg = some bs) : decodeN t msg.length bs = some (msg, []) :=
-- END SPEC
  sorry

end H016

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Both theorems follow from one fact: decoding a code word followed by any bits `rest` reads
    back exactly that symbol and leaves `rest` untouched (`decodeOne_codeOf`).
H2. `decodeOne_codeOf`: induction on `t` generalizing `c`; in the `node` case `split at h` (twice)
    exposes which subtree produced the code, then `simp [decodeOne, ih]`. `prefix_free`: with
    `cb = ca ++ rest`, `decodeOne t (ca ++ rest)` equals both `some (a, rest)` and `some (b, [])`.
    `decode_encode`: generalize the leftover bits and induct on `msg` generalizing `bs`.
H3. `prefix_free`: after `obtain ⟨rest, rfl⟩ := hpre`, instantiate `decodeOne_codeOf` twice (for `a`
    with `rest`, for `b` with `[]`) and compare the two results for the same input bits.
    Induction step for encode: after `split at h` and `cases h`, the goal is about
    `decodeN t (as.length + 1) ((c ++ cs) ++ rest)`; `simp [decodeN, List.append_assoc, decodeOne_codeOf t a c _ hc, ih cs hcs]`.
-/
