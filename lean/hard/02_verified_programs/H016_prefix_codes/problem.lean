/- H016 | Prefix codes from a code tree | 45-75 min | Huffman-style codes, prefix-free, decoding, List.IsPrefix, Option, split at
GOAL
  A binary code tree gives each leaf symbol a code word (its root-to-leaf path). Prove the code is
  prefix-free, and that decoding `msg.length` symbols from `encode t msg` returns `msg` with no bits left.

GUIDE
  Entries R1–R22: one per tactic or lemma, with the proof state before and after.
    cheatsheet.md   read
    guide.lean      step through in the infoview
  Each theorem below has a SKELETON: the order in which those entries are used.
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

/- SKELETON · decodeOne_codeOf   (MILESTONE 1: prove it first; prefix_free and MILESTONE 2 use it)
  1. Induction on the tree; the code word shrinks from `false :: c'` to `c'`, so generalize it:
       induction t generalizing c with | leaf b => … | node l r ihl ihr => …     R1
  2. leaf b: open `codeOf` in h, then split its `if`:                            R2, R3
       a = b:  substitute, solve h for c (c := []), compute `decodeOne`           R4, R5, R6
       a ≠ b:  h : none = some c is impossible                                    R7
  3. node l r: open `codeOf` in h, then split its first `match` (on `codeOf l a`): R2, R8
       arm `some`: name the code and its equation, hc : codeOf l a = some c';
         solve h for c (c := false :: c'); one `decodeOne` step; then `ihl _ hc`  R9, R5, R6, R10
       arm `none`: split the second `match` (on `codeOf r a`):                     R8
         arm `some`: as above with `true` and `ihr`                                R9, R5, R6, R10
         arm `none`: h : none = some c is impossible                               R7
-/
-- MILESTONE (optional: change or delete)
theorem decodeOne_codeOf {α : Type} [DecidableEq α] (t : CTree α) (a : α) (c rest : List Bool)
    (h : codeOf t a = some c) : decodeOne t (c ++ rest) = some (a, rest) := by
  sorry

/- SKELETON · decodeN_encode_append   (MILESTONE 2: uses MILESTONE 1; decode_encode uses it)
  1. Induction on the message; the bits shrink from `c ++ cs` to `cs`, so generalize them:
       induction msg generalizing bs with | nil => … | cons a as ih => …          R1
  2. nil: h becomes bs = []; substitute; compute `decodeN` at 0                    R11, R12, R6
  3. cons a as: `intro rest`; open `encode` in h; split its two-value `match`:     R2, R13
       arm `some c, some cs`: name c cs hc hcs; solve h for bs (bs := c ++ cs)    R9, R5
         goal: decodeN t (a :: as).length (c ++ cs ++ rest) = some (a :: as, rest)
         one `simp [decodeN, …]` call: length, regroup the bits, then both inner
         `match`es reduce by MILESTONE 1 at hc and by `ih cs hcs`                  R14, R15, R16 (with R10)
       fall-through arm: h : none = some bs is impossible                          R7
-/
-- MILESTONE (optional: change or delete)
theorem decodeN_encode_append {α : Type} [DecidableEq α] (t : CTree α) (msg : List α)
    (bs : List Bool) (h : encode t msg = some bs) :
    ∀ rest, decodeN t msg.length (bs ++ rest) = some (msg, rest) := by
  sorry

/- SKELETON · prefix_free   (uses MILESTONE 1 twice, on the same input bits)
  1. Unpack the prefix: `cb` becomes `ca ++ rest` everywhere                        R17
  2. MILESTONE 1 for a (code ca, leftover rest):
       h1 : decodeOne t (ca ++ rest) = some (a, rest)                               R18
     MILESTONE 1 for b (code ca ++ rest, leftover []):
       h2 : decodeOne t (ca ++ rest ++ []) = some (b, [])                           R18
  3. Drop the `++ []` in h2, then rewrite its left side with h1:
       h2 : some (a, rest) = some (b, [])                                           R19, R20
  4. Match the components (a and b become one variable), then close `a = a`:       R21, rfl
-/
-- BEGIN SPEC
theorem prefix_free {α : Type} [DecidableEq α] (t : CTree α) (a b : α) (ca cb : List Bool)
    (ha : codeOf t a = some ca) (hb : codeOf t b = some cb) (hpre : ca <+: cb) : a = b :=
-- END SPEC
  sorry

/- SKELETON · decode_encode   (uses MILESTONE 2)
  1. MILESTONE 2 at h and at rest := [] gives `decodeN t msg.length (bs ++ []) = some (msg, [])`;
     `simpa using` it: `simp` drops the `++ []` and the result is the goal               R22
-/
-- BEGIN SPEC
theorem decode_encode {α : Type} [DecidableEq α] (t : CTree α) (msg : List α) (bs : List Bool)
    (h : encode t msg = some bs) : decodeN t msg.length bs = some (msg, []) :=
-- END SPEC
  sorry

end H016

/- ─────────────────────────── HINTS (spoilers below) ───────────────────────────
H1. Everything follows from MILESTONE 1: decoding a code word followed by any bits `rest` reads back
    exactly that symbol and leaves `rest` untouched. Prove it first (induction on the tree); MILESTONE 2
    is the same fact for whole messages, and decode_encode is MILESTONE 2 with no leftover bits.
H2. MILESTONE 1: `induction t generalizing c`; in each case `simp only [codeOf] at h`, then `split at h`
    (twice in the node case), `rename_i`, `cases h`, and `simp [decodeOne, ih _ hc]`.
    MILESTONE 2: `induction msg generalizing bs`; in the cons case `intro rest`, `simp only [encode] at h`,
    `split at h`, `rename_i c cs hc hcs`, `cases h`. prefix_free: with `cb = ca ++ rest`, the bits
    `ca ++ rest` decode both to `(a, rest)` and to `(b, [])`. decode_encode: `simpa using` MILESTONE 2.
H3. prefix_free, after `obtain ⟨rest, rfl⟩ := hpre`: the key instance is the one for `b`,
    `decodeOne_codeOf t b (ca ++ rest) [] hb`; compare it with the instance for `a` at `rest`.
    MILESTONE 2, cons step after `cases h`:
    `simp [decodeN, List.append_assoc, decodeOne_codeOf t a c _ hc, ih cs hcs]`.
-/
