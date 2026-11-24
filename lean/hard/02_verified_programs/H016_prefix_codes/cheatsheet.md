# H016 · Prefix codes from a code tree: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `inductive`, pattern-matching `def`, `List`, `Option`,
`intro`, `exact`, `rfl`, `rw`, `simp`, `cases`, `induction`. **New here:** core Lean only (no Mathlib):
`induction … generalizing`, `split at h` on an `if` or a `match` inside a hypothesis, the inaccessible
names it creates and `rename_i`, `cases` on equations between constructors, `subst`, `obtain` with `rfl`,
the prefix relation `<+:`, and the strengthen-then-specialize pattern `simpa using`.

The problem in one paragraph. A code tree `t : CTree α` has symbols at its leaves. The code word of a
symbol `a` (`codeOf t a`) is the path from the root to the leftmost leaf labelled `a`, one bit per edge
(`false` = left, `true` = right); it is `none` when `a` is not in the tree. `encode` concatenates code
words. `decodeOne` walks down from the root reading bits until it reaches a leaf, and returns that leaf's
symbol and the unread bits. `decodeN t n` runs `decodeOne` `n` times. One fact carries everything
(MILESTONE 1): decoding `c ++ rest`, where `c` is the code word of `a`, returns `(a, rest)`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`, `G`) is "the rest of your goal". The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal. A hypothesis `k` or `h` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `[DecidableEq α]` says `a = b` can be
  decided by a program for `a b : α` (true of `Nat`, `Bool`, `Char`, `String`), which `codeOf` needs for
  its `if a = b`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- `∅` means the goal is closed.

## Reading the goals

| You see | It means |
|---|---|
| `CTree.leaf b`, `l.node r` | the constructors `CTree.leaf b` and `CTree.node l r`; `l.node r` is dot notation for `CTree.node l r` |
| `.leaf b` (in source) | `CTree.leaf b`, with `CTree` read off the expected type |
| `Option β`, `some x`, `none` | a value that may be missing: `some x` (present) or `none` (absent) |
| `α × List Bool`, `(a, rest)` | pairs; `(a, rest)` is a symbol together with the unread bits |
| `false :: c' ++ rest` | `(false :: c') ++ rest`: `::` binds tighter than `++`; `simp` turns it into `false :: (c' ++ rest)` (`List.cons_append`) |
| `c ++ cs ++ rest` | `(c ++ cs) ++ rest`: `++` groups to the left (R15 regroups it) |
| `(a :: as).length`, `[].length` | `List.length`; `simp` turns them into `as.length + 1` and `0` (R14) |
| `xs <+: ys` | `List.IsPrefix xs ys`: `∃ t, xs ++ t = ys` (R17) |
| `if b then r else l`, `b : Bool` | `if b = true then r else l` |
| `a✝`, `l✝`, `c✝`, `h✝`, `heq✝`, `heq✝¹` | inaccessible names: Lean made them, you cannot type them. `rename_i` names them (R9). `✝¹` is the one before `✝` |
| `inst✝ : DecidableEq α` | the unnamed instance argument `[DecidableEq α]` of the theorem; you never need it by name |
| `x✝ : Option (List Bool)` | the value a `match` was on, kept by `split`; you never need it |
| `x, x_1 => none` inside a printed `match` | the source arm `_, _ => none` |
| `case leaf.isTrue`, `case h_1`, `case h_2`, `case h_1.refl` | the goal's tag: the `then` branch of an `if` (`isFalse`: the `else` branch), the first / second `match` arm, after a `cases` on `=` |

---

## Part 1 · `decodeOne_codeOf` (MILESTONE 1)

Statement: if `codeOf t a = some c` then `decodeOne t (c ++ rest) = some (a, rest)`. Prove it first: both
`prefix_free` and MILESTONE 2 use it. Proof shape: induction on the tree; in each case open `codeOf` in
`h`, split its `if`/`match`, solve `h` for `c`, compute `decodeOne` one step.

**R1 · `induction t generalizing c`** changes the **goal list**: one goal per constructor of `CTree`. The
variable `c` is removed from the context first and quantified in each induction hypothesis, because in
the `node` case the code word `c = false :: c'` is not the one the hypothesis is about (it is about `c'`).
Placeholders: `{α : Type} (P : Tr α → List Bool → Prop) (t : Tr α) (c : List Bool)`.

| Before | After |
|---|---|
| `c : List Bool ⊢ P t c` | `a✝ : α, c : List Bool ⊢ P (Tr.leaf a✝) c`, `l✝ r✝ : Tr α ⊢ P (l✝.node r✝) c` |

The `node` goal also has the induction hypotheses `l_ih✝ : ∀ (c : List Bool), P l✝ c` and
`r_ih✝ : ∀ (c : List Bool), P r✝ c`. Write `induction t generalizing c with | leaf b => … | node l r ihl
ihr => …` to name everything yourself (W1).

**R2 · `simp only [f] at h`** changes the **context**: `h` mentions `f` applied to a constructor, and
`simp only [f]` replaces it by the matching clause of `f`'s definition. Placeholders: `{α : Type}
[DecidableEq α] (a b : α) (n : Nat)`, with `leftDepth` the guide's own search function.

| Before | After |
|---|---|
| `h : leftDepth (Tr.leaf b) a = some n ⊢ Q` | `h : (if a = b then some 0 else none) = some n ⊢ Q` |

In the problem: `h : codeOf (CTree.leaf b) a = some c` becomes `h : (if a = b then some [] else none) = some c`.

**R3 · `split at h` (an `if`)** changes the **goal list and the context**: one goal per branch. Each goal
gets the branch condition as an inaccessible hypothesis, and `h` becomes the branch's value.

| Before | After |
|---|---|
| `h : (if a = b then some 0 else none) = some n ⊢ Q` | `h✝ : a = b, h : some 0 = some n ⊢ Q`, `h✝ : ¬a = b, h : none = some n ⊢ Q` |

**R4 · `subst_vars`** changes the **context**: every hypothesis `x = e` with `x` a local variable is used to
replace `x` by `e` everywhere, and is dropped. In the leaf case it turns `a` into `b` (from `h✝ : a = b`).
Placeholders: `{α : Type} (a b : α)`.

| Before | After |
|---|---|
| `hab : a = b ⊢ P a b` | `⊢ P b b` |

**R5 · `cases h`, `h : some e = some c`** changes the **context**: `some` is a constructor, so the equation
holds only if `e = c`; `c` is a variable, so Lean replaces `c` by `e` everywhere and drops `h`. This is how
you "solve `h` for `c`". Placeholders: `(e c : List Bool)`.

| Before | After |
|---|---|
| `h : some e = some c ⊢ P c` | `⊢ P e` |

**R6 · `simp [f]`** changes the **goal**: it unfolds `f` where its argument is a constructor (`[]`,
`b :: bs`, `.leaf a`, `.node l r`) and reduces `if false then … else …` to the else branch (lemmas
`Bool.false_eq_true`, `↓reduceIte`). Placeholders: `{α : Type} (l r : α) (bs : List Bool)`, with `pick`
the guide's one-bit reader.

| Before | After |
|---|---|
| `⊢ P (pick l r (false :: bs))` | `⊢ P (some (l, bs))` |

In the problem: `simp [decodeOne]` turns `decodeOne (l.node r) (false :: c' ++ rest)` into
`decodeOne l (c' ++ rest)`, one step down the tree.

**R7 · `cases h`, `h : none = some c`** changes the **goal list**: `none` and `some` are different
constructors, so no case remains and the goal is closed. Every "symbol not found" branch ends this way.

| Before | After |
|---|---|
| `h : none = some c ⊢ Q` | ∅ |

**R8 · `split at h` (a `match` on `f x`)** changes the **goal list and the context**: one goal per arm of
the `match`. Each goal gets the equation saying which arm fired, and `h` becomes that arm's value. In the
example `h : (match f x with | some n => some (n + 1) | none => none) = some m` and the goal is `Q`.
Placeholders: `(f : Nat → Option Nat) (x m : Nat)`.

| Before | After |
|---|---|
| `⊢ Q` | `heq✝ : f x = some n✝, h : some (n✝ + 1) = some m ⊢ Q`, `heq✝ : f x = none, h : none = some m ⊢ Q` |

In the problem: in the `node` case, after R2, the first arm gives `heq✝ : codeOf l a = some c✝` and
`h : some (false :: c✝) = some c`. The `none` arm still has the second `match` (on `codeOf r a`) in `h`:
split again.

**R9 · `rename_i x hx`** changes the **context**: the last inaccessible names, in order, get the names you
give. Count from the end: after R8 the inaccessible names are `x✝ c✝ heq✝`, so `rename_i c' hc` names
`c✝ := c'` and `heq✝ := hc`. Placeholders: `(f : Nat → Option Nat) (x : Nat)`.

| Before | After |
|---|---|
| `n✝ : Nat, a✝ : f x = some n✝ ⊢ Q n✝` | `n : Nat, hn : f x = some n ⊢ Q n` |

**R10 · `simp [ih _ hc]`** changes the **goal**: `ih : ∀ c, Q c → g (c ++ rest) = some y` is a family of
equations; `ih _ hc` is the one for the `c` that `hc : Q c` is about (`_` is filled in from `hc`), and
`simp` rewrites with it. Placeholders: `(Q : List Bool → Prop) (g : List Bool → Option Nat) (rest c :
List Bool) (y : Nat)`.

| Before | After |
|---|---|
| `hc : Q c ⊢ P (g (c ++ rest))` | `⊢ P (some y)` |

In the problem: `ihl _ hc : decodeOne l (c' ++ rest) = some (a, rest)` closes the left-arm goal.

---

## Part 2 · `decodeN_encode_append` (MILESTONE 2)

Statement: if `encode t msg = some bs` then for every `rest`,
`decodeN t msg.length (bs ++ rest) = some (msg, rest)`: decoding an encoded message followed by any
further bits. `decode_encode` is its `rest := []` case (Part 4). Induct on `msg` generalizing `bs` (R1),
since `bs` shrinks from `c ++ cs` to `cs`; MILESTONE 1 decodes the first symbol. (A direct induction for
`decode_encode` works too, because MILESTONE 1 already allows leftover bits; the milestone is the
cleaner, reusable statement.)

**R11 · `simp [f] at h`** changes the **context**: unfolds `f` in `h`, then simplifies. `some x = some y`
becomes `x = y` (`Option.some.injEq`), and `[] = bs` is turned around to `bs = []` (`List.nil_eq`).
Placeholders: `(bs : List Bool)`, `code0` a guide function with `code0 [] = some []`.

| Before | After |
|---|---|
| `h : code0 [] = some bs ⊢ Q` | `h : bs = [] ⊢ Q` |

In the problem's `nil` case: `simp [encode] at h` leaves `h : bs = []`.

**R12 · `subst h`** changes the **context**: with `h : x = e` (or `e = x`) and `x` a local variable, it
replaces `x` by `e` everywhere and drops `h`. Placeholders: `(bs : List Bool)`.

| Before | After |
|---|---|
| `h : bs = [] ⊢ P bs` | `⊢ P []` |

**R13 · `split at h` (a `match` on two values with a fall-through arm)** changes the **goal list and the
context**. `encode` matches on `codeOf t a, encode t as` with arms `some c, some cs` and `_, _`. In the
example `h : (match f a, f b with | some m, some n => some (m + n) | _, _ => none) = some k`, goal `⊢ Q`.
Placeholders: `(f : Nat → Option Nat) (a b k : Nat)`.

| Before | After |
|---|---|
| `⊢ Q` | `heq✝¹ : f a = some m✝, heq✝ : f b = some n✝, h : some (m✝ + n✝) = some k ⊢ Q`, `h : none = some k ⊢ Q` |

The second goal also gets `x✝ : ∀ (m n : Nat), f a = some m → f b = some n → False` ("the first arm did
not fire"); you do not need it, because `h : none = some k` closes the goal (R7). In the problem, the first
goal's inaccessible names are `x✝¹ x✝ c✝ cs✝ heq✝¹ heq✝`, so `rename_i c cs hc hcs` (R9) names the last four,
and `cases h` (R5) replaces `bs` by `c ++ cs`. The goal is then
`decodeN t (a :: as).length (c ++ cs ++ rest) = some (a :: as, rest)`.

**R14 · `List.length_cons`** changes the **goal**: `(a :: as).length = as.length + 1`, which lets `decodeN`'s
`n + 1` clause unfold. `simp` uses it by itself. Placeholders: `{α : Type} (a : α) (as : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as).length` | `⊢ P (as.length + 1)` |

**R15 · `List.append_assoc`** changes the **goal**: `as ++ bs ++ cs = as ++ (bs ++ cs)`. It turns
`c ++ cs ++ rest` into `c ++ (cs ++ rest)`, the shape MILESTONE 1 reads (`c ++ rest'` with
`rest' := cs ++ rest`). `simp` uses it by itself (it is a `@[simp]` lemma); naming it does no harm.
Placeholders: `{α : Type} (as bs cs : List α)`.

| Before | After |
|---|---|
| `⊢ P (as ++ bs ++ cs)` | `⊢ P (as ++ (bs ++ cs))` |

**R16 · `simp [hx]` on a `match`** changes the **goal**: with `hx : g x = some y`, `simp` rewrites the
`match`'s discriminant `g x` to `some y` and then takes the `some` arm. Placeholders:
`(g : Nat → Option Nat) (x y : Nat)`.

```lean-goal
⊢ P (match g x with | none => none | some z => some (z + 1))
⊢ P (some (y + 1))
```

In the problem, unfolding `decodeN` gives two nested `match`es: on `decodeOne t (c ++ (cs ++ rest))`
(rewritten by MILESTONE 1 at `hc`, as in R10) and then on `decodeN t as.length (cs ++ rest)` (rewritten by
`ih cs hcs`). One `simp [decodeN, List.append_assoc, …]` call with both equations does R14, R15, R16 together.
MILESTONE 1 at `hc` is `decodeOne_codeOf t a c (cs ++ rest) hc`. You may write `_` for the leftover bits
instead of `(cs ++ rest)`: unlike in R10, `hc` does not fix them, so `simp` keeps the `_` as a pattern
variable and fills it in where the rule matches.

---

## Part 3 · `prefix_free`

Statement: if `codeOf t a = some ca`, `codeOf t b = some cb` and `ca <+: cb`, then `a = b`. Idea: write
`cb = ca ++ rest`. MILESTONE 1 applied to `a` decodes the bits `ca ++ rest` to `(a, rest)`; applied to `b`
with no leftover bits, it decodes the same bits `(ca ++ rest) ++ []` to `(b, [])`. One input, one output,
so `a = b`.

**R17 · `obtain ⟨rest, rfl⟩ := hpre`** changes the **context**: `hpre : xs <+: ys` is `∃ t, xs ++ t = ys`;
`obtain` takes the witness as `rest`, and the pattern `rfl` uses `xs ++ rest = ys` to replace `ys` by
`xs ++ rest` everywhere (here `cb`, so `hb` becomes `codeOf t b = some (ca ++ rest)`). Placeholders:
`{α : Type} (xs ys : List α)`.

| Before | After |
|---|---|
| `hpre : xs <+: ys ⊢ P xs ys` | `rest : List α ⊢ P xs (xs ++ rest)` |

**R18 · `have h1 := lem x c hq`** changes the **context**: it adds the statement of `lem` at those
arguments, computed by Lean (no type written). Placeholders:
`{α : Type} (Q R : α → List Bool → Prop) (lem : ∀ (x : α) (c : List Bool), Q x c → R x c)`.

| Before | After |
|---|---|
| `⊢ G` | `h1 : R x c ⊢ G` |

In the problem: `h1 : decodeOne t (ca ++ rest) = some (a, rest)` and
`h2 : decodeOne t (ca ++ rest ++ []) = some (b, [])`.

**R19 · `rw [List.append_nil] at h`** changes the **context**: `List.append_nil : as ++ [] = as`.
Placeholders: `{α : Type} (xs : List α) (Q : List α → Prop)`.

| Before | After |
|---|---|
| `h : Q (xs ++ []) ⊢ G` | `h : Q xs ⊢ G` |

**R20 · `rw [e] at h`** changes the **context**: with `e : u = v`, every `u` in `h` becomes `v`. In the
problem `e` is `h1`, and `h2` becomes `some (a, rest) = some (b, [])`. Placeholders: `{β : Type} (u v w : β)`.

| Before | After |
|---|---|
| `h : u = w ⊢ G` | `h : v = w ⊢ G` |

**R21 · `cases h`, `h : some (x, xs) = some (y, [])`** changes the **context**: `some` and the pair `( , )`
are constructors, so Lean matches componentwise: `x = y` and `xs = []`; both have a variable side, so
they are substituted, and `h` is gone. Placeholders: `{α : Type} (x y : α) (xs : List Bool)`, with
`h : some (x, xs) = some (y, [])` in the context before the step.

| Before | After |
|---|---|
| `⊢ P x y xs` | `⊢ P x x []` |

The goal `a = b` becomes `a = a` (or `b = b`): `rfl`.

---

## Part 4 · `decode_encode`

Statement: if `encode t msg = some bs` then `decodeN t msg.length bs = some (msg, [])`. It is MILESTONE 2
at `rest := []`, up to `bs ++ [] = bs`.

**R22 · `simpa using e`** **closes** the goal: it simplifies the type of `e` and the goal with the same
`simp` set, then checks they agree. `simp` removes `++ []` (`List.append_nil`). Placeholders:
`{α : Type} (xs : List α) (P : List α → Prop)`.

| Before | After |
|---|---|
| `e : P (xs ++ []) ⊢ P xs` | ∅ |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `leftDepth t a = some n → n ≤ height t` on the guide's tree `Tr`: the same shape as MILESTONE 1.
`induction t generalizing n with | leaf b => … | node l r ihl ihr => …` (R1), then in each case
`simp only [leftDepth] at h; split at h` (R2, R3 / R8), `rename_i m hm` (R9), `cases h` (R5, R7).

```lean-goal
⊢ n ≤ height t
```

**W2.** Reading two bits with `pick2`, which nests two `match`es on `pick`: `simp [pick2, pick]` unfolds
`pick` (R6) and reduces both `match`es (R16) in one call.

```lean-goal
⊢ pick2 l r (true :: false :: rest) = some (r, l, rest)
```

**W3.** Strengthen, then specialize: from `hall : ∀ rest, pick l r (false :: bs ++ rest) = some (l, bs ++ rest)`,
`simpa using hall []` proves the `rest`-free statement (R22).

```lean-goal
⊢ pick l r (false :: bs) = some (l, bs)
```

---

## Traps

- `codeOf t a = none` when `a` is not in the tree, so `encode` returns `none` on such a message. The
  hypothesis `h : … = some …` excludes this: every `none` branch after `split at h` has `h : none = some _`,
  which `cases h` closes (R7). Do not try to prove those branches any other way.
- `split at h` needs the `if`/`match` to be visible in `h`. Unfold first (`simp only [codeOf] at h`, R2);
  `split at h` on `h : codeOf t a = some c` fails.
- Forgetting `generalizing c` (or `generalizing bs`) leaves an induction hypothesis about the same `c` as
  the goal, which is useless in the `node` case, where the code word is `false :: c'`.
- `rename_i` names the LAST inaccessible hypotheses. Give exactly as many names as you need, counting from
  the end of the context.
- `cases h` on an equation peels matching constructors (`some`, pairs, `::`) and then needs a variable on
  one side of each remaining equation. On `h : some (f x) = some (g y)` it fails: use `simp at h` (R11) or
  `Option.some.inj h` instead.
- MILESTONE 2 quantifies `rest` inside the statement (`∀ rest, …`), so after `induction msg` the goal
  still starts with `∀ rest`: `intro rest` in the `cons` case, and the induction hypothesis keeps `∀ rest`.
- In `prefix_free`, MILESTONE 1 for `b` must be used with leftover bits `[]` and code word `ca ++ rest`, not
  with `rest`: the code word of `b` is the whole `cb`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induction, the IH for every `c` | `induction t generalizing c with \| leaf b => … \| node l r ihl ihr => …` | R1 |
| open a definition in `h` | `simp only [codeOf] at h` | R2 |
| case on the `if`/`match` in `h` | `split at h` | R3, R8, R13 |
| substitute variable equations | `subst_vars` / `subst h` | R4, R12 |
| `h : some e = some c` → `c := e` | `cases h` | R5, R21 |
| `h : none = some c` → done | `cases h` | R7 |
| compute a function on constructors | `simp [decodeOne]` | R6 |
| name `x✝`, `heq✝` | `rename_i c hc` | R9 |
| rewrite with an IH instance | `simp [ih _ hc]` | R10 |
| unfold and clean `h` | `simp [encode] at h` | R11 |
| `(a :: as).length`, `(xs ++ ys) ++ zs` | `simp [List.append_assoc]` (length is automatic) | R14, R15 |
| `match` on a known `some` | `simp [hx]` | R16 |
| `xs <+: ys` → `ys = xs ++ rest` | `obtain ⟨rest, rfl⟩ := hpre` | R17 |
| a lemma at given arguments | `have h1 := lem x c hq` | R18 |
| rewrite inside `h` | `rw [List.append_nil, e] at h` | R19, R20 |
| specialize a `∀ rest` statement | `simpa using lem … []` | R22 |
| see the state | infoview | |
