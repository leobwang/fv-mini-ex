# H013 · Run-length encoding, both directions: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): pattern-matching `def`, `List`, pairs, `intro`, `exact`,
`rfl`, `rw`, `simp`, `omega`, `cases`, `induction`, `<;>`. **New here:** core Lean only (no Mathlib):
a definition body written as `fun | … => …` around a `match` on the recursive call; `split` on a `match`
or an `if` in the goal, the inaccessible names it creates and `rename_i`; `subst_vars`, `absurd`,
`injection`; `simp_all`, `simpa using`, `obtain ⟨k, rfl⟩`; the list lemmas `List.replicate_succ`,
`List.singleton_append`, `List.cons_append`.

The problem in one paragraph. A *run list* `l : List (α × Nat)` is a list of pairs `(a, n)`: symbol `a`
repeated `n` times. `decode` expands it: `decode ((a, n) :: r) = List.replicate n a ++ decode r`.
`Canonical l` says every count is positive and neighbouring runs carry different symbols. You write
`encode : List α → List (α × Nat)` and prove three facts: `decode (encode xs) = xs`,
`Canonical (encode xs)`, and `encode (decode l) = l` for canonical `l`. The intended `encode` works from
the right: encode the tail, then either bump the count of its first run (same symbol) or push a new run
`(x, 1)`. Every proof follows that recursion.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`. It says what changes (**goal**, **context**,
or **goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` (or `Q`) is "the rest of your goal" (`P : β → Prop`). The step changes only the part inside
  `P (…)`, wherever it sits in a larger goal. A hypothesis `h` in an example is there only to finish it.
- Placeholders are written as Lean binders. `{α : Type}` is any type. `[DecidableEq α]` says `a = b` can
  be decided by a program for `a b : α` (true of `Nat`, `Bool`, `Char`, `String`); `encode` needs it for
  its `if x = y`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
  `∅` means the goal is closed.
- A goal containing `match … with | … ` is shown in a block, one goal per line, because `|` would break
  a table.

## Reading the goals

| You see | It means |
|---|---|
| `List (α × Nat)`, `(a, n)` | a run list; `(a, n)` is the pair "symbol `a`, count `n`" |
| `List.replicate n a` | the list of `n` copies of `a`; `List.replicate (0 + 1) a` is not simplified to `[a]` until you ask (R9) |
| `a :: as ++ bs` | `(a :: as) ++ bs`: `::` binds tighter than `++` (R18) |
| `(a, 0 + 1)`, `n + 1 + 1` | Lean does not normalise `0 + 1` to `1` by itself; `simp` or `omega` does |
| `match encode xs with \| (y, n) :: r => … \| [] => …` | the body of `encode (x :: xs)` after one unfolding (R11) |
| `x✝ : List (α × Nat)` | the value a `match` was on, kept by `split`; you never need it |
| `y✝ n✝ r✝ heq✝` | inaccessible names made by `split`: you cannot type them; `rename_i` names them (R13) |
| `heq✝ : encode xs = (y✝, n✝) :: r✝` | which `match` arm you are in (R12) |
| `h✝ : a = y✝`, `h✝ : ¬a = y✝` | which `if` branch you are in (R14); `¬a = y` is `a ≠ y` |
| `inst✝ : DecidableEq α` | the `[DecidableEq α]` argument, unnamed |
| `e ≠ t` | `e = t → False` (R16, R27) |
| `case h_1`, `case h_2`, `case h_1.isTrue`, `case h_1.isFalse` | goal tags: first/second `match` arm, then the `then`/`else` branch of the `if` |
| `case cons.cons.hy` | a side goal: `rw [lemma …]` without the lemma's argument `hy` asks you to prove `hy` after the main goal |
| `m_1`, `r_1` | a bound variable renamed because `m`, `r` are already in the context; same meaning as `m`, `r` |
| `[(a, n)]`, `Canonical [(_, n)]` | the one-element list; `_` in a pattern matches anything and is not named |
| `0 < n`, `a ≠ b`, `A ∧ B ∧ C` | `Canonical` unfolded: positive count, different neighbours, and the rest canonical |
| `case zero`, `case succ`, `case nil`, `case cons` | goal tags made by `induction`/`cases` |

---

## Part 1 · `encode` (a definition with a hole)

The frozen line is `def encode {α : Type} [DecidableEq α] : List α → List (α × Nat) :=`. Everything after
`:=` is yours, and it must be one term of type `List α → List (α × Nat)`.

**R1 · `fun | [] => … | x :: xs => … f xs …`** changes nothing in a proof: it is how to write a
recursive function when the `:=` is already there. `fun` with match arms is a function by cases on its
argument; a call `f xs` on the tail is structural recursion, exactly as for a definition by equations.
Example in the guide: `sumL : List Nat → Nat`, with `sumL [1, 2, 3] = 6` by `rfl`.

**R2 · `match f xs with …` and `if x = y then … else …`** inside an arm: compute the recursive result,
split it by its shape, and compare two symbols. The `if x = y` needs `[DecidableEq α]`, which is in the
signature. Example in the guide: `squash` (drop adjacent duplicates), `squash [1, 1, 2, 2, 2, 1] = [1, 2, 1]`.
For `encode`, the arms are: empty tail encoding → one run `(x, 1)`; first run `(y, n)` with `x = y` →
`(y, n + 1)`; otherwise → push `(x, 1)` in front. Check it with `example : encode [1, 1, 2] = [(1, 2), (2, 1)] := rfl`.

---

## Part 2 · `canonical_bump`, `canonical_push` (MILESTONES)

Statements: if `(y, n) :: r` is canonical, so is `(y, n + 1) :: r` (bump), and so is
`(x, 1) :: (y, n) :: r` when `x ≠ y` (push). `Canonical` has three clauses (`[]`, one run, two or more
runs), so `Canonical ((y, n) :: r)` unfolds only after you know whether `r` is empty: case on `r`, take
its head pair apart, unfold, then close.

**R3 · `cases r with | nil => … | cons q r => …`** changes the **goal list**: one goal per constructor of
`List`, with the constructor's arguments named in the arm. Placeholders: `{α : Type} (P : List α → Prop)
(r : List α)`.

| Before | After |
|---|---|
| `r : List α ⊢ P r` | `⊢ P []`, `q : α, r : List α ⊢ P (q :: r)` |

**R4 · `obtain ⟨b, m⟩ := q`** changes the **context**: a pair `q : α × β` is replaced by its components,
and `q` becomes `(b, m)` in the goal. Placeholders: `{α β : Type} (q : α × β)`.

| Before | After |
|---|---|
| `q : α × β ⊢ P q` | `b : α, m : β ⊢ P (b, m)` |

**R5 · `simp only [D] at h ⊢`** changes the **context and the goal**: in `h` and in the goal, `D` applied
to a visible constructor shape is replaced by the matching clause. Placeholders: the guide's
`Up : List Nat → Prop` (strictly increasing; same three-clause shape as `Canonical`), `(a b c : Nat)
(r : List Nat)`.

| Before | After |
|---|---|
| `h : Up (a :: b :: r) ⊢ Up (c :: a :: b :: r)` | `h : a < b ∧ Up (b :: r) ⊢ c < a ∧ a < b ∧ Up (b :: r)` |

**R6 · `omega`** **closes** a goal of linear arithmetic over `Nat`/`Int`, using the hypotheses.
Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `h : 0 < n ⊢ 0 < n + 1` | ∅ |

**R7 · `exact ⟨p, h.2⟩`** **closes** a conjunction: `⟨p, q⟩` builds `A ∧ B` from `p : A` and `q : B`, and
`h.1`, `h.2` are the two halves of `h : A ∧ B`. `⟨by omega, h.2⟩` proves the first half on the spot.
`A ∧ B ∧ C` nests to the right, so `⟨p, q, r⟩` builds it. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `hc : C, h : A ∧ B ⊢ C ∧ B` | ∅ |

---

## Part 3 · `encode_replicate_append` (MILESTONE)

Statement: if `encode ys` does not start with a run of `a` (`hy : ∀ m r, encode ys ≠ (a, m) :: r`), then
`encode (List.replicate (n + 1) a ++ ys) = (a, n + 1) :: encode ys`. This is the key fact for Part 6:
it re-encodes one decoded run. Induction on `n`.

**R8 · `induction n with | zero => … | succ n ih => …`** changes the **goal list**: the `0` case and the
`n + 1` case, the latter with the induction hypothesis `ih`. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n : Nat, ih : P n ⊢ P (n + 1)` |

**R9 · `simp only [List.replicate]`** changes the **goal**: `List.replicate (0 + 1) a` (the zero case's
`replicate (n + 1)`) computes to `[a]`. Placeholders: `{α : Type} (a : α)`.

| Before | After |
|---|---|
| `⊢ P (List.replicate (0 + 1) a)` | `⊢ P [a]` |

**R10 · `List.singleton_append`** changes the **goal**. The lemma is `[x] ++ l = x :: l`. Placeholders:
`{α : Type} (x : α) (l : List α)`.

| Before | After |
|---|---|
| `⊢ P ([x] ++ l)` | `⊢ P (x :: l)` |

**R11 · `simp only [f]` or `rw [f]`** changes the **goal**: `f (x :: xs)` becomes the `x :: xs` arm of
`f`'s body. For a function written as in R1–R2, that arm is the `match f xs with …`. Use it with `f :=
encode` once the argument is visibly a cons (after R9–R10, or R17–R18). Placeholders: the guide's
`squash`, `{α : Type} [DecidableEq α] (x : α) (xs : List α)`. Before: `⊢ P (squash (x :: xs))`. After:

```lean-goal
⊢ P (match squash xs with | [] => [x] | y :: r => if x = y then y :: r else x :: y :: r)
```

**R12 · `split`** on a `match` changes the **goal list and the context**: one goal per arm. In each, the
discriminant stays in the goal and `heq✝` records which arm you are in. Placeholders:
`{α β γ : Type} (g : γ → List α) (c : γ) (u : β) (v : α → List α → β)`. Before:

```lean-goal
⊢ P (match g c with | [] => u | y :: r => v y r)
```

| After |
|---|
| `heq✝ : g c = [] ⊢ P u` |
| `y✝ : α, r✝ : List α, heq✝ : g c = y✝ :: r✝ ⊢ P (v y✝ r✝)` |

In the exercise, `split` after unfolding `encode (x :: xs)` gives arm `h_1` with
`heq✝ : encode xs = (y✝, n✝) :: r✝` and goal the `if`, and arm `h_2` with `heq✝ : encode xs = []`.

**R13 · `rename_i y r heq`** changes the **context**: it names the most recent inaccessible hypotheses,
in order (`y✝ r✝ heq✝` → `y r heq`). In the exercise write `rename_i y n r heq`. `‹_›` uses a hypothesis
without naming it.

| Before | After |
|---|---|
| `y✝ : α, r✝ : List α, heq✝ : g c = y✝ :: r✝ ⊢ P (v y✝ r✝)` | `y : α, r : List α, heq : g c = y :: r ⊢ P (v y r)` |

**R14 · `split`** on an `if` changes the **goal list and the context**: the `then` goal gets `h✝ : c`,
the `else` goal `h✝ : ¬c`. Placeholders: `(c : Prop) [Decidable c] {β : Type} (u v : β)`.

| Before | After |
|---|---|
| `⊢ P (if c then u else v)` | `h✝ : c ⊢ P u`, `h✝ : ¬c ⊢ P v` |

**R15 · `subst_vars`** changes the **context and the goal**: every hypothesis `x = e` with a variable on one
side is used to replace that variable everywhere, then removed. In the zero case's `a = y` branch it turns
`hy` into a statement about `encode ys ≠ (y, m) :: r`, which contradicts `heq`. Placeholders:
`{α : Type} (a y : α) (P : α → α → Prop)`.

| Before | After |
|---|---|
| `hay : a = y ⊢ P a y` | `⊢ P y y` |

**R16 · `exact absurd h hn`** **closes** any goal from `h : p` and `hn : ¬p`. The lemma is
`absurd : p → ¬p → q`. With `hy : ∀ m r, encode ys ≠ (a, m) :: r`, the term `hy _ _` is such an `hn`;
Lean fills the `_` from `h`. Placeholders: `{α : Type} (Q : Prop) (e t : α)`.

| Before | After |
|---|---|
| `h : e = t, hn : e ≠ t ⊢ Q` | ∅ |

**R17 · `List.replicate_succ`** changes the **goal**. The lemma is
`List.replicate (n + 1) a = a :: List.replicate n a`. Placeholders: `{α : Type} (a : α) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (List.replicate (n + 1) a)` | `⊢ P (a :: List.replicate n a)` |

**R18 · `List.cons_append`** changes the **goal**. The lemma is `a :: as ++ bs = a :: (as ++ bs)`
(read the left side as `(a :: as) ++ bs`). Placeholders: `{α : Type} (a : α) (as bs : List α)`.

| Before | After |
|---|---|
| `⊢ P (a :: as ++ bs)` | `⊢ P (a :: (as ++ bs))` |

In the `succ` case, R17 then R18 make the argument of `encode` a cons, R11 (`rw [encode]`) unfolds one
step, and `rw [ih]` puts the known first run `(a, n + 1)` where the `match` can see it.

**R19 · `simp`** changes the **goal**: a `match` on a visible constructor picks its arm, and `if a = a`
picks the `then` branch. Placeholders: `{α β : Type} [DecidableEq α] (a : α) (t : List α) (u : β)
(v w : α → List α → β)`. Before:

```lean-goal
⊢ P (match a :: t with | [] => u | y :: r => if a = y then v y r else w y r)
```

| After |
|---|
| `⊢ P (v a t)` |

In the exercise, `simp` also normalises `n + 1 + 1` and closes the resulting `x = x`.

---

## Part 4 · `decode_encode`

Statement: `decode (encode xs) = xs`. Induction on `xs`; in the cons case unfold `encode` once (R11), then
three arms: bump, push, empty. They differ only in which `if`/`match` branch you are in, so handle them all
with one line.

**R20 · `try t`** runs `t`, and if `t` fails it does nothing instead of failing. `split <;> (try split)`
splits the `match`, then the `if` in the arm that has one (the empty arm has none). Placeholders:
`(A B : Prop)`.

| Before | After `try constructor` |
|---|---|
| `⊢ A ∧ B` | `⊢ A`, `⊢ B` |

**R21 · `simp_all [l]`** **closes** the goal (or simplifies it as far as it can): it simplifies every
hypothesis and the goal using the lemmas and definitions `l` and the hypotheses themselves. An equation
`heq : e = t` rewrites `e` elsewhere; this is how `heq` and `ih` reach the goal. For this part give it
`decode` and `List.replicate_succ`. Placeholders: `{α : Type} (f : List α → List α) (e t : List α)`.

| Before | After |
|---|---|
| `heq : f e = t, ih : t = e ⊢ f e = e` | ∅ |

---

## Part 5 · `encode_canonical`

Statement: `Canonical (encode xs)`. Induction on `xs`; the `nil` goal is `Canonical (encode [])`, which
computes to `True` (R22 sees through both definitions). In the cons case unfold `encode` once (R11), split
the `match` (R12), name the hypotheses (R13), move `heq` into `ih` (R23), split the `if` (R14) and use the
two Part 2 milestones; the empty arm is `Canonical [(x, 1)]`, i.e. `0 < 1`.

**R22 · `trivial`** **closes** `True`, and a definition that unfolds to `True` such as `Up []` (or
`Canonical []`).

| Before | After |
|---|---|
| `⊢ Up []` | ∅ |

**R23 · `rw [h] at h'`** changes the **context**: it rewrites inside the hypothesis `h'` instead of the
goal. Placeholders: `{α : Type} (e t : List α)`.

| Before | After |
|---|---|
| `heq : e = t, ih : P e ⊢ P t` | `ih : P t ⊢ P t` |

To apply a milestone, `exact canonical_bump _ _ _ ih`: the `_` are filled from `ih`'s type. The `else`
branch's `h✝ : ¬x = y` is the `x ≠ y` that `canonical_push` asks for (name it with R13).

---

## Part 6 · `encode_decode`

Statement: `Canonical l → encode (decode l) = l`. Induction on `l`; split the head pair (R4) and case on
the rest (R3), because `Canonical` looks two runs ahead. In both cases write the count as `k + 1` (R25),
then use `encode_replicate_append`; in the two-run case its hypothesis `hy` holds because the IH says the
rest re-encodes to `(b, m) :: r` and `b ≠ a`. The `nil` case `encode (decode []) = []` is `rfl`. After
`cases r`, the IH is `ih : Canonical ((b, m) :: r) → encode (decode ((b, m) :: r)) = (b, m) :: r`: an
implication, so feed it the third part of `h` (`have ih' := ih hr`).

**R24 · `obtain ⟨hn, hab, hr⟩ := h`** changes the **context**: `h : A ∧ B ∧ C` is replaced by its three
parts. Use it after unfolding `Canonical` in `h` (R5). Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `h : A ∧ B ∧ C ⊢ B` | `hn : A, hab : B, hr : C ⊢ B` |

**R25 · `obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩`** changes the **context and the goal**:
it proves `∃ k, n = k + 1` (from `0 < n` in context, by `omega`), takes the witness `k`, and the pattern
`rfl` substitutes `n := k + 1` everywhere. `n` disappears. Placeholders: `(P : Nat → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `n : Nat, hn : 0 < n ⊢ P n` | `k : Nat, hn : 0 < k + 1 ⊢ P (k + 1)` |

**R26 · `simpa [l] using e`** **closes** the goal: it simplifies the type of `e` and the goal with `l`
and then they must agree. In the one-run case, `e` is `encode_replicate_append a k [] (…)`, and
`simpa [decode, encode]` removes the `++ []` and `encode [] = []`. Placeholders:
`(P : List Nat → Prop) (l : List Nat)`.

| Before | After |
|---|---|
| `e : P (l ++ []) ⊢ P l` | ∅ |

**R27 · `intro m r h`** on a goal `∀ m r, e ≠ t m r` changes the **goal and the context**: `≠` is
`= → False`, so `intro` takes the equation too and the goal becomes `False`. This is how you prove
the milestone's `hy` argument. Placeholders: `{α : Type} (f : α → α → List α) (e : List α)`.

| Before | After |
|---|---|
| `⊢ ∀ (x y : α), e ≠ f x y` | `x y : α, hxy : e = f x y ⊢ False` |

**R28 · `injection h with h₁ h₂`** changes the **context**: from an equation between two applications of
the same constructor (`::`, or the pair `(·, ·)`) it gets the equations between the arguments. `h₁.symm`
turns `a = b` into `b = a`. In R27's `False` goal, `h : (b, m) :: r = (a, m') :: r'` needs two
`injection`s (list, then pair) to reach `b = a`, which contradicts `b ≠ a`. Placeholders:
`{α : Type} (a b : α) (l l' : List α) (n m : Nat)`.

| Before | After |
|---|---|
| `h : a :: l = b :: l' ⊢ False` | `h₁ : a = b, h₂ : l = l' ⊢ False` |
| `⊢ b = a`, with `h : (a, n) = (b, m)` | `h₁ : a = b, h₂ : n = m ⊢ b = a` |

Before rewriting with the milestone in the two-run case, `simp only [decode] at ih' ⊢` (R5) turns
`decode ((a, k + 1) :: (b, m) :: r)` into `List.replicate (k + 1) a ++ (List.replicate m b ++ decode r)`,
the exact shape `encode_replicate_append` rewrites.

---

## Worked combinations (W1–W3 in the guide, on `squash`)

**W1.** `(squash xs).length ≤ xs.length`: induction (R8), unfold (R11), `split` on the `match` (R12),
name (R13), move `heq` into `ih` (R23), `split` on the `if` (R14), close with `simp` and `omega` (R6).

**W2.** `squash (List.replicate (n + 1) a) = [a]`: the zero case by `simp only [List.replicate, squash]`
(R9, R11); the succ case by `rw [List.replicate_succ, squash, ih]` then `simp` (R17, R11, R19). The same
shape as Part 3's succ case.

**W3.** `squash xs = [] → squash (x :: xs) = [x]`: unfold once,

```lean-goal
⊢ (match squash xs with | [] => [x] | y :: r => if x = y then y :: r else x :: y :: r) = [x]
```

then `split <;> (try split) <;> simp_all` (R12, R20, R14, R21) closes all arms; the `y :: r` arms die
because `hx` and `heq✝` contradict each other.

---

## Traps

- The `:=` of `encode` is frozen: its body is a term (`fun | … => …`), not equations `| [] => …` written
  after the signature.
- `simp only [encode]` / `rw [encode]` unfold only `encode (x :: xs)` or `encode []`. If the argument is
  `List.replicate (n + 1) a ++ ys`, first make it a cons with R9–R10 or R17–R18.
- After `split`, the names are inaccessible (`heq✝`). `rw [heq✝]` does not parse: `rename_i` them (R13).
  `rename_i` names the *last* ones, so list all of them, in order (`rename_i y n r heq`).
- `split` tags the arms `h_1`, `h_2` in the order *you wrote them* in `encode`'s `match`, not in the
  order `[]` then cons. Your bullets after `split` must follow that order.
- `Canonical ((y, n) :: r)` does not unfold while `r` is a variable: case on `r` first (R3).
- `simp [Canonical]` closes `canonical_bump`'s `nil` case (`0 < n + 1`) but not `canonical_push`'s: there
  it leaves `¬x = y ∧ 0 < n`, which needs `hxy` and `h`. Use R5 then R7 (`⟨by omega, hxy, h⟩`).
- `rw [encode_replicate_append a k]` without its `hy` argument leaves `case hy` as a second goal, after the
  main one. Close the main goal first (`rw [ih']`), then prove `hy` (R27, R28).
- `grind` and `fun_induction` are banned: the recursion is handled by `induction` + `split`.
- Do not leave `exact?`, `apply?`, `try?` in the file; do not add imports.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| body after a frozen `:=` | `fun \| [] => … \| x :: xs => match f xs with …` | R1, R2 |
| case on a list / a pair | `cases r with \| nil => … \| cons q r => …` / `obtain ⟨b, m⟩ := q` | R3, R4 |
| unfold a clause-wise definition, in `h` and in the goal | `simp only [D] at h` plus the goal symbol, as in R5 | R5 |
| arithmetic | `omega` | R6 |
| build / take apart `A ∧ B` | `⟨p, q⟩`, `h.1`, `h.2` / `obtain ⟨p, q, r⟩ := h` | R7, R24 |
| induction on `n` | `induction n with \| zero => … \| succ n ih => …` | R8 |
| `replicate (0+1) a ++ l` → `a :: l` | `simp only [List.replicate, List.singleton_append]` | R9, R10 |
| `replicate (n+1) a ++ l` → `a :: (replicate n a ++ l)` | `rw [List.replicate_succ, List.cons_append]` | R17, R18 |
| unfold `encode (x :: xs)` once | `simp only [encode]` / `rw [encode]` | R11 |
| case on the `match` / the `if` | `split` | R12, R14 |
| name `heq✝` etc. | `rename_i y n r heq` | R13 |
| use `x = y` hypotheses | `subst_vars` | R15 |
| contradiction `h : p`, `hn : ¬p` | `exact absurd h hn` | R16 |
| finish after the `match` became visible | `simp` | R19 |
| all arms at once | `split <;> (try split) <;> simp_all [decode, List.replicate_succ]` | R20, R21 |
| `True` | `trivial` | R22 |
| rewrite a hypothesis | `rw [heq] at ih` | R23 |
| `0 < n` → `n = k + 1` | `obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩` | R25 |
| use a lemma up to simplification | `simpa [decode, encode] using lemma …` | R26 |
| prove `∀ m r, e ≠ …` | `intro m r h`, then `injection h with h …` | R27, R28 |
| see the state | infoview | |
