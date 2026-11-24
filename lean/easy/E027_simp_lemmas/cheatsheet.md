# E027 · simp lemmas: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics up to E026: `rfl` (E001), `def` (E002), `exact` (E003), and `simp`,
`simp only [l]`, `simp [f]` with the default simp set (E010). **New here:** the `@[simp]` attribute, which
adds your own lemma to the default simp set; simp lemmas whose variables are functions; `simp [-l]` to drop a
lemma for one call; `attribute [simp] l` to tag a lemma after it is declared. No Mathlib.

## How to read an entry

Each entry is one tactic, one attribute, or one kind of simp lemma. It says what changes (**goal**,
**context**, **goal list**, or the **simp set**), lists the placeholders with their types, then shows the
proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`, wherever it
  sits in a larger goal.
- The guide uses its own definitions: `addTwo n = n + 2`, `thrice f x = f (f (f x))` (and `triple n = 3 * n`
  in W4). The exercise's `twice` and `inc` work the same way.
- "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Nat → Nat` | functions from naturals to naturals |
| `twice f x`, `thrice g a` | the function `twice` / `thrice` applied to the function `f` and the number `x` |
| `twice inc` | a **partial application**: `twice` with its first argument only, itself a `Nat → Nat` |
| `twice (twice inc) n` | `twice` with `f := twice inc` and `x := n` |
| `g (g (g a))` | `g` applied three times, innermost first |
| `twice inc t` | application groups to the left: `(twice inc) t`, so it is a full call of `twice` with `f := inc`, `x := t` |
| `P (thrice g a)` | `P` applied to `thrice g a` |

---

## Part 1 · `twice_apply`

Statement: `twice f x = f (f x)` for every function `f : Nat → Nat` and `x : Nat`, tagged `@[simp]`. The right
side is the body of `twice`, so the equation holds by definition (R1). The tag (R2) and the function variable
`f` (R3) matter only for Part 3.

### What `@[simp]` does

`simp` rewrites with a set of equations `lhs = rhs`, always left to right (E010). The **default simp set** is
every theorem tagged `@[simp]`. Writing `@[simp]` before your own theorem adds it to that set for every `simp`
call **after** the declaration (and in every file that imports this one). The tag does not prove anything: the
theorem still needs its own proof.

| Form | Effect |
|---|---|
| `@[simp] theorem l … : lhs = rhs := proof` | declare `l` and add it to the default simp set |
| `attribute [simp] l` | add an already declared `l` to the default simp set (W4) |
| `simp` | rewrite with the default simp set, now including `l` |
| `simp [-l]` | the default simp set without `l`, for this call only (W3) |
| `simp only [l]` | only `l` (plus closing `t = t` and numeral arithmetic) |

A good simp lemma rewrites a more complicated left side into a simpler right side: `addTwo n` into `n + 2`,
`thrice f x` into `f (f (f x))`. The left side must not reappear inside the right side, or `simp` loops.

### Entries

**R1 · `rfl`** **closes** an equation whose two sides become the same term once definitions are unfolded.
`rfl` (E001) does that unfolding while it compares. The term `:= rfl` and the tactic `:= by rfl` prove the
same equations. Placeholders: the guide's `def addTwo (n : Nat) : Nat := n + 2`, `(n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ addTwo n = n + 2` | no goals |

**R2 · `@[simp] theorem l … : lhs = rhs`** changes the **simp set**: `l` is added to it. No goal changes at the
declaration. Every plain `simp` written afterwards rewrites `lhs` into `rhs`, with no `[l]` or `[addTwo]` in
brackets (compare E010, R4, where `simp [double]` had to be told). Placeholders: the guide's
`@[simp] theorem addTwo_eq (n : Nat) : addTwo n = n + 2 := rfl`, `(k : Nat) (P : Nat → Prop)`.

| Before `simp` | After `simp` |
|---|---|
| `⊢ P (addTwo k)` | `⊢ P (k + 2)` |

**R3 · a simp lemma with a function variable** changes the **goal** when `simp` uses it. In the guide's
`@[simp] theorem thrice_apply (f : Nat → Nat) (x : Nat) : thrice f x = f (f (f x)) := rfl`, both `f` and `x` are
variables, so the left side `thrice f x` matches `thrice` applied to any function and any number. It matches only
when `thrice` has **both** arguments: a bare `thrice g` is not rewritten. Placeholders:
`(g : Nat → Nat) (a : Nat) (P : Nat → Prop)`.

| Before `simp` | After `simp` |
|---|---|
| `⊢ P (thrice g a)` | `⊢ P (g (g (g a)))` |

---

## Part 2 · `inc_eq`

Statement: `inc n = n + 1`, tagged `@[simp]`. Again the right side is the body of `inc`, so R1 closes it; the
tag (R2) puts it in the simp set for Part 3. No new entries.

---

## Part 3 · `twice_twice_inc`

Statement: `twice (twice inc) n = n + 4`. With the two tagged lemmas above in the simp set, one plain `simp`
unfolds every `twice` (R3, R4) and every `inc` (R2), then closes the arithmetic (R5).

**R4 · nested calls** change the **goal**: `simp` rewrites inside its own results until no lemma matches. The
outer call `thrice (thrice g) a` matches R3 with `f := thrice g`, a partial application. The result
`thrice g (thrice g (thrice g a))` contains three full calls `thrice g t`, and each is rewritten in turn: nine
`g`s in all. Placeholders: `(g : Nat → Nat) (a : Nat) (P : Nat → Prop)`.

| Before `simp only [thrice_apply]` | After |
|---|---|
| `⊢ P (thrice (thrice g) a)` | `⊢ P (g (g (g (g (g (g (g (g (g a)))))))))` |

**R5 · `simp` closes an equation whose sides differ by numerals** **closes** the goal. It cancels common
summands with `Nat.add_right_cancel_iff : m + n = k + n ↔ m = k` and `Nat.add_left_cancel_iff :
n + m = n + k ↔ m = k` (E010, R10–R11). Placeholders: `(k : Nat)`.

| Before | After |
|---|---|
| `k : Nat ⊢ k + 2 + 2 + 2 = k + 6` | no goals |

**W1.** One plain `simp` closes `thrice addTwo n = n + 6`: R3 unfolds `thrice`, R2 unfolds each `addTwo`, R5
closes `n + 2 + 2 + 2 = n + 6`.

| Before `simp` | After `simp` |
|---|---|
| `n : Nat ⊢ thrice addTwo n = n + 6` | no goals |

**W2: the same rewriting, one lemma at a time.** `simp only [l]` uses only `l`, so each step is visible:

| Before | After `simp only [thrice_apply]` | After `simp only [addTwo_eq]` |
|---|---|---|
| `⊢ P (thrice addTwo n)` | `⊢ P (addTwo (addTwo (addTwo n)))` | `⊢ P (n + 2 + 2 + 2)` |

**W3: `simp [-l]`** removes the tagged lemma `l` for one call. `simp [-addTwo_eq, addTwo]` unfolds the
definition directly instead, and reaches the same goal:

| Before | After `simp [-addTwo_eq, addTwo]` |
|---|---|
| `⊢ P (addTwo n)` | `⊢ P (n + 2)` |

**W4: `attribute [simp] l`** tags a theorem that was declared without `@[simp]`. After
`theorem triple_eq (n : Nat) : triple n = 3 * n := rfl` and `attribute [simp] triple_eq`, plain `simp` unfolds
`triple`:

| Before `simp` | After `simp` |
|---|---|
| `⊢ P (triple k)` | `⊢ P (3 * k)` |

---

## Traps

- The tag acts only **after** the declaration. Inside the proof of `twice_apply` the lemma is not yet available,
  and plain `simp` on `twice f x = f (f x)` fails with `simp made no progress` (it does not unfold your own
  `def`). Prove the tagged lemmas with `rfl` (R1).
- A `sorry` proof still tags the lemma: in the stub, `simp` would already "use" `twice_apply`, but the checker
  rejects a spec theorem that rests on `sorry`. All three proofs are needed.
- A simp lemma matches only full applications. `twice_apply` does not rewrite a bare `twice inc`; it rewrites
  `twice inc t` once the outer call has produced it (R3, R4).
- Tag lemmas whose right side is simpler. Tagging the reverse direction, `n + 1 = inc n`, together with `inc_eq`
  makes `simp` loop: it fails with `maximum recursion depth has been reached`. Tagging a general library
  lemma (`attribute [simp] Nat.mul_comm`) changes every later `simp` call in the file and can make goals
  harder to read.
- If `simp` already closed the goal, a following `exact h` fails with "no goals".

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `d a = (body of d)` | `rfl` or `by rfl` | R1 |
| make plain `simp` use your lemma | `@[simp] theorem l … := proof` | R2 |
| unfold a function-taking `def` | `@[simp] theorem f_apply (f) (x) : d f x = … := rfl` | R3 |
| unfold nested / partial calls | plain `simp` (repeats inside its results) | R4 |
| sides differ only by numerals | `simp` | R5 |
| watch one lemma at a time | `simp only [l]` | W2 |
| drop a tagged lemma for one call | `simp [-l]` | W3 |
| tag an existing theorem | `attribute [simp] l` | W4 |
| see which lemmas `simp` used | `simp?` | |
| see the state | infoview | |
