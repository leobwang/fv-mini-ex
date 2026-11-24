# M029 · GCD by Euclid: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` with `if … then … else`, `Nat`, `intro`,
`exact`, `apply`, `have`, anonymous constructors, `∧` and `↔`.
**New here:** core Lean only (no Mathlib): a recursive `def` whose termination is proved by hand
(`termination_by` / `decreasing_by`, *well-founded recursion*); `fun_induction` (induction that
follows a function's own recursion); divisibility `a ∣ b` on `Nat` and the lemmas `Nat.dvd_refl`,
`Nat.dvd_zero`, `Nat.dvd_mod_iff`.

The problem in one paragraph. `euclid a b` is Euclid's algorithm: `euclid a 0 = a` and
`euclid a b = euclid b (a % b)` for `b ≠ 0`. You prove that its result `g` is a *greatest common
divisor* in the divisibility sense: `g ∣ a` and `g ∣ b` (`euclid_dvd`), and every common divisor `d`
of `a` and `b` divides `g` (`dvd_euclid`). Both proofs follow `euclid`'s recursion with
`fun_induction`; the only arithmetic fact is: when `k ∣ n`, `k ∣ m % n` and `k ∣ m` are equivalent.

## How to read an entry

Each entry is one tactic or one lemma used with `exact`/`apply`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
  `∅` means the goal is closed.
- `P`, `Q` are "the rest of your goal" (`P Q : Nat → Prop`, or `P : Prop`). The step changes only the
  part inside `P (…)`. A hypothesis `h1`, `hp`, `hQ` in an example is there only to finish it.
- Placeholders are written as Lean binders: `(a b : Nat)`, `(A B C : Prop)`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- The guide's recursive function is `dbl a b = a * 2 ^ b`:
  `if b = 0 then a else dbl (a + a) (b - 1)`, with `termination_by b`. Same `if b = 0` shape as
  `euclid`, different function.

## Reading the definition

```lean
def euclid (a b : Nat) : Nat := if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)
```

- The recursive call is on `(b, a % b)`, not on a constructor's argument, so Lean cannot check
  termination by structural recursion. `termination_by b` names a measure that must shrink at every
  call; `decreasing_by` proves it. Its goal is `a % b < b` with `¬b = 0` in context, and
  `Nat.mod_lt : ∀ (x : Nat) {y : Nat}, 0 < y → x % y < y` closes it (`omega` gives `0 < b`).
- Such a definition is compiled by *well-founded recursion* and marked irreducible: `#eval euclid 12 8`
  prints `4`, but `rfl` and `decide` cannot compute `euclid 12 8 = 4` inside a proof, and
  `simp [euclid]` loops (the unfolding equation `euclid a b = if b = 0 then a else euclid b (a % b)`
  can be applied again to its own right side). Reason about it with `fun_induction` instead.

## Reading the goals

| You see | It means |
|---|---|
| `a ∣ b` | `Dvd.dvd a b`, "`a` divides `b`": `∃ c, b = a * c`. The divides sign is U+2223, not the bar (Traps) |
| `a % b` | remainder of `a` divided by `b`; `a % 0 = a` on `Nat` |
| `h : ¬b = 0` | the `else` condition of the `if` (R1); `¬b = 0` is `b ≠ 0` |
| `ih : euclid b (a % b) ∣ b ∧ …` | the claim for the recursive call `euclid b (a % b)` (R1) |
| `ih : X → Y → Z` | an IH that first asks for your hypotheses about the recursive call's arguments (R8) |
| `hb : d ∣ 0` | your hypothesis `hb : d ∣ b` in the `b = 0` case: `b` was replaced by `0` (R8) |
| `case case1`, `case case2` | goal tags made by `fun_induction`: the `then` branch and the `else` branch |
| `case case2.ha`, `case case2.hb` | after `apply ih` (R9): the goals for `ih`'s premises, tagged by the hypothesis names `ha`, `hb` |
| `a✝`, `h✝`, `ih1✝` | inaccessible names: `fun_induction` without `with` arms. Name them (`case2 a b h ih`, R1) to use them |
| `h.1`, `h.2` | the two halves of `h : A ∧ B` (R3) |
| `(Nat.dvd_mod_iff hk).mp` | the left-to-right direction of the `↔` the lemma gives (R6) |

---

## Part 1 · `euclid_dvd`

Statement: `euclid a b ∣ a ∧ euclid a b ∣ b`, for all `a b : Nat`.

**R1 · `fun_induction dbl a b with | case1 a => … | case2 a b h ih => …`** changes the **goal list**:
one goal per branch of the function's `if`, with the call already replaced by that branch's result.
In `case1` the variable `b` is replaced by `0`; `case2` gets the condition `h : ¬b = 0` and the
induction hypothesis `ih` for the recursive call. An arm names, in order: the variables, the
condition, the IH. Placeholders: `(a b : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (dbl a b)` | `a : Nat ⊢ P a`, `h : ¬b = 0, ih : P (dbl (a + a) (b - 1)) ⊢ P (dbl (a + a) (b - 1))` |

For `euclid a b` this gives the two goals
`⊢ a ∣ a ∧ a ∣ 0` (case1) and, with `ih : euclid b (a % b) ∣ b ∧ euclid b (a % b) ∣ a % b`,
`⊢ euclid b (a % b) ∣ a ∧ euclid b (a % b) ∣ b` (case2): the call `euclid a b` is already replaced
by `euclid b (a % b)`, and the IH is the same claim for that call.

**R2 · `exact ⟨p, q⟩`** **closes** `A ∧ B` from `p : A` and `q : B` (the anonymous constructor for
`And.intro`). Placeholders: `(A B : Prop) (p : A) (q : B)`.

| Before | After |
|---|---|
| `p : A, q : B ⊢ A ∧ B` | `∅` |

**R3 · `h.1`, `h.2`** change the **context** when named with `have`: `h.1 : A`, `h.2 : B` for
`h : A ∧ B`. Usually you write them inline as arguments. Placeholders: `(A B : Prop) (h : A ∧ B)`.

| Before | After `have hb := h.2` |
|---|---|
| `h : A ∧ B ⊢ P` | `hb : B ⊢ P` |

**R4 · `Nat.dvd_refl`** **closes** `a ∣ a`. Statement: `Nat.dvd_refl : ∀ (a : Nat), a ∣ a`.

| Before | After `exact Nat.dvd_refl a` |
|---|---|
| `⊢ a ∣ a` | `∅` |

**R5 · `Nat.dvd_zero`** **closes** `a ∣ 0`. Statement: `Nat.dvd_zero : ∀ (a : Nat), a ∣ 0`
(`0 = a * 0`).

| Before | After `exact Nat.dvd_zero a` |
|---|---|
| `⊢ a ∣ 0` | `∅` |

**R6 · `(Nat.dvd_mod_iff hk).mp`** changes the **goal** (with `apply`) or proves `k ∣ m` outright
(with `exact … h`). Statement: `Nat.dvd_mod_iff : ∀ {k m n : Nat}, k ∣ n → (k ∣ m % n ↔ k ∣ m)`.
All three numbers are implicit: you pass only `hk : k ∣ n`, and Lean reads `m` off the goal or the
argument. Why it holds: `m = n * (m / n) + m % n` and `k ∣ n`. Placeholders: `(k m n : Nat)`,
`(hk : k ∣ n)`.

| Before | After `apply (Nat.dvd_mod_iff hk).mp` |
|---|---|
| `hk : k ∣ n, h : k ∣ m % n ⊢ k ∣ m` | `hk : k ∣ n, h : k ∣ m % n ⊢ k ∣ m % n` |

In case2 the IH gives both `euclid b (a % b) ∣ b` (the `hk`) and `euclid b (a % b) ∣ a % b`
(the `h`), and the goal's first half asks for `euclid b (a % b) ∣ a`.

---

## Part 2 · `dvd_euclid`

Statement: for `ha : d ∣ a` and `hb : d ∣ b`, `d ∣ euclid a b`.

**R8 · `fun_induction` with hypotheses about `a`, `b`** changes the **goal list** as in R1, and also the
**context**: every hypothesis that mentions the induction variables (here `ha`, `hb`) is moved into
each case, rewritten for that case, and listed after `ih`. The IH then needs those hypotheses for the
recursive call's arguments. No `revert` needed. Placeholders: `(Q P : Nat → Prop) (hq : Q a)`.

| Before | After |
|---|---|
| `hq : Q a ⊢ P (dbl a b)` | `hq : Q a ⊢ P a`, `ih : Q (a + a) → P (dbl (a + a) (b - 1)), hq : Q a ⊢ P (dbl (a + a) (b - 1))` |

For `euclid` you get `ha : d ∣ a, hb : d ∣ 0 ⊢ d ∣ a` (case1) and, in case2,
`ih : d ∣ b → d ∣ a % b → d ∣ euclid b (a % b)` with goal `d ∣ euclid b (a % b)`.

**R9 · `apply ih`** for `ih : A → B → C` changes the **goal list**: goal `C` becomes the goals `A`,
`B` (one per premise). In one line: `exact ih pa pb`. Placeholders: `(A B C : Prop)`.

| Before | After |
|---|---|
| `ih : A → B → C ⊢ C` | `ih : A → B → C ⊢ A`, `ih : A → B → C ⊢ B` |

**R7 · `(Nat.dvd_mod_iff hk).mpr`** changes the **goal**: `k ∣ m % n` becomes `k ∣ m`. `.mpr` is the
right-to-left direction of R6's `↔`. Placeholders as in R6.

| Before | After `apply (Nat.dvd_mod_iff hk).mpr` |
|---|---|
| `hk : k ∣ n, h : k ∣ m ⊢ k ∣ m % n` | `hk : k ∣ n, h : k ∣ m ⊢ k ∣ m` |

In case2 the second premise of `ih` is `d ∣ a % b`; `hb : d ∣ b` plays `hk`, `ha : d ∣ a` plays `h`.

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `a ≤ dbl a b` by R1: case1 `Nat.le_refl a`; case2 chains `a ≤ a + a` (`Nat.le_add_right`) with
`ih : a + a ≤ dbl (a + a) (b - 1)` (`Nat.le_trans`).

**W2.** `hd : d ∣ a ⊢ d ∣ dbl a b` by R8: case2 has `ih : d ∣ a + a → d ∣ dbl (a + a) (b - 1)`;
`apply ih` (R9) leaves `d ∣ a + a`, closed by `Nat.dvd_add hd hd`
(`Nat.dvd_add : a ∣ b → a ∣ c → a ∣ b + c`).

**W3.** On plain numbers: `⟨(Nat.dvd_mod_iff hk).mpr hm, hk⟩ : k ∣ m % n ∧ k ∣ n` (R2 with R7), and
`(Nat.dvd_mod_iff h.1).mp h.2 : k ∣ m` from `h : k ∣ n ∧ k ∣ m % n` (R3 with R6).

---

## Traps

- `induction b` gives an IH about `euclid a n` for `b = n + 1`, but `euclid` recurses on `a % b`:
  the IH is useless. Use `fun_induction euclid a b`.
- `rfl`, `decide` and `simp [euclid]` do not evaluate `euclid` (well-founded recursion; `simp` loops on
  the unfolding equation). `#eval` does, which is fine for testing, not for proofs.
- `Nat.dvd_mod_iff.mp` is an unknown name: `.mp` belongs to the `↔`, which exists only once the
  argument is given. Write `(Nat.dvd_mod_iff hk).mp`.
- `hk` is the divisibility of the *modulus* `n` (the right operand of `%`), not of `m`. In case2 of
  `euclid_dvd` it is `ih.1`; in `dvd_euclid` it is `hb`.
- Plain `fun_induction euclid a b` (no `with`) leaves the new variables inaccessible (`a✝`, `ih1✝`), so
  `Nat.dvd_refl a` or `ih.1` fails. Use the `with | case1 a => … | case2 a b h ih => …` form (R1).
- Do not `intro`/`revert` `ha hb` before `fun_induction`: it already moves them into each case (R8).
- `∣` (U+2223) is typed `\|` or `\mid` in the editor. The keyboard bar `|` is parsed as something else
  and gives an error.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| induct along `euclid`'s recursion | `fun_induction euclid a b with \| case1 a => … \| case2 a b h ih => …` | R1, R8 |
| build `A ∧ B` | `exact ⟨p, q⟩` | R2 |
| halves of `h : A ∧ B` | `h.1`, `h.2` | R3 |
| `a ∣ a` | `Nat.dvd_refl a` | R4 |
| `a ∣ 0` | `Nat.dvd_zero a` | R5 |
| `k ∣ m` from `k ∣ m % n` (given `hk : k ∣ n`) | `(Nat.dvd_mod_iff hk).mp h` | R6 |
| `k ∣ m % n` from `k ∣ m` (given `hk : k ∣ n`) | `(Nat.dvd_mod_iff hk).mpr h` | R7 |
| use an IH that needs premises | `exact ih p q` or `apply ih` | R9 |
| test a value | `#eval euclid 12 8` | |
| see the state | infoview | |
