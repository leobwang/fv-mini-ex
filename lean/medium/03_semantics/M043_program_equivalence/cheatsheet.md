# M043 · Program equivalence in IMP: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rfl`, `·` focusing, inductive types,
pattern-matching definitions. **New here:** inductive *relations* (a `Prop`-valued inductive whose
constructors are inference rules), inverting a derivation with `cases`, building one from rules, and
`↔` goals and hypotheses. No Mathlib. H021 uses the same IMP big-step semantics.

## How to read an entry

Each entry is one tactic or one proof move. It says what changes (**goal**, **context**, or **goal
list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Nat → Prop` or `P : Prop`). The step changes only the part
  inside `P (…)`.
- `{α : Type}` is any type; `Q R : α → α → Prop` are arbitrary two-place predicates.
- Inversion needs a concrete inductive relation, so R3–R6, R9, R10 use the guide's toy language, not
  IMP: `Cmd` (`nop`, `inc`, `seq c d`, `loop t c`), guards `Test` (`yes`, `no`, `below k`) evaluated by
  `test n t : Bool`, and `Run c n k : Prop` ("from counter `n`, `c` stops at counter `k`") with rules
  `nop`, `inc`, `seq`, `loopF`, `loopT`. They mirror IMP's `skip`, `assign`, `seq`, `whileF`, `whileT`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The objects

- `State := Nat → Int`: variable number ↦ value. `update s x v` is `s` with variable `x` set to `v`.
- `aeval s a : Int`, `beval s b : Bool`: values of arithmetic / boolean expressions in state `s`.
- `BigStep c s s' : Prop`: a *derivation* (proof tree) built from the seven rules `skip`, `assign`, `seq`,
  `iteT`, `iteF`, `whileF`, `whileT`. A proof of `BigStep c s s'` is such a tree; `cases` on it looks at
  its last rule.
- `Equiv c1 c2 := ∀ s s', BigStep c1 s s' ↔ BigStep c2 s s'`: same final states from every start state
  (nonterminating runs have no derivation, so they are "equal" too).

## Reading the goals

| You see | It means |
|---|---|
| `c1.seq c2` | `Com.seq c1 c2`, i.e. `c1; c2`. Lean prints `Com.seq x y` as `x.seq y` because `x : Com` |
| `Com.skip.seq c` | `Com.seq Com.skip c`, i.e. `skip; c` |
| `Com.while b c`, `Com.ite b c1 c2` | `while b do c`, `if b then c1 else c2` (first argument is a `BExp`, so no dot form) |
| `BExp.ff`, `Cmd.nop` | the constructor written `.ff`, `.nop` in the source |
| `s'✝`, `m✝` | an *inaccessible* name: a variable Lean introduced (the middle state of a `seq` or `whileT`); you cannot type it |
| `a✝`, `a✝¹` | an unnamed premise (you wrote `_` in the `cases` pattern) |
| `∀ (a b : α), Q a b` | `∀ a b, Q a b` with the binder types shown |
| `case mp`, `case mpr` | the `→` and `←` goals made by `constructor` on `↔` |
| `case mp.seq`, `case mp.whileT` | inside `mp`, the case for rule `seq` / `whileT` |

---

## Part 1 · `skip_seq`

Statement: `Equiv (.seq .skip c) c`: `skip; c` behaves like `c`. Unfold `Equiv` with two `intro`s, split the
`↔`, invert in one direction and build in the other.

**R1 · `intro a b` on a defined name** changes the **context** and the **goal**. `intro` unfolds a
definition by itself when its body starts with `∀`, so `intro s s'` on `⊢ Equiv c1 c2` gives
`⊢ BigStep c1 s s' ↔ BigStep c2 s s'`. Placeholders: `{α : Type} (Q : α → α → Prop)` and
`def AllPairs Q := ∀ a b, Q a b`.

| Before | After |
|---|---|
| `⊢ AllPairs Q` | `a b : α ⊢ Q a b` |

**R2 · `constructor` on `↔`** changes the **goal list**: `A ↔ B` becomes the two implications, tagged
`mp` and `mpr`. Start each with `intro h` (`· intro h`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R3 · `cases h with | seq h1 h2 => …`** changes the **context**: a derivation `h` whose conclusion fits
only one rule is replaced by that rule's premises, named in order. The rule's implicit arguments that
are not fixed by the goal (the middle counter `m`) appear as inaccessible `m✝`; write
`| @seq _ _ _ m _ h1 h2` to name them. In the guide `?_` keeps the case open; in a proof, write its
tactics after `=>`, which must close it. Apply `cases` again to a premise to invert a nested command
(`(c1; c2); c3`). Placeholders: `(c d : Cmd) (n k : Nat)`.

| Before | After |
|---|---|
| `h : Run (c.seq d) n k ⊢ P n k` | `m✝ : Nat, h1 : Run c n m✝, h2 : Run d m✝ k ⊢ P n k` |

**R4 · `cases h` on a rule without premises** changes the **context** and the **goal**: `Run.nop`
concludes `Run .nop n n`, so `h : Run .nop n k` forces `k = n`; `cases` deletes `h` and replaces `k` by
`n` everywhere. For IMP: `cases hs` with `hs : BigStep Com.skip s s'✝` replaces `s'✝` by `s`.
Placeholders: `(n k : Nat)`.

| Before | After |
|---|---|
| `h : Run Cmd.nop n k ⊢ P n k` | `⊢ P n n` |

**R6 · `exact .seq h1 h2`** **closes** the goal by applying a rule. `.seq` means `Run.seq` (for IMP,
`BigStep.seq`): Lean takes the namespace from the goal's head. The rule's implicit arguments are found
by matching its conclusion with the goal and its premises with `h1`, `h2`, so the premises must come in
the rule's order. Rules nest (`.seq h1 (.seq h2 h3)`), and a premise-free rule is just `.skip`.
Placeholders: `(c d : Cmd) (n m k : Nat)`.

| Before | After |
|---|---|
| `h1 : Run c n m, h2 : Run d m k ⊢ Run (c.seq d) n k` | no goals |

---

## Part 2 · `seq_assoc`

Statement: `Equiv (.seq (.seq c1 c2) c3) (.seq c1 (.seq c2 c3))`: `;` is associative. No new entries:
R1, R2, then in each direction R3 twice (the outer `seq`, then the inner one held by a premise) and one
nested R6. The two middle states arrive as two inaccessible names (`s'✝`, `s'✝¹`); `exact` never needs
to name them.

---

## Part 3 · `while_unroll`

Statement: `Equiv (.while b c) (.ite b (.seq c (.while b c)) .skip)`: a loop equals one guarded
iteration followed by the loop.

**R5 · `cases h with | loopF hb => … | loopT hb hc hw => …`** changes the **goal list**: when several
rules can conclude `h`, there is one goal per rule, each with that rule's premises. In the false-guard
rule the end state equals the start state, so `k` becomes `n` in that goal. Write `_` for a premise you
do not use. For IMP: `whileF`/`whileT` for a `while`, `iteT`/`iteF` for an `ite`. Placeholders:
`(t : Test) (c : Cmd) (n k : Nat)`.

| Before | After |
|---|---|
| `h : Run (Cmd.loop t c) n k ⊢ P n k` | `hb : test n t = false ⊢ P n n`, `m✝ : Nat, hb : test n t = true, hc : Run c n m✝, hw : Run (Cmd.loop t c) m✝ k ⊢ P n k` |

Then rebuild with R6: in each case the premises you got are exactly the premises of the matching rule
on the other side (a guard premise `hb`, a body run, a loop run), plus `.skip` or `.seq` to wrap them.
In the `←` direction the `ite` case leaves a `seq` or a `skip` premise: invert it with R3 or R4 first.

---

## Part 4 · `seq_congr`

Statement: from `h1 : Equiv c1 c1'` and `h2 : Equiv c2 c2'`, get `Equiv (.seq c1 c2) (.seq c1' c2')`:
`;` respects `≈`. `h1 : Equiv c1 c1'` is a function: `h1 s s' : BigStep c1 s s' ↔ BigStep c1' s s'`.

**R7 · `Iff.mp`** changes the **goal** (with `apply`) or builds a term (with `exact`). `Iff.mp : (A ↔ B) →
A → B`, written `(h a b).mp`; `(h _ _).mp` lets Lean find `a b` from what it is applied to. In this
problem it goes inside R6: `.seq ((h1 _ _).mp ha) …`. Placeholders: `{α : Type} (Q R : α → α → Prop)
(a b : α) (h : ∀ x y, Q x y ↔ R x y)`.

| Before | After `apply (h _ _).mp` |
|---|---|
| `⊢ R a b` | `⊢ Q a b` |

**R8 · `Iff.mpr`** is the other direction: `Iff.mpr : (A ↔ B) → B → A`, written `(h a b).mpr`. Same
placeholders.

| Before | After `apply (h _ _).mpr` |
|---|---|
| `⊢ Q a b` | `⊢ R a b` |

---

## Part 5 · `while_false`

Statement: `Equiv (.while .ff c) .skip`: a loop with guard `false` does nothing.

**R9 · `simp [f] at hb`** **closes** the goal when `hb` simplifies to `False`. In the `whileT` case
`hb : beval s BExp.ff = true`; `simp [beval] at hb` unfolds `beval` on `.ff` to `false = true`, which is
`False`, and a goal with a `False` hypothesis is done. Placeholders: `(n : Nat) (P : Prop)`.

| Before | After |
|---|---|
| `hb : test n Test.no = true ⊢ P` | no goals |

**R10 · `rfl` for a computed premise** **closes** `test n .no = false`: the left side reduces to `false`
by the defining equation of `test`. As a rule premise: `.loopF rfl`; for IMP, `.whileF rfl` proves
`BigStep (.while .ff c) s s` because `beval s .ff = false` holds by `rfl`.

The `←` direction is R4 (invert `skip`, so `s'` becomes `s`), then R6 with R10.

### Worked combinations (W1–W3, on `Cmd`/`Run`)

**W1.** Concrete runs are nested rules: `Run (.seq .inc .inc) 0 2 := .seq .inc .inc` and
`Run (.loop .no .inc) 5 5 := .loopF rfl` (R6, R10).

**W2: `c; nop` runs like `c`.** R1 (`intro n k`), R2, then R3 → R4 → `exact` one way and R6 the other.
After R1 and R2 the goals are:

```lean-goal
⊢ Run (c.seq Cmd.nop) n k ↔ Run c n k
⊢ Run (c.seq Cmd.nop) n k → Run c n k
⊢ Run c n k → Run (c.seq Cmd.nop) n k
```

**W3: a loop whose guard is false at 0.** From `h : Run (.loop (.below 0) c) n k` prove `k = n`: R5,
then `rfl` in the `loopF` case (R5 already replaced `k` by `n`, so the goal is `n = n`) and R9 in the `loopT`
case, where `hb : test n (.below 0) = true` simplifies to `n < 0`, which `simp` knows is `False`.

```lean-goal
⊢ k = n
```

---

## Traps

- `cases h with | rule … => tacs` must close each case; an alternative that leaves a goal is an
  "unsolved goals" error. Every rule that can conclude `h` needs its own `| rule … =>` line; rules
  that cannot (wrong command) are dropped by Lean automatically.
- The names after `| seq` bind the rule's **explicit** premises only, in order. The middle state is
  implicit and stays `s'✝` unless you use `| @seq …`.
- `intro h` first: `cases` inverts a hypothesis, so after R2 the goal `A → B` needs `intro h` before
  `cases h`.
- `simp at hb` without `[beval]` does not unfold `beval`; name the function.
- `exact .whileF hb` needs `hb : beval s b = false` for the **same** `s` as the goal's start state; after
  R4 substitutes, check the infoview to see which name survived.
- `t1 ; t2` runs `t2` on the first goal only; use `·` for each of the `mp` / `mpr` goals.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| open `Equiv c1 c2` | `intro s s'` | R1 |
| split `↔` | `constructor`, then `· intro h` twice | R2 |
| invert a `seq` derivation | `cases h with \| seq h1 h2 => …` | R3 |
| invert a `skip` derivation (states become equal) | `cases h` | R4 |
| invert `while` / `ite` (two rules) | `cases h with \| whileF hb => … \| whileT hb hc hw => …` | R5 |
| build a derivation | `exact .seq h1 h2`, `.iteT hb (.seq hc hw)`, `.skip` | R6 |
| use `h : Equiv c c'` forward / backward | `(h _ _).mp hd` / `(h _ _).mpr hd` | R7, R8 |
| impossible case `hb : beval s .ff = true` | `simp [beval] at hb` | R9 |
| premise `beval s .ff = false` | `rfl` | R10 |
| name a middle state | `\| @seq _ _ _ s₁ _ h1 h2 =>` | R3 |
| see the state | infoview | |
