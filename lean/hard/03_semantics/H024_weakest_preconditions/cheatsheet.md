# H024 · Hoare logic: weakest preconditions and relative completeness: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `constructor`, `cases`, `induction`,
`funext`, anonymous constructors `⟨a, b⟩`, projections `h.1`/`h.2`, `fun x => …`, Prop-valued `def`s.
**New here:** a big-step semantics as an inductive relation (`BigStep`), Hoare logic as an inductive
relation (`Derivable`), the weakest liberal precondition `wp`, and the term-level way of building
derivations with constructor dot notation (`.conseq`, `.while`, `.seq h1 h2`). Core Lean only, no Mathlib.

The problem's objects, in words:

- `State := Nat → Int`: variable `x : Nat` holds the integer `s x`. `Assn := State → Prop` is an
  assertion, a predicate on states.
- `BigStep c s s'`: running command `c` from state `s` can terminate in state `s'`. Its rules are
  `skip`, `assign`, `seq`, `iteT`/`iteF` (the test `b` was true / false), `whileF` (the loop exits at once)
  and `whileT` (one body run, then the rest of the loop).
- `Valid P c Q` (the meaning of `{P} c {Q}`): every terminating run from a `P`-state ends in a `Q`-state.
- `Derivable P c Q`: `{P} c {Q}` is provable with the six Hoare rules `skip`, `assign`, `seq`, `ite`,
  `while` (invariant `I`), `conseq` (rule of consequence).
- `wp c Q s := ∀ s', BigStep c s s' → Q s'`: from `s`, every terminating run of `c` ends in `Q`.

The guide teaches on a toy language instead: `Op` (`inc`, `andThen a b`, `«while» a` = repeat `a` while
the counter is below 10) on one counter `n : Nat`, its run relation `Run`, a predicate
`Up Q n := ∀ m, n ≤ m → Q m`, and a toy proof system `Ok` with a rule of consequence `weaken` and a loop
rule `loop`.

## How to read an entry

Each entry is one tactic or one term pattern. It says what changes (**goal**, **context**, or
**goal list**), lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal". The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.
- "no goals" means the step closed the goal.

## Reading the goals

| You see | It means |
|---|---|
| `c1.seq c2` | `Com.seq c1 c2`, the command `c1; c2` (Lean prints `f x y` as `x.f y` when `x` has type `Com`) |
| `Com.while b c` | `while b do c`; printed with the full name because its first argument `b` is a `BExp` |
| `Com.skip` | `.skip`, written with its type name |
| `Com.assign x a`, `Com.ite b c1 c2` | `x := a` and `if b then c1 else c2`; full names for the same reason as `Com.while` |
| `wp c Q s` | `wp c Q` is an assertion; applied to `s` it is the Prop `∀ s', BigStep c s s' → Q s'` |
| `beval s b = true` | the test `b` is true in `s` (`Bool`, compared with `= true`) |
| `fun s => A s ∧ B s` | the assertion "A and B" |
| `s'✝` | an inaccessible name made by `cases`: you cannot type it, write `_` where it is needed |
| `a✝`, `a✝¹`, `a✝²` | unnamed hypotheses made by `cases` / `induction` without `with` |
| `c1_ih✝`, `c2_ih✝`, `c_ih✝` | the IHs `induction` makes when you do not name them (name them in `\| seq c1 c2 ih1 ih2 =>`) |
| `case refine_1`, `case refine_2` | the goals left by the first and second `?_` of a `refine` |
| `case mp`, `case mpr` | the `→` and `←` halves after `constructor` on `↔` |
| `case mpr.seq`, `case mpr.whileT` | the `seq` / `whileT` rule's case inside the `mpr` half |
| `case while` | the `«while»` induction case (write `«while»` in `\| «while» b c ih =>`) |
| `ih : ∀ (Q : Assn), Derivable (wp c Q) c Q` | an IH quantified over `Q` (from `generalizing Q`) |
| `propext` | the axiom `(a ↔ b) → a = b`: equivalent propositions are equal |

---

## Part 1 · `wp_while_body` (milestone 1)

Statement: if `wp (.while b c) Q` holds in `s` and the test is true there, then after one run of the body,
`wp (.while b c) Q` holds again: `wp c (wp (.while b c) Q) s`. This is one step of unrolling the loop.

**R1 · `intro` through a definition** changes the **context**. A goal that is a definition whose body is a
`∀` (such as `Up Q n`, or `wp c Q s`) is unfolded by `intro` itself; you do not need `unfold`.
Placeholders: `(Q : Nat → Prop) (n : Nat)`. In the problem, the goal `wp c (wp (.while b c) Q) s` takes four
names: a state, a run of `c`, a state, a run of the loop. In a term, `fun m hm => …` against the expected
type `Up Q n` unfolds it the same way (the `seq` case of Part 6 uses `fun s h s1 h1 s2 h2 => …`).

| Before | After `intro m hm` |
|---|---|
| `⊢ Up Q n` | `m : Nat, hm : n ≤ m ⊢ Q m` |

**R2 · applying a hypothesis that is such a definition** closes the **goal**. `h : Up Q n` is a function:
`h m hm : Q m`. Likewise `h : wp c Q s` gives `h s' run : Q s'`, and `h : Valid P c Q` gives
`h s s' hP run : Q s'`. Placeholders: `(Q : Nat → Prop) (n m : Nat)`.

| Before | After `exact h m hm` |
|---|---|
| `h : Up Q n, hm : n ≤ m ⊢ Q m` | no goals |

**R3 · `.ctor h₁ h₂`: build a run with a rule** closes the **goal**. `.andThen h₁ h₂` means
`Run.andThen h₁ h₂`: the type name comes from the expected type, the implicit arguments `{a b n m k}` from
unification. In the problem: `.whileT hb h1 h2 : BigStep (Com.while b c) s s''` from
`hb : beval s b = true`, a body run and a run of the rest. Placeholders: `(a b : Op) (n m k : Nat)`.

| Before | After `exact .andThen h₁ h₂` |
|---|---|
| `h₁ : Run a n m, h₂ : Run b m k ⊢ Run (a.andThen b) n k` | no goals |

The milestone needs R1, then `h.1` (R2) applied to a run built with `.whileT h.2 …` (R3).

## Part 2 · `wp_while_exit` (milestone 2)

Statement: if `wp (.while b c) Q` holds in `s` and the test is false there, then `Q s`: the loop stops at
once, so `s` is a final state. Apply `h.1` (R2) to `s` and the run `.whileF h.2` (R3).

## Part 3 · `derivable_wp_while` (milestone 3)

Statement: given `ih : ∀ R, Derivable (wp c R) c R` (the body's case of `wp_derivable`), derive
`{wp (.while b c) Q} while b do c {Q}`. The invariant is `I := wp (.while b c) Q` itself; milestone 1 says
`I` is preserved by the body when the test is true, milestone 2 says `I` and a false test give `Q`.

**R4 · `.weaken pre d post`: rule of consequence** closes the **goal**. From `d : Ok P a Q`,
`pre : ∀ n, P' n → P n` and `post : ∀ n, Q n → Q' n` it proves `Ok P' a Q'`. The problem's rule is
`Derivable.conseq` with the same argument order. `fun _ h => h` proves `∀ n, Q n → Q n` (nothing to change).
Placeholders: `(P' Q : Nat → Prop) (pre : ∀ n, P' n → Q (n + 1))`.

| Before | After `exact .weaken pre .inc (fun _ h => h)` |
|---|---|
| `⊢ Ok P' Op.inc Q` | no goals |

**R5 · a lemma IS an implication between predicates** closes the **goal** (used as an argument). A lemma
`lt_succ_of_le' (k n : Nat) (h : n ≤ k) : n < k + 1`, given only `k`, has type
`∀ n, n ≤ k → n < k + 1`, which is exactly a `pre` for R4. In the problem, `wp_while_body b c Q` and
`wp_while_exit b c Q` are used this way. Placeholders: `(k : Nat) (Q : Nat → Prop)`.

| Before | After `exact .weaken (lt_succ_of_le' k) d (fun _ h => h)` |
|---|---|
| `d : Ok (fun n => n < k + 1) Op.inc Q ⊢ Ok (fun n => n ≤ k) Op.inc Q` | no goals |

**R6 · a rule's conclusion has a fixed shape** changes the **goal**. `.loop d` proves only
`Ok I (.while a) (fun n => I n ∧ 10 ≤ n)`; to reach a postcondition `Q`, wrap it in R4. The problem's
`Derivable.while` likewise concludes `Derivable I (Com.while b c) (fun s => I s ∧ beval s b = false)`, and
its premise has precondition `fun s => I s ∧ beval s b = true`. Placeholders:
`(I Q : Nat → Prop) (a : Op) (d : Ok (fun n => I n ∧ n < 10) a I)`.

| Before | After `refine .weaken (fun _ h => h) (.loop d) ?_` |
|---|---|
| `d : Ok (fun n => I n ∧ n < 10) a I ⊢ Ok I a.while Q` | `⊢ ∀ (n : Nat), I n ∧ 10 ≤ n → Q n` |

**W3: a loop with an invariant.** `Ok (fun n => n ≤ 10) (.while .inc) (fun n => n = 10)` with invariant
`n ≤ 10`: R4 around R6 around R4 around `.inc`, the two arithmetic side goals left as `?_` (R14):

```lean-goal
⊢ Ok (fun n => n ≤ 10) Op.inc.while fun n => n = 10
⊢ ∀ (n : Nat), n ≤ 10 ∧ n < 10 → n + 1 ≤ 10
⊢ ∀ (n : Nat), n ≤ 10 ∧ 10 ≤ n → n = 10
```

---

## Part 4 · `wp_seq`

Statement: `wp (.seq c1 c2) Q = wp c1 (wp c2 Q)`, an equality of assertions (functions `State → Prop`).

**R7 · `funext x`** changes the **goal and the context**: two functions are equal when they agree on every
input. Placeholders: `{α : Type} (f g : α → Prop)`. In the problem the goal becomes
`wp (c1.seq c2) Q s = wp c1 (wp c2 Q) s`, an equality of Props.

| Before | After |
|---|---|
| `⊢ f = g` | `x : α ⊢ f x = g x` |

**R8 · `apply propext`** changes the **goal**: an equality of propositions becomes `↔`. `propext` is the
axiom `(a ↔ b) → a = b` (one of the three the checker allows). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A = B` | `⊢ A ↔ B` |

**R9 · `constructor` on `↔`** changes the **goal list**: the `→` half (case `mp`) and the `←` half (case
`mpr`). Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `⊢ A → B`, `⊢ B → A` |

**R10 · `cases h` on a run: one fitting rule** changes the **context**. `h : Run (.andThen a b) n k` can
only come from `Run.andThen`, so `cases` gives one goal, with `h` replaced by that rule's premises and its
hidden middle counter `m✝`. With `cases h with | andThen h₁ h₂ => tac` the premises are named `h₁`, `h₂`;
the middle counter stays `m✝`, so write `_` for it. In the problem: `cases hc with | seq h1 h2 => …` on
`hc : BigStep (c1.seq c2) s s''`, middle state `s'✝`. Placeholders: `(a b : Op) (n k : Nat)`.

| Before | After `cases h` |
|---|---|
| `h : Run (a.andThen b) n k ⊢ P n k` | `m✝ : Nat, a✝¹ : Run a n m✝, a✝ : Run b m✝ k ⊢ P n k` |

**W2: invert, then rebuild.** From `h : Run (.andThen (.andThen a b) c) n k`, two nested `cases … with`
(R10) and one `.andThen ha (.andThen hb hc)` (R3) prove `Run (.andThen a (.andThen b c)) n k`.

## Part 5 · `wp_while`

Statement: the one-step unfolding equation
`wp (.while b c) Q = fun s => (beval s b = true → wp c (wp (.while b c) Q) s) ∧ (beval s b = false → Q s)`.
Start as in Part 4 (R7 → R8 → R9). The `→` half is a pair made from milestones 1 and 2.

**R11 · `intro ⟨h₁, h₂⟩`** changes the **context**: it introduces a conjunction and splits it at once.
Placeholders: `(A B C : Prop)`. It also works inside a longer `intro`, as in `intro s ⟨h, hb⟩ s' h'`.

| Before | After |
|---|---|
| `⊢ A ∧ B → C` | `h₁ : A, h₂ : B ⊢ C` |

**R12 · `cases h` on a run: two fitting rules** changes the **goal list**. A run of a loop came from `stop`
or from `again`, so there are two goals. In the `stop` goal the indices are unified: the final counter `k`
*is* `n`, so the goal `P n k` became `P n n`. In the problem: `cases hw with | whileF hb => … | whileT hb hc hw => …`;
in the `whileF` case the final state becomes `s`. Placeholders: `(a : Op) (n k : Nat)`.

| Before | After `cases h` |
|---|---|
| `h : Run a.while n k ⊢ P n k` | `a✝ : 10 ≤ n ⊢ P n n`, `m✝ : Nat, a✝² : n < 10, a✝¹ : Run a n m✝, a✝ : Run a.while m✝ k ⊢ P n k` |

**W1: an unfolding equation for `Up`**, `Up Q = fun n => Q n ∧ Up Q (n + 1)`, has the shape of `wp_while`.
R7, R8, R9 give:

```lean-goal
⊢ Up Q = fun n => Q n ∧ Up Q (n + 1)
⊢ Up Q n = (Q n ∧ Up Q (n + 1))
⊢ Up Q n ↔ Q n ∧ Up Q (n + 1)
⊢ Up Q n → Q n ∧ Up Q (n + 1)
⊢ Q n ∧ Up Q (n + 1) → Up Q n
```

The `→` half is a pair built with R2; the `←` half is R11 and R1, then `cases` on `hm : n ≤ m` (R12: the
rules of `≤` are `Nat.le.refl` and `Nat.le.step`).

---

## Part 6 · `wp_derivable`

Statement: `Derivable (wp c Q) c Q` for every `c` and `Q`: the weakest precondition is a derivable
precondition. By induction on `c`; the `«while»` case is milestone 3.

**R13 · `induction a generalizing n`** changes the **goal list**: one goal per constructor of `Op`, and
each IH is quantified over `n` (`a_ih✝ : ∀ (n : Nat), P a✝ n`). Without `generalizing n` the IH would be
about the single `n` of the context. In the problem, generalize `Q`: the `seq` case needs the IH of `c1`
at the postcondition `wp c2 Q`. `while` is a keyword, so its case is written `| «while» b c ih =>`.
Placeholders: `(P : Op → Nat → Prop) (a : Op) (n : Nat)`.

| Before | After |
|---|---|
| `a : Op, n : Nat ⊢ P a n` | `n : Nat ⊢ P Op.inc n`, `a✝ b✝ : Op, n : Nat ⊢ P (a✝.andThen b✝) n`, `a✝ : Op, n : Nat ⊢ P a✝.while n` |

**R14 · `refine .weaken ?_ d ?_`** changes the **goal list**: each `?_` becomes a goal. `d` fixes the inner
`P` and `Q`, so the side goals have no unknowns. In the problem: `refine .ite (.conseq ?_ (ih1 Q) (fun _ h => h)) (.conseq ?_ (ih2 Q) (fun _ h => h))`
leaves the two precondition sides. Placeholders: `(P P' Q Q' : Nat → Prop) (a : Op) (d : Ok P a Q)`.

| Before | After |
|---|---|
| `d : Ok P a Q ⊢ Ok P' a Q'` | `⊢ ∀ (n : Nat), P' n → P n`, `⊢ ∀ (n : Nat), Q n → Q' n` |

The cases of `wp_derivable`:

| Case | Rule inside `.conseq` | Precondition side (`∀ s, wp c Q s → <rule's pre> s`) |
|---|---|---|
| `skip` | `.skip` | apply `h` to the run `.skip` (R2, R3) |
| `assign x a` | `.assign` | apply `h` to the run `.assign` (R2, R3) |
| `seq c1 c2 ih1 ih2` | `.seq (ih1 _) (ih2 Q)` | take the two runs, apply `h` to a `.seq` run (R1, R2, R3) |
| `ite b c1 c2 ih1 ih2` | `.ite` around two `.conseq ?_ (ihi Q) _` (R14) | `intro s ⟨h, hb⟩ s' h'` (R11), then `.iteT` / `.iteF` (R3) |
| `«while» b c ih` | milestone 3 | — |

## Part 7 · `completeness`

Statement: `Valid P c Q → Derivable P c Q`. One R4: `.conseq pre (wp_derivable c Q) (fun _ h => h)`,
where `pre : ∀ s, P s → wp c Q s` takes `s`, `hP`, then (R1) a state and a run, and applies `h` (R2).
A term-mode proof: write it after `:=` without `by`.

---

## Traps

- This is completeness, not soundness (soundness of these rules is M045). You never invert a `Derivable`:
  you build derivations, and you invert only `BigStep` runs.
- `induction c with` without `generalizing Q`: the `seq` case then needs `Derivable (wp c1 (wp c2 Q)) c1 _`
  but the IH only gives `Derivable (wp c1 Q) c1 Q`.
- `| while b c ih =>` is a parse error: `while` is a keyword. Write `| «while» b c ih =>`.
- An inaccessible name such as `s'✝` cannot be typed. Pass `_` and let unification find it.
- `intro`, `exact` and anonymous constructors see through `wp` and `Valid`; `rw` and `simp` do not
  (E030). There is no need to unfold them.
- `wp_while_body`'s hypothesis is a conjunction: use `h.1` (the `wp`) and `h.2` (the test).
- In `refine`, a plain `_` that only a proof can fill (such as `∀ s, Q s → Q s`) is an error ("don't know
  how to synthesize placeholder"): write `fun _ h => h` or `?_`.
- `.while` concludes a fixed postcondition `fun s => I s ∧ beval s b = false` (R6); you need an outer
  `.conseq` to turn it into `Q`.
- In `refine`, a `?_` whose type still has unknown predicates is an error ("don't know how to synthesize
  implicit argument"): pass the derivation (`ih1 Q`) so the predicates are fixed (R14).
- `cases h with` lists only the rules that can produce `h`; naming an impossible rule (say `| skip` for a
  `seq` run) is an error.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| unfold `wp c Q s` in the goal | `intro s' hrun` | R1 |
| use `h : wp c Q s` / `h : Valid P c Q` | `h s' hrun` / `h s s' hP hrun` | R2 |
| build a run | `.seq h1 h2`, `.whileT hb h1 h2`, `.whileF hb`, `.iteT hb h`, `.skip`, `.assign` | R3 |
| rule of consequence | `.conseq pre d post`, trivial side `fun _ h => h` | R4 |
| a lemma as a side condition | `wp_while_body b c Q` (partially applied) | R5 |
| the loop rule | `.while d : Derivable I (.while b c) (fun s => I s ∧ beval s b = false)` | R6 |
| equality of assertions → `↔` | `funext s; apply propext; constructor` | R7, R8, R9 |
| invert a run | `cases hc with \| seq h1 h2 => …` | R10 |
| intro a conjunction | `intro ⟨h1, h2⟩` | R11 |
| invert a loop run | `cases hw with \| whileF hb => … \| whileT hb hc hw => …` | R12 |
| induction with an IH for every `Q` | `induction c generalizing Q with \| … \| «while» b c ih => …` | R13 |
| leave side conditions as goals | `refine .ite (.conseq ?_ (ih1 Q) (fun _ h => h)) (.conseq ?_ (ih2 Q) (fun _ h => h))` | R14 |
| see the state | infoview | |
