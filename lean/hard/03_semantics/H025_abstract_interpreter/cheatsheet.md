# H025 · An abstract interpreter for IMP: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `def` by pattern matching, `inductive`, `theorem`,
`intro`, `exact`, `rw`, `simp`, anonymous constructors `⟨_, _⟩`, `h.1` / `h.2`. The sign domain of M046
helps but is re-explained here. **New here:** case analysis and induction on your own inductive types,
`induction … generalizing`, induction on a *derivation* (a proof of an inductive `Prop` such as
`BigStep c s s'`), `generalize`, inversion with `cases`, and the core lemmas on signs of products. Core
Lean only: no Mathlib.

## The problem in one paragraph

A concrete state `s : State` maps each variable `x : Nat` to an `Int`. An abstract state `st : AState`
is a list of signs; `lookup st x` is entry `x`, and `top` when `x` is past the end, so `[]` describes
every state. `Sign.gamma a v` ("`a` describes `v`") is `v < 0`, `v = 0`, `0 < v` or `True` for
`neg, zero, pos, top`; `Approx st s` means `∀ x, (lookup st x).gamma (s x)`. `ajoin p q` joins entry by
entry and is cut to the shorter list (so a missing entry is again `top`); `aupdate` past the end changes
nothing. `aexec` runs a command on abstract states; for `while` it calls `iterate`, which repeats
`x ↦ ajoin st (aexec c x)` until the value is stable and returns `[]` when its fuel (10 rounds) runs out.
`BigStep c s s'` is the concrete big-step semantics: "running `c` from `s` terminates in `s'`".
`aexec_sound` says: if `st` describes `s` and `c` runs from `s` to `s'`, then `aexec c st` describes `s'`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**),
lists the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : α → Prop`). The step changes only the part inside `P (…)`.
- Placeholders are written as Lean binders. `{α : Type}` is any type; `[Decidable c]` says Lean can
  compute whether the proposition `c` holds (true for `=` on `Nat`, `Int`, lists of a type with
  `deriving DecidableEq`, and for `<`, `≤` on `Nat` and `Int`).
- The guide's own objects: `Light` (an enumeration), `Tree` (binary trees), `pick d l n` (entry `n` of
  `l`, default `d`), `Every Q` (`∀ x, Q x`), `descend` (a fuelled loop), and a toy loop language `Prog`
  with its run relation `Run p n m`. They are not the exercise's objects.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `(lookup st x).gamma v` | `Sign.gamma (lookup st x) v`: dot notation, `e.f a` is `T.f e a` when `e : T` |
| `Sign.neg.gamma n` | `Sign.gamma Sign.neg n`, which unfolds to `n < 0` |
| `.neg`, `.pos` (in source) | `Sign.neg`, `Sign.pos`: the leading dot takes the type from context |
| `[]`, `a :: as` | the empty list; the list with head `a` and tail `as` |
| `x + 1`, `n✝ + 1` | the successor case of a `Nat` after `cases` or `induction` |
| `h✝`, `a✝`, `n✝`, `head✝` | an inaccessible name: Lean made it, you cannot type it. Name it with `next h =>` (R10) or `with \| … =>` |
| `l_ih✝`, `a_ih✝`, `tail_ih✝` | an induction hypothesis Lean made |
| `s✝`, `s'✝` next to `s s' : State` | after `induction h`: the indices of the current rule; the old `s s'` are now unrelated |
| `fun k => s (k + 1)` | the state `s` shifted by one: variable `k` of it is variable `k + 1` of `s` |
| `update s x v y` | `(update s x v) y`, i.e. `if y = x then v else s y` |
| `Com.while b c`, `c1.seq c2`, `p.rep` | constructors applied to arguments, printed with dot notation |
| `decide (a ≤ b)` | the `Bool` that is `true` exactly when `a ≤ b` |
| `Le p q` | the milestone `def`: every state described by `p` is described by `q` (`p ⊑ q`) |
| `case isTrue`, `case cons.succ.succ` | the goal's tag: which branch of `split` / `cases` / `induction` it is |
| `«while»` | the name `while` written with French quotes, because `while` is a keyword |
| `abbrev State := Nat → Int` | `State` is another name for `Nat → Int`; Lean unfolds it freely |
| `!b`, `b1 && b2` (in `beval`) | Boolean not and Boolean and on `Bool` |
| `let x' := e; body` (in `iterate`) | a local name `x'` for `e` inside `body`; `simp only [iterate]` substitutes it (R19) |
| `deriving DecidableEq` | Lean writes the `=`-test for `Sign`, so `if a = b` (in `Sign.join`) and `if x' = x` on `List Sign` (in `iterate`) compute |
| `p ⊑ q` (in prose) | `Le p q`: `q` is less precise than `p`; `[]` is above everything |
| `∀ {s s' : State}, …` | implicit binders: Lean fills `s s'` from the next explicit argument, so `ih h st hs` needs no `s s'` |
| `Sign.top.gamma v` | unfolds to `True` (`top` describes every integer) |
| `¬c` | `c → False` |
| `fun _ h => h` | a function ignoring its first argument (`_`) and returning its second: here a proof of `Le p p` |

---

## Part 1 · `aeval_sound`

Statement: if `Approx st s`, then for every expression `e`, `(aevalSign st e).gamma (aeval s e)`. Add three
helper lemmas first (outside the spec, anywhere above): `plus_sound` and `times_sound`
(`a.gamma x → b.gamma y → (a.plus b).gamma (x + y)`, and the same for `times` and `*`) and
`ofInt_sound : (Sign.ofInt n).gamma n`.

**R1 · `cases a`** on an enumeration changes the **goal list**: one goal per constructor, with `a`
replaced by it. `cases a <;> cases b` gives all pairs (16 for `Sign`). Placeholders:
`(P : Light → Prop) (a : Light)`.

| Before | After |
|---|---|
| `a : Light ⊢ P a` | `⊢ P Light.red`, `⊢ P Light.amber`, `⊢ P Light.green` |

**R2 · `simp_all [d]`** changes the **context and the goal**: it unfolds `d` and simplifies every hypothesis
and the goal, each with the others; it closes the goal when a hypothesis becomes `False` (for example
`x < 0` next to `x = 0`). Placeholders: `(x y : Int)` and `Light.code`, which plays the role of
`Sign.gamma`.

| Before | After |
|---|---|
| `hx : Light.green.code x, hy : Light.green.code y ⊢ Light.green.code (x + y)` | `hx : 0 < x, hy : 0 < y ⊢ 0 < x + y` |

**R3 · `omega`** **closes** a goal of linear arithmetic over `Int` or `Nat` (`+`, `-`, numerals,
`<`, `≤`, `=`), using the hypotheses. It does not know `x * y` for two variables. Placeholders:
`(x y : Int)`.

| Before | After |
|---|---|
| `hx : 0 < x, hy : y < 0 ⊢ 0 < x - y` | no goals |

**R4–R7** **close** the four sign cases of a product, the ones `omega` cannot do. Placeholders `(a b : Int)`;
use them as `exact Int.mul_pos ha hb`.

| Entry | Lemma | Statement |
|---|---|---|
| R4 | `Int.mul_pos` | `0 < a → 0 < b → 0 < a * b` |
| R5 | `Int.mul_pos_of_neg_of_neg` | `a < 0 → b < 0 → 0 < a * b` |
| R6 | `Int.mul_neg_of_pos_of_neg` | `0 < a → b < 0 → a * b < 0` |
| R7 | `Int.mul_neg_of_neg_of_pos` | `a < 0 → 0 < b → a * b < 0` |

| Entry | Before | After |
|---|---|---|
| R4 | `ha : 0 < a, hb : 0 < b ⊢ 0 < a * b` | no goals |
| R5 | `ha : a < 0, hb : b < 0 ⊢ 0 < a * b` | no goals |
| R6 | `ha : 0 < a, hb : b < 0 ⊢ a * b < 0` | no goals |
| R7 | `ha : a < 0, hb : 0 < b ⊢ a * b < 0` | no goals |

After `cases a <;> cases b <;> simp_all [Sign.times, Sign.gamma]`, exactly these four goals remain, in
the order `neg·neg`, `neg·pos`, `pos·neg`, `pos·pos` (R5, R7, R6, R4).

**R8 · `unfold f`** changes the **goal**: the name `f` is replaced by its body. Placeholders:
`(n : Nat)`, `Light.byAge n := if n = 0 then .red else if n < 10 then .amber else .green`.

| Before | After |
|---|---|
| `⊢ P (Light.byAge n)` | `⊢ P (if n = 0 then Light.red else if n < 10 then Light.amber else Light.green)` |

**R9 · `split`** changes the **goal list**: an `if c then a else b` in the goal becomes two goals, one with
the hypothesis `c` (tag `isTrue`) and one with `¬c` (tag `isFalse`). Nested `if`s need one `split` each.
Placeholders: `{α : Type} (c : Prop) [Decidable c] (a b : α)`.

| Before | After |
|---|---|
| `⊢ P (if c then a else b)` | `h✝ : c ⊢ P a`, `h✝ : ¬c ⊢ P b` |

**R10 · `next h => tac`** changes the **context** of the first goal: its last inaccessible hypothesis
`h✝` gets the name `h`, then `tac` must close that goal. `next a b h =>` names several, oldest first.
Placeholders: `(c G : Prop)`. Below, `tac` closes the first goal, so the second is what is left.

| Before | After `next h => exact k h` |
|---|---|
| `h✝ : c ⊢ G`, `h✝ : ¬c ⊢ G` | `h✝ : ¬c ⊢ G` |

**R11 · `induction t`** on an inductive type changes the **goal list**: one goal per constructor, and for
every argument of the constructor's own type an induction hypothesis (IH). Write
`induction e with | num n => … | plus a b iha ihb => …` to name the arguments and IHs; the `with`
alternatives may be indented further than `induction`. Placeholders: `(P : Tree → Prop) (t : Tree)`.

| Before | After |
|---|---|
| `t : Tree ⊢ P t` | `n✝ : Nat ⊢ P (Tree.leaf n✝)`, `l_ih✝ : P l✝, r_ih✝ : P r✝ ⊢ P (l✝.node r✝)` |

For `aeval_sound`: `induction e with`, four alternatives, each closed by `exact` with one helper (or with
`h x`, since `Approx st s` is `∀ x, …`).

---

## Part 2 · `lookup_ajoin_left`, `lookup_ajoin_right`

Statement: if entry `x` of `p` (resp. `q`) describes `v`, so does entry `x` of `ajoin p q`. Prove the head
case first as helpers `join_left : a.gamma v → (a.join b).gamma v` and `join_right` (R8 on `Sign.join`,
R9, then R2 with `Sign.gamma`). Then recurse on the two lists and the index together.

**R12 · `induction l generalizing x`** changes the **goal list**: like R11, but `x` is put back into the
goal first, so the IH is `∀ x, …` instead of being about the one `x` in the context. You need this
whenever the recursive call uses a different argument: `lookup (_ :: as) (n + 1) = lookup as n` moves
`x` to `n`, and `ajoin` moves `q` to its tail. Placeholders: `{α : Type} (P : List α → Nat → Prop)
(l : List α) (x : Nat)`.

| Before | After |
|---|---|
| `l : List α, x : Nat ⊢ P l x` | `x : Nat ⊢ P [] x`, `x : Nat ⊢ P (head✝ :: tail✝) x` |

The `cons` goal also has the IH `tail_ih✝ : ∀ (x : Nat), P tail✝ x`: it is about every `x`. Without
`generalizing x` it would be `P tail✝ x` for the one `x` you started with.

**R13 · `cases q`** on a list changes the **goal list**: `q` is `[]` or `head :: tail`. No IH (use R12 for
that). `cases q with | nil => … | cons b bs => …` names the parts. Placeholders: `{α : Type} (q : List α)`.

| Before | After |
|---|---|
| `q : List α ⊢ P q` | `⊢ P []`, `head✝ : α, tail✝ : List α ⊢ P (head✝ :: tail✝)` |

**R14 · `cases n`** on a natural number changes the **goal list**: `n` is `0` or `m + 1`.
`cases x with | zero => … | succ n => …`. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ P n` | `⊢ P 0`, `n✝ : Nat ⊢ P (n✝ + 1)` |

**R15 · `simp only [f]`** (or `simp [f, …]`) changes the **goal**: `f` applied to constructors (`[]`,
`a :: as`, `0`, `n + 1`) is replaced using the equation for that pattern. With `simp [ajoin, lookup,
Sign.gamma]` the `nil` cases reduce to `True` and close. Placeholders: `{α : Type} (d a : α)
(as : List α) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (pick d [] n) ∧ P (pick d (a :: as) (n + 1))` | `⊢ P d ∧ P (pick d as n)` |

In the `cons`/`cons`/`succ` case the goal `(lookup (ajoin (a :: as) (b :: bs)) (n + 1)).gamma v`
reduces by definition to the IH's form, so `exact ih bs n h` works without unfolding first (`h`, about
`lookup (a :: as) (n + 1)`, likewise is already about `lookup as n`). In the `zero` case the goal reduces
to `(a.join b).gamma v` and `h` to `a.gamma v`, so `exact join_left h` works the same way.

---

## Part 3 · `approx_aupdate`

Statement: if `st` describes `s` and `a` describes `v`, then `aupdate st x a` describes `update s x v`.

**R16 · `intro y`** on a definition that is a `∀` changes the **context**: Lean unfolds the definition to
see the `∀`. Here `Approx (aupdate st x a) (update s x v)` becomes a goal about variable `y`. The same
works for `Le p q` (two `intro`s: `s`, then `hs`). In term mode, `h y` applies `h : Approx st s` to `y`.
Placeholders: `{α : Type} (Q : α → Prop)`, `Every Q := ∀ x, Q x`.

| Before | After |
|---|---|
| `⊢ Every Q` | `y : α ⊢ Q y` |

Then `induction st generalizing x y s` (R12), and in the `cons` case `cases x` and `cases y` (R14): four
cases. The three with a `0` close by `simpa [aupdate, lookup, update] using …` with `hv`, `h (m + 1)` or
`h 0` (R18). The `succ`/`succ` case uses the IH on the tail.

**R17 · `have := ih t ht`** changes the **context**: it adds `this`, the IH at a new argument. Because
`st` was generalized together with `s`, the IH holds for every state, in particular the shifted state
`fun k => s (k + 1)` (the tail `bs` describes it). `fun k => h (k + 1)` is the proof that `bs` describes
it: entry `k` of `bs` is entry `k + 1` of `b :: bs`. Placeholders: `{α : Type} (s : Nat → α)
(Q : Nat → α → Prop) (P : (Nat → α) → Prop)`.

| Before | After |
|---|---|
| `⊢ P fun k => s (k + 1)` | `this : P fun k => s (k + 1) ⊢ P fun k => s (k + 1)` |

**R18 · `simpa [d] using e`** **closes** the goal: it simplifies both `e` and the goal (unfolding `d`), then
closes the goal with the simplified `e`. `simp` knows `m + 1 = n + 1 ↔ m = n`, which is exactly why the
shifted `this` matches the goal in the `succ`/`succ` case. Placeholders: `{α : Type} (v : α)
(f : Nat → α) (m n : Nat)`.

| Before | After |
|---|---|
| `h : P (if m = n then v else f (m + 1)) ⊢ P (if m + 1 = n + 1 then v else f (m + 1))` | no goals |

---

## Part 4 · `iterate_post`

Statement: if `init ⊑ x`, the result `r = iterate f init k x` satisfies `init ⊑ r` and `f r ⊑ r` (a
*post-fixpoint*: one more step of `f` stays below it). Induct on the fuel with `induction k generalizing x`
(R12 on `Nat`: cases `zero` and `succ k ih`).

- `zero`: the result is `[]`, and `[]` describes every state. For each part, `fun _ _ y => by simp
  [iterate, lookup, Sign.gamma]` (R16 in term mode, then R15).
- `succ`: unfold one round (R19), then `split` on the stability test (R9) and name the hypothesis (R10).

**R19 · `simp only [f]`** on an equation with a `let` changes the **goal**: the `let y := …` is
substituted into the body, so the `if` becomes visible to `split`. For `iterate` the test becomes
`ajoin init (f x) = x`. Placeholders: `(g : Nat → Nat) (k x : Nat)`.

| Before | After |
|---|---|
| `⊢ P (descend g (k + 1) x)` | `⊢ P (if g x < x then descend g k (g x) else x)` |

**R20 · `refine ⟨h, fun y => ?_⟩`** changes the **goal**: the first part of `∧` is given now, and the
second is a hole under binders, which become hypotheses. In the stable branch:
`refine ⟨hx, fun s hs y => ?_⟩`, then `rw [← heq]` turns `x` back into `ajoin init (f x)` and
`lookup_ajoin_right` finishes. In the other branch the IH applies at `ajoin init (f x)`, with
`init ⊑ ajoin init (f x)` from `lookup_ajoin_left`. Placeholders: `{α : Type} (A : Prop) (Q : α → Prop)`.

| Before | After |
|---|---|
| `⊢ A ∧ ∀ (x : α), Q x` | `y : α ⊢ Q y` |

---

## Part 5 · `while_inv`

Statement: if the body `c` is sound (`hc`) and `I` is stable (`aexec c I ⊑ I`), then every terminating run
of `while b c` from a state described by `I` ends in a state described by `I`. Induct on the run `h`.

**R21 · `generalize hw : e = w at h`** changes the **context**: the term `e` inside `h` is replaced by a new
variable `w`, and `hw : e = w` remembers it. `induction` needs this: it refuses
`h : BigStep (Com.while b c) s s'`, whose command index is not a variable. Placeholders:
`(p : Prog) (n m : Nat) (h : Run p.rep n m)`.

| Before | After |
|---|---|
| `h : Run p.rep n m ⊢ Q` | `w : Prog, hw : p.rep = w, h : Run w n m ⊢ Q` |

**R22 · `induction h`** on a derivation changes the **goal list**: one goal per rule of the inductive
`Prop`, with the rule's variables (as `n✝`, `m✝`, …) and an IH for each premise of the same relation.
Hypotheses that mention the indices (here `hs : Approx I s`, `hw`) are carried along: they appear in each
goal about that rule's states, and each IH takes them as arguments. With `with`, name the rules you care
about and catch the rest with `| _ => …`. Placeholders: `(p : Prog) (n m : Nat) (h : Run p n m)`.

| Before | After |
|---|---|
| `h : Run p n m ⊢ n ≤ m` | `⊢ n✝ ≤ n✝` (`halt`), `a✝ : Run p✝ (n✝ + 1) m✝, a_ih✝ : n✝ + 1 ≤ m✝ ⊢ n✝ ≤ m✝` (`tick`), `⊢ n✝ ≤ n✝` (`repDone`), `a_ih✝¹ : n✝ ≤ m✝, a_ih✝ : m✝ ≤ k✝ ⊢ n✝ ≤ k✝` (`repMore`) |

For `BigStep` the rules are `skip, assign, seq, iteT, iteF, whileF, whileT`; after R21, only `whileF` and
`whileT` are possible, and `hw` refutes the other five (R23). In `whileT _ h1 _ _ ih2`, `ih2` takes
`Approx I s'` (from `hI` and `hc` applied to `h1`) and then `hw` again (pass `rfl` after R24).

**R23 · `cases hw`** with `hw : C₁ … = C₂ …` for **different** constructors **closes** the goal:
constructors of an inductive type are distinct, so the equation is impossible.

| Before | After |
|---|---|
| `hw : p.rep = Prog.halt ⊢ Q` | no goals |

**R24 · `cases hw`** with `hw : C a = C b` for the **same** constructor changes the **context**:
constructors are injective, so `b` is replaced by `a` everywhere. Placeholders: `(p q : Prog)
(P : Prog → Prop)`.

| Before | After |
|---|---|
| `h : P p, hw : p.rep = q.rep ⊢ P q` | `h : P p ⊢ P p` |

---

## Part 6 · `aexec_sound`

Statement: the main theorem. Prove the milestones of Parts 1–5 first; this proof only combines them.
Use `induction c generalizing s s' st` (R11, R12): the IH for the loop body must hold for every run of
it and every abstract state, because the body runs many times from different states. Lean puts `h`
back into the IH too, since `h` mentions `c`, so the IH reads
`∀ {s s'}, BigStep c s s' → ∀ st, Approx st s → Approx (aexec c st) s'`.
The `while` case is written `| «while» b c ih => …` (`while` is a keyword).

**R25 · `cases h`** on a derivation (inversion) changes the **goal list**: one goal per rule whose conclusion
can match `h`'s indices, with that rule's premises as new hypotheses; rules with the wrong constructor
disappear, and indices are substituted (in `repDone`, `m` becomes `n`). For `h : BigStep (.ite b c1 c2) s s'`
this leaves `iteT` and `iteF`; for `.seq` only `seq`; for `.skip` only `skip`, with `s'` replaced by `s`.
Write `cases h with | iteT hb h1 => … | iteF hb h2 => …`. Placeholders: `(p : Prog) (n m : Nat)
(h : Run p.rep n m)`.

| Before | After |
|---|---|
| `h : Run p.rep n m ⊢ P n m` | `⊢ P n n`, `a✝¹ : Run p n m✝, a✝ : Run p.rep m✝ m ⊢ P n m` |

The goals `Approx (aexec (Com.ite b c1 c2) st) s'` etc. unfold by definition (`aexec` on a constructor),
so `exact fun y => lookup_ajoin_left _ _ y _ (ih1 h1 _ hs y)` type-checks as is.

The `while` case: `iterate_post (aexec c) st 10 st (fun _ h => h)` gives `I := iterate (aexec c) st 10 st`
with `st ⊑ I` and `aexec c I ⊑ I`; `while_inv` with `hc` built from `ih` finishes.

---

## Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `cases a <;> cases b <;> simp_all [Light.code] <;> omega`: the 9 pairs of lights; `simp_all`
closes the 6 where `hab : a = b` is false and turns the rest into linear arithmetic (R1, R2, R3).

**W2.** `pick 0 (zipMin p q) x ≤ pick 0 p x`: `induction p generalizing q x`, then `cases q`, then
`cases x`, with `simp` on the `nil` cases and the IH on the `succ` case (R12–R15). Same shape as Part 2.

**W3.** An invariant `Q` of `p` is an invariant of every run of `rep p`: `generalize` (R21), `induction h with`
(R22), `cases hw` to substitute in `repMore` (R24) and to refute in the other rules (R23). Same shape as
Part 5.

---

## Traps

- `induction c` without `generalizing s s' st` gives an IH about one fixed run and one fixed `st`: useless
  for `seq` (the second command starts in `s'`) and for `while`.
- `induction h` directly on `h : BigStep (.while b c) s s'` fails with "Index in target's type is not a
  variable": the command index must be a variable. `generalize` first (R21).
- In `induction … with`, a rule you do not list needs a catch-all `| _ => cases hw`, or Lean reports the
  missing alternatives.
- `while` is a keyword: the alternative is `| «while» b c ih`, not `| while b c ih`.
- `omega` fails on `x * y`: use R4–R7. `simp_all` alone does not do `0 < x + y` either: follow it with
  `omega` (`<;> omega`).
- `ajoin` is cut to the shorter list, and a missing entry is `top`: the `nil` cases are true because
  `Sign.gamma .top v` is `True`, so `simp [ajoin, lookup, Sign.gamma]` closes them.
- `Sign.ofInt n` has two nested `if`s: two `split`s (R9), and `omega` for the last case (`¬n < 0`,
  `¬n = 0` gives `0 < n`).
- Do not leave search tactics (`exact?`, `apply?`, `try?`) in the file: they are not proofs.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| all cases of a finite type | `cases a <;> cases b` | R1 |
| unfold and simplify hypotheses and goal | `simp_all [Sign.plus, Sign.gamma]` | R2 |
| linear arithmetic | `omega` | R3 |
| sign of a product | `Int.mul_pos`, `Int.mul_pos_of_neg_of_neg`, `Int.mul_neg_of_pos_of_neg`, `Int.mul_neg_of_neg_of_pos` | R4–R7 |
| see the body of a definition | `unfold Sign.ofInt` | R8 |
| case on an `if` in the goal | `split`, then `next h => …` | R9, R10 |
| induction on an expression / command | `induction e with \| num n => … \| plus a b iha ihb => …` | R11 |
| IH for every value of another argument | `induction p generalizing q x` | R12 |
| list is `[]` or `b :: bs`; index is `0` or `n + 1` | `cases q with …`, `cases x with …` | R13, R14 |
| compute a definition on constructors | `simp [ajoin, lookup, Sign.gamma]` | R15 |
| goal `Approx st s` / `Le p q` | `intro y` / `intro s hs y` | R16 |
| IH at the shifted state | `have := ih (fun k => s (k + 1)) (fun k => h (k + 1)) n m` | R17 |
| close after simplifying both sides | `simpa [aupdate, lookup, update] using this` | R18 |
| one round of `iterate` | `simp only [iterate]` | R19 |
| give one part, open the other | `refine ⟨hx, fun s hs y => ?_⟩` | R20 |
| induct on a run of a `while` | `generalize hw : Com.while b c = w at h` | R21 |
| induction on a derivation | `induction h with \| whileF => … \| whileT _ h1 _ _ ih2 => … \| _ => cases hw` | R22 |
| impossible / injective constructor equation | `cases hw` | R23, R24 |
| which rule built `h` | `cases h with \| iteT hb h1 => … \| iteF hb h2 => …` | R25 |
| see the state | infoview | |
