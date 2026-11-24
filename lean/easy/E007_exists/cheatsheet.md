# E007 · Exists: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001 (`rfl`, `decide`), E003 (`intro`, `exact`, `apply`), E004 (`fun`, anonymous constructor
`⟨_, _⟩`), E005 (`obtain ⟨_, _⟩ := h` and `rintro ⟨_, _⟩` on `∧`).
**New here:** the existential quantifier. `∃ x, P x` ("there is an `x` with `P x`") is proved by a **pair**
`⟨w, hw⟩`: a **witness** `w` and a proof `hw : P w`. To **prove** an `∃`, you pick the witness yourself (R1–R4).
To **use** an `∃` hypothesis, you take the pair apart and get a fresh value `x` with `hx : P x`, but you never
learn which value it is (R5–R7). Also new: applying a `∀`-hypothesis to a value (R8) and the lemma
`Nat.succ_ne_zero` (R9).

## How to read an entry

Each entry is one tactic or one term. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that matter.
- `{α : Type}` is any type; in the exercise it is `Nat`. `P Q A B : α → Prop` are **predicates**: `P w` is a
  statement about the value `w : α`. `G : Prop` is any goal when the step does not look at it.
- A hypothesis `k` only finishes the example.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `∃ x, P x` | "some `x` satisfies `P`"; typed `\exists` or `\ex`. `x` is a bound name, like a lambda's argument |
| `p q : Nat → Prop` | `p`, `q` are predicates on `Nat`: for each `n : Nat`, `p n` is a statement (a `Prop`) |
| `∃ x, P x ∧ Q x` | `∃ x, (P x ∧ Q x)`: the body of `∃` extends as far right as possible |
| `(∃ x, P x) → G` | the parentheses end the `∃` before the `→`; without them `∃ x, P x → G` is `∃ x, (P x → G)` |
| `∃ n, n + 2 = 5` | Lean drops the type when it is clear: you wrote `∃ n : Nat, …` |
| `∀ (y : α), P y → G` | for every `y : α`, `P y` implies `G`; the same as `∀ y, P y → G`, printed with the type |
| `a ≠ b` | `¬(a = b)`, i.e. `a = b → False` ("`a = b` is impossible"); typed `\ne` |
| `m ≠ 0 ∧ p m` | `(m ≠ 0) ∧ p m`: `≠` and `=` bind tighter than `∧` |
| `n + 1`, `n.succ` | the successor of `n`, `Nat.succ n` (`n.succ` is dot notation for it); lemma names say `succ` for it |
| `left✝ : P x` | a hypothesis you discarded with `_`: it is there but has no name you can type |

---

## Part 1 · `exists_square`

Statement: `∃ n : Nat, n * n = 144`. Give the witness (it is a number you know) and prove the arithmetic that
is left once the witness is substituted for `n`. Build the pair at once (R1 with R4), or commit to the witness
first (R2 or R3) and then close the arithmetic (R4).

**R1 · `exact ⟨w, hw⟩`** **closes** `∃ x, P x`. The anonymous constructor builds `Exists.intro w hw`; the
witness comes **first**, the proof second. The proof may itself be a term such as `rfl`: `⟨w, rfl⟩`.
Placeholders: `{α : Type} (P : α → Prop) (w : α) (hw : P w)`.

| Before | After |
|---|---|
| `hw : P w ⊢ ∃ x, P x` | no goals |

**R2 · `refine ⟨w, ?_⟩`** changes the **goal**: you fix the witness now, and the hole `?_` becomes the next
goal, the body with `x` replaced by `w`. Placeholders: `{α : Type} (P : α → Prop) (w : α)`.

| Before | After |
|---|---|
| `⊢ ∃ x, P x` | `⊢ P w` |

**R3 · `exists w`** changes the **goal** like R2, then runs `try trivial`: if `P w` is closed by `rfl`,
`decide`, or a matching hypothesis, no goal is left; otherwise `P w` stays open. Placeholders:
`{α : Type} (P : α → Prop) (w : α)`.

| Before | After |
|---|---|
| `g : G, k : G → P w ⊢ ∃ x, P x` | `g : G, k : G → P w ⊢ P w` (trivial failed) |
| `⊢ ∃ n, n + 2 = 5` | no goals (`exists 3`: `3 + 2 = 5` closed by trivial) |

**R4 · `rfl`** **closes** `e = v` when both sides compute to the same value (E001). With a concrete witness,
the goal left after R2 is closed arithmetic on `Nat`, which Lean evaluates.

| Before | After |
|---|---|
| `⊢ 4 + 3 = 7` | no goals |

**W1** (R2, R4): `∃ n : Nat, n + n = 10`.

| Step | State |
|---|---|
| start | `⊢ ∃ n, n + n = 10` |
| `refine ⟨5, ?_⟩` | `⊢ 5 + 5 = 10` |
| `rfl` | no goals |

## Part 2 · `exists_weaken`

Statement: `(∃ x, p x ∧ q x) → ∃ x, q x`. Introduce the hypothesis (`intro`, E003), take it apart into the
witness and two proofs (R6), and rebuild a pair with the same witness and the proof you need (R1).

**R5 · `obtain ⟨x, hx⟩ := h`** changes the **context**: `h : ∃ x, P x` is replaced by a value `x : α` and a
proof `hx : P x`. The goal is unchanged. You get *some* `x`, not a particular one, so `x` is a fresh name of
your choice. Placeholders: `{α : Type} (P : α → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` (with `h : ∃ x, P x` in the context) | `x : α, hx : P x ⊢ G` |

**R6 · `obtain ⟨x, ha, hb⟩ := h`** changes the **context**: with `h : ∃ x, P x ∧ Q x`, one flat pattern takes
apart the `∃` and the `∧` at once (`⟨x, ha, hb⟩` is short for `⟨x, ⟨ha, hb⟩⟩`). Write `_` for a part you do
not need; it stays in the context as an unnamed `left✝`. Placeholders: `{α : Type} (P Q : α → Prop) (G : Prop)`.

| Before | After `obtain ⟨x, _, hb⟩ := h` |
|---|---|
| `⊢ G` (with `h : ∃ x, P x ∧ Q x` in the context) | `x : α, left✝ : P x, hb : Q x ⊢ G` |

**W2** (intro, R6, R10): unpack, then rebuild the pair in the other order.

| Step | State |
|---|---|
| start | `⊢ (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x` |
| `intro h` | `⊢ ∃ x, Q x ∧ P x` (with `h : ∃ x, P x ∧ Q x` in the context) |
| `obtain ⟨x, hp, hq⟩ := h` | `x : Nat, hp : P x, hq : Q x ⊢ ∃ x, Q x ∧ P x` |
| `exact ⟨x, hq, hp⟩` | no goals |

## Part 3 · `exists_map`

Statement: from `h : ∀ x, p x → q x`, prove `(∃ x, p x) → ∃ x, q x`. Introduce and unpack the `∃` in one step
(R7), push the proof through `h` (R8), and pair it with the same witness (R1).

**R7 · `rintro ⟨x, hx⟩`** changes the **goal and the context**: on a goal `(∃ x, P x) → G` it does `intro h`
and `obtain ⟨x, hx⟩ := h` in one step (E005 did the same for `∧`). Placeholders:
`{α : Type} (P : α → Prop) (G : Prop)`.

| Before | After |
|---|---|
| `⊢ (∃ x, P x) → G` | `x : α, hx : P x ⊢ G` |

**R8 · `exact h w hw`** **closes** `Q w`: `h w hw` is a term of type `Q w` when `h : ∀ x, P x → Q x`, `w : α`, `hw : P w`. `h` is a
function of two arguments: first the value, then the proof about that value. Use it inside a pair:
`⟨w, h w hw⟩`. Placeholders: `{α : Type} (P Q : α → Prop) (w : α)`.

| Before | After `exact h w hw` |
|---|---|
| `hw : P w ⊢ Q w` (with `h : ∀ (x : α), P x → Q x` in the context) | no goals |

**W4** (R7, R8 twice, R1): push the proof through two `∀`-hypotheses, read inside out.

| Step | State |
|---|---|
| start | `⊢ (∃ x, P x) → ∃ x, R x` |
| `rintro ⟨x, hx⟩` | `x : Nat, hx : P x ⊢ ∃ x, R x` |
| `exact ⟨x, h2 x (h1 x hx)⟩` | no goals (`h1 x hx : Q x`, `h2 x (h1 x hx) : R x`) |

## Part 4 · `exists_shift`

Statement: from `h : ∃ n, p (n + 1)`, prove `∃ m, m ≠ 0 ∧ p m`. Unpack `h` (R5) into `n` and `hn : p (n + 1)`.
The witness for `m` is the expression `n + 1`, not `n`: that is the value `hn` talks about. Then the pair needs
two proofs, `n + 1 ≠ 0` (R9) and `p (n + 1)` (you have it), assembled flat (R10).

**R9 · `Nat.succ_ne_zero n`** **closes** `n + 1 ≠ 0`. The lemma is `Nat.succ_ne_zero (n : Nat) : n + 1 ≠ 0`:
no successor is zero (`#check` prints it as `n.succ ≠ 0`, the same statement). Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `n : Nat ⊢ n + 1 ≠ 0` | no goals |

**R10 · `exact ⟨w, ha, hb⟩`** **closes** `∃ x, A x ∧ B x`: the flat pattern of R6, now building
(`⟨w, ⟨ha, hb⟩⟩`). The witness `w` may be any expression of type `α`, such as `n + 1`; then the proofs must be
about that expression. Placeholders: `{α : Type} (A B : α → Prop) (w : α) (ha : A w) (hb : B w)`.

| Before | After |
|---|---|
| `ha : A w, hb : B w ⊢ ∃ x, A x ∧ B x` | no goals |

**W3** (R5, R1): the witness is an expression built from the unpacked name.

| Step | State |
|---|---|
| start | `⊢ ∃ m, P m` (with `h : ∃ n, P (2 * n)` in the context) |
| `obtain ⟨n, hn⟩ := h` | `n : Nat, hn : P (2 * n) ⊢ ∃ m, P m` |
| `exact ⟨2 * n, hn⟩` | no goals |

---

## Traps

- The witness comes first: `⟨w, hw⟩`, never `⟨hw, w⟩`.
- `obtain … := h` needs `h` in the context. On a goal `(∃ x, …) → …`, `intro h` first, or use `rintro ⟨x, hx⟩`.
- After `obtain ⟨n, hn⟩ := h` with `hn : p (n + 1)`, the pair `⟨n, hn⟩` is wrong: `hn` is about `n + 1`, so the
  witness must be `n + 1`. Read the type of the proof you hold to find the witness.
- You cannot `obtain` a specific value: the unpacked `x` is arbitrary. Never pick a number for it.
- `∃ x, P x → G` is not `(∃ x, P x) → G` (Reading the goals).
- `exists w` silently closes the goal when `trivial` can; if a goal remains, it is `P w`, not the `∃`.
- `simp`, `simp_all` and `grind` are banned: build the pairs by hand.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| prove `∃ x, P x` in one term | `exact ⟨w, hw⟩` (`⟨w, rfl⟩` for arithmetic) | R1, R4 |
| fix the witness, prove the body next | `refine ⟨w, ?_⟩` | R2 |
| fix the witness, try to finish | `exists w` | R3 |
| closed `Nat` arithmetic | `rfl` | R4 |
| use `h : ∃ x, P x` | `obtain ⟨x, hx⟩ := h` | R5 |
| use `h : ∃ x, P x ∧ Q x` | `obtain ⟨x, hp, hq⟩ := h` (`_` to discard) | R6 |
| goal `(∃ x, P x) → G` | `rintro ⟨x, hx⟩` | R7 |
| `Q w` from `h : ∀ x, P x → Q x` | `h w hw` | R8 |
| `n + 1 ≠ 0` | `Nat.succ_ne_zero n` | R9 |
| prove `∃ x, A x ∧ B x` | `exact ⟨w, ha, hb⟩` | R10 |
| see the state | infoview | |
