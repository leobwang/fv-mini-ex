# E046 · Term-mode sugar: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md); this exercise bans
them (`BANNED: by`), so it is only for comparison: each entry below names the tactic its term replaces.

**Assumed:** Lean basics (easy tier E001–E033), in particular E004: a proof is a term, `fun h => …` proves an
implication, `⟨a, b⟩` proves `A ∧ B`, and applying `h : A → B` to `ha : A` gives `h ha : B`.
**New here:** the shorthand that tactic proofs usually hide: dot notation on hypotheses (`h.elim`, `h.mp`,
`h.trans`), `‹T›`, `h ▸ e`, `let ⟨…⟩ := h`, and `have` / `show … from` inside a term; the core lemmas
`Or.elim`, `Iff.mp`, `Iff.mpr`, `Iff.trans`, `Nat.le_trans`, `Nat.le_succ_of_le`. No Mathlib.

## How to read an entry

Each entry is one piece of term syntax or one lemma. With no tactic block there is no goal list; what plays
the role of the goal is the **expected type**: the type the term at the cursor must have. An entry says what
the step changes:

- **goal**: the expected type at the spot you still have to fill (R1 turns one expected `C` into two holes);
- **context**: the hypotheses available there (R7, R9 add some);
- **closes**: the term needs nothing more (R3, R5, R10, R12 applied to all their arguments).

How to see a state yourself: write `_` where a term is missing. Lean reports "don't know how to synthesize
placeholder" (with "for argument `left`" or similar when the `_` is a named argument of a lemma), lists the
context and then, after the turnstile `⊢`, the expected type at that `_`. Every
**Before** / **After** cell below is such a report, taken from the guide's examples with `_` in place of the
next term (only the hypotheses that change are shown; "expects `T`" is the line after the turnstile).
Undo the `_` before you move on: a file with `_` left in it does not compile.

- `A B C D : Prop` are arbitrary propositions; `{α : Type}` is any type (`Nat`, `List Nat`, …).
- `P : α → Prop` is "the rest of the statement": the step changes only the part inside `P (…)`.
- A hypothesis such as `k`, `f` or `g` in an entry is only there to finish the example.

## Reading the goals

| You see | It means |
|---|---|
| `A ∨ B`, `Or A B` | `A` or `B`; a proof is one of the two, so using it needs a case for each (R1) |
| `A ↔ B`, `Iff A B` | `A` if and only if `B`: a pair of implications `A → B` (`.mp`) and `B → A` (`.mpr`) |
| `h.elim`, `h.mp`, `h.trans` | dot notation: `T.f h`, where `T` is the head of `h`'s type (`Or`, `Iff`, …) |
| `‹A›` | the hypothesis of type `A`, whatever it is called (R3) |
| `h ▸ e` | `e`, with the expected type rewritten by the equation `h` (R6) |
| `p q : Nat → Prop` | predicates on `Nat`: for each `n`, `p n` is a proposition about `n` |
| `∃ n, p n ∧ q n` | some `n` has both properties; a proof is a pair `⟨n, ⟨hp, hq⟩⟩` |
| `∀ (x : α), r x → A` | how Lean prints a hypothesis `k : ∀ x, r x → A`: a function from `x` and a proof of `r x` to `A` |
| `left✝ : p x` | a hypothesis you named `_` in a pattern: it exists but you cannot refer to it |
| `m.succ`, `Nat.succ m` | `m + 1`; the two compute to the same term, so either form is accepted (R11) |
| `n ≤ m` on `Nat` | the usual order; `Nat.le_trans`, `Nat.le_succ_of_le` are its core lemmas |

---

## Part 1 · `or_mp`

Statement: from `h : P ∨ Q`, `hpr : P ↔ R` and `hqr : Q → R`, prove `R`. In words: both cases of the `∨`
lead to `R`, the first through the left-to-right half of an `↔`.

**R1 · `h.elim f g`** changes the **goal**: the expected `C` becomes two holes, one function per case. The
lemma is `Or.elim : a ∨ b → (a → c) → (b → c) → c`; `h.elim` is `Or.elim h` because `h : Or A B`. Tactic
form: `cases h` / `rcases h with ha | hb` (E006).
Placeholders: `{A B C : Prop} (h : A ∨ B)`.

| Before | After `h.elim _ _` |
|---|---|
| `h : A ∨ B` · expects `C` | first hole expects `A → C`; second hole expects `B → C` |

**R2 · `h.mp`, `h.mpr`** **close** a hole once given their argument: `Iff.mp : (a ↔ b) → a → b` and
`Iff.mpr : (a ↔ b) → b → a`. Without the argument, `h.mp` is itself a function `A → B`, which is exactly what
a hole of R1 expects. Placeholders: `{A B : Prop} (h : A ↔ B)`.

| Before | After |
|---|---|
| `h : A ↔ B` · expects `B` | `h.mp _`: the hole expects `A` |
| `h : A ↔ B` · expects `A` | `h.mpr _`: the hole expects `B` |

**W1.** `h.elim hca.mpr hbc` proves `C` from `h : A ∨ B`, `hca : C ↔ A`, `hbc : B → C`: R1 with R2 as its
first argument.

---

## Part 2 · `anon_hyp`

Statement: from `hp : P`, `hq : Q` and `h : P → Q → R`, prove `R`, naming the arguments by their types.

**R3 · `‹T›`** **closes** a hole of type `T` with a hypothesis of type `T` from the context. Its name does
not matter. Typed `\f<` and `\f>`. Under the hood it is the `assumption` tactic, which is why it works here
although the exercise bans tactic blocks. Placeholders: `{A B : Prop} (ha : A) (f : A → B)`.

| Before | After `f _` | After `f ‹A›` |
|---|---|---|
| `ha : A`, `f : A → B` · expects `B` | the hole expects `A` | nothing left |

---

## Part 3 · `iff_chain`

Statement: from `h1 : P ↔ Q` and `h2 : Q ↔ R`, prove `P ↔ R`.

**R4 · `h1.trans h2`** **closes** the hole: `Iff.trans : (a ↔ b) → (b ↔ c) → (a ↔ c)`, and
`h1.trans h2 = Iff.trans h1 h2`. The middle proposition of `h1` and `h2` must be the same. It chains:
`(h1.trans h2).trans h3`. Placeholders: `{A B C D : Prop} (h1 : A ↔ B) (h2 : B ↔ C) (h3 : C ↔ D)`.

| Before | After `(h1.trans _).trans h3` |
|---|---|
| expects `A ↔ D` | the hole expects `B ↔ C` |

---

## Part 4 · `subst_term`

Statement: from `h : n = 2`, prove `n + n = 4`. `rfl` alone fails: `n + n` does not compute while `n` is a
variable. After substituting `2` for `n` it does.

**R5 · `rfl`** **closes** `s = t` when both sides compute to the same value: `rfl : a = a`, and Lean
evaluates closed `Nat` arithmetic. Placeholders: none.

| Before | After `rfl` |
|---|---|
| expects `2 * 3 + 1 = 7` | nothing left |

**R6 · `h ▸ e`** changes the **goal**: with `h : a = b`, the expected type is rewritten by `h`, and `e` is
checked against the result. Typed `\t`. `▸` tries `h` in both directions (here it replaced `a` by `b`; with
`h : b = a` it would do the same). If the expected type is unknown, it rewrites the type of `e` instead.
Tactic form: `rw [h]` then `exact e` (E009).
Placeholders: `{α : Type} (a b : α) (P : α → Prop) (h : a = b)`.

| Before | After `h ▸ _` |
|---|---|
| `h : a = b` · expects `P a` | the hole expects `P b` |

**W2.** With `h : m = 3` and expected `m * m = 9`, `h ▸ _` leaves a hole that expects `3 * 3 = 9`, and R5
fills it: `h ▸ rfl`.

---

## Part 5 · `exists_let`

Statement: from `h : ∃ n, p n ∧ q n`, prove `∃ n, q n`. Take the witness and the `q n` part out of `h`, then
build a new `∃` with the same witness.

**R7 · `let ⟨x, hx⟩ := h` then the rest** changes the **context**: the witness and its proof are added, and
the expected type of the rest is unchanged. Patterns flatten: `⟨x, ha, hb⟩` means `⟨x, ⟨ha, hb⟩⟩`, so one
`let` also splits the `∧`. Write `_` for a part you do not need; it then shows as `left✝`. Taking an `∃`
apart this way is allowed because the expected type is a `Prop`. Tactic form: `obtain ⟨x, _, hr⟩ := h` (E007).
Placeholders:
`{α : Type} {A : Prop} (p r : α → Prop) (h : ∃ x, p x ∧ r x)`.

| Before | After `let ⟨x, _, hr⟩ := h; _` |
|---|---|
| `h : ∃ x, p x ∧ r x` · expects `A` | `x : α`, `left✝ : p x`, `hr : r x` · the hole expects `A` |

**R8 · `⟨w, hw⟩`** changes the **goal**: for an expected `∃ x, p x`, the first component is the witness, and
the second must then prove `p w`. It is `Exists.intro w hw`; tactic form `exact ⟨w, hw⟩` (E007). Placeholders: `{α : Type} (p : α → Prop) (w : α)`.

| Before | After `⟨w, _⟩` |
|---|---|
| expects `∃ x, p x` | the hole expects `p w` |

**W3.** `let ⟨k, hs, ht⟩ := h` then `⟨k, ht, hs⟩` turns `h : ∃ k, s k ∧ t k` into `∃ k, t k ∧ s k`: R7, then
R8 with a nested pair.

---

## Part 6 · `have_show`

Statement: from `h1 : a ≤ b` and `h2 : b ≤ c`, prove `a ≤ c + 1`. Name the intermediate fact `a ≤ c` with
`have`, then state the final type with `show … from`.

**R9 · `have h : T := e` then the rest on the next line** changes the **context**: `h : T` is added for the
rest, whose expected type is unchanged. `;` instead of the line break also works. It is the term form of the
tactic `have` (E021). Placeholders: `{A B C : Prop} (ha : A) (f : A → B)`.

| Before | After `have hb : B := f ha` then `_` |
|---|---|
| `ha : A`, `f : A → B` · expects `C` | `hb : B` · the hole expects `C` |

**R10 · `Nat.le_trans`** **closes** the hole given both arguments. The lemma is
`Nat.le_trans : n ≤ m → m ≤ k → n ≤ k` (`n m k` implicit, read off the arguments). Placeholders:
`(x y z : Nat) (hxy : x ≤ y)`.

| Before | After `Nat.le_trans hxy _` |
|---|---|
| `hxy : x ≤ y` · expects `x ≤ z` | the hole expects `y ≤ z` |

**R11 · `show T from e`** changes the **goal**: the expected type is replaced by the `T` you write, which must
agree with it by computation; then `e` is checked against `T`. Use it to say, in the source, what a term
proves. `m.succ` and `m + 1` agree. Tactic form: `show T` then `exact e` (E021). Placeholders: `(n m : Nat)`.

| Before | After `show n ≤ m.succ from _` |
|---|---|
| expects `n ≤ m + 1` | the hole expects `n ≤ m.succ` |

**R12 · `Nat.le_succ_of_le`** changes the **goal**: `Nat.le_succ_of_le : n ≤ m → n ≤ m.succ`, so a hole that
expects `x ≤ y + 1` (or `x ≤ y.succ`) gets an argument that expects `x ≤ y`. Placeholders: `(x y : Nat)`.

| Before | After `Nat.le_succ_of_le _` |
|---|---|
| expects `x ≤ y + 1` | the hole expects `x ≤ y` |

**W4.** `x ≤ y + 2` from `h : x ≤ y`: `have h1 : x ≤ y + 1 := Nat.le_succ_of_le h` (R9, R12), then
`show x ≤ y + 2 from Nat.le_succ_of_le h1` (R11, R12).

---

## Traps

- `by` is banned on purpose, comments excepted: every proof must be a term. Each theorem targets one
  shorthand: dot notation (`or_mp`, `iff_chain`), `‹P›` (`anon_hyp`), `▸` (`subst_term`), `let`
  (`exists_let`), `have` / `show` (`have_show`).
- Dot notation needs the head of the type: `h.mp` works for `h : A ↔ B`, and `h.elim` for `h : A ∨ B`. For
  `hqr : Q → R` there is no head to look up; pass `hqr` as it is.
- `‹T›` needs a hypothesis whose type is exactly `T`. `‹P›` does not find a proof of `P` hidden inside
  `h : P ∧ Q`.
- `h ▸ rfl` relies on the expected type being known. Inside a bigger term where it is not, give it:
  `(h ▸ rfl : m * m = 9)` (W2), or use `show` (R11).
- A `let` or `have` line and the line after it form one term: put the rest on the next line at the same
  indentation as `let` / `have` (or after `;` on the same line).
- `_` in a pattern hides the hypothesis (`left✝`): name it if you need it later.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| use `h : A ∨ B` | `h.elim (fun ha => …) (fun hb => …)` or `h.elim f g` | R1 |
| use `h : A ↔ B` forwards / backwards | `h.mp` / `h.mpr` | R2 |
| a hypothesis by its type | `‹A›` | R3 |
| `A ↔ B`, `B ↔ C` ⟹ `A ↔ C` | `h1.trans h2` | R4 |
| a closed computation `2 + 2 = 4` | `rfl` | R5 |
| substitute an equation into the expected type | `h ▸ e` | R6 |
| take `h : ∃ x, p x ∧ r x` apart | `let ⟨x, hp, hr⟩ := h` | R7 |
| prove `∃ x, p x` | `⟨w, hw⟩` | R8 |
| an intermediate fact | `have h : T := e` (next line: the rest) | R9 |
| `n ≤ m`, `m ≤ k` ⟹ `n ≤ k` | `Nat.le_trans h1 h2` | R10 |
| say what the term proves | `show T from e` | R11 |
| `n ≤ m` ⟹ `n ≤ m + 1` | `Nat.le_succ_of_le h` | R12 |
| see what a spot expects | write `_` there and read the error | |
