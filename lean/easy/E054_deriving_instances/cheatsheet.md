# E054 · Deriving instances: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033), in particular `decide` (E001), `rw` (E009), `simp` (E010),
`unfold` (E012, E030), `cases` (E016, E018), structures and fields (E017), instances and type classes
(E019), distinct constructors (E029), `<;>` (E031). **New here:** the `deriving` clause; the classes
`DecidableEq`, `BEq`, `LawfulBEq`, `Repr`; the `Bool` tests `a == b` and `decide p`; the core lemmas
`beq_iff_eq` and `decide_eq_true_iff`; `simp_all`. No Mathlib.

## How to read an entry

Each entry is one tactic, one term, or one lemma used with `rw`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before
and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Bool → Prop`, `P : Prop → Prop`, …). The step changes only the part
  inside `P (…)`, wherever it sits in a larger goal.
- "no goals" means the tactic closed the goal.
- `{α : Type} [DecidableEq α]` is any type with decidable equality: `Nat`, `Bool`, `Int`, `String`, and
  every type with `deriving DecidableEq` (the exercise's `Suit` and `Card`).
- All concrete entries use the guide's own enumeration `Color` (`red | green | blue`) and structure `Pen`
  (`width : Nat`, `color : Color`), both `deriving DecidableEq, Repr`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Deriving in one paragraph

`inductive T … deriving C₁, C₂` (or `structure`) asks Lean to *write* instances of the classes `Cᵢ` for `T`.
`DecidableEq T` is a function deciding `a = b` for any `a b : T`: for an enumeration it compares
constructors, for a structure it compares the fields one by one, so every field type needs `DecidableEq`
too (`Nat` and `Suit` have it). From any `DecidableEq T`, core supplies two more instances: `BEq T`, whose
`a == b` is `decide (a = b)` (so the two are equal by `rfl`), and `LawfulBEq T`, the promise that `==`
agrees with `=`. `Repr T` is a printer: `#eval (Suit.hearts : Suit)` shows `E054.Suit.hearts`. No proof in
this exercise needs `Repr`; it is there so that `#eval` on your values works. An instance can also be
derived after the declaration: `deriving instance Inhabited for Color` (then `default : Color` is
`Color.red`, the first constructor).

## Reading the goals

| You see | It means |
|---|---|
| `a == b` | `BEq.beq a b : Bool`, the Boolean equality test (R1) |
| `(a == b) = true` | the `Prop` "the test returned `true`"; a `Bool` used as a statement always shows `= true` |
| `decide p` | the `Bool` that is `true` exactly when the decidable `Prop` `p` holds (R2) |
| `inst✝ : DecidableEq α` | an anonymous instance argument; `✝` marks a name you cannot type |
| `{ width := 2, color := Color.red }` | the structure value `Pen.mk 2 Color.red` (`⟨2, .red⟩`) |
| `.red`, `.hearts` in source | `Color.red`, `Suit.hearts`: the type is read off the expected type |
| `a.suit` | `Card.suit a`, the `suit` field of `a` |
| `case red` | the goal `cases c` made for the constructor `Color.red` |
| `x ≠ y` | `¬ (x = y)`, i.e. `x = y → False` |

---

## Part 1 · `sameSuit` (definition body)

Statement: `sameSuit (a b : Card) : Bool`. You write the body: `true` exactly when the two cards have the
same `suit` field (the rank is ignored). `sameSuit_iff` pins down the meaning.

**R1 · `a == b`** is a **term**: the Boolean test from `BEq`, which `DecidableEq` supplies. As a tactic,
`exact a == b` **closes** a hole of type `Bool`. Placeholders: `{α : Type} [DecidableEq α] (a b : α)`.
In the exercise `α` is `Suit`, and `a`, `b` are the fields `a.suit`, `b.suit`.

| Before | After |
|---|---|
| `a b : α ⊢ Bool` | no goals |

**R2 · `decide (a = b)`** is a **term**: the decidable `Prop` `a = b` turned into a `Bool`. It is the same
function as R1 (`(a == b) = decide (a = b)` holds by `rfl`); the two bodies need different lemmas in Part 2
(R4 versus R5). Placeholders: `{α : Type} [DecidableEq α] (a b : α)`.

| Before | After |
|---|---|
| `a b : α ⊢ Bool` | no goals |

## Part 2 · `sameSuit_iff`

Statement: `sameSuit a b = true ↔ a.suit = b.suit`: the `Bool` test returns `true` exactly when the
suits are equal. Unfold `sameSuit` (R3), then the library iff for your body (R4 for `==`, R5 for
`decide`); or skip the unfold, since `exact` sees through definitions (R6).

**R3 · `unfold isRed`** changes the **goal**: the defined name, applied to its arguments, is replaced by its
body. In the exercise: `unfold sameSuit`. Placeholders: `(c : Color) (P : Bool → Prop)`, with
`def isRed (c : Color) : Bool := c == .red`.

| Before | After |
|---|---|
| `⊢ P (isRed c)` | `⊢ P (c == Color.red)` |

**R4 · `rw [beq_iff_eq]`** changes the **goal**. The lemma is
`beq_iff_eq {α} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = true ↔ a = b`; `rw` with an `↔` replaces the
left `Prop` by the right one. Placeholders: `{α : Type} [DecidableEq α] (a b : α) (P : Prop → Prop)`; the
`BEq` and `LawfulBEq` instances come from `DecidableEq`. If the goal becomes `X ↔ X`, `rw` closes it by itself.

| Before | After |
|---|---|
| `⊢ P ((a == b) = true)` | `⊢ P (a = b)` |

**R5 · `rw [decide_eq_true_iff]`** changes the **goal**. The lemma is
`decide_eq_true_iff {p : Prop} [Decidable p] : decide p = true ↔ p`. Use it if your body is `decide (…)`.
Placeholders: `(p : Prop) [Decidable p] (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (decide p = true)` | `⊢ P p` |

**R6 · `exact beq_iff_eq` through a definition** **closes** the goal (for a `decide` body:
`exact decide_eq_true_iff`). `exact` compares types up to unfolding
`def`s, so `isRed c = true ↔ c = Color.red` is accepted as `(c == Color.red) = true ↔ c = Color.red`, an
instance of R4's lemma. The same works as a term-mode proof, with no `by`. Placeholders: `(c : Color)`.
Alternative: `simp [isRed]` (`simp` knows `beq_iff_eq`).

| Before | After |
|---|---|
| `⊢ isRed c = true ↔ c = Color.red` | no goals |

**W1: R3 then R4 by hand** on `Pen.isThin p := p.width == 1` (the last `rw` closes `X ↔ X` itself):

```lean-goal
⊢ p.isThin = true ↔ p.width = 1
⊢ (p.width == 1) = true ↔ p.width = 1
```

**W2: the `decide` body** `Pen.isThin' p := decide (p.width = 1)`: R3, then R5.

```lean-goal
⊢ p.isThin' = true ↔ p.width = 1
⊢ decide (p.width = 1) = true ↔ p.width = 1
```

## Part 3 · `cards_ne`

Statement: `{ rank := 3, suit := .hearts } ≠ { rank := 3, suit := .spades }`: two concrete cards with the
same rank and different suits are different. Both sides are closed values, so the derived `DecidableEq Card`
can compute the answer (R7).

**R7 · `decide`** **closes** `x ≠ y` when `x`, `y` are closed values of a type with `DecidableEq`. `≠` is
`¬ (x = y)`, decidable because `x = y` is; `decide` runs the derived test, which compares the fields one by
one. No placeholders: `decide` works only on terms without variables.

| Before | After |
|---|---|
| `⊢ { width := 2, color := Color.red } ≠ { width := 2, color := Color.green }` | no goals |

**W3:** `decide` also evaluates a `Bool` test on a closed value: `(Pen.mk 1 .red).isThin = true`.

## Part 4 · `suit_cases`

Statement: for `s : Suit` with `h1 : s ≠ .hearts` and `h2 : s ≠ .spades`, `s = .clubs`. `s` is a variable,
so `decide` does not apply (Traps). Split `s` into its three constructors (R8); in every case some
hypothesis or the goal is decided by the constructors alone, and `simp_all` finishes (R9, R10). Run it on
all three cases at once with `<;>`.

**R8 · `cases c`** changes the **goal list**: one goal per constructor of the enumeration, with `c` replaced
by that constructor in the goal **and in every hypothesis**. Placeholders:
`(P : Color → Prop) (c : Color) (h : c ≠ Color.red)`.

| Before | After |
|---|---|
| `h : c ≠ Color.red ⊢ P c` | `h : Color.red ≠ Color.red ⊢ P Color.red`, `h : Color.green ≠ Color.red ⊢ P Color.green`, `h : Color.blue ≠ Color.red ⊢ P Color.blue` |

**R9 · `simp_all`** **closes** the goal when a hypothesis simplifies to `False`, as `x ≠ x` does
(`x = x` is `True`, so `¬ True` is `False`). `simp_all` simplifies every hypothesis and the goal, each using
the others. Placeholders: `(G : Prop)`. In the exercise this is the `hearts` case (`h1`) and the `spades`
case (`h2`).

| Before | After |
|---|---|
| `h : Color.green ≠ Color.green ⊢ G` | no goals |

**R10 · `simp` on a constructor equation** changes the **goal**: `Color.green = Color.blue` is `False`,
because distinct constructors are never equal (the simproc `reduceCtorEq`). Here `P ∨ False` then becomes
`P`. Placeholders: `(P : Prop)`. Inside `simp_all` the same step turns a hypothesis `Color.green ≠ Color.red`
into `True` (it is dropped). A goal `x = x`, such as `Suit.clubs = Suit.clubs`, is a different rule
(`eq_self`: `x = x` simplifies to `True`), also applied by `simp`/`simp_all`; it closes the `clubs` case.

| Before | After |
|---|---|
| `⊢ P ∨ Color.green = Color.blue` | `⊢ P` |

**W4:** `(c : Color) (h : c ≠ .blue) : c = .red ∨ c = .green` by `cases c <;> simp_all`: in `red` and `green`
one side of the `∨` is `x = x` (`True`) and the other a constructor equation (`False`, R10), in `blue` the
hypothesis is `Color.blue ≠ Color.blue` (R9).

---

## Traps

- `decide` needs a **closed** goal. On `suit_cases` it fails with "Expected type must not contain free
  variables". `decide +revert` then asks for `Decidable (∀ s : Suit, …)`, which core cannot build: a `∀`
  over a type is decidable only with a finite enumeration of it (`Fintype`, Mathlib). Use `cases s` (R8).
- `deriving DecidableEq` on a structure requires `DecidableEq` for every field type. `Card` can derive it
  because `Suit`, declared before it, derives it too.
- `sameSuit a b = true` is a `Prop`; `sameSuit a b` alone is a `Bool`. A `Bool` used as a statement is
  coerced to `b = true`, which is why the goals show `= true`.
- `beq_iff_eq` is for `==`, `decide_eq_true_iff` for `decide (…)`. With the wrong one, `rw` fails ("did not
  find instance of the pattern"); `exact` fails with a type mismatch. `simp [sameSuit]` handles both.
- `sameSuit` must ignore `rank`. `a == b` (whole cards) type-checks but makes `sameSuit_iff` false.
- `t1; t2` after `cases s` runs `t2` on the first case only; use `cases s <;> simp_all`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| derive equality test and printer | `deriving DecidableEq, Repr` after the type | (paragraph) |
| `Bool` equality test | `a == b` | R1 |
| a decidable `Prop` as a `Bool` | `decide (a = b)` | R2 |
| replace a `def` by its body | `unfold f` | R3 |
| `(a == b) = true` ↔ `a = b` | `beq_iff_eq` | R4 |
| `decide p = true` ↔ `p` | `decide_eq_true_iff` | R5 |
| close an iff up to unfolding | `exact beq_iff_eq` (or `simp [f]`) | R6 |
| closed (in)equality of derived data | `decide` | R7 |
| symbolic enumeration value | `cases s` | R8 |
| finish each case | `<;> simp_all` | R9, R10 |
| print a value | `#eval v` (needs `Repr`) | (paragraph) |
| see the state | infoview | |
