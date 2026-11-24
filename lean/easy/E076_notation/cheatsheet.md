# E076 · Notation: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `rw`, `simp`, `decide`, `exact`, `first | t₁ | t₂`
(E031), type ascription `(e : T)`. **New here:** the commands `infixl`, `infixr` and `notation`, which
add syntax for an existing function; precedence levels and associativity; the option
`pp.notation` for seeing the plain term behind notation.

## How to read an entry

Each entry is one command, tactic, or lemma. It says what changes (**goal**, **context**, **goal list**,
or, for a notation command, the **parse**: how Lean groups what you type), lists the placeholders with
their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : Nat → Prop`). The step changes only the part inside `P (…)`.
- A notation command has no proof state of its own. Its entry shows its effect through one `rw [e]`
  with `e : <subterm> = d`: `rw` only finds `<subterm>` if the parse made it a subterm, so the after
  state shows the grouping. If the grouping were different, `rw` would fail with "did not find instance
  of the pattern".
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `infixl:p " op " => f` | `a op b` is `f a b`; a chain `a op b op c` groups left, `(a op b) op c` |
| `infixr:p " op " => f` | the same, but a chain groups right, `a op (b op c)` |
| the level `p` | binding strength: higher binds tighter. Core levels: `=` 50, `+ -` 65, `* / %` 70, `^` 75 (right-assoc) |
| `infixl:p` in detail | `notation:p lhs:p " op " rhs:(p+1)`: the right argument must bind strictly tighter than `p` |
| `infixr:p` in detail | `notation:p lhs:(p+1) " op " rhs:p`: the right argument may be anything at level `p`, e.g. `b + c` when `p = 65` |
| `notation "⟪" a "⟫" => f a` | mixfix: any tokens around the arguments; the right side is any term in them |
| `a ⬝ b` | the exercise's `dot a b` (frozen: `infixl:70`, so it binds like `*`) |
| `a ⬝ a` where you wrote `‖a‖²` | `‖a‖²` expands to `dot a a`; a notation that repeats an argument is never printed back, so the infoview shows the `⬝` form (R6: `⌈x⌉²` shows as `x.mul x`) |
| `x.add y`, `x.mul x` | field notation for `Nat.add x y`, `Nat.mul x x` |
| `HAdd.hAdd a b`, `HMul.hMul a b`, `Eq x y` | `a + b`, `a * b`, `x = y` with notation printing switched off (R5); your `⊖` shows as `x.sub y` (`Nat.sub x y`) |
| `a.fst`, `a.snd` | `a.1`, `a.2` for a pair `a : Nat × Nat` |
| `10 ⊖ 3 ⊖ 2` | `Nat.sub` applied as your `⊖` line says; `Nat.sub a b` is truncated subtraction, `a - b` in `Nat` |

The frozen proofs have the shape `first | exact (by decide : <goal in your notation>) | sorry`. The
ascription `(by decide : T)` parses `T` with your notation and proves it by evaluation; `exact` then
needs `T` to be the theorem's statement up to unfolding. If `T` is false or means something else, the
first branch fails and `first` falls back to `sorry`, and `./check` lists that theorem as still open.

---

## Part 1 · the `⊖` line (`sub_left`, `sub_prec`, `sub_add_mix`, `add_sub_mix`, `sub_sub_eq`)

Make `a ⊖ b` mean `Nat.sub a b` with the associativity and level of `-`, so that `10 ⊖ 3 ⊖ 2 = 5`,
`10 ⊖ 2 * 3 = 4`, `10 ⊖ 2 + 3 = 11`, `10 + 2 ⊖ 3 = 9`, and `a ⊖ b ⊖ c` is the term `a - b - c`.

**R1 · `infixl:65 " +' " => Nat.add`** changes the **parse**: `a +' b` means `Nat.add a b`, and a chain groups
left, so `a +' b` is a subterm of `a +' b +' c`. Placeholders: `(a b c d : Nat) (e : a +' b = d)`.

| Before | After `rw [e]` |
|---|---|
| `⊢ P (a +' b +' c)` | `⊢ P (d +' c)` |

**R2 · `infixr:75 " ^' " => Nat.pow`** changes the **parse**: a chain groups right, so `b ^' c` is the
subterm. This is the grouping the stub's `⊖` line has. Placeholders: `(a b c d : Nat) (e : b ^' c = d)`.

| Before | After `rw [e]` |
|---|---|
| `⊢ P (a ^' b ^' c)` | `⊢ P (a ^' d)` |

**R3 · level 65 against `*` at 70** changes the **parse**: `*` binds tighter, so `a +' b * c` is
`a +' (b * c)`. With a level above 70 (the stub's 75) it would be `(a +' b) * c`. Placeholders:
`(a b c d : Nat) (e : b * c = d)`.

| Before | After `rw [e]` |
|---|---|
| `⊢ P (a +' b * c)` | `⊢ P (a +' d)` |

**R4 · same level as `+` (65), `infixl`** changes the **parse**: `+`, `-` and `+'` are all `infixl:65`, so a
mixed chain groups left whichever operator comes first. Placeholders:
`(a b c d₁ d₂ : Nat) (e₁ : a + b = d₁) (e₂ : a +' b = d₂)`, `(P : Nat → Nat → Prop)`.

| Before | After `rw [e₁, e₂]` |
|---|---|
| `⊢ P (a + b +' c) (a +' b + c)` | `⊢ P (d₁ +' c) (d₂ + c)` |

**R5 · `set_option pp.notation false in`** (before a command, on its own line) changes the **display** only:
the infoview prints the plain term, with field notation `x.add y` for `Nat.add x y`. Use it in a scratch
`example` to see how your `⊖` parses; `#eval 10 ⊖ 3 ⊖ 2` shows what it computes.
Placeholders: `(a b c : Nat)`.

| Before (R1, notation printed) | After (`pp.notation false`) |
|---|---|
| `⊢ P (a +' b +' c)` | `⊢ P ((a.add b).add c)` |

**W1 · `infixr:65 " -' " => Nat.sub`: right level, wrong associativity.** `infixr:65` lets its right argument
be `b + c`, so `a -' b + c` is `a -' (b + c)`. For `10 ⊖ 2 + 3` that is `10 - 5 = 5`, not `11`, so
`sub_add_mix` fails. Worse, `10 + 2 ⊖ 3` does not parse at all ("unexpected token"): `infixr:65` needs a left
argument at level 66, and `10 + 2` is at level 65. Placeholders: `(a b c d : Nat) (e : b + c = d)`.

| Before | After `rw [e]` |
|---|---|
| `⊢ P (a -' b + c)` | `⊢ P (a -' d)` |

---

## Part 2 · the `‖a‖²` line (`norm_sq_ex`, `norm_sq_eq`)

Make `‖a‖²` mean `dot a a`, so that `‖(3, 4)‖² = 25` by `decide` and `‖a‖² = a.1 * a.1 + a.2 * a.2` by `rfl`.

**R6 · `notation "⌈" a "⌉²" => Nat.mul a a`** changes the **parse**: `⌈x⌉²` is the term `Nat.mul x x`. The
right-hand side may use an argument any number of times. Because `a` is repeated, Lean does not print
the notation back: the goal shows `x.mul x`. Placeholders: `(x d : Nat) (e : Nat.mul x x = d)`.

| Before | After `rw [e]` |
|---|---|
| `⊢ P (x.mul x)` | `⊢ P d` |

---

## Part 3 · `dot_comm`

Statement: `a ⬝ b = b ⬝ a` for pairs `a b : Nat × Nat`, where `a ⬝ b` is `dot a b = a.1 * b.1 + a.2 * b.2`.

**R7 · `simp only [cross]`** (or `unfold cross`) changes the **goal**: a defined function behind an infix is
replaced by its body. Notation is only syntax, so the `⊗` disappears with `cross`. Placeholders:
`def cross (a b : Nat × Nat) : Nat := a.1 * b.2 + a.2 * b.1` with `infixl:70 " ⊗ " => cross`,
`(a b : Nat × Nat)`.

| Before | After |
|---|---|
| `⊢ P (a ⊗ b)` | `⊢ P (a.fst * b.snd + a.snd * b.fst)` |

**R8 · `rw [Nat.mul_comm]`** changes the **goal**. The lemma is `Nat.mul_comm : ∀ (n m : Nat), n * m = m * n`.
`rw` rewrites the first product it finds; give arguments (`Nat.mul_comm a b`) to pick one. In
`simp [Nat.mul_comm]` it is a permutation lemma: `simp` rewrites with it only when the result is smaller
in an internal term order, so it cannot loop and puts both sides' products in the same order.
Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `⊢ P (a * b)` | `⊢ P (b * a)` |

**W2 · unfold, then commute.** On `a ⊗ b = b ⊗ a`, R7 gives

```lean-goal
⊢ a.fst * b.snd + a.snd * b.fst = b.fst * a.snd + b.snd * a.fst
```

and `simp [Nat.mul_comm, Nat.add_comm]` closes it (this one also needs the sums reordered). `simp [cross, …]`
does both steps in one call.

---

## Traps

- Edit the existing `⊖` and `‖‖²` lines. A second declaration of the same token makes every use ambiguous
  (Lean reports "ambiguous, possible interpretations").
- `infixr:65` has the level of `-` but parses `10 ⊖ 2 + 3` as `10 ⊖ (2 + 3)` and rejects `10 + 2 ⊖ 3` with a
  parse error that breaks the whole file (W1). Both associativity and level must match `-`.
- A level between 65 and 70 (`infixl:66`) passes `sub_left` and `sub_prec` but makes `⊖` bind tighter
  than `+`: `10 + 2 ⊖ 3` becomes `10 + (2 ⊖ 3)`, which is `10` in `Nat`, and `add_sub_mix` fails.
- `Nat` subtraction truncates at 0 (`2 - 3 = 0`), so a wrong grouping can still produce a plausible number.
- The bans (`macro_rules`, `macro`, `syntax`, `elab`, `elab_rules`, `import`) stop a tactic macro from
  redefining the `sorry` fallback in the frozen proofs. This problem is about term notation only.
- `‖a‖²` shows up as `a ⬝ a` in the infoview (R6). That is expected, not a sign your line is wrong.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| left-assoc infix at level `p` | `infixl:p " op " => f` | R1 |
| right-assoc infix | `infixr:p " op " => f` | R2 |
| bind looser than `*` | a level below 70 | R3 |
| bind exactly like `+` / `-` | `infixl:65` | R4 |
| see the plain term | `set_option pp.notation false in` before an `example` | R5 |
| see what it computes | `#eval 10 ⊖ 3 ⊖ 2` | R5 |
| mixfix, argument used twice | `notation "⌈" a "⌉²" => f a a` | R6 |
| remove an infix in a proof | `simp only [f]` / `unfold f` | R7 |
| swap a product | `rw [Nat.mul_comm]`, or `simp [Nat.mul_comm]` | R8 |
| unfold and commute in one go | `simp [f, Nat.mul_comm]` | R7, R8 |
