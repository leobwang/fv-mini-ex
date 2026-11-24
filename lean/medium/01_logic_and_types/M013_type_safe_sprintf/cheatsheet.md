# M013 · Type-safe sprintf: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rfl`, `have`, inductive types,
definitions by pattern matching, `induction … with`, `cases`, `obtain`, `simp`. **New here:** a *type*
computed by recursion on a value (`Fmt.type fs : Type`), writing a function whose result type is such a
computed type, `fun` with several pattern-matched arguments, definitional unfolding of types, case
splits on arguments whose type is computed (`Unit` or a pair), and generalising an accumulator before
induction. No Mathlib.

## How to read an entry

Each entry is one tactic, one term construct or one lemma used with `rw`/`simp`. It says what changes
(**goal**, **context**, or **goal list**), lists the placeholders with their types, then shows the proof
state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : String → Prop`, `P : Tup 0 → Prop`, …). The step changes only the
  part inside `P (…)`. `Q` is an arbitrary predicate.
- Definitions are not tactic proofs, but each arm of a definition has an expected type, and Lean
  shows it as a goal when the arm is a hole `?_` (R1). So the definition entries use goals too.
- The entries use the guide's toy family, not `Fmt`: `Arity n` is the type of a function taking `n`
  strings and returning a `String` (`Arity 0 = String`, `Arity (n + 1) = String → Arity n`), and
  `Tup n` is a tuple of `n` strings (`Tup 0 = Unit`, `Tup (n + 1) = String × Tup n`). `call n f t`
  feeds the tuple `t` to `f`, `concat n t` joins its strings. They mirror the exercise's `Fmt.type`,
  `Fmt.Args`, `Fmt.apply` and `render`, with the index a number instead of a format list.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## The objects

- `Fmt`: a directive, `lit s` (literal text `s`), `nat` (a hole for a `Nat`) or `str` (a hole for a
  `String`). A format is `fs : List Fmt`, e.g. `[.lit "x=", .nat, .lit ", s=", .str]`.
- `Fmt.type fs : Type`: one argument per hole, then `String`. `Fmt.type [.lit "x=", .nat] = (Nat → String)`
  by computation: `lit` contributes nothing, `nat` a `Nat →`, `str` a `String →`.
- `Fmt.Args fs : Type`: the same arguments as a tuple ending in `()`: `Fmt.Args [.nat, .str] = Nat × (String × Unit)`.
- `Fmt.apply fs f a : String`: call the curried `f : Fmt.type fs` on the tuple `a : Fmt.Args fs`.
- `render fs a : String`: the specification, the output written piece by piece.
- `sprintfAux fs acc : Fmt.type fs`: yours to write. `acc` is the text produced so far.
  `sprintf fs := sprintfAux fs ""`. Then `sprintf [.lit "x=", .nat, .lit ", s=", .str] 3 "ab" = "x=3, s=ab"`,
  and `sprintf [.nat] "ab"` is a type error: the type of `sprintf` depends on the format.
- The theorem: `Fmt.apply fs (sprintf fs) args = render fs args` for every format and every argument tuple.

## Reading the goals

| You see | It means |
|---|---|
| `Fmt.type fs`, `Arity n` | a type computed from a value; Lean reduces it when it needs to see a `→` or `×` |
| `Type` | the type of types: `Fmt.type : List Fmt → Type` returns a type such as `String` or `Nat → String` |
| `(fs : List Fmt) → Fmt.type fs → String` | a *dependent* function type: the type of the second argument mentions the first argument `fs`. `A → B` is the special case where `B` does not mention the argument |
| `A × B` | the type of pairs `(a, b)` with `a : A`, `b : B`; `×` groups to the right, so `Nat × String × Unit` is `Nat × (String × Unit)` |
| `Unit`, `()` | the type with exactly one value `()`; it ends every argument tuple |
| `.lit s`, `.nat` | constructors of `Fmt` with the type name left out (`Fmt.lit s`, `Fmt.nat`); Lean fills it in from the expected type |
| `.lit _` (in a pattern) | `_` matches anything and gives it no name |
| `Fmt.lit s :: fs` | the list with head `.lit s` and tail `fs` (written `.lit s :: fs` in the source) |
| `toString n` | the decimal digits of `n : Nat` as a `String` (instance `ToString Nat`) |
| `n.repr` | `Nat.repr n`, the same string; `simp` rewrites `toString n` into it (R15) |
| `s₁ ++ s₂ ++ s₃` | `(s₁ ++ s₂) ++ s₃`: `++` groups to the left |
| `PUnit.unit` | the value `()` of `Unit` (R8) |
| `(n, a)` | a pair; `(a, b, ())` is `(a, (b, ()))` |
| `fs✝`, `args✝` | the theorem's own `fs`, `args`, shadowed by the `∀ fs … args` of your `have` (inaccessible names) |
| `case refine_1`, `case refine_2` | the arms of a `refine fun \| … => ?_` in the guide (R1) |
| `case nil`, `case cons`, `case cons.lit` | goals after `induction fs` and then `cases f` |
| `case nil.unit` | the `nil` goal after `cases args` (the one constructor of `Unit`) |

---

## Part 1 · `sprintfAux`

Statement: write `sprintfAux : (fs : List Fmt) → String → Fmt.type fs`. The body goes after the frozen
`:=`, so it is a term: `fun | [], acc => … | .lit s :: fs, acc => … | .nat :: fs, acc => … | .str :: fs, acc => …`.
Each arm's result type is `Fmt.type` of that arm's list, which reduces to `String`, `Fmt.type fs`,
`Nat → Fmt.type fs` and `String → Fmt.type fs`.

**R1 · `fun | p₁, q₁ => e₁ | p₂, q₂ => e₂`** changes the **goal list**: one goal per arm. A `fun` with `|`
arms matches on all its arguments at once; the patterns of an arm are separated by `,`, and the arms must
cover every case. In each arm the expected type is the declared result type with the patterns plugged
in. `refine` with `?_` holes shows those types as goals. Placeholders:
`(h0 : String → Arity 0) (h1 : (n : Nat) → String → Arity (n + 1))`.

| Before | After |
|---|---|
| `⊢ (n : Nat) → String → Arity n` | `acc : String ⊢ Arity 0`, `n : Nat, acc : String ⊢ Arity (n + 1)` |

**R2 · `show T'`** changes the **goal**: it replaces the goal by a type that it reduces to, and fails if
they do not agree. `Arity (n + 1)` reduces by the second equation of `Arity` to `String → Arity n`; any
term of the reduced type is accepted as a term of the original one (*definitional equality*). Use it, or
hover, to see what an arm of `sprintfAux` must produce. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ Arity (n + 1)` | `⊢ String → Arity n` |

**R3 · `exact acc`** **closes** a goal whose type reduces to the type of `acc`: `Arity 0` is `String`. In
the exercise: the `[]` arm returns the accumulator, and the `.lit s` arm returns a recursive call of
type `Fmt.type fs`, which is what `Fmt.type (.lit s :: fs)` reduces to. Placeholders: `(acc : String)`.

| Before | After |
|---|---|
| `acc : String ⊢ Arity 0` | no goals |

**R4 · `intro s`** changes the **goal and the context**; as a term it is `fun s => e`. `intro` reduces the
goal until it sees the `→`. In the exercise the `.nat` arm has type `Fmt.type (.nat :: fs)`, which is
`Nat → Fmt.type fs`, so the arm is `fun n => …` with `… : Fmt.type fs`. Placeholders: `(n : Nat)`,
`k : String → Arity n`.

| Before | After |
|---|---|
| `⊢ Arity (n + 1)` | `s : String ⊢ Arity n` |

**R5 · `toString` and `++`** build the new accumulator: `acc ++ s` appends a literal, `acc ++ toString n`
the digits of a number. Both compute on literals, so `rfl` **closes** a goal that evaluates.

| Before | After |
|---|---|
| `⊢ "x=" ++ toString 42 = "x=42"` | no goals |

**W1** puts R1–R5 together on the toy family:
`catAux : (n : Nat) → String → Arity n := fun | 0, acc => acc | n + 1, acc => fun s => catAux n (acc ++ s)`.
The step arm calls `catAux` on the smaller index: *structural recursion*, which Lean accepts with no
termination proof. `sprintfAux` recurses on the tail `fs` in the same way. Check your definition with
`rfl` on a concrete format, as W1 does (`call 2 (catAux 2 "<") ("a", "b", ()) = "<ab"`).

---

## Part 2 · `sprintf_correct`

Statement: `Fmt.apply fs (sprintf fs) args = render fs args`. Since `sprintf fs = sprintfAux fs ""`, the
accumulator starts at `""`, but after one step it is `"" ++ s`, so induction on the statement as given
gives an IH about `""` that does not apply. Prove the general fact for every `acc` first.

**R6 · `have key : ∀ m acc, Q m acc := …`** changes the **context**: it adds the general statement. In
the exercise it is the milestone `∀ fs acc args, Fmt.apply fs (sprintfAux fs acc) args = acc ++ render fs args`,
proved by `:= by …` (indent its proof further than `have`); at the end, `key` at `acc := ""` plus R14
gives the theorem. Placeholders: `(Q : Nat → String → Prop) (n : Nat)`.

| Before | After |
|---|---|
| `⊢ Q n ""` | `⊢ Q n ""`, with `key : ∀ (m : Nat) (acc : String), Q m acc` in the context |

**R7 · `intro xs`, then `induction xs with | nil => … | cons x xs ih => …`** changes the **goal list and
the context**. Introduce only the list: the remaining `∀ acc` stays in the goal, so `ih` is `∀ acc, …`
and can be used at the new accumulator `acc ++ s`. (Introducing `acc` before `induction` gives an `ih`
about that one `acc`.) Placeholders: `{α : Type} (Q : List α → String → Prop)`.

| Before | After `intro xs` | After `induction xs with …` |
|---|---|---|
| `⊢ ∀ (xs : List α) (acc : String), Q xs acc` | `xs : List α ⊢ ∀ (acc : String), Q xs acc` | `⊢ ∀ (acc : String), Q [] acc`, and `x : α, xs : List α ⊢ ∀ (acc : String), Q (x :: xs) acc` with `ih : ∀ (acc : String), Q xs acc` in the context |

In each case, `intro acc args` then gives names to the rest.

**R8 · `cases t`** on `t : Tup 0` changes the **context and the goal**: `Tup 0` reduces to `Unit`, whose
only value is `()`, printed `PUnit.unit`; `t` is replaced by it. Only then can the equations
`call 0 r () = r`, `concat 0 () = ""` fire. In the exercise: `cases args` with `args : Fmt.Args []`.
Placeholders: `(P : Tup 0 → Prop) (t : Tup 0)`.

| Before | After |
|---|---|
| `t : Tup 0 ⊢ P t` | `⊢ P PUnit.unit` |

**R9 · `cases o with | none => … | some a => …`** changes the **goal list**: one goal per constructor of the
head, with no induction hypothesis. In the exercise it is `cases f with | lit s => … | nat => … | str => …`
on the head directive `f : Fmt`; `args : Fmt.Args (f :: fs)` changes type with it, which is why you
`intro acc args` first. Placeholders: `{α : Type} (P : Option α → Prop) (o : Option α)`.

| Before | After |
|---|---|
| `o : Option α ⊢ P o` | `⊢ P none`, `a : α ⊢ P (some a)` |

**R10 · `obtain ⟨s, u⟩ := t`** on `t : Tup (n + 1)` changes the **context**: `Tup (n + 1)` reduces to
`String × Tup n`, so `t` is a pair and is replaced by its components. In the exercise: `args` in the `nat`
and `str` cases (`Fmt.Args (.nat :: fs)` is `Nat × Fmt.Args fs`). The `lit` case needs no split:
`Fmt.Args (.lit s :: fs)` is just `Fmt.Args fs`. Placeholders: `(n : Nat) (P : Tup (n + 1) → Prop)`.

| Before | After |
|---|---|
| `t : Tup (n + 1) ⊢ P t` | `s : String, u : Tup n ⊢ P (s, u)` |

**R11 · `simp only [call]`** changes the **goal**: it applies the defining equation of `call` whose
patterns match, here `call (n + 1) f (s, t) = call n (f s) t`. It needs the pair `(s, t)` (or `()`)
literally in the goal: that is what R8 and R10 are for. In the exercise: `simp [sprintfAux, Fmt.apply, render]`.
Placeholders: `(n : Nat) (f : Arity (n + 1)) (s : String) (t : Tup n) (P : String → Prop)`.

| Before | After |
|---|---|
| `⊢ P (call (n + 1) f (s, t))` | `⊢ P (call n (f s) t)` |

**R12 · `simp only [ih]`** with `ih : ∀ acc m, F acc m = acc ++ G m` changes the **goal**: `simp` and `rw`
instantiate the `∀` to match, here `acc := a ++ "x"`. That is why R7 keeps `ih` general.
Placeholders: `(F : String → Nat → String) (G : Nat → String) (a : String) (k : Nat)`.

| Before | After |
|---|---|
| `⊢ P (F (a ++ "x") k)` | `⊢ P (a ++ "x" ++ G k)` |

**R13 · `String.append_assoc`** changes the **goal**: `s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃)`. After R11 and
R12 the `lit` case is `acc ++ s ++ render fs args = acc ++ (s ++ render fs args)`: only the grouping
differs. It is not a `simp` lemma by default, so name it. Placeholders: `(a b c : String)`.

| Before | After |
|---|---|
| `⊢ P (a ++ b ++ c)` | `⊢ P (a ++ (b ++ c))` |

**R14 · `String.append_empty`, `String.empty_append`** change the **goal**: `s ++ "" = s` and `"" ++ s = s`.
Both are `simp` lemmas, so plain `simp` uses them: the `[]` case ends at `acc = acc ++ ""`, the final step
at `"" ++ render fs args = render fs args`. Placeholders: `(a : String)`.

| Before | After |
|---|---|
| `⊢ P (a ++ "")` | `⊢ P a` |
| `⊢ P ("" ++ a)` | `⊢ P a` |

**R15 · `Nat.toString_eq_repr`** changes the **goal**: `toString n = n.repr`. A `simp` lemma; in the `nat`
case `simp` rewrites `toString n` on both sides, so it does no harm, but you will see `n.repr` if
`simp` stops early. Placeholders: `(n : Nat)`.

| Before | After |
|---|---|
| `⊢ P (toString n)` | `⊢ P n.repr` |

**W2** is the whole shape on the toy family: `have key : ∀ n acc t, call n (catAux n acc) t = acc ++ concat n t`
by `intro n; induction n` (R6, R7), `cases t` + `simp` at `0` (R8, R11, R14), `obtain` + `simp [defs, ih,
String.append_assoc]` at `n + 1` (R10 → R11 → R12 → R13), then `simp [key]` for `acc = ""`.

---

## Traps

- The body of `sprintfAux` comes after a frozen `:=`, so you cannot use the equation-style
  `def f : … | [], acc => …`. Write `fun | [], acc => … | …` (R1).
- In the `.nat` arm the result must be a function: `fun n => …` (R4). Returning a `String` there is a
  type error, as is a missing `fun` in the `.str` arm.
- Do not `intro acc` before `induction fs`: the IH would be about one fixed `acc` (R7). Do not induct on
  `sprintf_correct` directly either: the `""` does not survive one step (R6).
- `simp` cannot unfold `Fmt.apply` on an opaque `args`: split it first (`cases args` for `[]`,
  `obtain ⟨n, a⟩ := args` for `nat`/`str`; R8, R10). You recognise this when `simp` stops at a goal that
  still has a bare `args`, e.g. `Fmt.apply [] acc args = acc ++ render [] args` or
  `Fmt.apply (Fmt.nat :: fs) (fun n => sprintfAux fs (acc ++ n.repr)) args = …`.
- `simp [sprintfAux, Fmt.apply, render, ih]` stops at a regrouping goal; add `String.append_assoc` (R13).
- A `have key : ∀ fs acc args, …` inside the theorem shadows its `fs`, `args`; they show as `fs✝`, `args✝`.
  Harmless; or name the bound variables differently.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| a body after a frozen `:=` matching two arguments | `fun \| [], acc => … \| .lit s :: fs, acc => … \| …` | R1 |
| see what an arm must produce | `show T'`, or hover the hole | R2 |
| base arm: return the text | `acc` (`Fmt.type []` is `String`) | R3 |
| hole arm: take the argument | `fun n => sprintfAux fs (…)` | R4 |
| append a number / a string | `acc ++ toString n`, `acc ++ s` | R5 |
| generalise the accumulator | `have key : ∀ fs acc args, … := by …` | R6 |
| induction keeping `∀ acc` | `intro fs; induction fs with \| nil => … \| cons f fs ih => …` | R7 |
| split `args : Fmt.Args []` | `cases args` | R8 |
| split the head directive | `cases f with \| lit s => … \| nat => … \| str => …` | R9 |
| split `args` of a hole | `obtain ⟨n, a⟩ := args` | R10 |
| unfold the definitions | `simp [sprintfAux, Fmt.apply, render]` | R11 |
| use the IH at a new `acc` | add `ih` to the `simp` list | R12 |
| regroup `++` | `String.append_assoc` | R13 |
| `s ++ ""`, `"" ++ s` | automatic in `simp` | R14 |
| `toString n` became `n.repr` | automatic in `simp` | R15 |
| finish from `key` | `simp [sprintf, key]` | R6, R14 |
| see the state | infoview | |
