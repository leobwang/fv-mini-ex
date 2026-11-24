# E022 · funext: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** E001–E021, in particular `rfl` (E001), `rw` (E009), `simp [h]` with a `∀`-hypothesis (E010 R9)
and `omega` (E011), and lists (E015).
**New here:** **function extensionality**: two functions `F G : α → β` are equal exactly when
`F x = G x` for every `x : α`. The `funext` tactic turns a goal about functions into a goal about values.
Also: anonymous functions (`fun n => …`, `(· + 2)`), the identity `id`, composition `∘`, and `List.map`.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses (the **context**) `Γ`, **goal** `G`. A cell shows only the
  hypotheses that matter or change, separated by `, `.
- `{α β γ : Type}` are arbitrary types; `F G : α → β` arbitrary functions; `s : Nat → Nat` an arbitrary
  function on naturals; `P : β → Prop` is "the rest of the goal": the step changes only the part inside
  `P (…)`.
- A hypothesis `k` only finishes the example. "no goals" means the tactic closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `F = G` with `F G : α → β` | equality of functions: same output at every input |
| `fun n => n + 0` | the anonymous function sending `n` to `n + 0` (a λ-term, `λ n. n + 0`) |
| `(· + 2)` in the source, `fun x => x + 2` in the infoview | shorthand: `·` (typed `\.`) marks where the argument goes |
| `id`, `id n` | the identity function `fun a => a`; `id n` computes to `n` |
| `f ∘ g` (typed `\comp`) | `Function.comp f g`, "first `g`, then `f`": `(f ∘ g) x = f (g x)` |
| `(f ∘ g) x` | the composition applied to `x`; `funext` leaves it in this form |
| `List.map f xs` | the list with `f` applied to every element of `xs` |
| `List.map f` (no list) | the function `List α → List β` that maps `f`; so `List.map f ∘ List.map g` is a composition of two such functions |
| `hf : ∀ (x : Nat), f x = x + 1` | a fact about `f` at every input; `hf 3 : f 3 = 3 + 1` |

---

## Part 1 · `add_zero_fun`

Statement: the function `n ↦ n + 0` equals `id`. Reduce to one input `n` (R1); the left side is a `fun`,
so `funext` substitutes `n` into it (R2). Both sides of `n + 0 = id n` compute to `n`, so `rfl` closes it
(R3, R4).

**R1 · `funext x`** changes the **goal and the context**. It applies the lemma
`funext : (∀ x, F x = G x) → F = G` backwards: to prove `F = G`, prove `F x = G x` for a fresh `x`, which
enters the context. Placeholders: `{α β : Type} (F G : α → β)`.

| Before | After |
|---|---|
| `⊢ F = G` | `x : α ⊢ F x = G x` |

**R2 · `funext x` on a `fun`** changes the **goal** as in R1, and a side written `fun n => e n` becomes
`e x`: Lean substitutes `x` for `n` (β-reduction) instead of showing `(fun n => e n) x`. Placeholders:
`(c : Nat) (F : Nat → Nat)`.

| Before | After |
|---|---|
| `⊢ (fun n => n * c) = F` | `x : Nat ⊢ x * c = F x` |

**R3 · `id_eq`** (statement: `id a = a`) changes the **goal**: `id a` becomes `a`. `simp` uses it by itself,
and `rfl` does not need it, since `id a` computes to `a`. Placeholders: `{α : Type} (a : α) (P : α → Prop)`.

| Before | After |
|---|---|
| `⊢ P (id a)` | `⊢ P a` |

**R4 · `rfl`** **closes** an equation whose sides compute to the same value. `Nat` addition recurses on its
second argument, so `t + 0` computes to `t` for any `t`, even a variable; `id t` computes to `t`.
Placeholders: `(a b : Nat)`.

| Before | After |
|---|---|
| `⊢ a + b + 0 = id (a + b)` | no goals |

**W1** (R1 with R2, then `simp`) on lists:

| Step | State |
|---|---|
| start | `⊢ (fun xs => xs ++ []) = id` |
| `funext xs` | `xs : List Nat ⊢ xs ++ [] = id xs` |
| `simp` | no goals (`List.append_nil` and R3) |

## Part 2 · `comp_twice`

Statement: if `f x = x + 1` for every `x`, then `f ∘ f` is the function `(· + 2)`. Reduce to one input
`x` (R1; the right side `(· + 2)` becomes `x + 2` by R5, the left stays `(f ∘ f) x`). Unfold the composition
(R6) and use `hf` on both calls (R7 twice, or R8 for all of it at once). The leftover arithmetic closes by
computation.

**R5 · `(· + c)`** is notation for `fun t => t + c`, and the infoview prints it that way. After `funext x`
it becomes `x + c` (R2). Placeholders: `(c : Nat) (F : Nat → Nat)`.

| Before | After |
|---|---|
| `⊢ F = fun x => x + c` | `x : Nat ⊢ F x = x + c` |

**R6 · `Function.comp_apply`** (statement: `(f ∘ g) x = f (g x)`) changes the **goal**: an applied
composition becomes nested calls. `funext` does not do this, because `f ∘ g` is a name (`Function.comp`),
not a `fun`. `simp` uses the lemma by itself. Placeholders: `{α β γ : Type} (f : β → γ) (g : α → β) (x : α)
(P : γ → Prop)`.

| Before | After |
|---|---|
| `⊢ P ((f ∘ g) x)` | `⊢ P (f (g x))` |

**R7 · `rw [h]`** with `h : ∀ x, s x = e x` changes the **goal**: `rw` picks the value of `x` from the first
match, here the outer call `s (s a)` with `x := s a`, and rewrites that **one** instance. A second `rw [h]`
rewrites the inner `s a`. Placeholders: `(s : Nat → Nat) (h : ∀ x, s x = 2 * x) (a : Nat) (P : Nat → Prop)`.

| Before | After |
|---|---|
| `⊢ P (s (s a))` | `⊢ P (2 * s a)` |

**R8 · `simp [h]`** with `h : ∀ x, s x = e x` rewrites **every** `s t` (inner ones too), applies R6 by itself,
and finishes arithmetic such as `a + 3 + 3 = a + 6` (E010 R9, R11). Here it **closes** the goal.
Placeholders: `(s : Nat → Nat) (h : ∀ x, s x = x + 3) (a : Nat)`.

| Before | After |
|---|---|
| `⊢ (s ∘ s) a = a + 6` | no goals |

**W2** (R1 + R5, R8, then `omega`) with `hg : ∀ x, g x = 2 * x`: `simp` cannot finish `2 * (2 * x) = 4 * x`.

| Step | State |
|---|---|
| start | `⊢ g ∘ g = fun x => 4 * x` |
| `funext x` | `x : Nat ⊢ (g ∘ g) x = 4 * x` |
| `simp [hg]` | `x : Nat ⊢ 2 * (2 * x) = 4 * x` |
| `omega` | no goals |

**W3** (R1 + R5, R6, R7 twice) with `hg : ∀ x, g x = x + 5`. The last `rw` leaves `x + 5 + 5 = x + 10`
and closes it with its own `rfl` (E009 R3).

| Step | State |
|---|---|
| `funext x` | `x : Nat ⊢ (g ∘ g) x = x + 10` |
| `rw [Function.comp_apply]` | `x : Nat ⊢ g (g x) = x + 10` |
| `rw [hg]` | `x : Nat ⊢ g x + 5 = x + 10` |
| `rw [hg]` | no goals |

## Part 3 · `map_comp_fun`

Statement: mapping `g` and then `f` over a list is the same function as mapping `f ∘ g` once. Both sides
are functions `List Nat → List Nat`, so reduce to one list `xs` (R1). Unfold the composition on the left
(R6), then fuse the two maps (R9). `simp [List.map_map]` does R6 and R9 in one call.

**R9 · `List.map_map`** (statement: `List.map g (List.map f l) = List.map (g ∘ f) l`) changes the **goal**:
two maps become one map of the composition. Watch the names: in the lemma the **inner** map is `f`, so the
composition is `g ∘ f` (outer first). `simp` uses the lemma by itself. Placeholders:
`{α β γ : Type} (f : α → β) (g : β → γ) (l : List α) (P : List γ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (List.map g (List.map f l))` | `⊢ P (List.map (g ∘ f) l)` |

**W4** (R1, then R6 and R9 twice, through `simp`) on three maps:

| Step | State |
|---|---|
| start | `⊢ List.map f ∘ List.map g ∘ List.map h = List.map (f ∘ g ∘ h)` |
| `funext xs` | `xs : List Nat ⊢ (List.map f ∘ List.map g ∘ List.map h) xs = List.map (f ∘ g ∘ h) xs` |
| `simp [List.map_map]` | no goals |

---

## Traps

- `funext` β-reduces a `fun` (R2, R5) but does **not** unfold `∘`: after `funext x` you still have
  `(f ∘ g) x`. `rw [hf]` cannot see the `f x` inside it until R6 (or `simp`) unfolds it.
- `rw [hf]` with `hf : ∀ x, f x = …` rewrites one instance (R7); `f (f x)` needs two `rw`s. `simp [hf]`
  rewrites all of them.
- `(· + 2)` prints as `fun x => x + 2`; it is the same term, not a different goal.
- `List.map_map`'s statement names the inner function `f` and the outer `g`; your `f`, `g` may be the other
  way round. `rw`/`simp` match by shape, not by name.
- `omega` cannot prove an equation between functions or lists; first `funext`, then arithmetic.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `F = G` for functions → one input | `funext x` | R1 |
| a side `fun n => e n` / `(· + c)` | nothing: `funext` substitutes, you see `e x` / `x + c` | R2, R5 |
| `id a` → `a` | `rfl` sees through it, or `simp` / `rw [id_eq]` | R3 |
| sides that compute to the same value (`t + 0`, `id t`) | `rfl` | R4 |
| `(f ∘ g) x` → `f (g x)` | `rw [Function.comp_apply]` (or `simp`) | R6 |
| use `h : ∀ x, s x = …` once | `rw [h]` | R7 |
| use it everywhere, unfold `∘`, finish arithmetic | `simp [h]` | R8 |
| `List.map g (List.map f l)` → `List.map (g ∘ f) l` | `rw [List.map_map]` (or `simp`) | R9 |
| arithmetic `simp` leaves | `omega` | E011 |
| see the state | infoview (cursor after a tactic) | |
