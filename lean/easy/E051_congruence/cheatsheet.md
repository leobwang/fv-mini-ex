# E051 · Congruence: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `exact`, `apply`, `intro`, `have`, term-mode proofs
(`fun h => …`, applying a proof of `A → B` to a proof of `A`), and `h.1`, `h.2` for the parts of `A ∧ B`.
**New here:** the core congruence lemmas `congrArg` (equal inputs give equal outputs) and `congrFun` (equal
functions give equal values), the `congr` tactic, the lambda shorthand `(· + 1)`, `≠` as a function into
`False`, and `Nat.succ_ne_self`. No Mathlib.

The point is to use these lemmas by hand: `rw`, `simp`, `subst`, `▸` and case analysis are banned, so you
cannot substitute an equation into the goal directly.

## How to read an entry

Each entry is one tactic or one lemma. It says what changes (**goal**, **context**, or **goal list**), lists
the placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `{α β γ : Type}` are arbitrary types (`Nat`, `List Nat`, …); `F`, `G`, `f`, `g` are arbitrary functions.
- A hypothesis `h` in an entry is only there to finish the example.
- The exercise is solved with terms (`congrArg F h`). The entries put the same term inside a tactic
  (`apply congrArg F`, `have ha := congrFun h a`) so that there is a state to look at; `exact t` and the
  term `t` prove the same thing.
- "no goals" means the step closed the goal.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `f = g` with `f g : α → β` | two functions are equal (as functions, not just at one point) |
| `fun n => n + 1` | the function sending `n` to `n + 1` |
| `(· + 1)`, `(· * k)` | you typed shorthand for `fun x => x + 1`, `fun x => x * k` (R3); Lean prints the `fun` form |
| `(fun n => 2 * n + 1) ≠ fun x => 0` | the two functions differ. Lean drops the parentheses around the last `fun` and names an unused `_` binder `x` |
| `a ≠ b` | `Ne a b`, defined as `a = b → False`: a proof is a function (R5) |
| `n.succ` | `Nat.succ n`, the same value as `n + 1` |
| `case e_a` | a goal produced by `congr`: one argument's equation |

---

## Part 1 · `congr_arg_ex`

Statement: from `h : a = b`, prove `f (g a) = f (g b)`. The two sides differ only at the spot where `a`
becomes `b`, so this is `congrArg` with the function "everything around that spot".

**R1 · `congrArg F h`** changes the **goal**: `F a = F b` is reduced to `a = b`. The lemma is
`congrArg : (f : α → β) → a₁ = a₂ → f a₁ = f a₂` (`a₁ a₂` implicit, read off `h`). As a term,
`congrArg F h : F a = F b`. Placeholders: `{α β : Type} (F : α → β) (a b : α) (h : a = b)`.

| Before | After `apply congrArg F` |
|---|---|
| `h : a = b ⊢ F a = F b` | `⊢ a = b` |

**R2 · `congrArg (fun x => F x c) h`** changes the **goal** in the same way when the changing part is not
the whole argument of one function: the function you pass is the expression with the changing spot
replaced by `x`. Lean accepts it because `(fun x => F x c) a` computes to `F a c` (β-reduction: substitute
the argument for `x`). Placeholders: `{α β γ : Type} (F : α → β → γ) (a b : α) (c : β) (h : a = b)`.

| Before | After `apply congrArg (fun x => F x c)` |
|---|---|
| `⊢ F a c = F b c` | `⊢ a = b` |

`congrArg F h` with just `F` would prove `F a = F b` (an equation between functions `β → γ`), which is not
the goal: the lambda must cover everything around the spot.

**W1.** `(f a + 1) * 2 = (f b + 1) * 2` from `h : a = b`: the spot `a` sits under `f`, `+ 1` and `* 2`, so
the lambda covers all three (R2, then R1).

| Before | After `apply congrArg (fun x => (f x + 1) * 2)` |
|---|---|
| `⊢ (f a + 1) * 2 = (f b + 1) * 2` | `⊢ a = b` |

---

## Part 2 · `congr_fun_ex`

Statement: from `h : f = g`, prove `f x + 1 = g x + 1`. First evaluate `h` at `x` (R4), then push the result
through "add one" (R1 with R3).

**R4 · `congrFun h a`** changes the **context** when you name it with `have`: from `h : f = g` it gives
`f a = g a`. The lemma is `congrFun : f = g → ∀ a, f a = g a`. Placeholders:
`{α β : Type} (f g : α → β) (a : α) (h : f = g)`.

| Before | After `have ha := congrFun h a` |
|---|---|
| `⊢ f a = g a` | `ha : f a = g a ⊢ f a = g a` |

**R3 · `(· * k)`** is the function `fun x => x * k`: `·` marks the hole and the parentheses delimit the
lambda. Passed to `congrArg` it changes the **goal** `x * k = y * k` to `x = y`. Placeholders:
`(x y k : Nat) (h : x = y)`.

| Before | After `apply congrArg (· * k)` |
|---|---|
| `⊢ x * k = y * k` | `⊢ x = y` |

**W2.** `f x * 2 = g x * 2` from `h : f = g`: R4, then R1 with R3.

| Before | After `have hx := congrFun h x` | After `exact congrArg (· * 2) hx` |
|---|---|---|
| `⊢ f x * 2 = g x * 2` | `hx : f x = g x ⊢ f x * 2 = g x * 2` | no goals |

---

## Part 3 · `succ_ne_id`

Statement: `(fun n : Nat => n + 1) ≠ (fun n => n)`. Assume the functions are equal (R5), evaluate that
equation at one point (R4), and contradict the value you get (R6).

**R5 · `intro hab`**, as a term `fun hab => …`, changes the **goal and the context**: `a ≠ b` unfolds to
`a = b → False`, so you assume `hab : a = b` and must prove `False`. Placeholders: `{α : Type} (a b : α)`.

| Before | After `intro hab` |
|---|---|
| `⊢ a ≠ b` | `hab : a = b ⊢ False` |

**R6 · `Nat.succ_ne_self`** **closes** `False` given an equation `k + 1 = k`. The lemma is
`Nat.succ_ne_self (n : Nat) : n.succ ≠ n`, a function from `n.succ = n` to `False`, so
`Nat.succ_ne_self k h : False`. `h : k + 1 = k` is accepted because `k + 1` and `k.succ` compute to the same
value. Placeholders: `(k : Nat) (h : k + 1 = k)`.

| Before | After `exact Nat.succ_ne_self k h` |
|---|---|
| `h : k + 1 = k ⊢ False` | no goals |

**W3.** `(fun n : Nat => 2 * n + 1) ≠ (fun _ => 0)`: R5, R4 at `0`, then `Nat.succ_ne_zero (n : Nat) :
n.succ ≠ 0`. `congrFun h 0` has type `(fun n => 2 * n + 1) 0 = (fun x => 0) 0`, and `have` shows it with both
sides computed:

| Before | After `intro h` | After `have h0 := congrFun h 0` |
|---|---|---|
| `⊢ (fun n => 2 * n + 1) ≠ fun x => 0` | `h : (fun n => 2 * n + 1) = fun x => 0 ⊢ False` | `h0 : 2 * 0 + 1 = 0 ⊢ False` |

then `exact Nat.succ_ne_zero (2 * 0) h0` closes it. The same proof as one term:
`fun h => Nat.succ_ne_zero (2 * 0) (congrFun h 0)`.

---

## Part 4 · `congr_two`

Statement: from `h1 : a = b` and `h2 : c = d`, prove `f a c = f b d` for a two-argument `f`.

**R7 · `congr`** changes the **goal list**: an equation between two applications of the same function becomes
one equation per argument (each named `case e_a`). It then closes every new goal it can by `rfl` or by a
hypothesis of exactly that type. Placeholders: `{α β γ δ : Type} (F : α → β → γ → δ) (a b : α) (c d : β)
(e : γ)`, and `(G : α → α → β)` for the second row.

| Before | After `congr` |
|---|---|
| `h : a = b ∧ c = d ⊢ F a c e = F b d e` | `⊢ a = b`, `⊢ c = d` (`e = e` was closed by `rfl`) |
| `h : a = b ⊢ G a a = G b b` | no goals (both `a = b` goals closed by `h`) |

**W4.** `congr` recurses through every layer of applications, `+` included; `congr 1` stops after one:

| Goal | After `congr` | After `congr 1` |
|---|---|---|
| `⊢ F (a + c) = F (b + d)` | `⊢ a = b`, `⊢ c = d` | `⊢ a + c = b + d` |

---

## Traps

- `▸`, `rw`, `subst` and `simp` are banned so that you build every step from `congrArg` / `congrFun`. `congr`
  would close `congr_arg_ex` too (it digs down to `a = b` and finds `h`); use it only for `congr_two`.
- `congrArg F h` proves `F a = F b` for the `F` you give. If `F` misses part of the context (only the
  outermost function instead of a lambda covering everything around the spot, W1), the type does not
  match the goal.
- `congrFun h x` gives `f x = g x`, not `f x + 1 = g x + 1`: wrap it in `congrArg` for the `+ 1`.
- `≠` is a function into `False`: you prove it with `fun h => …` (R5) and use it by applying it to an
  equation (R6). There is no separate "contradiction" step.
- `congr` goes as deep as it can (W4). If it produces goals you cannot prove, use `congr 1`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| `a = b` ⟹ `F a = F b` | `congrArg F h` | R1 |
| the changing part is inside a bigger expression | `congrArg (fun x => …x…) h` | R2, W1 |
| the lambda `fun x => x + 1` | `(· + 1)` | R3 |
| `f = g` ⟹ `f a = g a` | `congrFun h a` | R4 |
| prove `a ≠ b` | `fun hab => …` (tactic: `intro hab`), goal `False` | R5 |
| `False` from `k + 1 = k` | `Nat.succ_ne_self k h` | R6 |
| `False` from `k + 1 = 0` | `Nat.succ_ne_zero k h` | W3 |
| `F a c = F b d` ⟹ `a = b`, `c = d` | `congr` (one layer: `congr 1`) | R7 |
| see the state | infoview | |
