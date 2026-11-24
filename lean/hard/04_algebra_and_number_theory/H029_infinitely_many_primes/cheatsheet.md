# H029 · Infinitely many primes: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `theorem`, `intro`, `exact`, `have`, `rw`, `induction`,
`∃`/`∧`/`∨`/`¬`, `⟨…⟩`. **New here:** Mathlib's `Nat.Prime`, divisibility `∣` on `ℕ`, `Nat.factorial`,
strong induction (`Nat.strong_induction_on`), the tactics `by_cases`, `by_contra`, `push Not`, `obtain`,
`rintro rfl`, `omega`, and dot notation on proofs (`hp.pos`, `hlt.le`).

**The maths.** *Prime factor (milestone).* Every `n ≥ 2` has a prime factor, by strong induction on `n`
(the IH holds for every `m < n`). If `n` is prime, take `n`. Otherwise `n` has a divisor `m` with `m ≠ 1`,
`m ≠ n`. Then `m ≠ 0` (since `0 ∣ n` means `n = 0`), and `m ≤ n` (a divisor of a positive number is at most
it), so `2 ≤ m < n`. The IH gives a prime `p ∣ m`, and `p ∣ m ∣ n`. *Euclid.* Let `p` be a prime factor of
`n! + 1` (`n! + 1 ≥ 2` since `n! > 0`). If `p < n`, then `0 < p ≤ n`, so `p ∣ n!`; with `p ∣ n! + 1` this gives
`p ∣ 1`, so `p = 1`, but a prime is `> 1`. Hence `n ≤ p`.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`have`/`exact`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state before and
after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change. A
  hypothesis that itself contains a comma is written next to the state rather than inside it.
- `G : Prop` is an arbitrary goal and `g : … → G` is a hypothesis that only finishes the example once the step has
  put the right fact in the context. `Q`, `A`, `B`, `C` are arbitrary predicates or propositions.
- Placeholders are written as Lean binders. `{α : Type}` is any type. A bracket such as `[Monoid α]` is a
  requirement on the type (a *type class*). Each entry says which familiar types meet it.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Nat.Prime p` | `p` is prime: `2 ≤ p` and its only divisors are `1` and `p` (R6). Written `p.Prime` in source |
| `d ∣ n` (typed `\mid`, not `\|`) | "`d` divides `n`": by definition `∃ c, n = d * c`. `0 ∣ n` means `n = 0`; every `d ∣ 0` |
| `n.factorial` | `n! = 1 · 2 ⋯ n` (`0! = 1`). Printed `n !` only under `open Nat`; the problem does not open it |
| `¬a ≤ b`, `m ≠ n` | `¬` binds weaker than `≤`, `∣`, `=`; `m ≠ n` is notation for `¬m = n` |
| `∀ m < n, Q m` | `∀ m, m < n → Q m` (the strong-induction IH) |
| `∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n` | `∧` nests to the right: `m ∣ n ∧ (m ≠ 1 ∧ m ≠ n)`; the pattern `⟨m, h1, h2, h3⟩` takes it apart |
| `n✝`, `a✝`, `inst✝` | names Lean invented; you cannot type them. Name them with `with \| _ n ih =>` or `rename_i` (R1) |
| `hp✝` | an older `hp` hidden by a newer hypothesis of the same name: after `obtain ⟨p, hp, hpm⟩` in the milestone, `hp✝ : ¬Nat.Prime n` is the old one, `hp : Nat.Prime p` the new one |
| `this` | the name `have := e` gives a fact when you do not name it (the side proof of `2 ≤ n.factorial + 1`) |
| `case h` | the single goal of `Nat.strong_induction_on` (its premise is called `h`) |
| `case pos`, `case neg` | the two goals of `by_cases` (R2) |
| `hp.pos`, `hlt.le` | dot notation: `hp : Nat.Prime p`, so `hp.pos` is `Nat.Prime.pos hp`; `hlt : a < b`, so `hlt.le` is `LT.lt.le hlt` |

---

## Part 1 · `exists_prime_dvd` (milestone)

Statement: `∀ n, 2 ≤ n → ∃ p, Nat.Prime p ∧ p ∣ n`. Prove it first; `infinitely_many_primes` applies it to
`n.factorial + 1`.

### Strong induction and case splits

**R1 · `induction n using Nat.strong_induction_on`** changes the **context**: the IH for all smaller numbers
appears. The lemma is `Nat.strong_induction_on : (∀ n, (∀ m < n, Q m) → Q n) → Q n`. A hypothesis that
mentions `n` (here `hn : 2 ≤ n`) is reverted first, so it also becomes a premise of the IH, and is put back
under its own name. Without `with`, the new number and IH get invented names; `rename_i k ih` names them. In the
exercise write `induction n using Nat.strong_induction_on with | _ n ih => …` instead (W1). Placeholders:
`(Q : ℕ → Prop) (n : ℕ) (hn : 2 ≤ n)`.

| Before | After `induction …` | After `rename_i k ih` |
|---|---|---|
| `hn : 2 ≤ n ⊢ Q n` | `hn : 2 ≤ n✝ ⊢ Q n✝` | `k : ℕ, hn : 2 ≤ k ⊢ Q k` with `ih : ∀ m < k, 2 ≤ m → Q m` |

**R2 · `by_cases hA : A`** changes the **goal list**: one goal becomes two, one with `hA : A` and one with
`hA : ¬A` (excluded middle). Placeholders: `(A G : Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `hA : A ⊢ G`, `hA : ¬A ⊢ G` |

**R3 · `exact ⟨x, ha, hb⟩`** **closes** `∃ y, A y ∧ B y`: the anonymous constructor takes the witness first, then
one proof per conjunct (no inner brackets needed). Placeholders: `{α : Type} (A B : α → Prop) (x : α)`.

| Before | After |
|---|---|
| `ha : A x, hb : B x ⊢ ∃ y, A y ∧ B y` | no goals |

**R4 · `dvd_refl a`** changes the **context** (used inside `⟨…⟩` in the exercise). The lemma is
`dvd_refl a : a ∣ a`. Placeholders: `{α : Type} [Monoid α] (a : α)` (α has an associative `*` with `1`; `ℕ`, `ℤ`
qualify).

| Before | After `have h := dvd_refl a` |
|---|---|
| `⊢ G` | `h : a ∣ a ⊢ G` |

### Getting a divisor out of `¬ Nat.Prime n`

**R5 · `obtain ⟨x, ha, hb, hc⟩ : T := e`** changes the **context**: you state `T` (an `∃` with a conjunction),
`e` proves it (often `by …`), and the pattern names the witness and each conjunct. Without `: T`, write
`obtain ⟨…⟩ := e` with `e` an existing proof (an IH application, a milestone). Placeholders:
`{α : Type} (A B C : α → Prop)`.

| Before | After |
|---|---|
| `⊢ G` | `x : α, ha : A x, hb : B x, hc : C x ⊢ G` |

**R6 · `rw [Nat.prime_def] at hp`** changes the **context**. The lemma is
`Nat.prime_def : Nat.Prime p ↔ 2 ≤ p ∧ ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p`; `rw` can use an `↔`, also under `¬`.
Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `hp : ¬Nat.Prime n ⊢ G` | `⊢ G` with `hp : ¬(2 ≤ n ∧ ∀ (m : ℕ), m ∣ n → m = 1 ∨ m = n)` |

**R7 · `push Not at h`** changes the **context**: it moves `¬` inward. `¬(A ∧ B)` becomes `A → ¬B`, `¬∀ m, …`
becomes `∃ m, ¬…`, `¬(A ∨ B)` becomes `¬A ∧ ¬B`, `¬m = n` is shown as `m ≠ n`, and `¬a ≤ b` becomes `b < a`.
(`push_neg` is the deprecated old name.) Placeholders: `(n a b : ℕ)`.

| Before | After |
|---|---|
| `⊢ G` with `hp : ¬(2 ≤ n ∧ ∀ (m : ℕ), m ∣ n → m = 1 ∨ m = n)` | `⊢ G` with `hp : 2 ≤ n → ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n` |
| `h : ¬a ≤ b ⊢ G` | `h : b < a ⊢ G` |

After the first row, `hp hn` is the `∃` you wanted: `hp` is an implication, applied to `hn : 2 ≤ n`.

**R8 · `rintro rfl`** changes the **goal and the context**. The goal `m ≠ 0` is `m = 0 → False`; `rintro rfl`
introduces the equation and substitutes `0` for `m` in every hypothesis. Placeholders: `(m : ℕ) (Q : ℕ → Prop)`.

| Before | After |
|---|---|
| `hm : Q m ⊢ m ≠ 0` | `hm : Q 0 ⊢ False` |

**R9 · `simp at h`** changes the **context**: it simplifies a hypothesis. On `0 ∣ n` it uses
`zero_dvd_iff : 0 ∣ a ↔ a = 0`. Placeholders: `(n : ℕ)`.

| Before | After |
|---|---|
| `h : 0 ∣ n ⊢ G` | `h : n = 0 ⊢ G` |

**R10 · `omega`** **closes** any goal of linear arithmetic over `ℕ` or `ℤ` (`+`, `-`, multiplication by numerals,
`=`, `≠`, `≤`, `<`, `∧`, `∨`, `¬`, `False`) using the hypotheses of that shape. A term it does not understand, such as
`n.factorial`, counts as an unknown number; hypotheses such as `m ∣ n` or `Nat.Prime p` are ignored. In the exercise it proves `False` from `n = 0` and `2 ≤ n`, `0 < n` from
`2 ≤ n`, `2 ≤ m` from `m ≠ 0` and `m ≠ 1`, and `2 ≤ n.factorial + 1` from `0 < n.factorial`.

| Before | After |
|---|---|
| `h : n = 0, hn : 2 ≤ n ⊢ False` | no goals |
| `hn : 2 ≤ n, hm : m ≠ 0, hm1 : m ≠ 1 ⊢ 0 < n ∧ 2 ≤ m` | no goals |

### From a divisor to a smaller number

**R11 · `Nat.le_of_dvd`** changes the **context**. The lemma is `Nat.le_of_dvd : 0 < n → m ∣ n → m ≤ n` (it fails
for `n = 0`, which every `m` divides). Placeholders: `(m n : ℕ) (hn : 0 < n) (h : m ∣ n)`. In the exercise the
`0 < n` argument is `(by omega)`.

| Before | After `have hle := Nat.le_of_dvd hn h` |
|---|---|
| `⊢ G` | `hle : m ≤ n ⊢ G` |

**R12 · `Nat.lt_of_le_of_ne`** changes the **context**. The lemma is `Nat.lt_of_le_of_ne : m ≤ n → ¬m = n → m < n`;
a hypothesis `m ≠ n` fits the second argument, since `m ≠ n` is notation for `¬m = n`. Placeholders: `(m n : ℕ) (h1 : m ≤ n) (h2 : m ≠ n)`.

| Before | After `have hlt := Nat.lt_of_le_of_ne h1 h2` |
|---|---|
| `⊢ G` | `hlt : m < n ⊢ G` |

**R13 · `ih m hlt h2`** changes the **context**: the strong IH is a function; give it the smaller number, the proof
that it is smaller, then each extra premise (here `2 ≤ m`). Placeholders:
`(Q : ℕ → Prop) (n m : ℕ) (hlt : m < n) (h2 : 2 ≤ m)` and `ih : ∀ k < n, 2 ≤ k → Q k`.

| Before | After `have hm := ih m hlt h2` |
|---|---|
| `⊢ G` | `hm : Q m ⊢ G` |

**R14 · `dvd_trans`** changes the **context**. The lemma is `dvd_trans : a ∣ b → b ∣ c → a ∣ c`. Placeholders:
`{α : Type} [Semigroup α] (a b c : α)` (α has an associative `*`; `ℕ`, `ℤ` qualify).

| Before | After `have h := dvd_trans h1 h2` |
|---|---|
| `h1 : a ∣ b, h2 : b ∣ c ⊢ G` | `h : a ∣ c ⊢ G` |

---

## Part 2 · `infinitely_many_primes`

Statement: `∀ n, ∃ p, n ≤ p ∧ Nat.Prime p`. Take a prime factor of `n.factorial + 1` (milestone, R5), then argue by
contradiction.

**R15 · `Nat.factorial_pos n`** changes the **context**. The lemma is `Nat.factorial_pos : ∀ n, 0 < n.factorial`.
With R10 it gives the milestone's side condition `2 ≤ n.factorial + 1`. Placeholders: `(n : ℕ)`.

| Before | After `have hf := Nat.factorial_pos n` |
|---|---|
| `⊢ G` | `hf : 0 < n.factorial ⊢ G` |

**R16 · `refine ⟨x, ?_, hb⟩`** changes the **goal**: you give the witness and the second conjunct now; the first
conjunct `?_` is the new goal. Placeholders: `{α : Type} (A B : α → Prop) (x : α) (hb : B x)`.

| Before | After |
|---|---|
| `⊢ ∃ y, A y ∧ B y` | `⊢ A x` |

**R17 · `by_contra hA`** changes the **goal and the context**: the goal `A` becomes `False`, and `hA : ¬A` is
added. Follow it with R7 (`push Not at hA`) to turn `¬n ≤ p` into `p < n`. Placeholders: `(A : Prop)`.

| Before | After |
|---|---|
| `⊢ A` | `hA : ¬A ⊢ False` |

**R18 · `Nat.dvd_factorial`** changes the **context**. The lemma is
`Nat.dvd_factorial : 0 < m → m ≤ n → m ∣ n.factorial` (`m` is one of the factors `1, …, n`). Placeholders:
`(m n : ℕ) (hm : 0 < m) (hle : m ≤ n)`.

| Before | After `have h := Nat.dvd_factorial hm hle` |
|---|---|
| `⊢ G` | `h : m ∣ n.factorial ⊢ G` |

**R19 · `hp.pos`** changes the **context**. The lemma is `Nat.Prime.pos : Nat.Prime p → 0 < p`. Placeholders:
`(p : ℕ) (hp : Nat.Prime p)`.

| Before | After `have h := hp.pos` |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `h : 0 < p ⊢ G` |

**R20 · `hlt.le`** changes the **context**. The lemma is `LT.lt.le : a < b → a ≤ b`. Placeholders:
`(a b : ℕ) (hlt : a < b)` (any preorder: `ℕ`, `ℤ`, `ℝ`).

| Before | After `have h := hlt.le` |
|---|---|
| `hlt : a < b ⊢ G` | `h : a ≤ b ⊢ G` |

**R21 · `(Nat.dvd_add_right h).mp`** changes the **context**. The lemma is
`Nat.dvd_add_right : k ∣ m → (k ∣ m + n ↔ k ∣ n)`: if `k` divides `m`, it divides `m + n` exactly when it divides
`n`. `.mp` uses the `↔` left to right. Placeholders: `(k m n : ℕ) (h : k ∣ m) (hs : k ∣ m + n)`.

| Before | After `have h' := (Nat.dvd_add_right h).mp hs` |
|---|---|
| `h : k ∣ m, hs : k ∣ m + n ⊢ G` | `h' : k ∣ n ⊢ G` |

**R22 · `hp.one_lt`** changes the **context**. The lemma is `Nat.Prime.one_lt : Nat.Prime p → 1 < p`.
Placeholders: `(p : ℕ) (hp : Nat.Prime p)`.

| Before | After `have h := hp.one_lt` |
|---|---|
| `hp : Nat.Prime p ⊢ G` | `h : 1 < p ⊢ G` |

**R23 · `h.ne'`** changes the **context**. The lemma is `LT.lt.ne' : a < b → b ≠ a` (the primed version flips the
sides; `h.ne` gives `a ≠ b`). Since `b ≠ a` is `b = a → False`, `h.ne' e : False` for `e : b = a`. Placeholders:
`(a b : ℕ) (h : a < b)`.

| Before | After `have h' := h.ne'` |
|---|---|
| `h : a < b ⊢ G` | `h' : b ≠ a ⊢ G` |

**R24 · `Nat.dvd_one.mp`** changes the **context**. The lemma is `Nat.dvd_one : n ∣ 1 ↔ n = 1`. Placeholders:
`(n : ℕ) (h : n ∣ 1)`.

| Before | After `have h' := Nat.dvd_one.mp h` |
|---|---|
| `h : n ∣ 1 ⊢ G` | `h' : n = 1 ⊢ G` |

### Worked combinations (W1–W3, on facts that are not the exercise's)

**W1: strong induction stepping down by 2.** From `Q 0`, `Q 1` and `Q k → Q (k + 2)`, prove `Q n`: R1 with
`with | _ n ih =>`, R2 on `2 ≤ n`, then `obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩` (R5; `rfl` replaces
`n` by `k + 2`) and `step k (ih k (by omega))` (R13, R10). The small cases `n = 0`, `n = 1` come from R2 and R10.

```lean-goal
⊢ Q n
```

**W2: a divisor of `n + 1` other than `n + 1` is at most `n`.** R11 (with `(by omega)` for `0 < n + 1`) inside
R12, then R10:

```lean-goal
⊢ d ≤ n
```

with `hlt : d < n + 1` in the context before `omega`.

**W3: a prime cannot divide both `a` and `a + 1`.** R21 gives `h1 : p ∣ 1`; then `hp.one_lt.ne' (Nat.dvd_one.mp h1)`
(R22, R23, R24) proves the goal:

```lean-goal
⊢ False
```

---

## Traps

- `n !` is notation only under `open Nat`. In the exercise write `n.factorial` (or `Nat.factorial n`); this is
  also how the infoview prints it.
- In the milestone, `hn : 2 ≤ n` is in the context when you call `induction`, so the IH is
  `∀ m < n, 2 ≤ m → …`: you must pass both `m < n` and `2 ≤ m` (R13).
- `obtain … := exists_prime_dvd (n.factorial + 1) _` with a bare `_` fails: Lean cannot invent the proof of
  `2 ≤ n.factorial + 1`. Pass `(by …)` (R15, R10) or prove it first with `have`.
- `Nat.le_of_dvd` needs `0 < n`, not `n ≠ 0` or `2 ≤ n`; get it with `(by omega)`.
- `push Not` on `¬(A ∧ B)` gives the implication `A → ¬B`, not `¬A ∨ ¬B`; apply it to a proof of `A`.
- `∣` is typed `\mid`. The ASCII `|` is a different symbol and gives a parse error.
- `rintro rfl` needs the equation's variable to be a local (here `m`): it then disappears from the context.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| strong induction with names | `induction n using Nat.strong_induction_on with \| _ n ih => …` | R1 |
| case on a proposition | `by_cases hp : n.Prime` | R2 |
| prove `∃ p, A p ∧ B p` outright | `exact ⟨x, ha, hb⟩` | R3 |
| `a ∣ a` | `dvd_refl a` | R4 |
| state and destructure an `∃ … ∧ …` | `obtain ⟨m, h1, h2, h3⟩ : ∃ m, … := by …` | R5 |
| unfold `Nat.Prime` | `rw [Nat.prime_def] at hp` | R6 |
| push `¬` inward | `push Not at h` | R7 |
| prove `m ≠ 0` by substituting | `rintro rfl` | R8 |
| `0 ∣ n` → `n = 0` | `simp at h` | R9 |
| linear arithmetic on `ℕ` | `omega` | R10 |
| divisor ≤ number | `Nat.le_of_dvd (by omega) h` | R11 |
| `≤` and `≠` → `<` | `Nat.lt_of_le_of_ne hle hne` | R12 |
| use the strong IH | `ih m hlt h2` | R13 |
| `a ∣ b → b ∣ c → a ∣ c` | `dvd_trans h1 h2` | R14 |
| `0 < n.factorial` | `Nat.factorial_pos n` | R15 |
| choose the witness, keep one goal | `refine ⟨p, ?_, hp⟩` | R16 |
| proof by contradiction | `by_contra h` | R17 |
| `p ∣ n.factorial` for `0 < p ≤ n` | `Nat.dvd_factorial hpos hle` | R18 |
| `0 < p`, `1 < p` from primality | `hp.pos`, `hp.one_lt` | R19, R22 |
| `a < b` → `a ≤ b` / `b ≠ a` | `hlt.le` / `hlt.ne'` | R20, R23 |
| cancel a divisible summand | `(Nat.dvd_add_right h).mp hs` | R21 |
| `n ∣ 1` → `n = 1` | `Nat.dvd_one.mp h` | R24 |
| see the state | infoview | |
