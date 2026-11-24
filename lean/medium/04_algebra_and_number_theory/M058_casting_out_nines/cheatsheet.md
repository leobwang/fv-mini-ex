# M058 · Casting out nines: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033). **New here:** Mathlib's congruences `a ≡ b [MOD n]`
(`Nat.ModEq`) and their algebra (`.pow`, `.mul_right`, `.add_left`, `.symm`, `.trans`); decimal digits
`Nat.digits`; strong induction `Nat.strong_induction_on`; `calc` chains that mix `=` and `≡`; and the
tactics `simpa`, `rcases`, `decide`.

## How to read an entry

Each entry is one tactic or one lemma (used with `rw`, or as a term in `have`/`exact`/`calc`). It says
what changes (**goal**, **context**, or **goal list**), gives the lemma's statement, lists the
placeholders with their types, then shows the proof state before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℕ → Prop`, `P : List ℕ → Prop`, …). The step changes only the
  part inside `P (…)`, wherever it sits in a larger goal.
- `G : Prop` is an arbitrary goal; a hypothesis `g : … → G` is there only to finish the example. Such
  entries show the **context** gaining a fact.
- Placeholders are written as Lean binders. `{α : Type}` is any type; a bracket such as `[MulOneClass M]`
  is a requirement on `M` (a *type class*); each entry says which familiar types meet it.
- Dot notation: for `h : a ≡ b [MOD n]`, `h.pow k` means `Nat.ModEq.pow k h`. Lean finds the namespace
  `Nat.ModEq` from the type of `h`. The same goes for `.mul_right`, `.add_left`, `.symm`, `.trans`.
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `ℕ` | the natural numbers `0, 1, 2, …` (`Nat`) |
| `a % n`, `a / n` | remainder and quotient of `a` on division by `n`, so `a = a % n + n * (a / n)` |
| `a ≡ b [MOD n]` | `Nat.ModEq n a b`, *defined* as `a % n = b % n` (R1) |
| `Nat.digits 10 n` | the list of decimal digits of `n`, **least significant first**: `Nat.digits 10 123 = [3, 2, 1]`, `Nat.digits 10 0 = []` |
| `b.digits n` | the same function with a variable base `b` (`Nat.digits b n`); a numeral base prints as `Nat.digits 10 n` |
| `a :: l` | the list with head `a` and tail `l` |
| `l.sum` | `List.sum l`, the sum of the entries of `l` (`0` for `[]`) |
| `m ∣ n` | `m` divides `n`: `∃ c, n = m * c` (typed `\mid`, not the keyboard bar `\|`) |
| `∀ m < n, P m` | `∀ m, m < n → P m` |
| `n > 0` | the same as `0 < n` (`>` is notation for `<` flipped) |
| `n✝`, `a✝` | inaccessible names: Lean made them up, you cannot type them; `rename_i` names them (R5) |
| `inst✝ : MulOneClass M` | an anonymous type-class hypothesis from a `[…]` binder |
| `case h` | the single goal of `Nat.strong_induction_on` (R5) |
| `case inl`, `case inr` | the two goals from splitting an `∨` (left / right disjunct, R6) |
| `case calc_1` | the goal for step 1 of a `calc` written with `?_` (R11) |
| `case refine_1`, `case refine_2` | the goals left by the two `?_` of a `refine` (R17) |
| `case h.inr.calc_2` | case names nest with `.`: step 2 of a `calc` inside case `inr` inside case `h` |

---

## Part 1 · `ten_pow_modEq`

Statement: for every `k : ℕ`, `10 ^ k ≡ 1 [MOD 9]`, i.e. $10^k \bmod 9 = 1$. Prove `10 ≡ 1 [MOD 9]` by
computation, raise both sides to the `k`, and tidy `1 ^ k` to `1`.

**R1 · `unfold Nat.ModEq`** changes the **goal**: it shows the definition of a congruence. You rarely
need it in a proof; it explains why `decide` (R2) and `rfl` (R7) work. Placeholders: `(n a b : ℕ)`.

| Before | After |
|---|---|
| `⊢ a ≡ b [MOD n]` | `⊢ a % n = b % n` |

**R2 · `decide`** **closes** a congruence between numerals: `a % n` and `b % n` are computed and
compared. Example: `100 ≡ 1 [MOD 11]`. It fails as soon as a variable appears (`10 ^ k`).

**R3 · `h.pow k`** (lemma `Nat.ModEq.pow`) changes the **context** when used in `have`. Statement:
`Nat.ModEq.pow : ∀ {n a b : ℕ} (m : ℕ), a ≡ b [MOD n] → a ^ m ≡ b ^ m [MOD n]`. Placeholders:
`(n a b k : ℕ) (h : a ≡ b [MOD n])`.

| Before | After `have h' := h.pow k` |
|---|---|
| `h : a ≡ b [MOD n] ⊢ G` | `h' : a ^ k ≡ b ^ k [MOD n] ⊢ G` |

**R4 · `simpa using e`** **closes** the goal: it runs `simp` on the goal and on the type of `e`, then
closes the goal with `e` if the two now match. Here `simp` uses `one_pow : 1 ^ k = 1`. Placeholders:
`(n a k : ℕ) (h : a ≡ 1 ^ k [MOD n])`. A term works in place of `h`, e.g.
`simpa using (show 100 ≡ 1 [MOD 11] by decide).pow k` (W1).

| Before | After `simpa using h` |
|---|---|
| `h : a ≡ 1 ^ k [MOD n] ⊢ a ≡ 1 [MOD n]` | closed |

---

## Part 2 · `digits_sum_modEq`

Statement: for every `n : ℕ`, `n ≡ (Nat.digits 10 n).sum [MOD 9]`. The math: write
$n = d_0 + 10\,q$ with last digit $d_0 = n \bmod 10$ and $q = \lfloor n/10 \rfloor$. Since $10 \equiv 1$,
$n \equiv d_0 + q$, and $q < n$ (for $n > 0$) has the digits of $n$ minus $d_0$, so by induction
$q \equiv$ (its digit sum). Plain induction `n → n + 1` does not fit; you need the claim for `n / 10`,
which is **strong induction**.

### Strong induction and the case `n = 0`

**R5 · `induction n using Nat.strong_induction_on with | _ n ih => …`** changes the **context**: one
goal `P n`, with the extra hypothesis `ih` that the claim holds for every smaller number.
`Nat.strong_induction_on` is the principle `(∀ n, (∀ m < n, P m) → P n) → ∀ n, P n`. In the `with` form,
`_` matches its single case (named `h`), and `n ih` name the variables. Placeholders: `(P : ℕ → Prop)
(n : ℕ)`. Use `ih` as `ih m hm : P m` with `hm : m < n`.

| Before | After `induction … using Nat.strong_induction_on` | After `rename_i n ih` (= the `with` form) |
|---|---|---|
| `n : ℕ ⊢ P n` | `n✝ : ℕ ⊢ P n✝`, with `a✝ : ∀ m < n✝, P m` | `n : ℕ ⊢ P n`, with `ih : ∀ m < n, P m` |

**R6 · `rcases Nat.eq_zero_or_pos n with rfl | hn`** changes the **goal list**: two goals. The lemma is
`Nat.eq_zero_or_pos : ∀ (n : ℕ), n = 0 ∨ n > 0`. The pattern `rfl | hn` names the two disjuncts; `rfl`
substitutes `0` for `n` everywhere, so `n` leaves the context. Placeholders: `(P : ℕ → Prop) (n : ℕ)`.

| Before | After |
|---|---|
| `n : ℕ ⊢ P n` | `⊢ P 0`, `n : ℕ, hn : n > 0 ⊢ P n` |

**R7 · `rfl`** **closes** `a ≡ b [MOD n]` when both sides compute to the same remainder, since
`Nat.ModEq` is an `=` underneath (R1). `Nat.digits 10 0` computes to `[]` and `[].sum` to `0`, so the
case `n = 0` closes this way. Placeholders: `(n a : ℕ)`, goal `a ≡ a [MOD n]`; the guide's second
example, `0 ≡ (Nat.digits 7 0).sum [MOD n]`, shows the computing version.

### Digits of a number

**R8 · `rw [Nat.digits_def' hb hn]`** changes the **goal**: the digit list of a positive number splits
into its last digit and the digits of the rest. Statement:
`Nat.digits_def' : 1 < b → 0 < n → b.digits n = n % b :: b.digits (n / b)`. With `b = 10` write
`Nat.digits_def' (by norm_num) hn` (`norm_num` proves `1 < 10`; `hn : n > 0` is accepted as `0 < n`).
Placeholders: `(b n : ℕ) (hb : 1 < b) (hn : 0 < n) (P : List ℕ → Prop)`.

| Before | After |
|---|---|
| `⊢ P (b.digits n)` | `⊢ P (n % b :: b.digits (n / b))` |

**R9 · `rw [List.sum_cons]`** changes the **goal**: the sum of `a :: l` is `a` plus the sum of `l`.
Statement: `List.sum_cons : (a :: l).sum = a + l.sum` (for any type with `+` and `0`; here `ℕ`).
Placeholders: `(a : ℕ) (l : List ℕ)`.

| Before | After |
|---|---|
| `⊢ P (a :: l).sum` | `⊢ P (a + l.sum)` |

**R10 · `have hlt : n / k < n := Nat.div_lt_self hn hk`** changes the **context**: it adds the bound
you feed to `ih` (R5). Statement: `Nat.div_lt_self : ∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n`.
Placeholders: `(n k : ℕ) (hn : 0 < n) (hk : 1 < k)`; with `k = 10`, write `(by norm_num)` for `hk`.

| Before | After |
|---|---|
| `hk : 1 < k ⊢ G` | `hlt : n / k < n ⊢ G` |

### Chaining congruences

**R11 · `calc`** changes the **goal list**: it proves `a ≡ c [MOD n]` as a chain of steps, each
`_ rel rhs := proof`, where `_` is the previous right side and `rel` is `=` or `≡ [MOD n]` (they mix
freely; the chain's relation is `≡` as soon as one step is). Write `:= ?_` to leave a step as a new goal,
or give its proof term directly. Placeholders: `(n a b c : ℕ)`.

| Before | After `calc a = b := ?_` / `_ ≡ c [MOD n] := ?_` |
|---|---|
| `⊢ a ≡ c [MOD n]` | `⊢ a = b`, `⊢ b ≡ c [MOD n]` |

Layout: the first step goes on the `calc` line, every further step on its own line starting with `_`,
indented further than `calc`.

**R12 · `(Nat.mod_add_div m k).symm`** is the first `calc` step: it splits a number into remainder and
quotient. Statement: `Nat.mod_add_div : ∀ (m k : ℕ), m % k + k * (m / k) = m`; `.symm` flips an equation.
In `have` it changes the **context**. Placeholders: `(m k : ℕ)`.

| Before | After `have h := (Nat.mod_add_div m k).symm` |
|---|---|
| `⊢ G` | `h : m = m % k + k * (m / k) ⊢ G` |

**R13 · `h.mul_right c`** (lemma `Nat.ModEq.mul_right`) multiplies both sides on the right. Statement:
`Nat.ModEq.mul_right : ∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a * c ≡ b * c [MOD n]`. In `have` it changes
the **context**. Placeholders: `(n a b c : ℕ) (h : a ≡ b [MOD n])`.

| Before | After `have h' := h.mul_right c` |
|---|---|
| `h : a ≡ b [MOD n] ⊢ G` | `h' : a * c ≡ b * c [MOD n] ⊢ G` |

**R14 · `h.add_left c`** (lemma `Nat.ModEq.add_left`) adds the same number on the left. Statement:
`Nat.ModEq.add_left : ∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → c + a ≡ c + b [MOD n]`. It **closes** a goal
of that shape: `exact h.add_left _`, where `_` lets Lean read `c` off the goal. It composes with R13:
`(h.mul_right _).add_left _ : c + a * d ≡ c + b * d [MOD n]`. Placeholders: `(n a b c : ℕ) (h : a ≡ b [MOD n])`.

| Before | After `exact h.add_left _` |
|---|---|
| `h : a ≡ b [MOD n] ⊢ c + a ≡ c + b [MOD n]` | closed |

**R15 · `rw [one_mul]`** changes the **goal**: `1 * a` becomes `a`. Statement: `one_mul : 1 * a = a`.
Placeholders: `{M : Type} [MulOneClass M] (a : M)`; `MulOneClass` means "has `*` and a `1` that is
neutral for it", which `ℕ`, `ℤ`, `ℝ` meet. After R13 with `10 ≡ 1`, the goal has `1 * (n / 10)`; remove
the `1 *` before using `ih`.

| Before | After |
|---|---|
| `⊢ P (1 * a)` | `⊢ P a` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1.** `100 ^ k ≡ 1 [MOD 11]`: `have h : 100 ≡ 1 [MOD 11] := by decide` (R2), then `simpa using h.pow k`
(R3, R4).

**W2.** `n ≡ n % 100 + n / 100 [MOD 99]` as a three-step `calc` (R11): split `n` with R12, replace `100`
by `1` with `(h100.mul_right _).add_left _` (R13, R14), then drop `1 *` with `by rw [one_mul]` (R15). The
goal, which the `have h100 : 100 ≡ 1 [MOD 99] := by decide` leaves unchanged:

```lean-goal
⊢ n ≡ n % 100 + n / 100 [MOD 99]
```

**W3.** Base-7 digits of a positive `n`: R8 with `(by norm_num)`, then R9:

```lean-goal
⊢ P (Nat.digits 7 n).sum
⊢ P (n % 7 :: Nat.digits 7 (n / 7)).sum
⊢ P (n % 7 + (Nat.digits 7 (n / 7)).sum)
```

---

## Part 3 · `nine_dvd_iff_digits`

Statement: `9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum`. Turn both divisibilities into congruences with `0`
(R16), split the `↔` (R17), and in each direction chain `digits_sum_modEq n` (Part 2, flipped with R18
where needed) with the hypothesis (R19).

**R16 · `rw [← Nat.modEq_zero_iff_dvd]`** changes the **goal**. Statement:
`Nat.modEq_zero_iff_dvd : ∀ {n a : ℕ}, a ≡ 0 [MOD n] ↔ n ∣ a`; `rw` can rewrite with an `↔` like with an
`=`, and `←` uses it right to left. Each `rw [← …]` rewrites the first `_ ∣ _` it finds (and every copy
of it), so a goal with two different divisibilities needs it twice. `rw [← …] at h ⊢` rewrites `h` and
the goal (W4). Placeholders: `(n a : ℕ) (P : Prop → Prop)`.

| Before | After |
|---|---|
| `⊢ P (n ∣ a)` | `⊢ P (a ≡ 0 [MOD n])` |

**R17 · `refine ⟨fun h => ?_, fun h => ?_⟩`** changes the **goal list**: an `A ↔ B` is a pair of
implications, so it gives two goals, each with the assumption named `h`. (`constructor` also splits `↔`,
leaving `A → B` and `B → A` without introducing `h`.) Placeholders: `(A B : Prop)`.

| Before | After |
|---|---|
| `⊢ A ↔ B` | `h : A ⊢ B`, `h : B ⊢ A` |

**R18 · `h.symm`** (lemma `Nat.ModEq.symm`) swaps the two sides. Statement:
`Nat.ModEq.symm : a ≡ b [MOD n] → b ≡ a [MOD n]`. In `have` it changes the **context**. Placeholders:
`(n a b : ℕ) (h : a ≡ b [MOD n])`.

| Before | After `have h' := h.symm` |
|---|---|
| `h : a ≡ b [MOD n] ⊢ G` | `h' : b ≡ a [MOD n] ⊢ G` |

**R19 · `h1.trans h2`** (lemma `Nat.ModEq.trans`) chains two congruences and **closes** the goal.
Statement: `Nat.ModEq.trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n]`. The middle terms must
match. Placeholders: `(n a b c : ℕ) (h1 : a ≡ b [MOD n]) (h2 : b ≡ c [MOD n])`.

| Before | After `exact h1.trans h2` |
|---|---|
| `h1 : a ≡ b [MOD n], h2 : b ≡ c [MOD n] ⊢ a ≡ c [MOD n]` | closed |

**W4.** From `hab : a ≡ b [MOD 11]` and `hb : 11 ∣ b` to `11 ∣ a`: `rw [← Nat.modEq_zero_iff_dvd] at hb ⊢`
(R16) gives

| Before | After |
|---|---|
| `hb : 11 ∣ b ⊢ 11 ∣ a` | `hb : b ≡ 0 [MOD 11] ⊢ a ≡ 0 [MOD 11]` |

and `exact hab.trans hb` (R19) closes it.

---

## Traps

- Search tactics (`exact?`, `apply?`, `rw?`, `hint`, `try?`) are fine for exploring, but they close goals
  with Mathlib's own digit lemmas, which are **BANNED** here, so their output cannot stay in the file.
- `decide` (R2) needs concrete numbers: it proves `10 ≡ 1 [MOD 9]` but not `10 ^ k ≡ 1 [MOD 9]`.
- `Nat.digits_def'` (R8) needs `0 < n`: split off `n = 0` (R6) **inside** the strong induction (R5),
  so that `ih` is available in the case `n > 0`.
- `ih` asks for a proof of `m < n`: prove `hlt : n / 10 < n` (R10) before you need it.
- `h.mul_right c` puts the new factor `c` on the **right**: from `h10 : 10 ≡ 1 [MOD 9]` it gives
  `10 * c ≡ 1 * c [MOD 9]`. The split `n % 10 + 10 * (n / 10)` has `10` on the left of `*`, so
  `.mul_right` (not `.mul_left`, which gives `c * 10 ≡ c * 1`) is the one that fits.
- After the `10 → 1` step the goal has `1 * (n / 10)`, not `n / 10`; `ih` will not match until you
  `rw [one_mul]` (R15).
- `.trans` needs the middle terms to agree literally up to definitions: flip a congruence with `.symm`
  (R18) when it points the wrong way.
- In a `calc`, each `_ ≡ x [MOD 9]` needs its `[MOD 9]`; a step written `_ = x` must be a true equation.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| see what `≡ [MOD n]` means | `unfold Nat.ModEq` | R1 |
| numeric congruence | `decide` | R2 |
| raise a congruence to a power | `h.pow k` | R3 |
| tidy `1 ^ k` and close | `simpa using e` | R4 |
| induction with all smaller cases | `induction n using Nat.strong_induction_on with` / `\| _ n ih => …` | R5 |
| split `n = 0` / `n > 0` | `rcases Nat.eq_zero_or_pos n with rfl \| hn` | R6 |
| congruence of equal computations | `rfl` | R7 |
| last digit off a digit list | `rw [Nat.digits_def' (by norm_num) hn]` | R8 |
| sum of a cons | `rw [List.sum_cons]` | R9 |
| `n / 10 < n` | `Nat.div_lt_self hn (by norm_num)` | R10 |
| chain `=` and `≡` | `calc a = b := … ` / `_ ≡ c [MOD n] := …` | R11 |
| `n = n % 10 + 10 * (n / 10)` | `(Nat.mod_add_div n 10).symm` | R12 |
| `a * c ≡ b * c`, `c + a ≡ c + b` | `h.mul_right _`, `h.add_left _` | R13, R14 |
| drop `1 *` | `rw [one_mul]` | R15 |
| `n ∣ a` → `a ≡ 0 [MOD n]` | `rw [← Nat.modEq_zero_iff_dvd]` | R16 |
| split `↔` with names | `refine ⟨fun h => ?_, fun h => ?_⟩` | R17 |
| flip / chain congruences | `h.symm`, `h1.trans h2` | R18, R19 |
| see the state | infoview | |
