# Lean 4 reference

A cumulative cheat sheet for the Lean track (Lean 4.32.0, Mathlib v4.32.0, physlib `ba2a946`), grouped
by topic. Each row cites the problems that teach it, so you can jump from an API to an exercise that
uses it. Problem cards list only what that one problem needs; this file is the union. Everything here
was taken from a verified card or solution or checked with `#check` at the pinned versions.

- [Core syntax and tactics](#core-syntax-and-tactics)
- [Logic and types, verified programs, semantics](#logic-and-types-verified-programs-semantics)
- [Algebra, number theory, analysis and sets (Mathlib)](#algebra-number-theory-analysis-and-sets-mathlib)
- [Probability and statistics](#probability-and-statistics)
- [Numerical analysis](#numerical-analysis)
- [Quantum computing and information (Mathlib matrices + QuantumInfo)](#quantum-computing-and-information-mathlib-matrices--quantuminfo)
- [Condensed matter and statistical mechanics (physlib + Mathlib)](#condensed-matter-and-statistical-mechanics-physlib--mathlib)
- [Physics with PhysLean (physlib)](#physics-with-physlean-physlib)
- [Cheatsheet](#cheatsheet)


## Core syntax and tactics

Problems E001–E094. Core Lean only (no `import`): E001–E033, E046–E062, E076–E086. With
`import Mathlib` as the first line: E034–E045, E063–E075, E087–E094. The last column lists the problems
that teach or lean on each entry. Snippets come from the cards and reference solutions or were
`#check`ed at Lean 4.32.0 / Mathlib v4.32.0.

### Commands, files, scoping

| Construct | Example | Gloss | IDs |
|---|---|---|---|
| `def` / `theorem` / `example` | `theorem double_three : double 3 = 6 := rfl` | definition / named proof / anonymous proof | E001 |
| `#eval`, `#check`, `#check @c` | `#check @Nat.le_trans` | run; show a type; `@` also shows the implicit args | E001, E023 |
| `by` | `example (P Q : Prop) : P → Q → P := by intro hp hq; exact hp` | tactic block; separate tactics with `;` or newlines | E003 |
| `import Mathlib` | `import Mathlib` | first command of the file; gives ℕ ℤ ℚ ℝ ℂ and the Mathlib tactics | E034 |
| `namespace X … end X` | `namespace Shape … end Shape` | names inside become `Shape.area` | E015, E056 |
| `open X` / `open X in` | `by open Shape in rw [area_comm h w]; omega` | drop the `X.` prefix (for the rest of the file / one command or tactic) | E042, E056 |
| `section` + `variable` | `variable {α : Type} (xs ys : List α) (hne : xs ≠ [])` | each later declaration takes the variables it mentions, until `end` | E056 |
| `include h in` | `include hne in theorem twice_ne_nil : twice xs ≠ [] := …` | also pass a variable the statement does not mention | E056 |
| `universe u`, `Sort u`, `Type u` | `def idU {α : Sort u} (a : α) : α := a` | universe-polymorphic definition; `Sort 0 = Prop`, `Type u = Sort (u+1)`, `Type : Type 1` | E078 |
| `ULift` | `example : (ULift.up 3 : ULift.{1} Nat).down = 3 := rfl` | copy a type one universe up | E078 |
| `set_option pp.notation false in` | `set_option pp.notation false in #check 2 + 3 * 4` | prints `HAdd.hAdd 2 (HMul.hMul 3 4)`: the terms behind notation | E076 |
| `exact?`, `apply?` | `example (n : Nat) (h : n ≠ 0) : 0 < n := by exact?` | prints `Try this: exact Nat.zero_lt_of_ne_zero h`; paste it | E033 |
| `noncomputable def` | `noncomputable def root (h : ∃ n : ℕ, n * n = 49) : ℕ := h.choose` | required for a def that uses choice | E090 |

### Definitions and data

| Construct | Example | Gloss | IDs |
|---|---|---|---|
| equations by pattern matching | `def tri : Nat → Nat \| 0 => 0 \| n + 1 => tri n + (n + 1)` | structural recursion; computes, so `rfl` works | E002, E014 |
| `match` on an argument | `def pred' (n : Nat) : Nat := match n with \| 0 => 0 \| k + 1 => k` | `match xs, ys with` matches two | E002, E016 |
| two-argument patterns | `def ack : Nat → Nat → Nat \| 0, n => n + 1 \| m + 1, 0 => ack m 1 \| m + 1, n + 1 => ack m (ack (m + 1) n)` | Lean finds the lexicographic measure `(m, n)` itself | E079, E084 |
| pattern-matching lambda | `def second : List Nat → Option Nat := fun \| _ :: y :: _ => some y \| _ => none` | also `fun (a, b) => a * b`, `fun ⟨hp, _⟩ => hp` | E004, E032, E052 |
| `·` shorthand | `List.map (· * 2) xs` | `(· * 2)` = `fun x => x * 2`; `(· + ·)` takes two args | E022, E024, E051 |
| `if` / dependent `if` | `if h : i < xs.length then xs[i] else 0` | `h : c` / `h : ¬c` in scope in the branches | E012, E059 |
| `termination_by` | `def cd (n : Nat) : List Nat := if n = 0 then [] else n :: cd (n - 1) termination_by n` | well-founded recursion on a measure; `termination_by m n => (m, n)` is lexicographic | E026, E079 |
| `mutual … end` | `mutual def f : Nat → Nat \| 0 => 0 \| n + 1 => g n  def g : Nat → Nat \| 0 => 1 \| n + 1 => f n end` | functions that call each other | E080 |
| `where` / `let rec` | `def len (xs : List Nat) : Nat := go xs 0 where go : List Nat → Nat → Nat \| [], a => a \| _ :: t, a => go t (a + 1)` | helper is a top-level `len.go` with its own equations; `let rec go …; go xs 0` gives `len'.go` | E085 |
| `structure` | `structure Point where x : Nat  y : Nat` | values `⟨1, 2⟩`, `{ x := 1, y := 2 }`, update `{ p with x := 0 }`, project `p.x` | E017 |
| eta | `example (p : Pair) : (Pair.mk p.a p.b) = p := rfl` | rebuilding a structure gives it back by definition | E017, E052 |
| `extends` | `structure B extends A where b : Nat` | flat `{ a := 1, b := 2 }`, `q.a`, `q.toA`, `{ x with b := 0 }` from `x : A`, `⟨x, 0⟩` | E053 |
| `@[ext]` | `@[ext] structure V2 where x : Int  y : Int` | generates `V2.ext : p.x = q.x → p.y = q.y → p = q` | E019 |
| `inductive` | `inductive Color where \| red \| green deriving DecidableEq, Repr` | `.red` means `Color.red` when the type is known | E018, E054 |
| constructor arguments | `inductive Shape where \| circle (r : Nat) \| rect (w h : Nat)` | injective, pairwise distinct | E029 |
| `deriving instance` | `deriving instance Inhabited for Color` | add a derived instance after the fact | E054 |
| `instance` | `instance instAddV2 : Add V2 := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩` | now `p + q` works; also `instance … where mul p q := …` | E019 |
| `Coe`, `@[coe]` | `instance instCoePosNat : Coe Pos Nat := ⟨Pos.toNat⟩` | `↑a` / `(a : Nat)` elaborate to `Pos.toNat a`; `@[coe]` makes it print as `↑a` | E055 |
| `Prop`-valued `def` | `def Pos (n : Nat) : Prop := 0 < n` | a predicate; `unfold Pos` to see `0 < n` | E030 |
| pairs `α × β` | `example (p : Nat × Nat) : (p.1, p.2) = p := rfl` | `.1`/`.fst`, `.2`/`.snd`; `Prod.ext` | E052 |
| subtype `{ x // p x }` | `example : { n : Nat // n > 2 } := ⟨5, by decide⟩` | `.val` (data), `.property` (proof); `Subtype.ext` | E057 |
| Σ-type `(n : Nat) × T n` | `example : (n : Nat) × Fin (n + 1) := ⟨3, 2⟩` | 2nd component's type depends on the 1st; `.1`/`.2`; unlike `∃`, returns its witness | E057 |
| `Fin n` | `Nat.le_of_lt_succ s.2.isLt` | `i.val` / `↑i` is the number; `i.isLt : ↑i < n` | E057, E070 |
| `Setoid`, `Quotient` | `def Parity.mk (n : Nat) : Parity := Quotient.mk parityRel n` | `Setoid α` = an equivalence `r` + proof `iseqv`; `a ≈ b` means `r a b` | E081 |
| `Quotient.lift` | `Quotient.lift (fun n => n % 2 == 0) (fun a b (h : a % 2 = b % 2) => by simp [h])` | function out of a quotient; must respect `≈`; computes on `mk` by `rfl` | E081 |
| `Option` | `def safePred (n : Nat) : Option Nat := if n = 0 then none else some (n - 1)` | partial results; `o.getD d`, `o.map f` | E016, E032 |
| list indexing | `xs[i]`, `xs[0]'h`, `[10, 20, 30][7]? = none`, `[10, 20, 30][7]! = 0` | bound from context / explicit proof / `Option` / `default` (panics at runtime) | E059 |
| `Array` | `#eval #[1, 2].push 3` | literal `#[..]`, `a.push x`, `a.size`, `a[i]?`, `a[i]` (needs `i < a.size` in context), `a.toList` | E082 |
| `BitVec w` | `example : 5#4 + 12#4 = 1#4 := by decide` | w-bit words mod `2^w`; `n#w` literal; `&&&` `\|\|\|` `^^^` `<<<` `>>>`; `<`/`≤` unsigned | E083 |
| `String`, `Char` | `example : "hi".toList = ['h', 'i'] := by decide` | `'a'.toNat = 97`, `'7'.isDigit : Bool`, `String.singleton c`, `s.length` | E086 |
| user notation | `infixl:65 " +' " => Nat.add` | `infixr:75`, `notation "⟪" a ", " b "⟫" => dot a b`; precedence `+ -` 65, `* /` 70; higher binds tighter | E076 |
| tactic macros | ``macro "triv" : tactic => `(tactic\| first \| rfl \| decide)`` | `syntax "t" : tactic` + several `macro_rules` = alternatives tried in turn | E077 |

### Logic: introduction and elimination

| Goal / hypothesis | Example | Gloss | IDs |
|---|---|---|---|
| `P → Q` | `intro hp hq` / `fun hp => hp` | assume; a proof of `→` is a function | E003, E004 |
| use `∀`/`→` | `exact h 3`, `apply h` | `∀` is a function; `apply` leaves one goal per premise | E003 |
| `P ∧ Q` | `constructor`, `⟨hp, hq⟩` | use: `h.1`/`h.2`, `obtain ⟨hp, hq⟩ := h` | E004, E005 |
| `P ↔ Q` | `constructor <;> intro h <;> exact h` | use: `h.mp : P → Q`, `h.mpr : Q → P` (also `h.1`, `h.2`) | E004, E005 |
| `P ∨ Q` | `left` / `right`, `Or.inl hp` / `Or.inr hq` | use: `cases h with \| inl hp => … \| inr hq => …`, `rcases h with hp \| hq \| hr` | E006 |
| nested patterns | `rintro (⟨hp, hq⟩ \| ⟨hp, hr⟩)` | `⟨_, _⟩` for ∧/∃, `a \| b` for ∨; `obtain ⟨hp, hq \| hr⟩ := h` | E005, E006, E008 |
| `∃ x, P x` | `⟨3, rfl⟩`, `exists 3` (core), `use 3` / `use 1, 2` (Mathlib) | use: `obtain ⟨n, hn⟩ := h` | E007, E041 |
| `rfl` pattern | `obtain ⟨r, rfl⟩ := h` | substitutes the equation (`n := r + r` everywhere) | E025, E030, E038 |
| `¬P` (= `P → False`) | `intro hp`; `hn hp : False` | `absurd hp hn : Q`, `contradiction`, `exfalso` (goal ↦ `False`) | E008 |
| `∀ x ∈ xs, P x` | `h y hy` | = `∀ x, x ∈ xs → P x`; `∃ x ∈ xs, P x` = `∃ x, x ∈ xs ∧ P x` | E025 |
| `∀ ε > 0, P` | `intro ε hε` | = `∀ ε, ε > 0 → P`; `∃ δ > 0, Q` = `∃ δ, δ > 0 ∧ Q`, build `⟨ε / 2, by positivity, by linarith⟩` | E066 |
| `∃! x, p x` (`\exists!`) | `⟨2, rfl, fun _ hy => hy⟩` | = `∃ x, p x ∧ ∀ y, p y → y = x`; use: `obtain ⟨x, hx, hu⟩ := h`, `h.exists` | E087 |
| case on a Prop | `by_cases h : a ≤ b` | two goals, `h : a ≤ b` / `h : ¬a ≤ b`; core, any Prop (classical) | E013, E058 |
| excluded middle | `rcases Classical.em Q with hq \| hnq` | `Classical.em p : p ∨ ¬p` | E058 |
| by contradiction (core) | `Classical.byContradiction h` | `(¬p → False) → p`; `by_contra` is Mathlib only | E058 |
| contrapositive (Mathlib) | `contrapose! h` | goal `Q`, `h : P` ↦ goal `¬P`, `h : ¬Q`, negations pushed in | E065 |
| contradiction (Mathlib) | `by_contra! hn` | `hn : ¬goal`, pushed (`¬ n < 2` ↦ `2 ≤ n`); goal `False` | E065 |
| push negations (Mathlib) | `push Not at h` | `¬∀` ↦ `∃¬`, `¬∃` ↦ `∀¬`, `¬ a < b` ↦ `b ≤ a` | E041 |
| `A ∨ B`, `¬A` ⊢ `B` | `h.resolve_left hne` | `Or.resolve_left` | E092 |
| Skolemize (Mathlib) | `choose g hg using h` | `h : ∀ x, ∃ y, P x y` ↦ `g`, `hg : ∀ x, P x (g x)`; `choose g h1 h2` splits `∧` | E090 |
| witness of one `∃` | `h.choose_spec` | `h.choose` is the witness, `h.choose_spec : p h.choose` | E090 |

### Term-mode proofs

| Construct | Example | Gloss | IDs |
|---|---|---|---|
| anonymous constructor | `fun ⟨hp, hq⟩ => ⟨hq, hp⟩` | builds/destructures any one-constructor type | E004 |
| dot notation | `h.elim hpr.mp hqr`, `h1.trans h2`, `hp.two_le` | `h.f` = `T.f h` where `T` is the head of `h`'s type | E043, E046 |
| `‹P›` | `h ‹P› ‹Q›` | "the hypothesis of type P" | E046 |
| `h ▸ e` | `h ▸ hb` | rewrite the type of `e` with `h : a = b` (either direction) | E046 |
| `let` pattern | `let ⟨n, _, hq⟩ := h; ⟨n, hq⟩` | destructure `∃`/`∧` inside a term | E046, E047 |
| `have` / `show … from` | `have hac : a ≤ c := Nat.le_trans h1 h2; show a ≤ c + 1 from Nat.le_succ_of_le hac` | term-mode intermediate fact / restated goal | E046 |
| term `match` | `match h with \| .inl hp => .inr hp \| .inr hq => .inl hq` | `.inl` gets its namespace from the expected type | E047 |
| tactic `match` | `match n with \| 0 => contradiction \| k + 1 => rfl` | branches see `n` replaced in goal and hypotheses | E047 |
| recursive theorem | `theorem half_le : (n : Nat) → half n ≤ n \| 0 => … \| 1 => … \| n + 2 => by have ih := half_le n; …` | the recursive call is the IH; `fib (n+2)` gets two | E048, E080 |
| `congrArg` | `congrArg (· * 3) h` | `a = b → f a = f b` | E023, E051 |
| `congrFun` | `congrFun h 0` | `f = g → f a = g a` | E051 |
| `.symm`, `.trans` on `=` | `⟨1, (Nat.mul_one n).symm⟩` | flip / chain equations | E023, E030 |
| proof irrelevance | `example (h1 h2 : 2 < 5) : h1 = h2 := rfl` | two proofs of one Prop are definitionally equal | E057 |
| constructor clash | `nofun` | proves `T.leaf ≠ T.node a b` (no case to handle) | E029 |

### Structuring proofs, goals and context

| Construct | Example | Gloss | IDs |
|---|---|---|---|
| `have` | `have h0 : f 0 ≤ f 1 := h 0` | intermediate fact; write the type (see traps) | E021 |
| `suffices` | `suffices hs : n + n = 6 by omega` | prove goal from `hs` now, then prove `hs` | E021 |
| `show` | `show evenB (2 * n + 2) = true` | restate the goal up to definitional equality | E021, E030, E048 |
| `calc` | `calc a < b := h1` / `_ ≤ c := h2` | `_` is the previous RHS; `<` and `≤` chain to `<` | E020, E089, E093 |
| `·` bullets | `constructor` then `· exact hp` / `· exact hq` | focus one goal (type `\.`) | E005 |
| `refine ?_` | `refine ⟨?_, ?_⟩ <;> assumption` | each `?_` becomes a goal | E031, E066, E087 |
| `t <;> s` | `cases b <;> rfl` | run `s` on every goal `t` produced | E016, E031 |
| `all_goals`, `first` | `constructor <;> first \| rfl \| omega` | run on all goals / first tactic that succeeds | E031, E077 |
| `assumption` | `constructor <;> constructor <;> assumption` | close a goal with a matching hypothesis | E031 |
| `case`, `next` | `case succ k ih => rw [Nat.add_succ, ih]` | select a goal by tag (and name its variables) / take the first goal | E049 |
| `intros`, `rename_i` | `intros; rename_i hp hpq; exact hpq hp` | intro with inaccessible names `a✝`, then name the newest ones | E049 |
| `specialize` | `specialize h 4` | replace `h : ∀ n, …` by its instance (`have h3 := h 3` keeps `h`) | E050 |
| `replace` | `replace h : n = 5 := by rw [Nat.zero_add] at h; exact h` | new statement, same name; the old one is gone | E050 |
| `subst` | `subst h3 h2 h1` | `h : x = e` or `e = x` deletes the variable `x` | E034, E050 |
| `clear` | `clear h2` | delete a hypothesis | E050 |
| `generalize` | `generalize n % 3 = m at h ⊢` | replace a compound term by a fresh variable | E088 |
| `set` (Mathlib) | `set y := x ^ 2 + 1 with hy` | abbreviate a subterm everywhere, `hy : y = x ^ 2 + 1`; only renames | E088 |
| `unfold` | `unfold UpperBound at *` | replace a `def` by its body; `at h ⊢`, `at *` | E012, E030, E082 |

### Rewriting and simplification

| Construct | Example | Gloss | IDs |
|---|---|---|---|
| `rw` | `rw [h, List.length_append, Nat.add_comm]` | rewrite left→right in order, then try `rfl` | E009 |
| `rw [← h]`, `rw … at` | `rw [h] at h1 h2` | right→left; in hypotheses (`at *` everywhere) | E009, E050, E069 |
| `rw (occs := [k])` | `rw (occs := [1]) [Nat.add_comm a b]` | only the k-th match (core); Mathlib: `nth_rw 1 [h]` | E061 |
| `rw` with a one-off fact | `rw [halvings, if_neg (by omega)]` | `rw [f]` unfolds one equation; `if_pos h`/`if_neg h`, `dif_pos h`/`dif_neg h` pick a branch | E026, E059, E082 |
| `simp` family | `simp`, `simp only [List.append_nil]`, `simp [sq]`, `simp [hf]`, `simp at h`, `simp_all` | default set / only these / also unfold `sq` / use hyp / in hyp / everything | E010, E016 |
| simp set | `@[simp] theorem inc_eq (n : Nat) : inc n = n + 1 := rfl` | `attribute [simp] foo`, `simp [-foo]` drops one | E027 |
| `simpa using` | `(by simpa using h)` | simp the goal and `h`, then close with `h` | E059 |
| `split` | `unfold clamp; split <;> omega` | one goal per branch of an `if`/`match` in the goal | E012 |
| `funext`, `ext` | `funext n; simp` | function equality pointwise; `ext x` for sets, `ext i j` for matrices | E022, E040, E074 |
| `congr` | `by congr` | `f a c = f b d` ↦ `a = b`, `c = d`, closed by `rfl`/hypotheses | E051 |
| `injection` | `injection h with h1 h2` | `C a b = C c d` gives `a = c`, `b = d` | E029 |
| `nomatch` | `intro h; nomatch h` | close a goal from an impossible equation (`false = true`, distinct ctors) | E029, E049 |
| `conv` | `conv => lhs; intro x; rw [Nat.mul_one]` | rewrite at one position, also under `fun`; `arg i`, `rhs`; closes by `rfl` at the end | E061 |
| `conv at h` / `conv in` | `conv in _ * 1 => rw [Nat.mul_one]` | in a hypothesis / at the first match of a pattern; Mathlib adds `conv_lhs` | E061 |
| `simp_rw` (Mathlib) | `simp_rw [h, ← two_mul, mul_add, mul_one]` | rewrite each rule in turn, under binders (`fun`, `∀`, `∑`) where `rw` fails | E064 |

### Computation and decision procedures

| Tactic | Example | Proves | IDs |
|---|---|---|---|
| `rfl` | `example : f 3 = 4 := rfl` | both sides compute to the same value (also `pred' (k + 1) = k`) | E001, E002 |
| `decide` | `example : 10 < 20 := by decide` | closed decidable Prop by evaluation (literals, BitVec, String, small sums) | E001, E018, E042, E083, E086 |
| `omega` | `example (n : Nat) (h : n > 2) : n - 1 ≥ 2 := by omega` | linear arithmetic over Nat/Int: `+ -`, `*`/`/`/`%` by literals, Nat→Int casts, `toNat` | E011, E060 |
| `grind` | `example (b : Bool) (h : (if b then 1 else 2) = 1) : b = true := by grind` | congruence + linear arith + ring normalization + `if` splits; no induction, no nonlinear `≤` | E028 |
| `bv_omega` | `example (x : BitVec 8) (h : x < 5#8) : x.toNat < 5 := by bv_omega` | linear BitVec facts via `toNat` + omega; no bitwise ops on variables (`simp` knows `x ^^^ x = 0`) | E083 |
| `trivial` | `rcases h with hp \| hq \| hr <;> trivial` | closes `True`, assumptions, `rfl`, simple `decide` | E006, E077 |
| `contradiction` | `match n with \| 0 => contradiction \| …` | hypothesis clash, `h : 0 ≠ 0`, `False` in context | E008, E047 |

### Mathlib automation

| Tactic | Example | Proves / does | IDs |
|---|---|---|---|
| `ring` | `example (a b : ℤ) : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring` | commutative (semi)ring identities; ignores hypotheses | E034 |
| `ring_nf` | `ring_nf; rw [I_sq]; ring` | normalize without closing (also under binders) | E073 |
| `linarith [..]` | `linarith [sq_nonneg (a - b)]` | linear consequences of hyps over ordered fields; nonlinear monomials are atoms | E035 |
| `nlinarith [..]` | `nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (x - y))]` | multiplies pairs of hyps/hints, then linarith | E068, E089 |
| `linear_combination` | `linear_combination (a + b + 3) * h - 2 * h2` | goal − Σ cᵢ·(hypᵢ) closes by `ring`; works in ℂ (no order needed) | E067 |
| `norm_num` | `example : (1 : ℚ) / 3 < 1 / 2 := by norm_num` | literal arithmetic, `%`, `⁻¹`, `Nat.Prime 97`, `¬ Nat.Prime 91`, `(6 : ℤ) ∣ 42` | E036, E039, E043 |
| `positivity` | `example (x : ℝ) : 0 ≤ x ^ 2 + \|x\| := by positivity` | only `0 < e`, `0 ≤ e`, `e ≠ 0`, by the syntax of `e` (uses `0 < a` atoms from context) | E037 |
| `gcongr` | `example (x y : ℝ) (hx : 0 < x) (h : x < y) : 1 / y < 1 / x := by gcongr` | `f a ≤ f b` from `a ≤ b` for same-shape sides; side goals by positivity | E044 |
| `gcongr with i hi` | `gcongr with i hi; exact h i hi` | term-by-term on `∑`/`∏` over one index set; `hi : i ∈ s` | E071 |
| `field_simp` | `field_simp; ring` | clear denominators; needs `x ≠ 0` facts in context; `at h` too | E045 |
| casts | `push_cast; ring`, `exact_mod_cast h`, `norm_cast at h` | push `↑` to the leaves / prove up to casts / pull `↑` out; `push_cast [h]` uses `h : b ≤ a` | E063, E092 |
| `zify` | `zify [h, h2]; ring` | ℕ goal ↦ ℤ; the `b ≤ a` facts make `↑(a - b) = ↑a - ↑b` | E092 |
| `lift` | `lift x to ℕ using hx` | `x : ℤ` with `hx : 0 ≤ x` becomes `x : ℕ` (seen as `↑x`) | E092 |
| `abel` | `example {G : Type} [AddCommGroup G] (a : G) : a + a = 2 • a := by abel` | additive commutative groups; numeral `n • a` only | E093 |
| `group` | `example {G : Type} [Group G] (a b : G) : a * b * b⁻¹ = a := by group` | any (noncommutative) group; ignores hypotheses | E093 |
| `tauto` | `example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬P) := by tauto` | propositional tautologies (∧ ∨ → ¬ ↔), classical; not under ∀ | E091 |
| `aesop` | `aesop (add norm Set.subset_def)` | search: intro, simp, split, apply; extra rewrite rule via `add norm` | E091 |
| `fun_prop` | `fun_prop (disch := norm_num)` | `Continuous`, `Differentiable ℝ`, `ContinuousAt` from pieces; `disch` proves side goals like `2 ≠ 0` | E075 |
| `fin_cases` | `fin_cases i <;> simp [f]` | one goal per value of `i : Fin n` or `ZMod n` | E072, E074 |
| `interval_cases` | `interval_cases n <;> norm_num` | one goal per value between bounds in context (ℕ has 0; ℤ needs both) | E094 |
| `ext i j` | `ext i j; fin_cases i <;> fin_cases j <;> rfl` | matrix identity entrywise; `ext i` for vectors | E074 |

### Induction and recursion

| Construct | Example | Gloss | IDs |
|---|---|---|---|
| Nat induction | `induction n with \| zero => decide \| succ k ih => simp only [tri]; omega` | `ih` for `k`, goal for `k + 1` | E014, E079 |
| List induction | `induction xs with \| nil => rfl \| cons x xs ih => simp [app, ih]` | | E015 |
| `generalizing` | `induction n generalizing acc with` | IH for every accumulator | E085 |
| unnamed then `case` | `induction n` then `case succ k ih => …` | tags `zero`/`succ`, `nil`/`cons` | E049 |
| `cases` on data | `cases o with \| none => simp \| some x => simp` | Bool, Option, enums: no IH | E016, E018, E054 |
| from a base | `induction n, hn using Nat.le_induction with \| base => norm_num \| succ k hk ih => nlinarith` | for `hn : n₀ ≤ n` (Mathlib) | E089 |
| functional induction | `fun_induction ack m n with \| case1 n => omega \| case2 m ih => omega \| case3 m n ih1 ih2 => omega` | one goal per equation, one IH per recursive call; call already unfolded | E084 |
| `fun_cases` | `fun_cases pred2 n <;> omega` | same split, no IHs; non-recursive `f` too | E084 |
| `f.induct`, `f.eq_k` | `#check @half.induct`, `#check @ack.eq_3` | the principle `fun_induction` uses; one equation lemma per pattern | E079, E084 |

### Bool vs Prop

| Name | Statement | IDs |
|---|---|---|
| `decide p` | `decide (2 < 3) = true := rfl`: a decidable Prop as a Bool | E054, E062 |
| `decide_eq_true` / `of_decide_eq_true` | `p → decide p = true` / `decide p = true → p` | E062 |
| `decide_eq_true_iff` | `decide p = true ↔ p` | E054 |
| `beq_iff_eq` | `(a == b) = true ↔ a = b` (`==` Bool, `=` Prop; BEq comes with DecidableEq) | E054, E062 |
| `Bool.and_eq_true` | `((a && b) = true) = (a = true ∧ b = true)`: an `=` of Props, use with `rw` | E062 |
| `List.all_eq_true` | `l.all f = true ↔ ∀ x ∈ l, f x = true` | E062 |
| Bool as Prop | `example (b : Bool) (h : b) : b = true := h`: coerced to `b = true` | E062 |

### Library names by area (E001–E094)

| Area | Names | IDs |
|---|---|---|
| Nat | `Nat.add_comm`, `Nat.add_zero`, `Nat.zero_add`, `Nat.mul_one`, `Nat.mul_comm`, `Nat.mul_assoc`, `Nat.add_mul`, `Nat.mul_add`, `Nat.add_succ`, `Nat.le_add_left`, `Nat.le_trans`, `Nat.le_succ`, `Nat.le_succ_of_le`, `Nat.lt_of_succ_lt`, `Nat.succ_lt_succ`, `Nat.succ_ne_zero`, `Nat.succ_ne_self`, `Nat.le_of_lt_succ`, `Nat.lt_add_one`, `Nat.zero_lt_of_ne_zero`, `Nat.pos_iff_ne_zero`, `Nat.add_pos_left`, `Nat.one_pos`, `Nat.mul_le_mul`, `Nat.pow_succ`, `Nat.sub_sub`, `Nat.le_of_dvd`, `Nat.mod_lt`, `Nat.add_mod_right`, `Nat.div_mul_le_self`, `Nat.div_zero` | E007–E092 |
| Int | `Int.add_comm`, `Int.ediv_zero`, `Int.emod_zero`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`, `Int.toNat_of_nonneg`; `x.tdiv`, `x.tmod`, `x.toNat`, `x.natAbs` | E019, E060 |
| Lists | `List.length_append`, `List.length_map`, `List.length_reverse`, `List.length_filter_le`, `List.append_nil`, `List.cons_append`, `List.append_eq_nil_iff`, `List.reverse_append`, `List.map_map`, `List.map_id'`, `List.filter_map`, `List.foldl_append`, `List.range_succ`, `List.mem_map`, `List.mem_append`, `List.mem_cons`, `List.getElem_map`, `List.getElem?_eq_getElem`, `List.countP_append`, `List.countP_le_length`, `List.countP_singleton` | E009–E086 |
| Arrays | `Array.size_push`, `Array.toList_push`, `Array.getElem?_push`, `Array.getElem?_eq_getElem` | E082 |
| BitVec | `BitVec.toNat_add` (`(x + y).toNat = (x.toNat + y.toNat) % 2 ^ w`), `BitVec.isLt`, `BitVec.lt_def` | E083 |
| Strings | `String.toList_append`, `String.length_toList`, `String.toList_singleton`, `Char.isDigit`, `Char.toNat` | E086 |
| Logic, functions | `absurd`, `Classical.em`, `Classical.byContradiction`, `Or.inl`/`Or.inr`, `Or.elim`, `Or.resolve_left`, `Iff.trans`, `congrArg`, `congrFun`, `funext_iff` (core), `Function.comp_apply`, `Prod.ext`, `Subtype.ext`, `Fin.isLt`, `if_pos`/`if_neg`, `dif_pos`/`dif_neg` | E008–E092 |
| Quotients | `Quotient.mk`, `Quotient.lift`, `Quotient.sound` (`a ≈ b → mk a = mk b`), `Quotient.exact` (converse), `Quotient.ind` | E081 |
| Algebra (Mathlib) | `two_mul`, `zero_add`, `add_zero`, `mul_add`, `mul_one`, `mul_comm`, `pow_succ`, `sq_nonneg`, `mul_nonneg`, `add_nonneg`, `sub_ne_zero`, `lt_irrefl`, `zero_ne_one` | E035–E089 |
| Parity, divisibility, primes | `Even` (`∃ r, n = r + r`), `Odd` (`∃ k, n = 2 * k + 1`), `even_iff_two_dvd`, `dvd_add`, `dvd_sub`, `dvd_mul_of_dvd_right`, `Nat.Prime.two_le`, `Nat.Prime.odd_of_ne_two`, `Nat.Prime.eq_one_or_self_of_dvd`, `Nat.dvd_prime`, `Nat.one_le_pow` | E038, E039, E043, E092 |
| Sets | `Set.mem_inter_iff`, `Set.mem_union`, `Set.mem_setOf_eq`, `Set.mem_insert_iff`, `Set.mem_singleton_iff`, `Set.subset_def`, `Set.mem_Icc` | E040, E066, E091 |
| Finset, Fin sums | `Finset.sum_range_succ`, `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.prod_range_succ`, `Finset.prod_const`, `Finset.card_range`, `Finset.mem_range`, `Fin.sum_univ_two`, `Fin.sum_univ_three`, `Fin.sum_univ_succ`, `Fin.val_succ` | E042, E064, E070, E071, E074 |
| Real analysis | `abs_sub_lt_iff`, `abs_mul`, `pow_le_one₀`, `div_zero`, `div_self`, `Real.sqrt_eq_zero_of_nonpos`, `Real.log_zero`, `Real.exp`, `Real.sin`, `Real.cos`, `Real.log` | E037, E066, E069, E075 |
| Complex | `Complex.ext`, `Complex.I_sq`, `Complex.conj_re`, `Complex.conj_im`, `Complex.normSq_apply` | E073 |
| Matrices | `Matrix.det_fin_two`, `Matrix.mul_apply`, `Matrix.mulVec`, `dotProduct` | E074 |

### Math notation (Mathlib) and how to type it

| Notation | Meaning | Typed | IDs |
|---|---|---|---|
| `ℕ ℤ ℚ ℝ ℂ` | number types (`Nat`, `Int`, …) | `\N \Z \Q \R \C` | E034 |
| `(5 : ℝ)` | fix a literal's type (default is ℕ) | | E036 |
| `↑n`, `(n : ℝ)` | cast of `n : ℕ` into ℝ (or ℤ); `↑i` for `i : Fin n` is its value in ℕ | `\u` | E063, E070, E092 |
| `a ∣ b` | divides: `∃ c, b = a * c` | `\mid` (not `\|`) | E039 |
| `∑ i ∈ s, f i`, `∏ i ∈ s, f i` | finite sum / product over a `Finset`; `range n = {0, …, n-1}` | `\sum`, `\prod` | E042, E070 |
| `∑ i, g i` | sum over every `i : Fin n` (`Finset.univ`) | | E070, E074 |
| `#s` | number of elements of a finset | | E070 |
| `{n : ℕ \| n < 3}`, `A ∩ B`, `A ∪ B`, `A ⊆ B` | set-builder, intersection, union, subset (`∀ x, x ∈ A → x ∈ B`) | `\cap \cup` | E040 |
| `Set.Icc a b` | closed interval [a, b]; membership is `a ≤ x ∧ x ≤ b` | | E066 |
| `\|x\|`, `√x`, `x⁻¹` | absolute value, `Real.sqrt x`, inverse | `\sqrt`, `\inv` | E036, E066, E069 |
| `ZMod n` | ℤ modulo n; `(2 : ZMod 3) + 2 = 1 := rfl` | | E072 |
| `![a, b, c]` | vector `Fin 3 → α`: 0 ↦ a, 1 ↦ b, 2 ↦ c | | E072, E074 |
| `!![a, b; c, d]`, `M i j` | 2×2 `Matrix (Fin 2) (Fin 2) α`, rows split by `;`; entry row i, col j from 0 | | E074 |
| `Mᵀ`, `M *ᵥ v`, `c • M`, `(1 : Matrix _ _ ℝ)` | transpose, matrix–vector product, scalar multiple, identity (`ᵀ`, `*ᵥ` need `open Matrix`) | `\^T`, `*\_v`, `\smul` | E074 |
| `z.re`, `z.im`, `I`, `conj z`, `Complex.normSq z` | parts, `I ^ 2 = -1`, conjugate (`open ComplexConjugate`; shown `(starRingEnd ℂ) z`), squared modulus `re² + im²` | | E073 |
| `n • a` | `a + … + a` (n times) in an additive group | `\smul` | E093 |
| `Continuous f`, `Differentiable ℝ f`, `ContinuousAt f a` | continuity everywhere, differentiability over the field ℝ, continuity at the point `a` | | E075 |

### Traps

- Nat subtraction truncates (`3 - 5 = 0`): `n - m + m = n` needs `m ≤ n`; casting `↑(a - b) = ↑a - ↑b` needs `b ≤ a` (`push_cast [h]`, `zify [h]`). (E011, E063, E092)
- `have h := f 0` for `f : ∀ n, P n (n + 1)` gives `P 0 (0 + 1)`; write the type: `have h : P 0 1 := f 0`. (E021)
- `0 + n` is not definitionally `n` (`n + 0` is), so `rfl` fails on it; use `Nat.zero_add`. (E049, E050)
- `omega` treats `x * y` and `2 ^ n` as opaque atoms: expand with `Nat.add_mul`/`Nat.mul_add` or `Nat.pow_succ` first. (E011, E014, E048)
- Well-founded definitions (`termination_by`, `ack`) do not compute by `rfl`/`decide`; use `simp [f]` or `rw [f]`. Structural ones do. (E026, E079)
- `obtain`, `intro`, `⟨_, _⟩` see through a `def … : Prop`; `rw`, `simp`, `omega` do not, so `unfold` it first. (E030)
- An `∃` eliminates only into `Prop`: `def f (h : ∃ n, p n) : Nat := match h with | ⟨n, _⟩ => n` is rejected; use a Σ-type, a subtype, or `noncomputable` + `h.choose`. (E057, E090)
- `Bool.and_eq_true` is an `=` between Props, so `exact` fails where `rw` works. (E062)
- Without `generalizing acc` the IH is about the original accumulator and the step gets stuck. (E085)
- `case …`/`next …`/`have … := by …` on one line swallow every later `;` tactic; use newlines or parentheses: `have : n = 0 ∨ n = 1 := (by omega); rcases this with rfl | rfl <;> decide`. (E031, E049)
- Macro hygiene: a name written inside a `` `(tactic| …) `` quotation is renamed (`hp✝`); reach hypotheses with `assumption`/`simp_all`. (E077)
- A second `notation`/`infixl` for the same token makes every use ambiguous; edit the existing line. (E076)
- Mathlib's partial operations return junk values: `x / 0 = 0`, `√(-4) = 0`, `Real.log 0 = 0`, `n / 0 = 0` in ℕ and ℤ, `a % 0 = a` in ℤ. Honest lemmas carry side conditions (`div_self : a ≠ 0 → a / a = 1`). (E060, E069)
- Int `/` and `%` are `Int.ediv`/`Int.emod`: `(-9) / 4 = -3`, `(-9) % 4 = 3` (remainder ≥ 0). C-style truncation is `Int.tdiv`/`Int.tmod`: `-2`, `-1`. `toNat` clamps negatives to 0. (E060)
- `ring`, `group`, `abel` ignore hypotheses: `subst`/`rw` first, use a `calc`, or `linear_combination`. `field_simp` needs the `≠ 0` facts in context. (E034, E045, E067, E093)
- `abel` handles numeral `3 • a`, not `n • (a + b)` with a variable `n`. (E093)
- `positivity` only proves `0 < e`, `0 ≤ e`, `e ≠ 0`; `gcongr` with powers needs `0 ≤ a`. (E037, E044)
- `push_neg` is deprecated in favour of `push Not` (still works, with a warning). `by_contra`, `conv_lhs`, `nth_rw`, `use` are Mathlib only; in core use `Classical.byContradiction`, `conv => lhs`, `rw (occs := [k])`, `exists`. (E041, E058, E061)
- `funext_iff` is the core name (`f = g ↔ ∀ x, f x = g x`); `Function.funext_iff` does not exist at this Mathlib version. (E051)
- `tauto` does not look inside `∀` or `∩`; plain `aesop` makes no progress on `⊆` for sets without `(add norm Set.subset_def)`. (E091)
- `interval_cases` on `x : ℤ` needs a lower bound in context; ℕ gets 0 for free. Close branches whose substituted hypothesis is false with `simp_all`. (E094)
- `bv_omega` does not understand `&&&`, `|||`, `^^^` on variables; `<` on `BitVec` is unsigned. (E083)
- Core has no `Fintype`, so `decide` cannot check `∀ s : Suit, …`; split with `cases s`. (E054)
- A `String` is UTF-8 data, not a `List Char`: reason through `s.toList`; `simp` does not turn `s.length` into `s.toList.length` (`rw [← String.length_toList]`). (E086)
- In `∑ i : Fin n, g ((i : ℕ) + 1)` the `+ 1` is in ℕ after the cast, not wrap-around `Fin` addition. (E070)
- `Sort u` vs `Type`: with `{α : Type}`, `idU Nat` fails because `Nat : Type` but `Type : Type 1`. (E078)

## Logic and types, verified programs, semantics

Medium/hard topics 01-03 (M001-M050, H001-H028). Core Lean 4.32.0 only (no Mathlib) unless noted;
`import Std.Tactic.Do` for the `mvcgen` problems. Snippets are taken from the cards and reference
solutions or were `#check`ed at the pinned toolchain. Names like `Star`, `BigStep`, `run`, `update`
are each problem's own definitions, not library names.

### Inductive types, predicates and rule induction

An inductive `Prop` is a set of inference rules: each constructor is a rule and a proof term is a
derivation tree. `cases h` inverts the last rule; `induction h` is rule induction.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| unary naturals | `inductive N \| zero \| succ (n : N)` | `add n zero = n` is `rfl`; `add zero n = n` needs induction; write helpers `zero_add`, `succ_add` | M002 |
| inductive predicate | `inductive Small : Nat → Prop \| zero : Small 0 \| one : Small 1` | rules as constructors; build proofs with `.one`, `.step h h2` | M004, M005 |
| relation with parameters | `example : M005.Star R a c := .step h h2` | `Star R a b`: reflexive-transitive closure (`.refl a`, `.step (h : R a b) (hs : Star R b c)`) | M005, M041, H006, H023, H027 |
| rule induction | `induction h with \| refl e => … \| step s _ ih => …` | one case per rule, an IH per recursive premise | M004, M005, M041, H001 |
| inversion | `example : ¬ Small 2 := by intro h; cases h` | only rules whose conclusion unifies survive; none left closes the goal | M004, M040, H020 |
| inversion, named premises | `cases h with \| seq h1 h2 => …` | name each surviving rule's premises | M043, H014, H024, H025 |
| no rule fits | `example (h : H006.R4 .pa x) : False := nomatch h` | also `fun _ b h => nomatch h` inside terms | H005, H006 |
| implicit ctor arg in a pattern | `\| @step _ q _ st _ ih => …` | `@` exposes implicit constructor args (here the middle configuration) | M020, H023, H022 |
| uniform index = parameter | `induction h` on `h : Prov (a :: Γ) b` | `Γ` is the same in every rule, so Lean promotes it to a parameter: no `generalize` needed | H001 |
| named implicit at a use site | `.mp (a := a) (.hyp (by simp)) (.hyp (by simp))` | fix the cut formula so the `by simp` premises see no metavariable | H001, H002, H022 |
| induction on a formula/type | `induction a generalizing w w' with \| imp a b iha ihb => …` | structural induction on syntax, IH over every world / term | H002, H027 |
| shared alternatives | `\| neg _ ih \| andL _ ih \| orL _ ih => simp [eval, ih]` | one tactic for several cases (same binder names) | M042, H005 |
| determinism pattern | `induction h1 generalizing e2 <;> cases h2 <;> simp_all` | invert the second derivation in each case of the first | M040, H021 |
| inversion lemma | `theorem cat_inv (h : Matches (.cat r s) w) : ∃ u v, w = u ++ v ∧ …` | state over a variable index, prove by `cases h`; use with `obtain ⟨u, v, rfl, hu, hv⟩` | H022, H028 |

### Generalizing indices before `induction`

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| make an index a variable | `generalize hw : Com.while b c = w at h` | `induction h` needs variable indices; `hw` remembers the shape | M045, H021, H025 |
| kill impossible cases | `\| whileT hb hc _ _ ih2 => cases hw; …` / `\| _ => cases hw` | `cases hw` unifies in the right rules, refutes the rest | M045, H022 |
| pair-valued indices | `generalize hp : (c, s) = p at h; generalize hq : (Com.skip, s') = q at h` | generalize every non-variable index, then `induction h generalizing c s` | H023 |
| non-variable context | `generalize hΓ : (fun _ => none : Ctx) = Γ at h` | closed context before inducting on typing | H026 |
| list-valued index | `generalize hΔ : a :: Γ = Δ at h` | same trick for a context list | H001 |
| split pair variable | `obtain ⟨c', t⟩ := q` | after naming `q` with `@step` | H023 |

### Dependent types

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Fin n` | `example : Fin 5 := ⟨3, by decide⟩` | value + proof `< n`; `i.val`, `i.isLt`, `Fin.ext`, `Fin.last n : Fin (n+1)`, `Fin.castSucc` | M006 |
| subtype | `abbrev Pos := {n : Nat // 0 < n}` | `⟨v, proof⟩`, `p.val`, `p.property`, `Subtype.ext h` | M007, H004 |
| subtype proof for omega | `have := p.property; omega` | omega does not look inside `.property` | M007 |
| length-indexed vector | `def Vec.tail' : Vec α (n + 1) → Vec α n \| .cons _ xs => xs` | matching refines the index; the `nil` case is impossible, so omitted | M008, M012 |
| index arithmetic | `example (n m : Nat) : m + (n + 1) = (m + n) + 1 := rfl` | `+` recurses on its 2nd argument, so `append : Vec α n → Vec α m → Vec α (m + n)` checks by `rfl` | M008 |
| indexed families | `inductive Instr : Nat → Nat → Type \| push {n} (k : Nat) : Instr n (n + 1)` | stack depth in the type: `run` needs no error case | M012 |
| match on implicit indices | `def Code.run : {n m : Nat} → Code n m → Vec Nat n → Vec Nat m \| _, _, .nil, s => s` | bind the indices with `_` | M012, H009 |
| fix an implicit by name | `(compile (n := 0) (.add (.num 2) (.num 3))).run .nil` | also `rename_typing (ρ := Nat.succ)`, `hoare_while (I := …)` | M012, H026, M045 |
| type-level function | `def Fmt.type : List Fmt → Type \| [] => String \| .nat :: fs => Nat → Fmt.type fs` | the type of `sprintf fs` is computed from `fs` | M013 |
| unpack computed types | `cases args` (on `Unit`), `obtain ⟨n, a⟩ := args` (on a pair) | args of a type computed by recursion | M013 |
| reducible type map | `@[reducible] def Ty.denote : Ty → Type \| .nat => Nat \| .bool => Bool` | lets instances (`+` on `t.denote`) see through the map | H009 |
| dependent pair | `example : (Σ t, H009.Expr t) := ⟨.nat, .lit 3⟩` | `Σ t, Expr t`: a type tag and a term of that type | H009 |
| cast along an equation | `example (h : t1 = t2) (x : Expr t1) : Expr t2 := h ▸ x` | `subst h` first and `h ▸ x'` becomes `x'` | H009, H021 |
| Σ injectivity | `Sigma.mk.inj : ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ → a₁ = a₂ ∧ b₁ ≍ b₂` | `simp at h` applies it; `Sigma.mk.inj_iff` does not exist | H009 |
| heterogeneous equality | `simp at h; obtain ⟨rfl, h⟩ := h; cases h` | `x ≍ y` is `HEq x y`; once types agree, `cases` substitutes | H009 |
| intrinsic typing | `inductive Expr : Ty → Type \| plus (a b : Expr .nat) : Expr .nat` | ill-typed terms are unrepresentable; `eval : Expr t → t.denote` cannot fail | H009 |

### Type classes, monads, decidability

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| class with laws | `class Pointed (α : Type) where pt : α; pt_eq : pt = pt` | proof fields; use as `MyMonoid.op_assoc a b c`, `CMon.op_comm a b` under `[C α]` | M009, H008 |
| instance | `instance instPointedNat : Pointed Nat := { pt := 0, pt_eq := rfl }` | or `where` syntax | M009 |
| structure value with binder fields | `{ W := Unit, le _ _ := True, refl _ := trivial, … }` | field-as-function syntax; law fields usable as lemmas `M.trans h1 h2` | H002 |
| decidability by reduction | `fun n => decidable_of_iff (n < 3) (by …)` | `decidable_of_iff (q) (h : q ↔ p) [Decidable q] : Decidable p`; then `decide` works | M010 |
| bounded search | `example : IsSmall 2 := by decide` | `∃ k, k ≤ n ∧ …` is decidable already | M010 |
| `deriving DecidableEq` | `inductive Ty \| base \| arr (A B : Ty) deriving DecidableEq` | makes `if A = B then … else …` legal | M049, H009, H011 |
| hand-built Monad | `instance : Monad (St σ) where pure a := fun s => (a, s); bind m f := fun s => f (m s).1 (m s).2` | state monad `St σ α := σ → α × σ` | M014 |
| `LawfulMonad.mk'` | `LawfulMonad.mk' (St σ) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)` | args after `m`: `id_map`, `pure_bind`, `bind_assoc`; the rest are autoParams | M014 |
| unfold a `do` block | `simp only [relabel, bind, pure] at *` | over a hand-made instance; then `(relabel t s).2` is a plain projection | M014 |
| `Except` | `def quarter (n : Int) : Except String Int := do let m ← halve n; halve m` | `pure` = `.ok`, `throw e` = `.error e`; an error short-circuits | M039 |
| split a monadic sub-result | `cases h : eval a with \| ok x => … \| error e => …` | M039 supplies `rfl` simp lemmas `ok_bind`, `error_bind`, `map_ok` | M039 |
| `List.range'` | `example : List.range' 3 4 = [3, 4, 5, 6] := rfl` | `List.range'_append_1 : range' s m ++ range' (s + m) n = range' s (m + n)` | M014 |

### Foundations: extensionality, axioms, choice

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| function equation at a point | `congrFun h x : f x = g x` | from `h : f = g` | M011 |
| function extensionality | `funext fun y => propext (hx y)` | pointwise ↔ ⇒ predicates equal (also Hoare assertions) | M011, H003, H024 |
| propositional extensionality | `propext ⟨h1, h2⟩ : p = q` | ↔ to `=` on `Prop` | M011, H003 |
| transport | `cast h hp : Q` | from `h : P = Q`, `hp : P` | M011 |
| diagonal | `fun n => !f n n` | Lawvere with `t := Not` gives Russell | M011 |
| proof irrelevance | `example (h1 h2 : ∃ x, P x) : h1 = h2 := rfl` | definitional | H003 |
| `subst` vs `rw` | `subst h; rfl` | `subst` rewrites inside other hypotheses' types; `rw` fails with "motive is not type correct" | H003 |
| constructor clash | `Bool.noConfusion h : False` | from `h : true = false` | H003 |
| axiom audit | `#print axioms H003.diaconescu` | card line `AXIOMS: propext, Quot.sound` forbids `Classical.choice` | H003 |
| choice | `Classical.choose h`, `Classical.choose_spec h : p (Classical.choose h)` | witness of an `∃` | H004 |
| by contradiction | `Classical.byContradiction fun h => …` | proves `p` from `¬p → False` | H004 |
| iterate a function | `fun n => Nat.rec x (fun _ y => g y) n` | `x, g x, g (g x), …` (descending chain) | H004 |

### Well-founded relations

`Acc r a`: every `r`-descending path from `a` is finite. `WellFounded r`: every `a` is `Acc`.
Convention: `r y x` means `y` is smaller, so "no infinite chain `a₀ → a₁ → …`" is `WellFounded (fun b a => R a b)`.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| build `Acc` | `.intro a (h : ∀ y, r y a → Acc r y)` | `Acc.intro` | H004 |
| build / use `WellFounded` | `⟨fun ⟨a, b⟩ => acc_lex hs (hr.apply a) b⟩` | `WellFounded.intro` is `⟨h⟩`; `h.apply a : Acc r a` | H004 |
| well-founded induction | `induction a using h.induction with \| _ a ih => …` | `ih : ∀ y, r y a → P y`; also through a def like `Terminating R` | H004, H006 |
| induction on `Acc` | `induction ha generalizing b with \| intro a _ iha => …` | same `ih` shape | H004 |
| lexicographic order | `Prod.Lex.left b₁ b₂ (h : ra a₁ a₂)`, `Prod.Lex.right a (h : rb b₁ b₂)` | split with `cases hp with \| left _ _ h => … \| right _ h => …` | H004 |
| measure pull-back | `InvImage.wf weight Nat.lt_wfRel.wf` | `<` on `Nat` along `weight` | H005 |
| subrelation | `Subrelation.wf (fun h => weight_decreases h) (…)` | `q ⊆ r`, `r` well-founded ⇒ `q` well-founded | H005 |
| power facts for weights | `Nat.pow_lt_pow_right (by omega) h`, `Nat.lt_two_pow_self`, `Nat.one_le_two_pow` | also `Nat.pow_le_pow_right`, `Nat.pow_succ`, `Nat.pow_add` | H005 |
| product atoms for omega | `Nat.mul_le_mul_left k h : k * a ≤ k * b` | and `_right`; hand omega bounds on `2 ^ x * 2 ^ y` | H005 |
| Bool De Morgan | `Bool.not_and x y : (!(x && y)) = (!x \|\| !y)` | and `Bool.not_or` | H005 |
| local confluence ⇒ confluence | `obtain ⟨d, hbd, hcd⟩ := hl _ _ _ h1 h2` | Newman's lemma by WF induction; `cases h1 <;> cases h2` enumerates step pairs | H006 |

### Quotients

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| equivalence | `⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => by unfold R at *; omega⟩` | `Equivalence.mk` fields `refl`, `symm`, `trans` | H007 |
| setoid | `instance intSetoid : Setoid (Nat × Nat) := ⟨R, R_equiv⟩` | `a ≈ b` unfolds to `R a b` | H007 |
| quotient type | `def MyInt : Type := Quotient intSetoid` | `Quotient.mk intSetoid (a, b)` | H007 |
| lift a function | `Quotient.lift (fun x => MyInt.mk x.2 x.1) (by …)` | proof obligation: respects `≈` | H007 |
| two arguments | `Quotient.lift₂ f (by intro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ h1 h2; …)` | binder order `a₁ b₁ a₂ b₂`, then `a₁ ≈ a₂ → b₁ ≈ b₂ →` | H007 |
| equal classes | `⟨Quotient.exact, fun h => Quotient.sound h⟩` | `sound : a ≈ b → mk a = mk b`; `exact` is the converse | H007 |
| quotient induction | `induction x using Quotient.inductionOn with \| h p => …` | replace `x` by `Quotient.mk _ p` | H007 |
| restate a definitional hyp | `intro ⟨a, b⟩ ⟨c, d⟩ (h : a + d = c + b)` | type ascription unfolds `≈`; `show a + d = c + b` for the goal | H007 |
| Int round trip | `Int.toNat_sub_toNat_neg : (n.toNat : Int) - ((-n).toNat : Int) = n` | surjectivity witness `MyInt.mk n.toNat (-n).toNat` | H007 |

### Proof by reflection

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| reify | `inductive Expr \| atom (i : Nat) \| unit \| op (a b : Expr)` | syntax of the goal; `denote ρ` maps it back (`ρ i` = value of atom `i`) | H008 |
| soundness of normaliser | `theorem reflect (h : norm e1 = norm e2) (ρ) : e1.denote ρ = e2.denote ρ` | normal form: sorted atom list | H008 |
| close by computation | `exact reflect e1 e2 (by decide) (fun i => [a, b, c, d].getD i unit)` | the kernel computes both normal forms | H008 |
| Perm rule induction | `induction h with \| nil => _ \| cons x _ ih => _ \| swap x y l => _ \| trans _ _ ih1 ih2 => _` | permutation-invariance of `denoteList` | H008 |
| push `=` through a function | `congrArg (denoteList ρ) h` | `congrArg f : a₁ = a₂ → f a₁ = f a₂` | H008 |

### Accumulators and loop invariants

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| generalize the accumulator | `induction n generalizing acc` | the IH must hold for every `acc` (the loop invariant); specialise afterwards: `foo n 0` | M001, M015, M016, M026 |
| two accumulators | invariant `a = fib k`, `b = fib (k + 1)` | state the general lemma, then instantiate | M026 |
| `for` loop as `foldl` | `example : sumLoop xs = xs.foldl (fun b a => b + a) 0 := by simp [sumLoop]` | `Id.run do let mut s := 0; for x in xs do s := s + x; return s` | M018 |
| foldl step | `List.foldl_cons : foldl f b (a :: l) = foldl f (f b a) l` | | M018, H018 |
| foldl over the prefix read | `induction l generalizing p st`, then `simpa using ih (p ++ [x]) _ step` | invariant indexed by the processed prefix | H018 |
| strengthen before induction | `suffices ∀ rest, P (bs ++ rest) by simpa using this []` | | H016 |
| arbitrary threshold | `induction xs generalizing t S` | spec starts at `0`; the IH needs any `t` | H017 |
| general stack | `induction e generalizing n` / `… generalizing s` | compiler correctness on every initial stack/depth | M012, H019 |

### Termination and functional induction

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| measure | `termination_by xs => xs.length` / `termination_by hi - mid` | well-founded recursion | M017, M035, H010, H011 |
| prove the decrease | `decreasing_by · have := lows_le p xs; simp only [List.length_cons]; omega` | one goal per recursive call | M017, M035 |
| lexicographic, found automatically | `\| x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else …` | one list shrinks, the other stays | M030, H010, H015 |
| equation lemmas | `#check @loop.eq_2` / `rw [loop]` | wf defs do not compute by `rfl`/`decide`; unfold one step | M035 |
| follow the recursion | `fun_induction qsort xs with \| case1 => … \| case2 p xs ih1 ih2 => …` | one case per arm/branch, `if` conditions as hyps, an IH per call | M017, M025, M029, M030, H010 |
| with `generalizing` | `fun_induction merge h1 h2 generalizing lo with \| case3 .. ih \| case4 .. ih` | overlapping matches give one case each | H015 |
| all cases at once | `fun_induction opt c <;> simp_all [Code.run, Instr.run]` | | M012 |
| `let` in a case | `show powFast (b * b) (e / 2) = b ^ e` | `let r := …` appears as a local def; `show` unfolds it (or `simp only [half]`) | M027, H010 |
| `if x = y` arm | (automatic) | `fun_induction` substitutes `y := x` in that case | M031 |
| filter length | `List.length_filter_le p l : (l.filter p).length ≤ l.length` | for `decreasing_by` | M017 |
| non-linear via atoms | `simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at h ⊢; omega` | expand `(r+1)*(r+1)` so omega sees `r * r` as one atom | M028 |
| Nat powers | `Nat.pow_two`, `Nat.pow_mul`, `Nat.pow_succ'` | with `congr 1` to reduce `b ^ x = b ^ y` to `x = y` | M027 |
| Euclid | `Nat.dvd_mod_iff : k ∣ n → (k ∣ m % n ↔ k ∣ m)` | `Nat.dvd_refl`, `Nat.dvd_zero` | M029 |
| strong induction | `induction n using Nat.strongRecOn with \| _ n ih => …` | `ih : ∀ m < n, P m` | M003 |

### Hoare triples with `mvcgen` (Std.Do)

Header: `import Std.Tactic.Do`, `open Std.Do`, `set_option mvcgen.warning false`.
`⦃P⦄ prog ⦃⇓ r => Q⦄`: run from a state satisfying `P`, `prog` returns some `r` with `Q`.
`⌜φ⌝` lifts a `Prop` to an assertion. `wp⟦prog⟧ Q` is the weakest precondition; `⊢ₛ A` means
assertion `A` holds. Type them as `\{{ \}}`, `\ulc \urc`, `\d=`.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| a triple | `example : ⦃⌜True⌝⦄ (pure 3 : Id Nat) ⦃⇓ r => ⌜r = 3⌝⦄ := by mvcgen` | | M036, H012 |
| loop invariant | `mvcgen [maxLoop] invariants · ⇓⟨cur, m⟩ => ⌜(∀ x ∈ cur.prefix, x ≤ m) ∧ …⌝` | `cur.prefix` processed, `cur.suffix` to go | M036 |
| several `let mut`s | `· ⇓⟨cur, st⟩ => ⌜MajInv cur.prefix st.1 st.2⌝` | `st.1`, `st.2` in declaration order | H012 |
| discharge VCs | `all_goals grind [majInv_nil, majInv_reset, …]` | one VC per loop-body branch + entry + exit | M036, H012 |
| invariant skeleton | `mvcgen [f] invariants?` | prints the shape (not inductive) | M036, H012 |
| labelled invariant | `invariants \| inv1 c _ => ⇓⟨cur, n⟩ => ⌜n = cur.prefix.count c⌝` | names a value bound earlier by `←` | H012 |
| compose specs | `mvcgen [majorityChecked, majority_spec]` | use a proved triple where `g` calls `f` | H012 |
| triple ⇒ `.run` fact | `(Id.of_wp_run_eq rfl _ (maxLoop_spec xs)).1 x hx` | `prog.run = x → ∀ P, (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x` | M036, H012 |
| counting | `List.count_append`, `List.count_cons` | strict majority: `xs.length < 2 * xs.count m` | H012, H015 |

### List library for program proofs

Notation: `l₁ ~ l₂` = `List.Perm` (same multiset); `xs.Pairwise R` = `R` on every (earlier, later) pair;
`<+` Sublist (delete entries); `<+:` IsPrefix (`∃ rest, xs ++ rest = ys`); `<:+` IsSuffix (`∃ t, t ++ l₁ = l₂`);
`<:+:` IsInfix (contiguous segment, `∃ s t, s ++ l₁ ++ t = l₂`).

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| Perm building | `.refl l`, `h.cons x`, `List.Perm.swap x y l`, `h1.trans h2` | `swap : (y :: x :: l) ~ (x :: y :: l)` | M020, H008, H015 |
| Perm lemmas | `List.perm_middle`, `List.Perm.append`, `List.Perm.append_left`, `List.perm_append_comm` | `perm_middle : (l₁ ++ a :: l₂) ~ (a :: (l₁ ++ l₂))` | M021, M030, H010, H015 |
| Perm consequences | `(merge_perm _ _).mem_iff`, `h.length_eq` | membership / length preserved | M017, M030, H010 |
| Perm by counting | `List.perm_iff_count : l₁ ~ l₂ ↔ ∀ a, count a l₁ = count a l₂` | then omega over counts | H015 |
| filters | `List.filter_cons`, `List.mem_filter`, `List.filter_append_perm` | `filter_append_perm : filter p l ++ filter (!p ·) l ~ l` | M017, M021, M047 |
| Pairwise | `List.Pairwise.cons`, `.of_cons`, `List.rel_of_pairwise_cons`, `List.pairwise_cons`, `List.pairwise_singleton` | `Pairwise (· ≤ ·)` sorted, `(· < ·)` strict | M024, M030, M031, H010, H017 |
| inductive `Sorted` | `\| @cons y z rest hyz hs ih => …` | rule induction on a custom sortedness predicate | M020 |
| Bool check ↔ Prop | `simp only [Bool.and_eq_true, decide_eq_true_eq]` | `beq_iff_eq : (xs == ys) = true ↔ xs = ys` | M024, M032 |
| safe indexing | `(x :: xs)[i + 1]? = xs[i]?` (`rfl`) | `List.getElem?_cons_zero/_succ`, `List.getElem?_map`, `List.getElem?_reverse`, `List.getElem?_eq_none`, `List.ext_getElem?` | M016, M022, M032, M033, M049 |
| Option results | `cases hs : search k xs with \| none => … \| some i' => …` | `Option.map_eq_some_iff` | M022 |
| reverse | `List.reverse_cons`, `List.reverse_append`, `List.reverse_eq_nil_iff`, `List.append_assoc` | | M016, M034 |
| take/drop/sum | `List.take_append_drop`, `List.take_succ_cons`, `List.sum_cons`, `List.sum_append` | | H010, M033, H018 |
| membership | `rcases List.mem_cons.mp hm with rfl \| hm` | `List.mem_cons_self`, `List.mem_cons_of_mem`, `List.mem_append` | M023, H001, H017 |
| replicate | `List.replicate_succ : replicate (n + 1) a = a :: replicate n a` | `List.cons_append`, `List.singleton_append` | H013 |
| prefix | `obtain ⟨rest, rfl⟩ := hpre` | `xs <+: ys` unfolds to an `∃` | H016 |
| sublist | `cases hsub with \| cons _ h => _ \| cons_cons _ h => _` | `List.Sublist.cons`/`cons_cons`/`subset`, `List.sublist_of_cons_sublist` | H017 |
| segments | `List.suffix_concat_iff`, `List.infix_concat_iff`, `List.IsSuffix.isInfix` | `List.nil_infix`, `List.nil_suffix`, `List.eq_nil_of_infix_nil`, `List.eq_nil_of_suffix_nil` | H018 |
| word splits | `List.append_eq_nil_iff`, `List.append_eq_cons_iff` | `as ++ bs = x :: c ↔ (as = [] ∧ …) ∨ ∃ as', …` | H022 |
| map/flatten | `List.map_congr_left (f := …) (g := …) ih` | `List.map_map`, `List.map_reverse`, `List.sum_reverse`, `List.length_flatten`, `List.map_id`, `List.reverse_reverse` | M037 |
| strings | `String.append_assoc : s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃)` | `toString (42 : Nat) = "42"` by `rfl` | M013 |

### Arrays

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| index with proof | `Array.getElem?_eq_getElem h : a[i]? = some a[i]` | `a[i]` bound discharged by omega from context | M025 |
| swap | `Array.swap_perm`, `Array.Perm.trans` | `(xs.swap i j) ~ xs` | H011 |
| read after swap | `rw [Array.getElem_swap]; split; · …; split` | `if k = i then xs[j] else if k = j then xs[i] else xs[k]`; omega kills impossible branches | H011 |
| size after swap | `(a.swap 0 1).size = a.size := by simp` | | H011 |
| range invariant | `[0, lo)` red, `[lo, mid)` white, `[mid, hi)` unknown, `[hi, size)` blue | state as `∀ i (h : i < a.size), …` | H011, M025 |

### Trees and data structures

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| recursive Prop on trees | `example (h : M019.All p (.node l k r)) : p k := h.2.1` | `mem`, `All` unfold with `simp [mem]` | M019, H014 |
| BST inversion | `cases h with \| node hl hr bl br => exact bl` | the four premises of `BST (.node l k r)` | H014 |
| section notation | `All (· < k) l` | `(· < k)` is `fun y => y < k` | H014 |
| grind for mem + arithmetic | `split` then `simp only [mem, ih]` and `grind` | omega cannot see inside `mem y l` | M019, H014 |
| nested inductive | `inductive Rose \| node (x : Nat) (cs : List Rose)` | `induction` rejects it | M037 |
| recursive theorem | `have ih : ∀ c ∈ cs, P c := fun c _ => thm c` | inside `match t with \| .node x cs =>`; Lean checks structural recursion | M037 |
| abstraction function | `toList q = front ++ back.reverse` | `obtain ⟨f, b⟩ := q; cases f` picks the `dequeue` arm | M034 |
| potential method | `cost + Φ after ≤ 2 + Φ before` with `Φ q := q.back.length` | telescopes over a run by induction | M034 |
| rank invariant | `2 ^ rank ≤ size + 1` with `Nat.pow_le_pow_right` | leftist heap; `HeapOrd lo h` carries a lower bound | H015 |
| function returning `some` | `cases hm` on `f (.node ..) = some m` | substitutes `m` directly | H015, H016 |
| code tree | `codeOf t a = none` when `a ∉ t` | prefix-freeness via `<+:` | H016 |

### Case splits inside goals and hypotheses

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `match`/`if` in goal | `split <;> omega` | one goal per arm | M028, M038, H008 |
| in a hypothesis | `split at h` | on `h : (match run n c s with …) = some s'`; arm equations become hyps | M034, M044, M049, H009, H014, H016 |
| name the new hyps | `rename_i y f hb` / `next heq => …` | `split` makes inaccessible names (`b✝`) | M028, M034, H006, H013, H025 |
| split keeping the equation | `cases h : p x <;> simp [partition, ih, List.filter_cons, h]` | also `cases hb : b.reverse with \| nil => _ \| cons y f => _` | M021, M034, H001 |
| match with equation | `match hd : e with` | | M034 |
| pair injectivity | `by injection h` / `simp only [Prod.mk.injEq] at h` | from `(a, n) = (b, m)` | H013, M034 |
| `some` injectivity | `Option.some.inj h`, `simp only [Option.some.injEq] at h; subst h` | `cases h` also works on `some a = some b` / `none = some _` | M044, M049, H009, H016 |
| `if` branches | `if_pos hp`, `if_neg`, `dif_pos` | `simp only [run, hb, if_true]` takes the `then` branch | M044, M050 |
| Bool from ¬ | `simpa using h` | `h : ¬ b = true` to `b = false` | M044 |
| anonymous hyp | `‹beval s b = true›`, `ih _ _ _ ‹_›` | refer to a hypothesis by its type | M044, M049 |
| substitute everything | `subst_vars` | every `x = e` in context | M049 |
| index split | `by_cases h : n < c` / `by_cases h : y = x <;> simp [update, h]` | | M042, M047, M048 |
| finite enums | `cases a <;> cases b <;> simp_all [defs]` | full case split on two signs | M046 |
| pair destructuring | `obtain ⟨x, a⟩ := xa` | inside a list induction | M047 |

### Expressions, evaluators, compilers

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| smart constructors | `unfold mkPlus; split; simp_all [eval]` | one lemma per smart constructor, then induction on `e` | M038 |
| compiler correctness | `exec env (i :: is) s = exec env is (step env i s)` | generalize the stack; lemma for `exec` on `p ++ q`; CPS variant avoids `++` | H019 |
| typed compiler | `compile_correct : (compile e).run s = .cons e.eval s` | `simp [compile, run_append, iha, ihb, Code.run, Instr.run]` | M012 |
| peephole optimiser | `\| _, _, .cons (.push a) (.cons (.push b) (.cons .add c)) => .cons (.push (a + b)) (opt c)` | overlapping arms; `fun_induction opt c` | M012 |
| typed constant folding | `split <;> simp_all [Expr.eval]` | fold's signature already preserves types | H009 |
| checker inverts erasure | `check e.erase = some ⟨t, e⟩` | `simp` discharges `if h : t = t` | H009 |
| object vs meta logic | `.imp a b` vs `→` | `.imp` is object-level syntax; `Prov Γ a` is derivability; `neg a := a → ⊥` | H001, H002 |
| Bool semantics | `cases h : eval v a <;> simp [eval, h]` | `grind` closes Bool tautologies | H001 |
| Kripke model | `Forces M w (.imp a b)`: every `w' ≥ w` forcing `a` forces `b` | `Forces` unfolds by `rfl`, so `intro w' hle ha` works | H002 |

### Operational semantics: small-step, big-step, fuel

IMP: `AExp`/`BExp`/`Com` (`skip`, `assign`, `seq`, `ite`, `while`), `State := Nat → Int`,
`update s x v` = `s[x ↦ v]`, `BigStep c s s'` = "running `c` from `s` terminates in `s'`".

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| build a step | `.plusL .plusNum` | rules are constructors | M040, H020 |
| progress split | `rcases h with ⟨n, rfl⟩ \| ⟨e', h'⟩` | `(∃ n, e = .num n) ∨ ∃ e', Step e e'`; same for `Value t ∨ ∃ t', Step t t'` | M040, H020, H026 |
| lift congruence to `Star` | `star_map (f) (hf : ∀ {a b}, Step a b → Step (f a) (f b))` | one generic lemma for every context | M041 |
| apply, leave holes | `refine star_trans (star_map (fun x => .plus x b) .plusL iha) ?_` | | M041, M045 |
| big-step derivation | `.iteT hb (.seq hc hw)` | | M043 |
| contradictory guard | `simp [beval] at hb` | on `hb : beval s .ff = true` | M043, H021 |
| program equivalence | `Equiv c1 c2 := ∀ s s', BigStep c1 s s' ↔ BigStep c2 s s'` | start `intro s s'; constructor` | M043 |
| keyword constructor | `\| «while» b c ih =>` | guillemets in `cases`/`induction` alternatives | M044, H024, H025 |
| fuel interpreter | `run : Nat → Com → State → Option State` | `none` = out of fuel; soundness by induction on fuel | M044 |
| completeness with fuel | `obtain ⟨n1, h1⟩ := ih1` then fuel `max n1 n2 + 1` | `Nat.le_max_left`, `Nat.le_max_right`, `Nat.lt_or_ge`, given `run_mono` | M050 |
| unfold one fuel step | `simp only [run]; rw [h1]` | rewrite the scrutinee so its `match` reduces | M050 |
| configurations | `example : H023.Star (.seq .skip .skip, s) (.skip, s) := .step .seqSkip (.refl _)` | small step on `Com × State` | H023 |
| divergence | `while_true_diverges : ¬ BigStep (.while .tt c) s s'` | `generalize` then induction | H021 |
| type safety | progress: `induction h`; preservation: `induction hs generalizing T` then `cases h` | canonical forms: a `nat` value is a literal | H020 |
| Brzozowski | `rmatch_iff : rmatch r w = true ↔ Matches r w` | `deriv c r` matches `w` ⇔ `r` matches `c :: w`; `nullable r` ⇔ `r` matches `[]` | H022 |

### Hoare logic and weakest preconditions

`Assn := State → Prop`. `Hoare P c Q` / `Valid P c Q` (partial correctness): `∀ s s', P s → BigStep c s s' → Q s'`.
`Derivable P c Q`: provable from the Hoare rules.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| substitution lemma | `aeval s (subst x a e) = aeval (update s x (aeval s a)) e` | core of the assignment rule | M042 |
| `update` | `by_cases h : y = x <;> simp [M042.update, h]` | `update s x v y = if y = x then v else s y` | M042, M045, M047 |
| non-occurrence | `Bool.or_eq_false_iff : (x \|\| y) = false ↔ x = false ∧ y = false` | | M042 |
| assignment rule | `intro s s' hp h; cases h; exact hp` | inverts a non-loop command | M045 |
| while rule | `hoare_while (I := fun s => 0 ≤ s 0) (…)` | give the invariant by name | M045 |
| consequence (derived) | `.conseq (fun _ h => h.1) .skip (fun _ h => h)` | strengthen pre / weaken post | H024 |
| weakest liberal pre | `def wp (c : Com) (Q : Assn) : Assn := fun s => ∀ s', BigStep c s s' → Q s'` | | H024 |
| assertion equality | `funext s; apply propext; constructor` | e.g. `wp (.seq c1 c2) Q = wp c1 (wp c2 Q)` | H024 |
| relative completeness | `.conseq (fun s hP s' hc => h s s' hP hc) (wp_derivable c Q) (fun _ h => h)` | loop invariant is `wp (.while b c) Q` itself | H024 |

### Static analysis and abstract interpretation

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| concretisation | `Sign.gamma a v` | γ: "sign `a` describes value `v`"; domain {neg, zero, pos, top} | M046, H025 |
| sign of a product | `Int.mul_pos hx hy`, `Int.mul_neg_of_pos_of_neg`, `Int.mul_neg_of_neg_of_pos`, `Int.mul_pos_of_neg_of_neg` | omega treats `x * y` as an atom | M046, H025 |
| abstract state | `example : H025.lookup [] 5 = .top := rfl` | list of signs; missing entries are `top`, so `[]` describes every state | H025 |
| join | `H025.ajoin [.pos, .neg] [.pos, .zero] = [.pos, .top]` | pointwise, cut to the shorter list | H025 |
| post-fixpoint | `Le (f I) I` with `Le p q := ∀ s, Approx p s → Approx q s` | Kleene iteration (fuel 10, `[]` on give-up) gives a loop invariant | H025 |
| shifted state | `induction st generalizing x y s` with `fun k => s (k + 1)` | push a pointwise invariant through a cons | H025 |
| liveness | `live p L`, agreement on `live p L` ⇒ agreement on `L` | `List.mem_filter`, `List.mem_append`, `induction p generalizing s1 s2` | M047 |

### Lambda calculus: binders, typing, normalisation, confluence

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| de Bruijn shift | `shift 1 0 (.lam (.app (.var 0) (.var 1))) = .lam (.app (.var 0) (.var 2))` | `var k` = k-th enclosing `lam`; cutoff grows under `lam`: `induction t generalizing c` | M048 |
| arithmetic side facts in simp | `simp [shift, h, show ¬ n + 1 < c by omega]` | | M048 |
| list contexts | `(A :: Γ)[0]? = some A`, `(A :: Γ)[n + 1]? = Γ[n]?` | `List.getElem?_cons_zero`, `List.getElem?_cons_succ` | M049 |
| checker soundness/completeness | `split at h <;> simp_all` | `typeOf Γ t = some A → HasType Γ t A` and back; types are unique | M049 |
| function contexts | `abbrev Ctx := Nat → Option Ty`; `Ctx.cons A Γ` | `intro n A hn; cases n with \| zero => … \| succ n => …` | H026 |
| renaming / substitution | `rename ρ`, `upRen ρ`; `subst σ`, `up σ`, `beta v` | renaming lemma first, then substitution lemma (`up σ (n+1) = rename Nat.succ (σ n)`) | H026 |
| logical relation | `def Red : Ty → Tm → Prop \| .base, t => WN t \| .arr A B, t => WN t ∧ ∀ u, Red A u → Red B (.app t u)` | Tait reducibility, recursion on types | H027 |
| normal form | `theorem normal_K : Normal .K := by intro t' h; cases h` | `Normal t := ∀ t', ¬ Step t t'`; `WN t := ∃ v, Star t v ∧ Normal v` | H027 |
| parallel reduction | `Par`: contract any set of redexes at once | has the diamond property, `Step ⊆ Par ⊆ Star`; `Step` alone has none (`S x y z` copies `z`) | H028 |
| head inversion | `obtain ⟨x', rfl, hx⟩ := par_Kx h` | `par_Kx : Par (.app .K x) t → ∃ x', t = .app .K x' ∧ Par x x'` | H028 |
| ctor injectivity by cases | `cases he` | on `he : Tm.app .K u = Tm.app .K v` unifies `u` and `v` | H028 |
| strip lemma | `induction hc generalizing b` | one `Par` against a `Star`; stack strips for Church-Rosser | H028 |

### Gotchas

- `grind` is banned where it would skip the lesson: M012, M034, M041, M042, M045, M046, M048, M049, H008, H009, H013. `try?` is banned in all of those and in M011, H004, H005; leave no `exact?`/`apply?` in any file. H013 also bans `fun_induction` (use `induction` + `simp only [f]` + `split`).
- No imports, Core only: M011, M012, H004, H008, H009, H013. `Function.exists_fixed_point_of_surjective` (M011) is a Mathlib name and is banned anyway.
- Banned library shortcuts: `List.reverseAux_eq`/`List.reverse_eq_reverseAux` (M016), `List.filter_append_perm` (M021), `Nat.gcd`/`Nat.gcd_rec` (M029), `ac_rfl`/`ac_nf` (H008), and every ready-made lex lemma plus `termination_by`/`decreasing_by` (H004: prove `acc_lex` by induction on `Acc`).
- H003 `AXIOMS: propext, Quot.sound`: `Classical.*`, `by_cases`/`by_contra` on a bare Prop, `grind`, `decide` and some `simp` lemmas pull in `Classical.choice`. Check with `#print axioms`.
- `rw` on a goal whose other parts depend on the rewritten term fails with "motive is not type correct"; use `subst h` (H003).
- `induction h` fails when an index is not a variable: `generalize` every such index (both pairs in H023, one alone still fails). Inside `generalize` write `Com.skip`, not `.skip`: there is no expected type (H023).
- `while` is a keyword: write `| «while» b c ih =>` (M044, H024, H025).
- Implicit cut formulas: `.mp (a := a)` / `.impE (a := a)` / `.cat (u := …)`, or each `by simp` premise meets a metavariable (H001, H002, H022).
- `LawfulMonad.mk'`: pass the three laws as arguments; `apply LawfulMonad.mk'` turns the automatic laws into goals (M014).
- Frozen `:=` with a learner-written body: write it as `fun | [], acc => … | .lit s :: fs, acc => …` (M013, H013).
- `Vec.append` returns `Vec α (m + n)`, not `n + m`, so the `cons` case checks by `rfl` (M008).
- `rw [ih]` before unfolding helper defs like `lows`/`highs`, or the IH no longer matches (M017).
- Wf-recursive defs do not reduce by `rfl`/`decide`: `rw [loop]` or `loop.eq_2` (M035).
- `simp [Heap.rank]` unfolds `r.rank` into a `match` omega cannot read; use `show` with the folded form (H015). To drop a lower bound before reusing a spec, `cases h` once (H015).
- omega treats products and powers (`x * y`, `2 ^ x`, `2 ^ x * 2 ^ y`) as atoms: supply bounds with `have` (M028, M046, H005). It does handle `max`/`min` on Nat and Int (M001, M023, H018).
- `grind` closes Int ring identities with Nat casts such as `↑(a*c+b*d) - ↑(a*d+b*c) = (↑a-↑b)*(↑c-↑d)` without `push_cast` (H007).
- `mvcgen invariants?` prints a skeleton that is usually too weak; `set_option mvcgen.warning false` silences the experimental warning (M036, H012).
- H012/M036's `Id.of_wp_run_eq` takes `rfl` first, then the postcondition predicate (or `_`), then the triple.
- Given frozen lemmas (`run_mono` in M050) sit in SPEC regions: use them, do not change them.

## Algebra, number theory, analysis and sets (Mathlib)

Medium/hard topics 04-05: M051–M078, H029–H049. Every file starts with `import Mathlib`, except
H042–H044, whose imports are frozen inside the SPEC region (only ℝ's order and `sSup`; `import`
itself is banned). When a card bans lemmas it usually also bans `exact?`, `apply?`, `rw?`, `hint`
and `try?`: use them to explore, then write out the step they find in your own terms.

### Reading the notation

| Notation | Meaning | Needs | IDs |
|---|---|---|---|
| `∑ i ∈ range n, f i`, `∏ x ∈ s, f x` | finite sum / product over a `Finset`; `range n = {0, …, n-1}` | `open Finset` for bare `range`, `sum_range_succ` | M051, H033 |
| `#s` | `s.card` | `open Finset` (scoped notation) | H035, H037 |
| `{a ∈ s \| p a}` = `s.filter p`; `#{x \| p x}` | filtered finset (the second filters `univ`) | `DecidablePred p` (`classical` gives it) | M056, H035, H037 |
| `s ×ˢ t`, `Finset.Ico m n`, `Finset.univ`, `s.erase a`, `s \ t` | product finset; `{m, …, n-1}`; every element of a `Fintype`; remove `a`; difference | | H033, H036, H047 |
| `n.factorial` / `n !` | n! | `open Nat` for `n !` | H029, M064 |
| `a ∣ b` (`\mid`) | `∃ c, b = a * c` | | M055, H031 |
| `a ≡ b [MOD n]`, `a ≡ b [ZMOD n]` | `Nat.ModEq n a b`, which is `a % n = b % n` by definition; `Int.ModEq` | | M058, M061, H032 |
| `ZMod n`, `(k : ZMod n)` | the ring ℤ/nℤ; the cast is `k mod n`, so `(p : ZMod p) = 0` | | M053, M064, H034 |
| `Fact P`, `[Fact p.Prime]` | a proof of `P` packaged as an instance argument | | M064, H034 |
| `G →* H`, `Equiv.Perm G` (= `G ≃ G`) | monoid hom; permutations, where `*` is composition and `1` is `id` | | M059, M060 |
| `⊥`, `⊤` on `Subgroup G` | `{1}`, the whole group | | M063 |
| `Nat.card G`, `orderOf g`, `Subgroup.zpowers g` | number of elements; least `n > 0` with `g ^ n = 1`; `{g ^ (k : ℤ)}` | | M063, H037 |
| `ℚ[X]`, `X`, `p.eval x`, `p.IsRoot x` | polynomials over ℚ, the variable, evaluation, root | `open Polynomial` | M062 |
| `p.natDegree : ℕ`, `p.degree : WithBot ℕ` | the zero polynomial has `degree = ⊥` | | M062 |
| `GaussianInt` = `ℤ√(-1)`, `⟨s, t⟩`, `z.re`, `z.im`, `star z`, `z.norm` | s + t·i, its conjugate, `N = re² + im²` | no `ℤ[i]` notation: Lean reads it as list indexing | H038 |
| `√x` (`Real.sqrt x`), `\|x\|`, `⌈x⌉₊` | square root, absolute value, ceiling as a ℕ | | M072, M073, H045 |
| `Irrational x` | `x ∉ Set.range ((↑) : ℚ → ℝ)` | | H030 |
| `sSup s` | least upper bound of `s : Set ℝ`; Mathlib returns `0` if `s` is empty or unbounded (`Real.sSup_empty`, `Real.sSup_of_not_bddAbove`) | | M074, H041 |
| `f '' A`, `f ⁻¹' B`, `Aᶜ` | image, preimage (`\inv'`), complement | | M070, H040 |
| `⋃ i, A i`, `⋃ i ∈ t, U i`, `⋂₀ S`, `⋃₀ S` | indexed union; union over a finset `t`; intersection / union of a set of sets | | M077, H039, H046 |
| `Set.Icc a b`, `Set.Ioo a b`, `Set.range f` | [a, b], (a, b), `{f y \| y}` | | M074, H041, H049 |
| `f^[n] x` | `f` applied `n` times | | H044, H047 |
| `𝓝 c`, `Tendsto u atTop (𝓝 L)`, `∀ᶠ n in atTop, P n` | neighbourhood filter of `c`; `u n → L`; `P n` for all large `n` | `open Filter Topology` | H045, H047 |
| `∫ x in a..b, f x`, `c • x` | interval integral against Lebesgue measure `MeasureTheory.volume`; scalar multiplication (`smul_eq_mul` on ℝ) | | H048 |
| `HasDerivAt f d x`, `ContinuousOn f s`, `IsMaxOn f s c`, `IsLocalMax f a` | `f'(x) = d`; `f` restricted to `s` is continuous; `∀ x ∈ s, f x ≤ f c`; max near `a` | | H049 |
| `∃! x, P x` | exactly one `x`; build with `⟨x, hx, fun y hy => _⟩` | | H047 |

### Finite sums, products, counting

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Finset.sum_range_succ`, `sum_range_succ'` | `rw [sum_range_succ, mul_add, ih]; ring` | split off the last / first (`f 0`) term: the induction step for range sums | M051, M052, H032 |
| `range_add_one`, `filter_insert`, `card_insert_of_notMem` | `rw [range_add_one, range_add_one, filter_insert, filter_insert]` | `range (n+1) = insert n (range n)`; filter of an insert is an `if`; `a ∉ s → #(insert a s) = #s + 1` | M056 |
| `mem_range`, `mem_filter`, `mem_image`, `mem_product`, `mem_erase`, `mem_sdiff`, `mem_insert`, `mem_singleton`, `mem_univ` | `simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, not_or] at ha` | unfold finset membership | H033, H035, H036 |
| `Finset.dvd_sum` | `apply Finset.dvd_sum; intro i hi` | divides every term, so divides the sum | H032 |
| `add_pow` | `rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']` | `(x+y)^n = ∑ m ∈ range (n+1), x^m * y^(n-m) * n.choose m` | H032 |
| `Set.InjOn g ↑s`; `sum_image`, `prod_image` | `rw [prod_image (mul_mod_inj n a ha)]` | reindex over `s.image g` when `g` is injective on `s`; prove InjOn with `intro k hk j hj hkj` | H035, H036 |
| `card_image_of_injOn`, `card_image_of_injective`, `eq_of_subset_of_card_le` | `rw [card_image_of_injective _ (mul_right_injective g)]` | an injective image keeps `#`; `s ⊆ t → #t ≤ #s → s = t` (injective self-map of a finset is onto) | H035, H037 |
| `card_eq_sum_card_image`, `sum_const_nat` | `rw [card_eq_sum_card_image (coset H) univ, sum_const_nat hfib]` | count `s` by the fibres of a map; a sum of equal terms is `#s * m` | H037 |
| `prod_involution` | `refine Finset.prod_involution (fun x _ => x⁻¹) ?_ ?_ ?_ ?_` | `∏ = 1` if an involution pairs terms with product 1; goals: `f a * f (g a) = 1`, `f a ≠ 1 → g a ≠ a`, `g a ∈ s`, `g (g a) = a` | H033 |
| `prod_sdiff`, `prod_pair` | `rw [← Finset.prod_sdiff hsub, prod_rest, one_mul]` | `s₁ ⊆ s₂ → (∏ s₂ \ s₁) * ∏ s₁ = ∏ s₂`; `a ≠ b → ∏ x ∈ {a, b}, f x = f a * f b` | H033 |
| `prod_congr`, `prod_mul_distrib`, `prod_const`, `card_range` | `rw [prod_mul_distrib, prod_const, Nat.totient_eq_card_coprime]` | termwise rewrite; `∏ f * g = ∏ f * ∏ g`; `∏ _ ∈ s, b = b ^ #s` | H034, H035 |
| `prod_neg`, `prod_range_reflect`, `prod_range_add_one_eq_factorial` | `rw [← prod_range_add_one_eq_factorial, ← prod_range_reflect]` | `∏ -f = (-1)^#s * ∏ f`; reindex `j ↦ n-1-j`; `∏ i ∈ range n, (i+1) = n!` | H034 |
| `prod_nat_mod` | `_ = (∏ k ∈ R, a * k % n) % n := prod_nat_mod _ _ _` | reduce each factor mod `n` | H035 |
| `sum_mul_sum`, `sum_product` | `rw [divisors_eq m n h, sum_image (mul_inj m n h), sum_mul_sum, sum_product]` | product of sums = double sum = sum over `s ×ˢ t` | H036 |
| `sum_le_sum`, `sum_mul`, `sum_div`, `sum_sub_distrib`, `sum_range_sub` | `exact Finset.sum_le_sum fun k _ => (piece f hf _ hN k).1` | termwise `≤`; pull `* a`, `/ a`, `-` through `∑`; telescoping `∑ (f (i+1) - f i) = f n - f 0` | H047, H048 |

### Divisibility, primes, gcd

| API | Example | Gloss | IDs |
|---|---|---|---|
| build `a ∣ b` | `exact ⟨a * u - b * u, by linear_combination (-a) * huv⟩`, `Dvd.intro c h` | witness `c` with `b = a * c` (`Dvd.intro` takes `a * c = b`) | M061, H031 |
| `Nat.Prime.dvd_mul` (Euclid's lemma) | `rcases hp.dvd_mul.mp h with h \| h` | `p ∣ m * n ↔ p ∣ m ∨ p ∣ n` | M055 |
| `pow_two`, `mul_dvd_mul`, `dvd_pow`, `dvd_mul_of_dvd_right`, `dvd_mul_right`, `dvd_mul_left`, `hpd.trans` | `exact mul_dvd_mul ha ha` | divisibility algebra | M055, M064, M065 |
| `Nat.prime_def` | `rw [Nat.prime_def] at hp; push Not at hp` | `p.Prime ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`; negated, it yields a proper divisor | H029, H033, M065 |
| `hp.two_le`, `hp.one_lt`, `hp.pos`, `hp.eq_one_or_self_of_dvd`, `hp.eq_two_or_odd`, `hp.eq_two_or_odd'` | `exact hp.one_lt.ne' (Nat.dvd_one.mp h2)` | facts about a prime; `eq_two_or_odd` gives `p % 2 = 1`, the primed form gives `Odd p` | H029, M063, M064, H034 |
| `Nat.exists_prime_and_dvd` | `Nat.exists_prime_and_dvd (n := (2 * n.factorial) ^ 2 + 1) (by nlinarith)` | `n ≠ 1 → ∃ p, p.Prime ∧ p ∣ n` (banned in H029, which proves it) | M064 |
| `Nat.dvd_factorial`, `Nat.factorial_pos`, `Nat.dvd_add_right`, `Nat.dvd_one`, `Nat.le_of_dvd`, `Nat.dvd_sub` | `have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp hpd` | Euclid's `n! ± 1` argument: `0 < m → m ≤ n → m ∣ n!`, then cancel | H029, H033, M064, M065 |
| `Nat.prime_two.dvd_of_dvd_pow` | `obtain ⟨k, rfl⟩ : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ p ^ 2 from ⟨q ^ 2, h⟩)` | `p ∣ m ^ n → p ∣ m`; `rfl` substitutes `p := 2 * k` | H030 |
| strong induction | `induction q using Nat.strong_induction_on generalizing p with \| _ q ih => …` | `ih : ∀ m < q, ∀ p, …`; infinite descent | H029, H030, M058, M065 |
| `Nat.gcd.induction` | `induction a, b using Nat.gcd.induction with \| H0 n => _ \| H1 m n hm ih => _` | induction along Euclid's algorithm: `P 0 n`; `0 < m → P (n % m) m → P m n` | H031 |
| `Nat.gcd_rec`, `Nat.mod_add_div`, `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, `Nat.gcd_comm`, `Nat.gcd_eq_left` | `rw [Nat.gcd_rec m n, ← h]` | `gcd m n = gcd (n % m) m`; `m % k + k * (m / k) = m`; `m ∣ n → gcd m n = m` | H031, H035, H036 |
| `Nat.Coprime m n` | `rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]` | by definition `Nat.gcd m n = 1`: a gcd proof passes as a Coprime proof | H031, H032, H035 |
| `Nat.Prime.coprime_iff_not_dvd`, `Nat.Coprime.gcd_mul`, `.dvd_of_dvd_mul_right`, `.coprime_dvd_left`, `.coprime_dvd_right`, `.mul_right`, `.symm`, `Nat.coprime_prod_right_iff` | `Nat.coprime_prod_right_iff.mpr fun k hk => (mem_filter.mp hk).2` | coprimality toolkit | H032, H035, H036 |
| `Int.natCast_dvd_natCast` | `exact Int.natCast_dvd_natCast.mp (int_dvd_of_bezout p a b x y hxy h')` | `(↑m : ℤ) ∣ ↑n ↔ m ∣ n`: prove in ℤ, come back to ℕ | H031 |
| `Nat.mul_mod`, `Nat.mod_lt`, `interval_cases` | `interval_cases a % 4 <;> interval_cases b % 4 <;> simp_all` | case split on residues; first `rw [Nat.mul_mod] at h` and add `a % 4 < 4 := Nat.mod_lt a (by norm_num)` | M065 |
| `Nat.divisors`, `Nat.mem_divisors` | `simp only [mem_image, mem_product, Nat.mem_divisors, Prod.exists]` | divisor finset (`∅` for 0); `n ∈ m.divisors ↔ n ∣ m ∧ m ≠ 0` | H036 |
| `Nat.totient`, `Nat.totient_eq_card_coprime` | `example (n : ℕ) : n.totient = ((Finset.range n).filter n.Coprime).card := rfl` | φ(n), by definition | H035 |
| `Nat.Prime.dvd_choose_self` | `hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)` | `k ≠ 0 → k < p → p ∣ p.choose k` | H032 |
| `Nat.digits`, `Nat.digits_def'`, `Nat.div_lt_self`, `List.sum_cons` | `rw [Nat.digits_def' (by norm_num) hn, List.sum_cons]` | digits, least significant first: `Nat.digits 10 123 = [3, 2, 1]` | M058 |
| `Nat.ascFactorial_eq_prod_range`, `Nat.factorial_mul_ascFactorial` | `rw [← Nat.ascFactorial_eq_prod_range, Nat.factorial_mul_ascFactorial, two_mul]` | `n! * ∏ i ∈ range k, (n + 1 + i) = (n + k)!` | H034 |
| `Nat.eq_zero_or_pos`, `Nat.pos_of_dvd_of_pos`, `Nat.dvd_antisymm`, `Nat.eq_of_mul_eq_mul_left` | `rcases Nat.eq_zero_or_pos n with rfl \| hn` | split off `n = 0`; positivity of divisors; cancel a positive factor | M058, H035, H036 |

### Congruences

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Nat.ModEq` methods | `(h10.mul_right _).add_left _`, `h.pow k`, `h.add_right c`, `h.symm`, `h1.trans h2` | congruences multiply, add, power, chain | M058, H032 |
| closed congruence | `(show 10 ≡ 1 [MOD 9] by decide).pow k` | `decide` checks numerals | M058 |
| `calc` over `≡` | `calc n = n % 10 + 10 * (n / 10) := (Nat.mod_add_div n 10).symm` then `_ ≡ … [MOD 9] := …` | mix `=` and `≡ [MOD n]` steps | M058, H032 |
| `Nat.modEq_zero_iff_dvd` | `rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]` | `a ≡ 0 [MOD n] ↔ n ∣ a` | M058, H032 |
| `Nat.ModEq.cancel_left_of_coprime` | `apply Nat.ModEq.cancel_left_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr ha)` | `m.gcd c = 1 → c * a ≡ c * b [MOD m] → a ≡ b [MOD m]` | H032, H035 |
| definitional unfolding | `(hkj : a * k ≡ a * j [MOD n])`, `unfold Nat.ModEq at h` | `a % n = b % n` and `a ≡ b [MOD n]` convert by ascription | H035 |
| `Int.modEq_iff_dvd` | `rw [Int.modEq_iff_dvd] at *` | `a ≡ b [ZMOD n] ↔ n ∣ b - a` | M061 |
| `IsCoprime m n` (ℤ) | `obtain ⟨u, v, huv⟩ := h` | unfolds to Bézout `∃ u v, u * m + v * n = 1` | M061 |
| `linear_combination` | `linear_combination (-(y - x)) * huv + u * m * ht + v * n * hs` | goal is `Σ cᵢ · hᵢ` up to `ring` | M061, H033 |

### ZMod and casts

| API | Example | Gloss | IDs |
|---|---|---|---|
| `decide` over `ZMod n` | `revert x; decide` | ZMod n is finite: checks every element (plain `decide` rejects free variables) | M053 |
| `decide +revert` | `exact ⟨1, by decide +revert⟩` | also reverts local hypotheses and instances such as `[Fact p.Prime]` | H034 |
| `ZMod.intCast_mod`, `push_cast [h] at h1`, `generalize` | `generalize (a : ZMod 4) = x at h1` | move an ℤ fact to residues, then forget where `x` came from so `decide` can range over it | M053 |
| `ZMod.natCast_eq_zero_iff`, `ZMod.natCast_self` | `exact_mod_cast (ZMod.natCast_eq_zero_iff _ p).mpr hpd` | `((a : ℕ) : ZMod b) = 0 ↔ b ∣ a`; `(n : ZMod n) = 0` | M064, H034 |
| `Fact` | `haveI := Fact.mk hp`, `haveI : Fact (2 < p) := ⟨by omega⟩`, `(Fact.out : p.Prime)` | provide or read back an instance-argument proof | M064, H034 |
| `ZMod.mod_four_ne_three_of_sq_eq_neg_one` | `have h3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq` | `[Fact p.Prime] → y ^ 2 = -1 → p % 4 ≠ 3` | M064 |
| `ZMod.pow_card_sub_one_eq_one`, `ZMod.wilsons_lemma`, `ZMod.neg_one_ne_one` | `have hfl := ZMod.pow_card_sub_one_eq_one hx0` | Fermat `a ≠ 0 → a ^ (p-1) = 1`; Wilson `((p-1)! : ZMod p) = -1`; `-1 ≠ 1` under `Fact (2 < n)` | H034 |
| sign lemmas | `rw [hk, pow_mul, hx, (odd_two_mul_add_one k).neg_one_pow] at hfl` | `eq_neg_iff_add_eq_zero`, `neg_one_sq`, `Odd.neg_one_pow`, `odd_two_mul_add_one` | M064, H034 |
| cast lemmas | `rw [h1, Nat.cast_mul, Nat.cast_prod, prod_congr rfl h2, prod_neg]` | `Nat.cast_mul`, `Nat.cast_prod`, `Nat.cast_add`, `Nat.cast_one`; `push_cast`, `exact_mod_cast` | M064, H031, H034 |

### Groups, homomorphisms, structure instances

| API | Example | Gloss | IDs |
|---|---|---|---|
| group axioms | `inv_eq_of_mul_eq_one_right (h a)` | `mul_inv_cancel`, `mul_inv_rev`, `mul_assoc`, `inv_mul_cancel_left`, `mul_inv_cancel_left`, `mul_inv_eq_one`, `one_mul`, `inv_one`; nothing commutes | M054, M059, M060 |
| `group` | `exact ⟨g⁻¹ * x, hx, by group⟩` | normalises words in a group | M054, H037 |
| `G →* H`: `map_mul`, `map_one`, `map_inv` | `rw [map_mul, ha, hb, one_mul]` | homs preserve `*`, `1`, `⁻¹` | M059 |
| `Subgroup` instance | `{ carrier := {g \| f g = 1}, one_mem' := map_one f, mul_mem' := …, inv_mem' := … }` | `mul_mem'` binds `a b` implicitly: start with `intro a b ha hb` | M059 |
| set-builder membership | `example {G : Type} (P : G → Prop) (g : G) (h : P g) : g ∈ {x \| P x} := h` | `g ∈ {x \| P x}` is `P g` by definition; or `simp only [Set.mem_setOf_eq] at *` | M059, M071 |
| `Equiv.Perm` instance | `{ toFun := fun x => g * x, invFun := fun x => g⁻¹ * x, left_inv := fun x => inv_mul_cancel_left g x, right_inv := fun x => mul_inv_cancel_left g x }` | a bijection with its inverse and both round trips | M060 |
| `G →*` instance | `map_mul' := fun a b => by ext x; simp [mul_assoc]` | `ext x` is `Equiv.ext`; `(σ * τ) x = σ (τ x)` by `rfl` | M060 |
| evaluate an equation of functions | `have := congrArg (fun σ : Equiv.Perm G => σ 1) h`, `congrFun h n` | apply both sides at a point | M060, M071 |
| subgroup closure | `simpa [mul_assoc] using H.mul_mem (H.inv_mem hx) hy` | `H.one_mem`, `H.mul_mem`, `H.inv_mem` | H037 |
| cyclic subgroups, Lagrange | `exact absurd (Subgroup.zpowers_eq_bot.mp (Subgroup.card_eq_one.mp h1)) hg` | `Subgroup.card_subgroup_dvd_card`, `card_eq_one` (`= 1 ↔ = ⊥`), `zpowers_eq_bot`, `eq_top_of_card_eq`, `isCyclic_iff_exists_zpowers_eq_top`, `Nat.card_zpowers` (`= orderOf a`) | M063, H037 |
| nontrivial finite group | `haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hp.one_lt)`; `obtain ⟨g, hg⟩ := exists_ne (1 : G)` | an element `≠ 1` | M063 |
| finiteness | `obtain ⟨b, hb⟩ := Finite.injective_iff_surjective.mp hinj 1` | self-map of a finite type: injective ↔ surjective; `mul_left_cancel₀`, `mul_right_injective` | M063, H037 |
| `Finite` to `Fintype` | `classical; haveI := Fintype.ofFinite G; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]` | turn `Nat.card` into a `Finset` count `#{x \| p x}` | H037 |

### Fields, polynomials, Gaussian integers

| API | Example | Gloss | IDs |
|---|---|---|---|
| `mul_eq_zero`, `sub_eq_zero`, `eq_neg_of_add_eq_zero_left` | `rcases mul_eq_zero.mp h' with h1 \| h1` | a product is zero only if a factor is | M057, H033 |
| factor via `ring_nf` | `have h' : (x - 2) * (x + 2) = 0 := by ring_nf; linarith` | normalise both sides, then use the hypothesis | M057 |
| field inverse | `exact mul_inv_cancel₀ ha.1` | `mul_inv_cancel₀`, `inv_ne_zero`, `inv_inv`; `0⁻¹ = 0` | H033 |
| `irreducible_of_degree_le_three_of_not_isRoot` | `apply irreducible_of_degree_le_three_of_not_isRoot` | over a field, degree 1–3 and no root ⇒ `Irreducible`; goals `natDegree ∈ Icc 1 3` (`rw [hdeg]; decide`) and no root | M062 |
| `compute_degree!` | `have hdeg : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!` | `natDegree` / `degree` of an explicit polynomial | M062 |
| evaluate | `simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]` | root condition to arithmetic, then `positivity` / `nlinarith [sq_nonneg (x + 1 / 2)]` | M062 |
| `degree_eq_one_of_irreducible_of_root` | `have h1 := degree_eq_one_of_irreducible_of_root h hroot` | an irreducible with a root has degree 1; `Complex.I` is a root of `X^2+1` over ℂ (`by simp`) | M062 |
| Zsqrtd norm | `rw [← Zsqrtd.norm_conj b, ← Zsqrtd.norm_mul, mul_conj_sub, Zsqrtd.norm_def]` | `norm_def`, `norm_mul`, `norm_conj`, `norm_eq_mul_conj : ((n.norm : ℤ) : ℤ√d) = n * star n`; `ring` works; `simp` knows `Zsqrtd.re_mul` | H038 |
| `GaussianInt.norm_pos` | `have hN : 0 < b.norm := GaussianInt.norm_pos.mpr hb` | `0 < x.norm ↔ x ≠ 0` | H038 |
| ℤ division | `have h3 := Int.emod_add_mul_ediv u n` | `a % b + b * (a / b) = a`; `Int.emod_nonneg`, `Int.emod_lt_of_pos` for the remainder range | H038 |

### Real inequalities, roots, irrationality

| API | Example | Gloss | IDs |
|---|---|---|---|
| `nlinarith` + square hints | `nlinarith [sq_nonneg (a - b)]` | AM-GM style inequalities | M072, M062 |
| Bernoulli step | `push_cast; rw [pow_succ]; nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg x)]` | with `mul_le_mul_of_nonneg_right ih h1` in context | M066 |
| `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.sq_sqrt` | `rw [show (a + b) / 2 = Real.sqrt (((a + b) / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]` | monotone √; `0 ≤ x → √(x²) = x`; `0 ≤ a → √a ^ 2 = a` | M072, H030 |
| `irrational_iff_ne_rational` | `rw [irrational_iff_ne_rational]; intro a b hb0 h` | `Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b` | H030 |
| ℝ → ℤ → ℕ | `have h3 : a ^ 2 = 2 * b ^ 2 := by exact_mod_cast h2` | then `simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h3`; `Int.natAbs_pos`, `div_pow`, `field_simp at this` | H030 |
| abs | `rw [sub_zero, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]` | `abs_of_pos`, `abs_of_nonneg`, `abs_of_neg`, `sq_abs`, `abs_nonneg` | M067, H038 |

### ε-N and ε-δ by hand

Cards define `ConvergesTo a L := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε`, `ContAt f x := ∀ ε > 0, ∃ δ > 0, ∀ y, |y - x| < δ → |f y - f x| < ε`, and variants (`UnifConv`, `IsCauchy`). `intro ε hε` opens one; applying it is `ha (ε / 2) (by positivity)`.

| Step | Example | Gloss | IDs |
|---|---|---|---|
| unpack | `obtain ⟨δ, hδ, hc⟩ := hF N x (ε / 3) (by positivity)` | `∃ δ > 0, …` is `∃ δ, δ > 0 ∧ …` | M068, M076 |
| witness | `refine ⟨max N1 N2, fun n hn => ?_⟩` | then `le_of_max_le_left hn`, `le_max_left _ _` | M067, M068, H042 |
| Archimedes | `obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)` | `∃ n : ℕ, x < n` | M067, M074, M078, H045, H048 |
| denominators | `rw [div_lt_iff₀ hε] at hN` | `0 < c → (b / c < a ↔ b < a * c)`; `div_le_iff₀` for `≤` | M067, M078, H048 |
| cast the index | `have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn` | then `nlinarith` | M067, M078 |
| triangle in `calc` | `_ ≤ \|a n - La\| + \|b n - Lb\| := abs_add_le _ _` | `abs_add_le`, `abs_add_three`, `abs_sub_comm`, `abs_mul`, `abs_two`; first step `:= by ring_nf` | M068, M073, M076 |
| finish a `calc` | `_ < ε / 2 + ε / 2 := add_lt_add e1 e2`, `_ = ε := by ring` | ε/2 and ε/3 splits | M068, M076 |
| unpack `\|·\|` | `rw [abs_lt] at h ⊢; constructor <;> linarith` | `abs_lt`, `abs_le`, `abs_sub_lt_iff` | M075, H041, H042, H044 |
| δ as a `min` | `refine ⟨min 1 (ε / (2 * \|a\| + 1)), by positivity, fun y hy => ?_⟩` | then `lt_of_lt_of_le hy (min_le_left _ _)`; build points with `lt_min`; `min_choice` | M073, H041, H046 |
| compare parts | `_ < ε / 3 + ε / 3 + ε / 3 := by rw [abs_sub_comm (f y)]; gcongr` | `gcongr` matches the shapes | M073, M076 |
| `field_simp` | `_ = ε := by field_simp` | `ε / c * c = ε` | M073 |
| negate a definition | `unfold ContAt at hf; push Not at hf` | `¬ ∀ ε > 0, …` to `∃ ε > 0, ¬ …` | M078 |
| `choose` | `choose a ha1 ha2 using fun n : ℕ => hbad (1 / ((n : ℝ) + 1)) (by positivity)` | turn `∀ n, ∃ x, P ∧ Q` into a sequence and its specs | M077, M078, H044, H045 |
| contradiction at one index | `exact absurd (hN N le_rfl) (not_lt.mpr (ha2 N))` | `not_lt : ¬ a < b ↔ b ≤ a` | M078 |
| `le_of_forall_pos_lt_add` | `refine le_of_forall_pos_lt_add fun ε hε => ?_` | `(∀ ε > 0, a < b + ε) → a ≤ b` | H045 |

### Suprema, monotone sequences, completeness

| API | Example | Gloss | IDs |
|---|---|---|---|
| `le_csSup`, `csSup_le`, `exists_lt_of_lt_csSup` | `exact ⟨le_csSup ⟨b, hS⟩ ha, csSup_le ⟨a, ha⟩ hS⟩` | `BddAbove s → a ∈ s → a ≤ sSup s`; `s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a`; `s.Nonempty → b < sSup s → ∃ a ∈ s, b < a` | M075, H041–H046 |
| side conditions | `⟨M, h⟩ : BddAbove S`, `⟨a, h⟩ : S.Nonempty`, `Set.range_nonempty a`, `Set.mem_range_self y` | `BddAbove S` is `∃ M, ∀ x ∈ S, x ≤ M` | M075, H041, H045 |
| `IsLUB.csSup_eq` | `apply IsLUB.csSup_eq _ ⟨_, Set.mem_range_self 0⟩; constructor` | `IsLUB s a`: `a ∈ upperBounds s ∧ ∀ b ∈ upperBounds s, a ≤ b`; `mem_upperBounds` | M074 |
| elements of `Set.range` | `rintro _ ⟨n, rfl⟩`, `obtain ⟨_, ⟨N, rfl⟩, hN⟩ := exists_lt_of_lt_csSup …` | substitute `x := a n`; `dsimp only` beta-reduces `(fun n => …) n` | M074, M075, H043 |
| `ε` below the sup | `exists_lt_of_lt_csSup (Set.range_nonempty a) (sub_lt_self _ hε)` | some term exceeds `sSup - ε`: monotone convergence | M075, H044 |
| name the set | `set S : Set ℝ := {x \| x ∈ Set.Icc a b ∧ f x ≤ 0}`, `set c := sSup S` | IVT; Cauchy limit as `sSup {x \| ∃ M, ∀ n ≥ M, x < a n}` | H041, H042, H046 |
| `Monotone`, `Antitone`, `StrictMono`, `BddBelow` | `have h2 : a N ≤ a n := hm hn` | `Monotone a` is `m ≤ n → a m ≤ a n` | M075, H044 |
| one-step monotonicity | `monotone_nat_of_le_succ fun k => …` | also `antitone_nat_of_succ_le`, `strictMono_nat_of_lt_succ` | H043, H044 |
| `StrictMono.id_le` | `hφ.id_le n : n ≤ φ n` | subsequence indices grow | H045 |
| peaks | `rcases Set.finite_or_infinite {n \| ∀ m > n, a m ≤ a n} with hfin \| hinf` | `Set.Finite.bddAbove`; `Nat.nth p` is the k-th `n` with `p n`: `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite` | H044 |
| iterates | `rw [Function.iterate_succ_apply']` | `f^[n.succ] x = f (f^[n] x)` | H044, H047 |
| recursive def | `noncomputable def I (f : ℕ → ℝ) : ℕ → ℝ × ℝ \| 0 => (0, 1) \| n + 1 => step (I f n) (f n)` | `simp only [I] at h1 h2` unfolds one step; pairs `p.1`, `p.2` | H043 |
| `if` on ℝ | `unfold step; split_ifs with hz` | `if z < c then … else …` needs `noncomputable` | H043 |
| antitone by negation | `fun i j hij => neg_le_neg (ha hij)`, `abs_neg` | reuse monotone convergence for `-a` | H044 |

### Sets and functions

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Injective`, `Surjective`, `Bijective` | `fun _ _ h => hg (hf h)` | `Injective f`: `f a = f b → a = b`; `Surjective f`: `∀ b, ∃ a, f a = b`; `(f ∘ g) x = f (g x)` is `rfl` | M069, H040 |
| use surjectivity | `obtain ⟨b, rfl⟩ := hf c` | substitute `c := f b` | M069 |
| image / preimage | `rintro y ⟨x, hx, rfl⟩`, `fun x hx => ⟨x, hx, rfl⟩` | `Set.mem_image`, `Set.mem_preimage` (`a ∈ f ⁻¹' s ↔ f a ∈ s`, definitional) | M070 |
| set equality | `ext y; constructor; rintro ⟨x, hx \| hx, rfl⟩` | preimage of `∩` is `ext x; rfl` | M070 |
| diagonal | `obtain ⟨a, ha⟩ := hf {x \| x ∉ f x}`; `⟨fun n => !f n n, fun n h => ?_⟩` | Cantor | M071 |
| `⋂₀`, `⋃₀` | `exact (hf _ _ (lfp_least f A hA)).trans hA` | `Set.sInter_subset_of_mem`, `Set.subset_sInter`, `Set.subset_sUnion_of_mem`, `Set.sUnion_subset`, `subset_antisymm`, `h.le` for `⊆` from `=` | H039, H040 |
| inverses | `rw [leftInverse_invFun hg y]` | `Function.invFun g` (needs `Nonempty`), `leftInverse_invFun : Injective f → invFun f (f a) = a`; `isEmpty_or_nonempty β` | H040 |
| complements | `apply Set.compl_subset_compl.mpr; apply Set.image_mono` | `compl_compl`, `Set.mem_compl_iff` | H040 |
| piecewise function | `classical` then `fun x => if x ∈ A then f x else invFun g x` | `by_cases h1 : x1 ∈ A <;> by_cases h2 : x2 ∈ A <;> simp only [h1, h2, if_true, if_false] at h` | H040 |
| unions | `obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx`, `mem_iUnion₂.mpr ⟨i, Finset.mem_singleton_self i, hi⟩` | `⋃ i ∈ t, U i` is a double union | M077, H046 |
| `⊆` as a function | `⟨Nat.unpair, fun p _ => ⟨Nat.pair p.1 p.2, Nat.unpair_pair p.1 p.2⟩⟩` | `s ⊆ t` is `∀ x, x ∈ s → x ∈ t`; `Set.mem_range` | M077 |
| pairing ℕ × ℕ ≃ ℕ | `fun k => f k.unpair.1 k.unpair.2` | `Nat.unpair_pair a b : Nat.unpair (Nat.pair a b) = (a, b)` | M077 |
| intervals | `⟨⟨le_rfl, hab⟩, ha⟩`, `Set.nonempty_Icc.mpr hab.le` | `Set.mem_Icc`, `Set.mem_Ioo`, `Set.Icc_subset_Icc_right`, `Set.Ioo_subset_Icc_self` | H041, H049 |
| finite subcover | `exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hzi⟩` | `Finset.mem_insert_self`, `Finset.mem_insert_of_mem` (needs `classical` for `insert`) | H046 |

### Topology, filters, metric spaces

| API | Example | Gloss | IDs |
|---|---|---|---|
| compose limits | `(hf.tendsto c).comp hlim` | `Continuous.tendsto : Tendsto f (𝓝 c) (𝓝 (f c))`, `Filter.Tendsto.comp` | H045 |
| eventual facts | `((hlim.eventually_lt_const (lt_add_one (f c))).and (eventually_ge_atTop ⌈f c + 1⌉₊)).exists` | `Tendsto.eventually_lt_const`, `eventually_ge_atTop`, `Eventually.and`, `Eventually.exists` | H045 |
| `filter_upwards` | `filter_upwards [eventually_ge_atTop n] with k hk` | prove `∀ᶠ k in atTop, P k` given `hk : n ≤ k` | H045 |
| limit of a bound | `have hMc := ge_of_tendsto hlim hev` | `Tendsto u l (𝓝 c) → (∀ᶠ n in l, b ≤ u n) → b ≤ c` | H045 |
| ceiling | `(Nat.le_ceil _).trans (by exact_mod_cast hn2)` | `a ≤ ⌈a⌉₊` | H045 |
| open sets | `obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU j) s hj` | `∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s`; `rw [Metric.mem_ball, Real.dist_eq, abs_lt]` | H046 |
| distance sums | `dist_le_Ico_sum_dist (fun i => f^[i] x0) hmn` | `dist (u m) (u n) ≤ ∑ i ∈ Ico m n, dist (u i) (u (i+1))`; `geom_sum_Ico_le_of_lt_one` bounds `∑ x^i ≤ x^m / (1 - x)` | H047 |
| Cauchy, completeness | `rw [Metric.cauchySeq_iff']`; `cauchySeq_tendsto_of_complete h` | `CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε`; a Cauchy sequence converges in a `CompleteSpace` | H047 |
| limit algebra | `simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const (dist x0 (f x0))).div_const (1 - k)` | `r ^ n → 0`; `.mul_const`, `.const_mul`, `.div_const` | H047 |
| ε-N from `Tendsto` | `(hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop` | `∃ N, ∀ n ≥ N, u n < ε` | H047 |
| squeeze | `refine squeeze_zero (fun n => dist_nonneg) (fun n => hf _ L) ?_` | after `rw [tendsto_iff_dist_tendsto_zero] at hL ⊢` | H047 |
| shift, uniqueness | `(tendsto_add_atTop_iff_nat 1).mpr hL`, `tendsto_nhds_unique hfL hshift` | limit of `u (n + k)`; limits are unique | H047 |
| distances | `dist_le_zero.mp this` | `dist_nonneg`, `dist_comm`, `dist x y ≤ 0 ↔ x = y` | H047 |
| point of a nonempty type | `obtain ⟨x0⟩ := ‹Nonempty X›` | `‹P›` names the instance | H047 |

### Derivatives and integrals

| API | Example | Gloss | IDs |
|---|---|---|---|
| extreme values on `[a, b]` | `obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn hne hfc` | `IsCompact.exists_isMaxOn` / `exists_isMinOn` need `s.Nonempty` and `ContinuousOn f s` | H049 |
| Fermat | `(hmax.isLocalMax (Icc_mem_nhds hc.1 hc.2)).hasDerivAt_eq_zero hd` | `IsMaxOn.isLocalMax` (`s ∈ 𝓝 a`), `Icc_mem_nhds`, `IsLocalMax.hasDerivAt_eq_zero`; `IsMinOn.isLocalMin` likewise | H049 |
| derivative rules | `simpa using ((hasDerivAt_id x).sub_const a).const_mul k` | `hasDerivAt_id`, `.sub_const`, `.const_mul`, `.sub` | H049 |
| continuity on a set | `hfc.sub (by fun_prop)`, `hfc.mono (Set.Icc_subset_Icc_right hx.2)` | combine, restrict; `fun_prop` for polynomials | H049 |
| `IsMaxOn` by hand | `show f x ≤ f ((a + b) / 2)` | `IsMaxOn f s c ↔ ∀ x ∈ s, f x ≤ f c` is `Iff.rfl` | H049 |
| integral comparison | `intervalIntegral.integral_mono_on hle (intervalIntegrable_const (μ := MeasureTheory.volume)) hf.intervalIntegrable (fun x hx => hf hx.1)` | `a ≤ b`, both integrable, pointwise `≤` on `Icc a b` | H048 |
| constants | `rw [intervalIntegral.integral_const, smul_eq_mul, hw] at this` | `∫ x in a..b, c = (b - a) • c` | H048 |
| integrability | `hf.intervalIntegrable`, `intervalIntegrable_const` | `Monotone.intervalIntegrable`; constants need `(μ := MeasureTheory.volume)` | H048 |
| split `[0, 1]` | `intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := MeasureTheory.volume) (a := fun k : ℕ => (k : ℝ) / (n + 1)) (n := n + 1) (fun k _ => hf.intervalIntegrable)` | `∑ k ∈ range n, ∫ in a k..a (k+1) = ∫ in a 0..a n` | H048 |

### Gotchas

- Renamed at these pins: `Finset.card_insert_of_notMem` (`card_insert_of_not_mem` is gone), `div_lt_iff₀` / `div_le_iff₀` (no unsuffixed `div_lt_iff`), `push Not` (not `push_neg`). (M056, M067, M078)
- Scoped notation fails without its `open`: `#s` (`open Finset`), `n !` (`open Nat`), `ℚ[X]` (`open Polynomial`), `𝓝` (`open Topology`), `atTop`/`Tendsto` (`open Filter`). (M062, H035, H045)
- `decide` refuses goals with free variables: `revert x` first, or `decide +revert`, which also handles a local `[Fact p.Prime]`. (M053, H034)
- ℕ subtraction truncates: `p - 1`, `4 * n.factorial - 1`. Put `Nat.factorial_pos n` / `hp.one_lt` in context for `omega`, and use `Nat.sub_add_cancel` to undo `- 1`. (M065, H032)
- Restate ℕ `%` and `/` in ℤ before calling `ring`: `((n % m : ℕ) : ℤ) = n - m * (n / m : ℕ)` via `exact_mod_cast Nat.mod_add_div n m`. (H031)
- `exact_mod_cast` lines up casts only when the cast sits on the same ℕ term: to reuse `((2 * n !) ^ 2 + 1 : ℕ)` cast to `ZMod p` being `0`, state the goal about `((2 * n.factorial : ℕ) : ZMod p)`. (M064)
- `sSup` is total: on an empty or unbounded set it is `0`, so every `cs…` lemma needs a `Nonempty` and/or `BddAbove` argument. (M074, H041)
- `set c := sSup S` makes `c` a local definition: `rintro rfl` on `c = b` fails; rewrite with `rw [h] at …` instead. (H041)
- `nlinarith` does not find side facts: pass `sq_abs x`, `abs_nonneg x`, `dist_nonneg`, `mul_nonneg …` as hints. (M066, H038, H047)
- In characteristic 2, `1 = -1`, so `{1, -1}` has one element: split on `(1 : K) = -1` before `Finset.prod_pair`. (H033)
- Field inverse is total, `0⁻¹ = 0`: work over `univ.erase 0`. (H033)
- `natDegree : ℕ` but `degree : WithBot ℕ`; `compute_degree!` proves both. (M062)
- `Finset.filter`, `insert` and `if x ∈ A` need decidability: start with `classical`. (H037, H040, H046)
- `Finite G` gives no `Finset.univ`: `haveI := Fintype.ofFinite G`, then convert `Nat.card` with `Nat.card_eq_fintype_card`. (H037)
- An `if` on reals, or a choice, makes a definition `noncomputable`; M077 bans `noncomputable`, so `interleave` must be the explicit `Nat.unpair` formula. (M077, H043)
- Ban walls: M073, M075, M076, M078, H041 and H048 ban `Continuous`, `Tendsto`, `Filter`, `Metric`, `fun_prop` (M074 bans `Tendsto`/`Filter`); work from the card's own `ContAt` / `ConvergesTo`. M077 bans the `Countable` API. H042–H044 freeze the imports. H045/H046 ban compactness in every form; H049 bans Mathlib's Rolle/MVT. (M073–M078, H041–H049)
- `Function.iterate_succ_apply'` gives `f (f^[n] x)` (outer step); the unprimed one gives `f^[n] (f x)`. (H044, H047)

## Probability and statistics

Mathlib measure-theoretic probability (`import Mathlib`). Every file opens with
`open MeasureTheory ProbabilityTheory`; add `Filter Topology` for limits (`atTop`, `𝓝`), `open scoped NNReal`
for `ℝ≥0`, `open scoped ENNReal` for `ℝ≥0∞`. A random variable is a plain function `X : Ω → ℝ`; an event is a
`Set Ω`; a distribution is a `Measure`. Easy E095–E103, medium M079–M101, hard H050–H061.

### Setup and notation

| Construct | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| sample space + probability | `{Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]` | σ-algebra on `Ω`, measure `μ`, instance `μ univ = 1` | E095 |
| event | `MeasurableSet A`; `hB.diff hA`, `hB.compl`, `(hmeas i).inter hA` | `A` is in the σ-algebra; closure by dot notation | E095, M079, M081 |
| `μ s : ℝ≥0∞` | `μ Aᶜ = 1 - μ A` | `ℝ≥0∞` = `ENNReal` = [0, ∞]; truncated `-` | E095 |
| `μ.real s : ℝ` | `measureReal_def : μ.real s = (μ s).toReal`; `probReal_univ : μ.real univ = 1` | probability as a real number | E095, M084, M101 |
| expectation `μ[X]` | `μ[fun ω => a * X ω + b] = a * μ[X] + b` | `∫ ω, X ω ∂μ`; needs `open ProbabilityTheory`; `P[X]` for a measure named `P` | E096, E101 |
| variance `Var[X; μ]` | `Var[fun ω => a * X ω + b; μ] = a ^ 2 * Var[X; μ]` | `ProbabilityTheory.variance X μ`, a real; 0 if `X ∉ L²` | E097 |
| independence `X ⟂ᵢ[μ] Y` | `(hXY : X ⟂ᵢ[μ] Y)` | `IndepFun X Y μ` | E099 |
| conditional probability `μ[B \| A]` | `μ[B \| A] = μ B` | `cond μ A B = (μ A)⁻¹ * μ (A ∩ B)` (thing after `\|` is a **set**) | E100, M081 |
| conditional expectation `μ[X \| m]` | `μ[X \| m] = X` | `condExp m μ X : Ω → ℝ` (thing after `\|` is a **σ-algebra**) | E103, M100 |
| almost everywhere | `∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1`; `f =ᵐ[μ] g`; `0 ≤ᵐ[μ] f` | holds off a `μ`-null set | E102, M085, M100 |
| filters | `∀ᶠ n in atTop, ω ∉ s n`; `∃ᶠ n in atTop, p n`; `Tendsto f atTop (𝓝 a)` | for all large `n`; infinitely often; `f n → a` | H050, H051 |
| `X * Y`, `X ^ 2`, `X + Y` on functions | `Pi.pow_apply : (f ^ n) x = f x ^ n`, `Pi.add_apply`, `Pi.mul_apply` | pointwise operations; unfold with `simp only` | M088, M091 |
| sums of random variables | `Finset.sum_apply : (∑ c ∈ s, g c) a = ∑ c ∈ s, g c a` | `∑ i ∈ s, X i` is a function | M092, H050 |
| `ℝ≥0`, `unitInterval` | `(v : ℝ≥0)`, `(p : unitInterval)`, `p.2.1 : 0 ≤ (p : ℝ)`, `p.2.2 : (p : ℝ) ≤ 1` | parameters of `gaussianReal`, `poissonMeasure`, `binomial`, `geometricMeasure` | E101, M094, H055 |
| `∑' n, f n` | `tsum_fintype : ∑' b, f b = ∑ b, f b`; `tsum_bool` | infinite sum (0 if not summable; always exists in `ℝ≥0∞`) | M081, M083, H051 |

### Event algebra and measures of sets

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `prob_compl_eq_one_sub` / `probReal_compl_eq_one_sub` | `prob_compl_eq_one_sub hA : μ Aᶜ = 1 - μ A` | complement rule (ENNReal / real) | E095, M082, M096 |
| `measure_mono`, `prob_le_one`, `measureReal_mono` | `⟨prob_compl_eq_one_sub hA, measure_mono hAB, prob_le_one⟩` | monotonicity, `μ s ≤ 1` | E095, M087, H051 |
| `measure_ne_top` | `measure_ne_top μ A : μ A ≠ ∞` | finite measure side condition | E100, M082 |
| `measure_union` | `measure_union Set.disjoint_sdiff_right (hB.diff hA)` | additivity, disjoint, 2nd set measurable | M079 |
| `measure_inter_add_sdiff` | `(measure_inter_add_sdiff B hA).symm : μ B = μ (B ∩ A) + μ (B \ A)` | split a set along `A` | M079, M082 |
| `Set.union_sdiff_self`, `Set.disjoint_sdiff_right`, `Set.sdiff_eq` | `rw [← Set.union_sdiff_self]` | `s ∪ t \ s = s ∪ t`; `s \ t = s ∩ tᶜ` | M079, M082 |
| `measure_union_le` | `(measure_union_le _ _).trans (add_le_add le_rfl ih)` | subadditivity (union bound step) | M080 |
| `Finset.induction_on` | `classical; induction s using Finset.induction_on with \| empty => simp \| insert a s ha ih => _` | induction over a finite index set | M080 |
| `Finset.set_biUnion_insert`, `Finset.sum_insert` | `rw [Finset.set_biUnion_insert, Finset.sum_insert ha]` | peel `a` off `⋃ i ∈ insert a s` and `∑` | M080 |
| `measure_iUnion` + `tsum_fintype` | `rw [measure_iUnion hdisj' hmeas', tsum_fintype]` | countable additivity; pairwise disjoint = `Pairwise (Function.onFun Disjoint B)` | M081 |
| `Set.iUnion_inter`, `Disjoint.mono` | `(hdisj hij).mono Set.inter_subset_left Set.inter_subset_left` | intersect a partition with `A` | M081 |
| `measure_iUnion_le` | `measure_iUnion_le _ : μ (⋃ i, s i) ≤ ∑' i, μ (s i)` | countable subadditivity | H051 |
| `limsup_eq_iInf_iSup_of_nat'` | `rw [limsup_eq_iInf_iSup_of_nat']; exact iInf_le _ n` | `limsup s atTop = ⋂ n, ⋃ i, s (i + n)` ("infinitely often"); `⨅`/`⨆` on sets are `⋂`/`⋃` | H051 |
| `ENNReal.tendsto_sum_nat_add`, `ge_of_tendsto'` | `le_antisymm (ge_of_tendsto' (ENNReal.tendsto_sum_nat_add _ hs) h) bot_le` | tails of a finite `tsum` → 0; Borel–Cantelli | H051 |
| `ENNReal.tendsto_tsum_compl_atTop_zero` | tails `∑' b : {x // x ∉ F}, f b → 0` as `F : Finset` grows | Borel–Cantelli over a countable unordered index | H051 |
| `ae_iff`, `Filter.not_eventually` | `rw [ae_iff, setOf_not_eventually]` | `(∀ᵐ a, p a) ↔ μ {a \| ¬p a} = 0`; `¬∀ᶠ = ∃ᶠ ¬` | H051 |
| `Finset.measurableSet_biUnion` / `_biInter` | `Finset.measurableSet_biInter t fun i _ => hA i` | finite unions/intersections are events | H052 |
| `Set.mem_iUnion₂`, `Set.mem_iInter₂` | `Set.mem_iUnion₂.mpr ⟨i, hi, hω⟩` | membership in `⋃ i ∈ s` / `⋂ i ∈ t` | H052 |

### ℝ≥0∞ arithmetic

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `ENNReal.inv_mul_cancel` | `ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A)` | `a⁻¹ * a = 1` needs `a ≠ 0` **and** `a ≠ ∞` | E100 |
| `ENNReal.add_sub_cancel_left` | `ENNReal.add_sub_cancel_left (measure_ne_top μ _)` | `a + b - a = b` for `a ≠ ∞` | M082 |
| `ENNReal.mul_sub` | `ENNReal.mul_sub (fun _ _ => measure_ne_top μ A)` | `a * (b - c) = a * b - a * c` | M082 |
| `ENNReal.inv_two_add_inv_two` | `rw [ENNReal.inv_two_add_inv_two]` | `2⁻¹ + 2⁻¹ = 1` | M083 |
| `ENNReal.toReal_eq_toReal_iff'`, `ENNReal.toReal_add` | `rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]` | move an `ℝ≥0∞` identity to `ℝ`, then `norm_num` | M083 |
| `finiteness` | `(by finiteness) : (3 / 4 : ℝ≥0∞) ≠ ∞` | proves `x ≠ ∞` side goals | M083 |
| `ENNReal.toReal_inv`, `ENNReal.toReal_natCast`, `ENNReal.toReal_nsmul` | `rw [ENNReal.toReal_nsmul]; simp [ENNReal.toReal_inv]` | casting PMF masses to `ℝ` | M101, H054 |
| `ENNReal.ofReal` lemmas | `ENNReal.ofReal_sub`, `ENNReal.ofReal_one`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_inv_of_pos`, `ENNReal.ofReal_le_ofReal` | `ℝ → ℝ≥0∞`; gather into one `ofReal (…)`, then `congr 1; ring` | M096, H050 |
| `ENNReal.tendsto_ofReal`, `ENNReal.ofReal_zero` | `rw [← ENNReal.ofReal_zero]; apply ENNReal.tendsto_ofReal` | push a real limit into `ℝ≥0∞` | H050 |
| `bot_le` | `Eventually.of_forall fun _ => bot_le` | `0 ≤ x` in `ℝ≥0∞` (`0 = ⊥`) | H050, H051 |
| `div_eq_mul_inv` | `rw [..., div_eq_mul_inv]; ring` | `a / b = a * b⁻¹`; `ring` treats `⁻¹` as an atom | M081 |

### Conditional probability and independent events

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `cond_apply` | `rw [cond_apply hA, h, ← mul_assoc, ENNReal.inv_mul_cancel hA0 (measure_ne_top μ A), one_mul]` | `μ[t \| s] = (μ s)⁻¹ * μ (s ∩ t)` | E100, M096 |
| `cond_mul_eq_inter` | `simp_rw [cond_mul_eq_inter (hmeas _)]` | `μ[t \| s] * μ s = μ (s ∩ t)`; total probability | M081 |
| `cond_eq_inv_mul_cond_mul` | `cond_eq_inv_mul_cond_mul hA (hmeas j)` | Bayes: `μ[t \| s] = (μ s)⁻¹ * μ[s \| t] * μ t` | M081 |
| `IndepSet A B μ` | `rw [indepSet_iff_measure_inter_eq_mul hA hB.compl μ]` | independent events ↔ `μ (A ∩ B) = μ A * μ B` (pass `μ` explicitly) | M082 |
| `Set.Ioi_inter_Ioi` | `rw [Set.Ioi_inter_Ioi, max_eq_right (by linarith)]` | `Ioi a ∩ Ioi b = Ioi (max a b)` (prints `a ⊔ b`) | M096 |

### Expectation: integral algebra

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `integral_add` / `integral_sub` | `rw [integral_add (hX.const_mul a) (integrable_const b), integral_const_mul]` | linearity; both pieces `Integrable` | E096, M089 |
| `integral_const_mul`, `integral_div` | `integral_div _ _ : μ[fun ω => X ω / m ^ 2] = m / m ^ 2` | pull out constants; no integrability needed | E096, M093 |
| `integral_const`, `probReal_univ` | `simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]` | `∫ c = μ.real univ • c = c` | E096, M089 |
| `integral_finsetSum`, `integrable_finsetSum` | `integral_finsetSum _ (fun i _ => (hL2 i).integrable one_le_two)` | `E[∑ Xᵢ] = ∑ E Xᵢ` (no independence) | M092, H055, H060 |
| `integral_mono` | `integral_mono (f := fun ω => 2 / m - X ω / m ^ 2) hl hinv hpt` | integrate a pointwise `f ≤ g` | M084, M093, H056 |
| `integral_nonneg` | `integral_nonneg fun ω => sq_nonneg _` | `0 ≤ f → 0 ≤ ∫ f` | M090, H061 |
| `integral_pos_iff_support_of_nonneg` | `rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hX]` | `0 < ∫ f ↔ 0 < μ (support f)` | M093 |
| `integral_congr_ae` | `integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hWm hWX hXi)` | a.e.-equal integrands, equal integrals | H061 |
| `discrim_le_zero`, `discrim` | `have := discrim_le_zero key; rw [discrim] at this; nlinarith` | quadratic `≥ 0` everywhere ⇒ `b² - 4ac ≤ 0` (Cauchy–Schwarz) | M090, H056 |

### Integrability, Lᵖ, measurability

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `Integrable X μ` | `hX.const_mul a`, `i1.add i2`, `hX2.sub h2`, `hX.div_const _`, `integrable_const b` | `∫ \|X\| < ∞` + a.e.-measurable; closure lemmas | E096, M087, M093 |
| `MemLp X 2 μ` | `hX.integrable one_le_two`, `hX.integrable_sq`, `hX.integrable_mul hY`, `hX.sub (memLp_const c)`, `hX.add hY` | `X ∈ L²` (`E X² < ∞`) | M085, M089, M091, H061 |
| `memLp_finsetSum'`, `MemLp.const_mul` | `(memLp_finsetSum' (Finset.range n) fun i _ => hL2 i).const_mul (n : ℝ)⁻¹` | sums and multiples stay in `L²` | M092, H050 |
| `memLp_of_bounded` | `memLp_of_bounded hb hX.aestronglyMeasurable 2` | a.e. in `Icc a b` ⇒ `MemLp f p μ` for every `p` | M088, M099 |
| `memLp_two_iff_integrable_sq` | `(memLp_two_iff_integrable_sq h.aestronglyMeasurable).2 hsq` | `L²` ↔ `X²` integrable | H053 |
| `Integrable.of_bound` | `Integrable.of_bound (hX i).aestronglyMeasurable 1 (ae_of_all _ hb)` | bounded on a finite measure ⇒ integrable | H058, H060 |
| `Integrable.mul_bdd` | `hXi.mul_bdd (c := 1) (measurable_const.indicator hA).aestronglyMeasurable h` | integrable × bounded | H056, H060 |
| `AEStronglyMeasurable` | `hX.aestronglyMeasurable` (from `Measurable` or `MemLp`), `hX.const_mul a` | a.e. equal to a measurable function (weakest form) | E097, E099, M091 |
| `StronglyMeasurable.of_discrete` | `StronglyMeasurable.of_discrete.aestronglyMeasurable` | any `f : ℕ → ℝ` is measurable | H055 |
| `measurableSet_le` / `measurableSet_lt` | `measurableSet_le measurable_const hmeas : MeasurableSet {ω \| c ≤ X ω}` | events defined by inequalities | M084, H056 |
| `Finset.measurable_sum` | `(Finset.measurable_sum _ fun i _ => hmeas i).aemeasurable` | measurability of a finite sum | H057 |
| `Filter.Eventually.of_forall`, `ae_of_all` | `Filter.Eventually.of_forall fun ω => sq_nonneg _`; `ae_of_all _ fun _ => Set.mem_univ _` | an everywhere fact is an a.e. fact | E102, M085, M088 |

### Indicators

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `S.indicator f` | `S.indicator (fun _ => c) ≤ X`; `A.indicator (1 : Ω → ℝ) ω` | `f ω` on `S`, `0` off it; `1_A` with `f = 1` | M084, H052, H056 |
| `Set.indicator_of_mem` / `_of_notMem`, `Set.indicator_apply` | `rw [Set.indicator_of_mem h]` | evaluate; `indicator_apply` gives an `if` | M084, H052, H056 |
| `integral_indicator_const` | `rwa [integral_indicator_const c hS, smul_eq_mul, mul_comm] at this` | `∫ S.indicator (fun _ => e) = μ.real S • e` | M084, H058 |
| `integral_indicator_one` | `rw [← integral_indicator_one hU]` | `∫ s.indicator 1 = μ.real s` (turn probabilities into integrals) | H052, H056 |
| `Integrable.indicator`, `Measurable.indicator` | `((integrable_const (1 : ℝ)).indicator (hI t)).const_mul _` | indicators of events are integrable/measurable | M084, H052, H058 |
| `Finset.prod_sub`, `Finset.sum_filter`, `Finset.sum_erase_add` | `rw [indicator_biUnion, Finset.prod_sub]` | `1 - ∏(1 - 1_{Aᵢ})` expands over the powerset (inclusion–exclusion) | H052 |
| `Finset.sum_boole` | `exact Finset.sum_boole _ _` | `∑ (if p x then 1 else 0) = #{x ∈ s \| p x}` (empirical counts) | H058 |

### Variance

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `variance_add_const`, `variance_const_mul` | `rw [variance_add_const (hX.const_mul a), variance_const_mul]` | `Var(X + c) = Var X`; `Var(cX) = c² Var X` | E097, H050 |
| `variance_eq_sub` | `rw [variance_eq_sub hL2, hsq]; ring` | `Var X = μ[X ^ 2] - μ[X] ^ 2` (needs `MemLp X 2 μ`) | M088, M091, H053 |
| `variance_eq_integral` | `rw [← variance_eq_integral hX.aemeasurable] at hm` | `Var X = ∫ (X - μ[X])²` | M085, M087 |
| `variance_nonneg` | `variance_nonneg X μ : 0 ≤ Var[X; μ]` | | M087 |
| `IndepFun.variance_sum` | `IndepFun.variance_sum (fun i _ => hL2 i) (fun i _ j _ hij => hindep hij)` | variance of a pairwise-independent finite sum | M092, H050 |
| `obtain ⟨v, hv⟩ : ∃ v, Var[X; μ] = v := ⟨_, rfl⟩` | then `rw [hv] at hk ⊢` | name a big term so `field_simp`/`nlinarith` see an atom | M087 |

### Independence and product measures

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `IndepFun.integral_mul_eq_mul_integral` | `hXY.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable` | `E[XY] = E X · E Y` | E099, M091 |
| `Pairwise fun i j => X i ⟂ᵢ[μ] X j` | `hindep hij` for `hij : i ≠ j` | pairwise independence of a sequence | M092, H050, H058 |
| `iIndepFun X μ` | `hindep.mgf_sum hmeas`; `hindep.indep_comap_natural_of_lt hX h` | mutual independence of a family | M099, H057, H060 |
| `IndepFun.comp`, `IdentDistrib.comp` | `(hindep hij).comp hf hf`; `(hident i).comp hf` | survive composing with measurable maps | H058 |
| `IdentDistrib X Y μ μ` | `(hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)` | same law (i.i.d. = independent + `IdentDistrib`) | M099, H058 |
| `IndepFun_iff_Indep` | `((IndepFun_iff_Indep _ _ _).mp hXY).symm` | `X ⟂ᵢ Y ↔ Indep σ(X) σ(Y) μ` | M100 |
| `Measure.pi`, `iIndepFun_pi` | `(iIndepFun_pi (μ := fun _ => die) (X := fun _ x => x) h).indepFun (by decide)` | product measure on `ι → α`; coordinates are independent | M101 |
| `Measure.pi_singleton`, `sum_measure_singleton` | `rw [measureReal_def, hs, ← sum_measure_singleton]` | point mass of a product; `∑ x ∈ s, μ {x} = μ ↑s` | M101 |

### Inequalities and moment generating functions

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| Markov `mul_meas_ge_le_integral_of_nonneg` | `mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall h) hint (c ^ 2)` | `ε * μ.real {ε ≤ f} ≤ ∫ f` for `0 ≤ᵐ f` | M085, M087 |
| Chebyshev `meas_ge_le_variance_div_sq` | `meas_ge_le_variance_div_sq hY hε` | `μ {c ≤ \|X - μ[X]\|} ≤ ofReal (Var/c²)` (ENNReal) | H050 |
| Jensen `ConvexOn.map_integral_le` | `ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hX hexp` | `g (E f) ≤ E (g ∘ f)`; 6 args: convex, continuous on `s`, `s` closed, a.e. in `s`, two integrabilities | E102 |
| convexity facts | `convexOn_exp`, `Even.convexOn_pow even_two`, `(continuous_pow 2).continuousOn`, `isClosed_univ` | | E102 |
| `mgf X μ t` | `mgf_gaussianReal hX.map_eq`, `mgf_pos_iff.mp`, `mgf_nonneg` | `μ[fun ω => exp (t * X ω)]` | M086, H057 |
| Chernoff `measure_ge_le_exp_mul_mgf` | `measure_ge_le_exp_mul_mgf ε ht0 hint` | `μ.real {ε ≤ X} ≤ exp (-t ε) * mgf X μ t` | M086, H057 |
| Hoeffding's lemma | `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hmeas.aemeasurable (Eventually.of_forall hbdd) hmean ht` | mgf of a mean-0 `[a, b]` variable ≤ `exp ((‖b - a‖₊/2)² t²/2)` | H057 |
| `iIndepFun.mgf_sum`, `integrable_exp_mul_of_mem_Icc` | `rw [e, hindep.mgf_sum hmeas, Real.exp_nat_mul]` | mgf of an independent sum = product of mgfs | H057 |
| `coe_nnnorm`, `Real.norm_eq_abs` | `rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos h]` | `(‖x‖₊ : ℝ) = \|x\|` | H057 |

### Distributions and laws

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `PMF α`, `p.toMeasure` | `(PMF.uniformOfFintype (Fin 6)).toMeasure {i} = 6⁻¹` | mass function `α → ℝ≥0∞` summing to 1, and its measure | E098, M101, H054 |
| `PMF.uniformOfFintype_apply`, `PMF.toMeasure_apply_singleton` | `rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), PMF.uniformOfFintype_apply]` | uniform mass `(card α)⁻¹`; singleton mass | E098, M083 |
| `PMF.integral_eq_sum` | `rw [PMF.integral_eq_sum]; simp [Fin.sum_univ_succ]` | `∫ f ∂p.toMeasure = ∑ a, (p a).toReal • f a` (finite) | E098, H054 |
| PMF monad | `show (coin.bind fun a => coin.bind fun b => PMF.pure (a \|\| b)) true = 3 / 4` | `do`/`←`/`return` = `PMF.bind`/`PMF.pure`; `PMF.bind_apply`, `PMF.pure_apply`, `tsum_bool` | M083 |
| `HasLaw X ν P` | `hX.integral_eq`, `hX.variance_eq`, `hX.map_eq`, `hX.integral_comp`, `hX.aemeasurable` | law of `X` under `P` is `ν` (`P.map X = ν`) | E101, M086, H055 |
| `gaussianReal m v` | `rw [hX.integral_eq, integral_id_gaussianReal]`; `variance_id_gaussianReal` | `N(m, v)`, `v : ℝ≥0` | E101, M086, M099 |
| `binomial n p` (`Bin(n, p)`) | `rw [integral_binomial, ← Nat.range_succ_eq_Iic]`; `integrable_binomial _` | `p : unitInterval`; expectation = finite sum over `Iic n` | M094, H053 |
| `poissonMeasure r` (`Po(r)`) | `rw [integral_poissonMeasure]`; `(hasSum_one_poissonMeasure r).mul_left (r : ℝ)` | `r : ℝ≥0`; expectation = `tsum` | M095 |
| `geometricMeasure p` | `rw [integral_geometricMeasure hp]`; `integrable_geometricMeasure_iff hp` | # failures before first success; `p ≠ 0` | H055 |
| `expMeasure r`, `cdf` | `rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hx]`; `haveI := isProbabilityMeasure_expMeasure hr` | `Exp(r)`; `cdf μ x = P(T ≤ x)` (real) | M096 |
| series tools | `hasSum_nat_add_iff' 1`, `HasSum.tsum_eq`, `tsum_mul_left`, `tsum_coe_mul_geometric_of_norm_lt_one`, `summable_pow_mul_geometric_of_norm_lt_one` | index shift, geometric series moments | M095, H055 |
| `integrable_map_measure` | `(integrable_map_measure hmeas (hT k hk).aemeasurable).1 h` | integrability transfers between `X` and its law | H055 |
| binomial algebra | `Nat.add_one_mul_choose_eq`, `add_pow`, `Finset.sum_range_succ'`, `Finset.mul_sum` | `k C(n,k)` resummation | M094, H053 |
| permutations | `Fintype.card_perm`, `Finset.card_eq_sum_card_fiberwise`, `Finset.card_bij`, `Equiv.swap`, `Finset.sum_comm` | uniform law on `Equiv.Perm (Fin n)` (give it `⊤` as σ-algebra) | H054 |

### Limit theorems and a.e. reasoning

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| `TendstoInMeasure`, `tendstoInMeasure_iff_dist` | `rw [tendstoInMeasure_iff_dist]; intro ε hε` | convergence in probability: `μ {ε ≤ dist (f n x) (g x)} → 0` | H050 |
| squeeze | `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun _ => bot_le) h` | eventual bounds; `tendsto_const_div_atTop_nhds_zero_nat` | H050 |
| `strong_law_ae` | `filter_upwards [strong_law_ae Y hint hind hid] with ω hω` | SLLN: a.s. `(↑n)⁻¹ • ∑ X i ω → E X 0` (pairwise indep, i.d., integrable) | H058 |
| `tendstoInDistribution_inv_sqrt_mul_sum_sub` | `tendstoInDistribution_inv_sqrt_mul_sum_sub (by rwa [hvar]) hL2 hindep hident` | CLT; first arg `HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P'` | M099 |
| `TendstoInDistribution Z atTop Y (fun _ => P) P'` | | convergence in distribution; `x.toNNReal = max x 0` | M099 |
| `ae_all_iff` | `rw [ae_all_iff]; intro q` | swap `∀ᵐ` and `∀ q` over a countable type (`ℚ`) | H058 |
| `filter_upwards [h] with ω hω` | `filter_upwards [h2] with ω hω; simp [h1, hω]` | prove `∀ᵐ`/`=ᵐ`/`∀ᶠ` pointwise from a.e. hypotheses | M100, H050, H058 |
| `tendsto_order`, `exists_rat_btwn`, `Metric.eventually_nhds_iff` | `obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - δ < t by linarith)` | sandwich an empirical CDF between rationals | H058 |

### Conditional expectation and martingales

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| sub-σ-algebra | `{m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)` | last-declared `mΩ` is the default instance | E103, H061 |
| `Measurable[m] X`, `StronglyMeasurable[m] X` | `hXm.stronglyMeasurable` | measurability w.r.t. `m`; goal view drops `[m]` | E103, M100 |
| `σ(X)` | `MeasurableSpace.comap X inferInstance`; `hX.comap_le`; `comap_measurable X` | σ-algebra generated by `X`, `≤ mΩ`, `X` is σ(X)-measurable | M100, H060 |
| `integral_condExp` | `integral_condExp hm : ∫ ω, (μ[X \| m]) ω ∂μ = ∫ ω, X ω ∂μ` | tower property | E103, H061 |
| `condExp_of_stronglyMeasurable` | `condExp_of_stronglyMeasurable hm hXm.stronglyMeasurable hX` | known variable: `μ[X \| m] = X` | E103, M100 |
| `condExp_indep_eq` | `condExp_indep_eq hY.comap_le hX.comap_le (comap_measurable Y).stronglyMeasurable hind` | independent of `m₂`: `μ[f \| m₂] =ᵐ fun _ => μ[f]` (σ-algebra of `f` first) | M100, H060 |
| `condExp_add` | `(condExp_add hXi hYi _).trans ?_` | linearity, a.e. | M100 |
| `condExp_mul_of_stronglyMeasurable_left` | `condExp_mul_of_stronglyMeasurable_left hXm hXYi hYi` | pull out known factor: `μ[f * g \| m] =ᵐ f * μ[g \| m]` | M100, H060, H061 |
| `stronglyMeasurable_condExp`, `MemLp.condExp` | `hX.condExp one_le_two : MemLp μ[X \| m] 2 μ` | `E[X \| m]` is `m`-measurable and in `L²` | H061 |
| `Filtration.natural X hX` | `Filtration.stronglyAdapted_natural hX i`, `(Filtration.natural X hX).mono h`, `Filtration.le _ n` | `ℱₙ = σ(X 0, …, X n)` | H060 |
| `iIndepFun.indep_comap_natural_of_lt` | `hindep.indep_comap_natural_of_lt hX n.lt_succ_self` | `X j` independent of `ℱᵢ` for `i < j` | H060 |
| `Martingale f ℱ μ`, `martingale_of_condExp_sub_eq_zero_nat` | `apply martingale_of_condExp_sub_eq_zero_nat` (3 goals: adapted, integrable, `μ[f (i+1) - f i \| ℱ i] =ᵐ 0`) | | H060 |
| `Finset.stronglyMeasurable_fun_sum` | `apply Finset.stronglyMeasurable_fun_sum` | partial sums are adapted | H060 |

### Markov chains and statistics

| Name | Example (Lean) | Gloss | IDs |
|---|---|---|---|
| matrix / vector literals | `!![1 - a, a; b, 1 - b]`, `![b / (a + b), a / (a + b)]` | transition matrix (rows = next-state laws), probability vector | M097, H059 |
| `Matrix.vecMul` | `simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, P] at h0` | `π P` (row vector times matrix) | M097 |
| entrywise proofs | `ext i j; fin_cases i <;> fin_cases j <;> simp [P, Pinf, Matrix.mul_apply, Fin.sum_univ_two]` | also `Matrix.add_apply`, `Matrix.smul_apply` | M097, H059 |
| matrix powers | `rw [pow_succ', ih, mul_add, mul_smul_comm, ..., smul_smul, pow_succ]` | `Pⁿ` closed form by induction | H059 |
| `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` | `(tendsto_const_nhds).add (h0.mul tendsto_const_nhds)` | `rⁿ → 0` for `\|r\| < 1` | H059 |
| Gibbs inequality | `Real.log_le_sub_one_of_pos`, `Real.log_div` | MLE without calculus | M098 |
| sample statistics | `sampleMean`, `sampleVar` as `noncomputable def … (∑ i ∈ Finset.range n, X i ω) / n` | `field_simp` needs `(n : ℝ) ≠ 0`, `(n : ℝ) - 1 ≠ 0` | M092, H050 |

### Traps

- `μ[X]` (expectation), `Var[X; μ]`, `X ⟂ᵢ[μ] Y`, `μ[B | A]` (cond), `Bin(n, p)`, `Po(r)` are scoped in `ProbabilityTheory`;
  with only `open MeasureTheory`, `μ[X]` fails as `GetElem (Measure Ω) …`. `μ[X | m]` (condExp) is in `MeasureTheory`. (E096, E100, E103)
- `μ[B | A]` is conditional *probability* when `A` is a set; `μ[X | m]` is conditional *expectation* when `m` is a
  σ-algebra. Same brackets. (E100, E103)
- `ℝ≥0∞` subtraction truncates at 0 and `⁻¹` cancels only with `≠ 0` and `≠ ∞`: `ring`/`field_simp` will not do it.
  Rewrite with `ENNReal.*` lemmas, or move to `ℝ` (`toReal_eq_toReal_iff'`, `toReal_add`, `finiteness`). `norm_num`
  cannot evaluate `2⁻¹ * 2⁻¹ + 2⁻¹` in `ℝ≥0∞`. State identities with `+` on both sides (`μ (A ∪ B) + μ (A ∩ B) = …`). (E095, E100, M079, M082, M083)
- `rw [integral_add hf hg]` only fires if `hf : Integrable (fun ω => …) μ` has the integrand's exact lambda shape;
  `i1.add i2` has type `Integrable (f + g)`, so restate it with `have i12 : Integrable (fun ω => … + …) μ := i1.add i2`. (M087, M089, M090, M091, H056, H061)
- `integral_mono` with `hpt : ∀ ω, … ≤ …` may not unify; pass `(f := fun ω => …)`. (M093)
- `rw` cannot rewrite under `∑ i, …`; use `simp_rw`. `conv_lhs => rw [h]` rewrites one side only. (M081, H052)
- Jensen needs a closed domain: `x⁻¹` on `(0, ∞)` is not covered (and `0⁻¹ = 0` breaks convexity on `[0, ∞)`); integrate the tangent line instead. (E102, M093)
- `Measurable[m] X` displays as `Measurable X`; hover or `set_option pp.explicit true` to see the σ-algebra. (E103)
- Mathlib sets `μ[X | m] = 0` and `Var[X; μ] = 0` for non-integrable / non-`L²` `X`; most lemmas still need the hypotheses. (E097, E103)
- `gaussianReal m v` takes `v : ℝ≥0`; the goal shows the coercion `(v : ℝ)`. `0 < v` transfers by `have : (0 : ℝ) < v := hv`, and `field_simp` needs `(v : ℝ) ≠ 0`. (M086)
- Hoeffding's lemma is `protected`: write `ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero` in full. (H057)
- `condExp_indep_eq` wants the σ-algebra of the averaged function first: after `IndepFun_iff_Indep`, flip with `.symm`. (M100)
- ℕ subtraction in binomial/coupon sums (`m + 1 - (k + 1)`, `n - 1 - k`, `(n - k : ℕ)`): `rw [show … = m - k by omega]` or `Nat.cast_sub` before `ring`. (M094, M098, H055)
- `convert … using 1` on a `HasSum` leaves instance goals: prove the function identity by `funext` and `rw` it instead. (M095)
- `ring` cannot see through `ENNReal.ofReal`: gather into one `ofReal (…)`, then `congr 1; ring`. (M096)
- Many problems ban the library theorem they rebuild (M079 `measure_union_add_inter`, M080 `measure_biUnion_finset_le`,
  M084 Markov `mul_meas_ge_le_integral_of_nonneg`, M085 `meas_ge_le_variance_div_sq`, M091 `variance_add`, H051
  `measure_limsup_atTop_eq_zero`, H052 `measureReal_biUnion_eq_sum_powerset`, H057 `HasSubgaussianMGF`); later
  problems use them freely (M085 uses Markov, H050 uses Chebyshev). Check the card's `BANNED` line. (M079–H057)

## Numerical analysis

All of these problems use `import Mathlib`. The usual opens are `open Polynomial` (for `ℝ[X]`, `X`, `C`), `open Filter Topology` (for `atTop`, `𝓝`), `open Matrix` or `open scoped Matrix` (for `*ᵥ`, `⬝ᵥ`, `ᵀ`) and `open Set` (for `uIcc`). Do not combine `open Polynomial` with `open Matrix` in one section. Write `lam`, not `λ`, because `λ` is reserved syntax (M118, M123). A `def` that divides reals needs `noncomputable` (M103, M106, M123).

### Notation decoder

| Notation | Example | Meaning | IDs |
|---|---|---|---|
| `ℝ[X]`, `X`, `C a` | `(X ^ 2 - 2 * X + 1 : ℝ[X])` | real polynomials, the variable, the constant polynomial `a` (needs `open Polynomial`) | E104, M102 |
| `p.eval x`, `p.coeff i` | `(X + C 2 : ℝ[X]).eval 1 = 3` | value at `x`; coefficient of `Xⁱ` | E104, M102 |
| `p.natDegree : ℕ`, `p.degree : WithBot ℕ` | `p.degree < s.card` | degree; `natDegree 0 = 0`, `degree 0 = ⊥` | M102, M114 |
| `p.IsRoot r` | `h.eq_zero : p.eval r = 0` | `r` is a root | E104 |
| `⌊x⌋ : ℤ`, `round x : ℤ` | `⌊(3.7 : ℝ)⌋ = 3` | floor (toward -∞); nearest integer with ties going up | E108, M103 |
| `(2 : ℝ) ^ (e : ℤ)` | `(2 : ℝ) ^ (e - p)` with `e : ℤ`, `p : ℕ` | `zpow`, an integer exponent; `(p : ℤ)` casts | M103, H075 |
| `√a` (`Real.sqrt a`) | `Real.sq_sqrt ha : √a ^ 2 = a` | square root; equals `0` for `a < 0` | M109, M124 |
| `f^[n] x` | `(newton f)^[n] x₀` | `f` applied `n` times; `f^[0] x = x` | M107, H065, H071, H075 |
| `Tendsto u atTop (𝓝 L)` | `Tendsto (heron a x₀) atTop (𝓝 √a)` | `u n → L` as `n → ∞` | M107, H062–H064 |
| `Tendsto u atTop atTop` | `Tendsto (fun n => \|euler lam h y₀ n\|) atTop atTop` | `u n → +∞` | M118, H075 |
| `∀ᶠ n in atTop, P n` | `filter_upwards [eventually_ge_atTop N] with n hn` | `P n` holds for all large `n` (`Filter.Eventually`) | H073 |
| `⨆ n, u n`, `⨅ n, u n` | `set r := ⨆ n, lo n` | sup / inf of a sequence (conditionally complete, `ciSup`/`ciInf`) | H062, H064 |
| `HasDerivAt f f' x`, `deriv f x` | `HasDerivAt Real.exp (Real.exp x) x` | `f` has derivative `f'` at `x`; `deriv` is that number, or junk `0` if `f` is not differentiable | E105 |
| `ContDiff ℝ k f`, `iteratedDeriv k f x` | `hM : ∀ y, \|iteratedDeriv 2 f y\| ≤ M` | `f` is Cᵏ; the k-th derivative `f⁽ᵏ⁾(x)` | M111, H065, H066 |
| `iteratedDerivWithin k f s x`, `derivWithin f s x` | `iteratedDerivWithin 1 f (uIcc x y) x` | derivatives taken inside the set `s` (they show up as Taylor coefficients) | M111, H065 |
| `taylorWithinEval f n s x₀ x` | `taylorWithinEval f 1 (uIcc x y) x y` | degree-`n` Taylor polynomial of `f` at `x₀`, evaluated at `x` | M111, H065, H066 |
| `Set.Icc a b`, `Set.Ioo a b`, `Set.uIcc a b`, `Set.uIoo a b` | `x ∈ Set.Icc a b` unfolds to `a ≤ x ∧ x ≤ b` | `[a,b]`, `(a,b)`, `[min a b, max a b]`, the open version | M108, H067 |
| `∫ x in a..b, f x` | `∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3` | oriented interval integral; when `∂μ` is left out the measure is Lebesgue `volume` | E106 |
| `IntervalIntegrable f volume a b` | `hf.intervalIntegrable a b` for `hf : Continuous f` | `f` is integrable on `[a,b]`; spelled `MeasureTheory.volume` unless `MeasureTheory` is open | E106, M113 |
| `ℝ≥0` (`NNReal`) | `LipschitzWith (1 / 2) g` | nonnegative reals; Lipschitz constants live here and `↑K : ℝ` casts them | E107 |
| `LipschitzWith K f`, `ContractingWith K f` | `⟨by norm_num, hlip⟩ : ContractingWith (1/2) g` | `edist (f x) (f y) ≤ K * edist x y`; `ContractingWith K f` is `K < 1 ∧ LipschitzWith K f` | E107 |
| `Function.IsFixedPt f x`, `Set.MapsTo f s t` | `norm_num [Function.IsFixedPt]` | `f x = x`; `∀ ⦃x⦄, x ∈ s → f x ∈ t` | E107, M108 |
| `∃! p, P p` | `refine ⟨p, hp, fun q hq => ?_⟩` | exactly one: `∃ p, P p ∧ ∀ q, P q → q = p` | M108, M114 |
| `Matrix (Fin n) (Fin n) ℝ`, `A i j`, `!![a, b; c, d]` | `(!![4, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 1` | real n×n matrix, entry, literal written row by row | M120, H070 |
| `A *ᵥ v`, `v ᵥ* A`, `v ⬝ᵥ w`, `Aᵀ`, `c • v` | `(A *ᵥ v) i = ∑ j, A i j * v j := rfl` | matrix·vector, row vector vᵀA, dot product, transpose, scalar·vector | H063, H070, H074 |
| `‖v‖` for `v : Fin n → ℝ` | `norm_le_pi_norm v i : ‖v i‖ ≤ ‖v‖` | sup norm `maxᵢ \|vᵢ\|` | M121, H071 |
| `‖A‖` under `open scoped Matrix.Norms.Operator` | `Matrix.linfty_opNorm_mulVec A v` | ∞-operator norm (max row sum of `\|A i j\|`) | M121 |
| `Module.End.HasEigenvalue (Matrix.toLin' A) μ` | `eigenvalue_mem_ball hμ` | `μ` is an eigenvalue of `x ↦ A *ᵥ x` (some `v ≠ 0` has `A v = μ v`) | M120 |
| `univ.erase i` | `∑ j ∈ univ.erase i, \|A i j\|` | all indices except `i` (off-diagonal row sum) | M120, H070, H071 |
| `Lagrange.interpolate s v r`, `Lagrange.basis s v i` | `Lagrange.interpolate s v r : ℝ[X]` | interpolant through the nodes `v i` (i ∈ s) with values `r i`, a linear map applied to `r`; the basis polynomial `Lᵢ` | M114, M115 |
| `Polynomial.Chebyshev.T ℝ n` | `(Polynomial.Chebyshev.T ℝ n).eval (Real.cos θ)` | Chebyshev polynomial `Tₙ`, indexed by `n : ℤ` | M125 |

### Polynomials, Horner, interpolation

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `eval_add`, `eval_sub`, `eval_mul`, `eval_pow`, `eval_C`, `eval_X` | `rw [eval_add, eval_mul, eval_C, hp, hq]` | evaluation commutes with each operation; `simp` and `norm_num` know them all | E104 |
| `IsRoot.eq_zero` | `simp [h.eq_zero]` | turn `p.IsRoot r` into `p.eval r = 0` | E104 |
| `Polynomial.eval_eq_sum_range` | `rw [horner_eq_sum, eval_eq_sum_range]` | `p.eval x = ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ i` | M102 |
| `List.getD`, `List.getD_cons_zero`, `List.getD_cons_succ`, `List.getD_eq_getElem?_getD` | `simp [List.getD_eq_getElem?_getD, hi]` | `xs.getD i 0` is the i-th entry, or 0 past the end; peel indices under `::` | M102 |
| `Finset.sum_range_succ'`, `Finset.mul_sum`, `Finset.sum_congr rfl` | `exact Finset.sum_congr rfl fun i _ => by ring` | split off the `i = 0` term; pull `x *` into a sum; compare sums term by term (the Horner induction step) | M102 |
| `Lagrange.degree_interpolate_lt`, `Lagrange.eval_interpolate_at_node` | `Lagrange.eval_interpolate_at_node r hv hi` | `(interpolate s v r).degree < s.card`; value `r i` at node `v i` (both need `hv : Set.InjOn v s`) | M114 |
| `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'` | `apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' d (s.image v)` | root counting: `p` vanishes on Finset `t` and `natDegree p < t.card` gives `p = 0` | M114 |
| `Polynomial.degree_sub_le`, `Polynomial.natDegree_lt_iff_degree_lt` | `rw [natDegree_lt_iff_degree_lt hd]` | `(p - q).degree ≤ max ..`; switch between `natDegree` and `degree` when `p ≠ 0` | M114 |
| `Finset.card_image_of_injOn`, `Finset.mem_image` | `rw [Finset.card_image_of_injOn hv]` | `(s.image v).card = s.card` for injective `v`; `obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx` | M114 |
| `Lagrange.eq_interpolate`, `Lagrange.interpolate_apply` | `conv_lhs => rw [Lagrange.eq_interpolate hv hp, Lagrange.interpolate_apply]` | a polynomial of degree `< s.card` equals the interpolant of its own values, which is `∑ i ∈ s, C (r i) * basis s v i` | M115 |
| `Polynomial.eval_finsetSum` | `simp only [eval_finsetSum, eval_mul, eval_C]` | eval of a Finset sum is the sum of evals (`eval_finset_sum` is the deprecated name) | M115 |
| `Polynomial.continuous` | `((Polynomial.continuous p).intervalIntegrable a b).const_mul c` | `fun x => p.eval x` is continuous, so it is integrable | M115 |
| `Polynomial.Chebyshev.T_real_cos`, `Real.cos_eq_zero_iff` | `rw [Polynomial.Chebyshev.T_real_cos, Real.cos_eq_zero_iff]` | `(T ℝ n).eval (cos θ) = cos (n θ)`; `cos θ = 0 ↔ ∃ k : ℤ, θ = (2k+1)π/2` | M125 |

### Rounding and floating-point error models

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Int.floor_le`, `Int.lt_floor_add_one` | `⟨Int.floor_le x, Int.lt_floor_add_one x⟩` | `↑⌊x⌋ ≤ x < ↑⌊x⌋ + 1` | E108 |
| `Int.floor_eq_iff`, `round_eq` | `norm_num [round_eq, Int.floor_eq_iff]` | `⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1`; `round x = ⌊x + 1/2⌋`; together they evaluate concrete floors and rounds | E108 |
| `abs_sub_round` | `nlinarith [abs_sub_round (x / h)]` | `\|x - round x\| ≤ 1/2`; scaled to the grid `h ℤ` it gives error `≤ h/2` | E108, M103 |
| `zpow_add₀`, `zpow_add_one₀`, `zpow_sub_one₀` | `rw [zpow_add₀ two_ne_zero, zpow_one]` | `a ≠ 0 → a^(m+n) = a^m * a^n` for `m n : ℤ`; `a^(n±1) = a^n * a` (or `* a⁻¹`) | M103, H075 |
| `positivity` on zpow | `example (e : ℤ) : (0 : ℝ) < 2 ^ e := by positivity` | positivity of powers with integer exponents | M103 |
| relative-error model | `def RelErr (u : ℝ) (fl : ℝ → ℝ) : Prop := ∀ x, ∃ δ, \|δ\| ≤ u ∧ fl x = x * (1 + δ)` | the standard model: `fl` is abstract and this is all you know; use it with `obtain ⟨δ, hδ, hs⟩ := hfl s` | M104, H069 |
| error composition | `example (θ δ : ℝ) : (1 + θ) * (1 + δ) = 1 + (θ + δ + θ * δ) := by ring` | relative errors compose multiplicatively; for products this gives `\|θ\| ≤ (1+u)ⁿ - 1` | M104 |
| summation error identity | `example (s e δ : ℝ) : (s + e) * (1 + δ) - s = e * (1 + δ) + s * δ := by ring` | propagated error plus new rounding; key bound `((1+u)^d - 1)(1+u) + u = (1+u)^(d+1) - 1` | H069 |
| `List.prod_cons`, `List.sum_cons`, `List.sum_nonneg` | `rw [fprod, hfx, hq, List.prod_cons]` | unfold list products and sums; `0 ≤ (xs.map abs).sum` via `List.sum_nonneg (by simp)` | M104, H069 |
| `pow_le_pow_right₀`, `one_le_pow₀` | `ihl.trans (by gcongr; exacts [by linarith, le_max_left _ _])` | `1 ≤ a → n ≤ m → a^n ≤ a^m` lifts both subtree bounds to depth `max l r`; `1 ≤ a → 1 ≤ a^n` | H069, M119 |
| structural induction on your own tree | `induction t with \| leaf x => _ \| node l r ihl ihr => _` | one IH per subtree (the summation tree `STree`) | H069 |
| interval soundness | `rcases le_total 0 y with hy \| hy` + `le_min`, `max_le`, `min_le_left`, `le_max_right` | case on the sign of `y`, then place `x*y` between the endpoint products | M105 |
| cancellation bound | `abs_pos.mpr (sub_ne_zero.mpr hxy) : 0 < \|x - y\|` | relative error of `x - y` is `≤ u(\|x\|+\|y\|)/\|x - y\|`, unbounded as `x → y` | M124 |
| stable quadratic formula | `generalize √(b ^ 2 - 4 * a * c) = s at hs hsn ⊢` then `field_simp; linear_combination hs` | hide the root behind `s` (keeping `s^2 = D`, `0 ≤ s`) before clearing denominators | M124 |

### Derivatives (`HasDerivAt` calculus)

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| base facts | `hasDerivAt_pow n x`, `hasDerivAt_id' x`, `hasDerivAt_const t b`, `Real.hasDerivAt_exp x`, `Real.hasDerivAt_sin x`, `Real.hasDerivAt_cos t` | `xⁿ ↦ ↑n * x^(n-1)`, `x ↦ 1`, `c ↦ 0`, `exp`, `sin ↦ cos`, `cos ↦ -sin` | E105, M108, H068 |
| combinators | `hf.add hg`, `.sub`, `.mul`, `.const_mul c`, `.const_add c`, `.sub_const c`, `.pow n`, `.div_const c`, `.exp`, `.neg` | sum, product, constant, chain rules on `HasDerivAt` facts | E105, M117, H067, H068 |
| `HasDerivAt.congr_deriv` | `((hasDerivAt_pow 3 a).add ((hasDerivAt_id' a).const_mul 2)).congr_deriv (by norm_num)` | the rules produce `↑3 * a ^ (3 - 1) + 2 * 1`; fix the shape with an equality proof (`by ring`, `by norm_num`, `by simp`) | E105, M117, H067, H068 |
| `HasDerivAt.deriv` | `rw [(hf.const_mul 2).deriv]` | `HasDerivAt f f' x → deriv f x = f'` | E105 |
| `HasDerivAt.hasDerivWithinAt` | `(Real.hasDerivAt_cos t).hasDerivWithinAt` | restrict a derivative to a set (input for the MVT bound) | M108 |
| continuity from derivatives | `continuous_iff_continuousAt.mpr fun t => (h t).continuousAt` | `∀ t, HasDerivAt g (g' t) t` gives `Continuous g`; then `.continuousOn` | H067, H068, H072 |
| `ContDiff` helpers | `hf.differentiable (by norm_num)`, `hf.contDiffAt.of_le (by norm_num)`, `hf.contDiffOn` | lower the smoothness order or the scope of a `ContDiff ℝ k f` fact | M111, H065, H066 |

### Taylor, mean value, Rolle

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `taylor_mean_remainder_lagrange_iteratedDeriv` | `obtain ⟨ξ, -, hξ⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn` | `x₀ ≠ x → ContDiffOn ℝ (n+1) f (uIcc x₀ x) → ∃ ξ ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = iteratedDeriv (n+1) f ξ * (x - x₀)^(n+1) / (n+1)!`; pick `n`, `x₀`, `x` by named arguments | M111, H065, H066 |
| `taylorWithinEval_succ`, `taylor_within_zero_eval` | `rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval, d1, d2] at hξ` | unfold the Taylor polynomial one degree at a time; degree 0 is `f x₀`; on ℝ, `•` is `*` | M111, H065, H066 |
| `iteratedDerivWithin_eq_iteratedDeriv`, `iteratedDeriv_one` | `rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc, iteratedDeriv_one]` | `UniqueDiffOn ℝ s → ContDiffAt ℝ n f x → x ∈ s →` (within `s`) `= iteratedDeriv n f x`; degree 1 is `deriv f` | H065, H066 |
| `iteratedDerivWithin_one`, `DifferentiableAt.derivWithin` | `(hf.differentiable (by norm_num) x).derivWithin (uniqueDiffOn_Icc (by linarith) x ⟨le_rfl, by linarith⟩)` | the M111 route: `derivWithin f s x = deriv f x` when `f` is differentiable at `x` | M111 |
| `UniqueDiffOn` of an interval | `by rw [Set.uIcc_of_le h.le]; exact uniqueDiffOn_Icc h` | `uniqueDiffOn_Icc : a < b → UniqueDiffOn ℝ (Icc a b)`; `Set.uIcc_of_le`/`Set.uIcc_of_ge` orient `uIcc`; `Set.left_mem_uIcc : a ∈ uIcc a b` | M111, H065, H066 |
| two-sided expansion | `obtain ⟨ξ₂, h2⟩ := taylor2 f hf x (-h) (by linarith)` then `rw [← sub_eq_add_neg] at h2` | expand at `x ± h`; the central differences cancel the even (resp. odd) terms | H066 |
| `exists_hasDerivAt_eq_slope` | `exists_hasDerivAt_eq_slope y y' (show t < t + h by linarith) hcont.continuousOn (fun s _ => hy s)` | MVT: `∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a)` | H072 |
| `exists_hasDerivAt_eq_zero` | `exists_hasDerivAt_eq_zero hax cφ.continuousOn (φa.trans φx.symm) fun t _ => hφ t` | Rolle: `a < b`, `f a = f b` gives `∃ c ∈ Ioo a b, f' c = 0`; apply it three times to an auxiliary `φ` | H067 |
| `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` | `… (fun t _ => (Real.hasDerivAt_cos t).hasDerivWithinAt) hd (convex_Icc 0 1) hy hx` | MVT as a bound: `‖f'‖ ≤ C` on convex `s` gives `‖f y - f x‖ ≤ C * ‖y - x‖` | M108 |
| `intermediate_value_Icc'` | `intermediate_value_Icc' (by norm_num) (by fun_prop) ⟨_, _⟩` | `a ≤ b → ContinuousOn f (Icc a b) → Icc (f b) (f a) ⊆ f '' Icc a b` (IVT for a sign change from `+` to `-`) | M108 |
| trig facts | `Real.sin_lt one_pos : sin 1 < 1` | `Real.sin_le_sin_of_le_of_le_pi_div_two`, `Real.sin_nonneg_of_nonneg_of_le_pi`, `Real.cos_nonneg_of_mem_Icc`, `Real.cos_le_one`, `Real.pi_gt_three`, `Real.pi_pos` | M108 |

### Interval integrals and quadrature

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `integral_pow`, `integral_id` | `rw [integral_pow]; norm_num` | `∫ x in a..b, x^n = (b^(n+1) - a^(n+1))/(n+1)`; `∫ x = (b² - a²)/2` | E106, M113, M125 |
| `norm_num [integral_pow]` | `norm_num [integral_pow] at h0 h1 h2 h3` | evaluate moments `∫ x^k` with numeral bounds, in hypotheses too | M125 |
| `intervalIntegral.integral_add` | `rw [intervalIntegral.integral_add (hf.const_mul 2) intervalIntegrable_const]` | splits `∫ (f + g)` and needs both summands `IntervalIntegrable` | E106, M113 |
| `intervalIntegral.integral_const_mul`, `integral_const`, `integral_neg` | `rw [intervalIntegral.integral_const, smul_eq_mul]` | `∫ c * f = c * ∫ f`; `∫ c = (b - a) • c`; `∫ -f = -∫ f` | E106, M113, H068 |
| integrability side goals | `Continuous.intervalIntegrable (by fun_prop) a b`, `intervalIntegrable_const`, `hf.const_mul 2` | continuous gives integrable; `fun_prop` proves the `Continuous`, not `IntervalIntegrable` directly | E106, M113, M117 |
| `intervalIntegral.integral_finsetSum` | `rw [intervalIntegral.integral_finsetSum fun i _ => …]` | swap `∫` with a finite sum given integrability of each term | M115 |
| `intervalIntegral.sum_integral_adjacent_intervals` | `… (μ := MeasureTheory.volume) (f := f) (a := fun k : ℕ => a + k * h) (n := n) (fun k _ => hf.intervalIntegrable _ _)` | `∑ k < n, ∫ over [a k, a (k+1)] = ∫ over [a 0, a n]`: split a composite rule into panels | M116 |
| `intervalIntegral.integral_mul_deriv_eq_deriv_mul` | `intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int hv'int` | integration by parts: `∫ u v' = u b v b - u a v a - ∫ u' v`, with `HasDerivAt` on `uIcc a b` and integrable `u'`, `v'` | M117, H068 |
| `intervalIntegral.integral_eq_sub_of_hasDerivAt` | `rw [integral_eq_sub_of_hasDerivAt hF hint]` | FTC: `∫ x in a..b, f' x = f b - f a` | H068 |
| `intervalIntegral.abs_integral_le_integral_abs`, `intervalIntegral.integral_mono_on` | `abs_integral_le_integral_abs hab` | `a ≤ b → \|∫ f\| ≤ ∫ \|f\|`; pointwise `f ≤ g` on `Icc a b` gives `∫ f ≤ ∫ g` | H068 |
| Peano kernel | `(∫ t in a..b, f t) - (b - a) / 2 * (f a + f b) = -∫ t in a..b, (t - a) * (b - t) / 2 * f'' t` | trapezoid error identity from two integrations by parts, then a bound by `M ∫ w = M (b-a)³/12` | H068 |
| exactness of rules | `∑ i ∈ s, (∫ x in a..b, (Lagrange.basis s v i).eval x) * p.eval (v i)` | interpolatory rule with weights `wᵢ = ∫ Lᵢ`; Simpson `(b-a)/6 (f a + 4 f m + f b)` and Gauss rules: compute `∫` of each monomial, then `ring` / `linear_combination` | E106, M113, M115, M125 |

### Fixed points, iteration, contraction

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `LipschitzWith.of_dist_le_mul` | `refine LipschitzWith.of_dist_le_mul fun x y => ?_` | reduce `LipschitzWith K f` to `dist (f x) (f y) ≤ ↑K * dist x y` | E107 |
| `Real.dist_eq`, `NNReal.coe_div`, `NNReal.coe_one`, `NNReal.coe_ofNat` | `simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]` | `dist x y = \|x - y\|`; move the `ℝ≥0` constant to `ℝ` | E107, M120 |
| `Function.iterate_succ_apply'` | `rw [Function.iterate_succ_apply']` | `f^[n.succ] x = f (f^[n] x)`: peel the last step | M107, H065, H071, H075 |
| a priori bound | `\|f^[n] x₀ - p\| ≤ K ^ n * \|x₀ - p\|` by induction + `gcongr` | rewrite `p` as `f p` (`by rw [hp]`), then apply Lipschitz | M107, H071 |
| a posteriori bound | `rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith` | `\|xₙ₊₁ - p\| ≤ K/(1-K) \|xₙ₊₁ - xₙ\|`, which uses only computable quantities | M107 |
| fixed point as a rewrite target | `conv_lhs => rw [← jacobi_fixed A b xs hdiag hsol]` | rewrite `x*` into `step x*` on one side so the contraction applies | H071 |
| uniqueness from contraction | `nlinarith [abs_nonneg (q - p), sin_one_lt_one]` then `abs_nonpos_iff.mp` | `\|q - p\| ≤ s\|q - p\|` with `s < 1` forces `q = p` | M108 |

### Limits and convergence

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `tendsto_iff_norm_sub_tendsto_zero` + `squeeze_zero` | `rw [tendsto_iff_norm_sub_tendsto_zero]; refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0` | `u → L` iff `‖u n - L‖ → 0`; squeeze between `0` and a bound going to `0` | M107, H071, H073 |
| `squeeze_zero'` | `refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h` | the same with eventual bounds (`∀ᶠ`) | H073 |
| `tendsto_pow_atTop_nhds_zero_of_lt_one` + `.mul_const` | `simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK).mul_const c` | `0 ≤ r < 1 → rⁿ → 0`; `simpa` cleans `0 * c` | M107, M123, H062, H071 |
| limit algebra | `h.add g`, `h.const_mul c`, `h.mul_const c`, `hf.div hg hb`, `h.congr fun n => …`, `tendsto_const_nhds` | combine limits; `.congr` swaps in a pointwise-equal sequence | H062, H063, M123 |
| `tendsto_const_div_atTop_nhds_zero_nat` | `tendsto_const_div_atTop_nhds_zero_nat (x ^ 2 * Real.exp \|x\|)` | `C / n → 0` | H073 |
| `filter_upwards`, `eventually_ge_atTop`, `exists_nat_ge` | `filter_upwards [eventually_ge_atTop (max N 1)] with n hn` | prove `∀ᶠ n in atTop, P n` from `N ≤ n` | H073 |
| monotone convergence | `tendsto_atTop_ciSup hmono hbdd`, `tendsto_atTop_ciInf anti bdd` | a monotone (antitone), bounded sequence tends to its `⨆` (`⨅`) | H062, H064 |
| `monotone_nat_of_le_succ`, `antitone_nat_of_succ_le` | `antitone_nat_of_succ_le fun n => babylon_le …` | monotonicity from a one-step comparison | H062, H064 |
| `le_ciSup`, `ciSup_le`, `le_ciInf`, `BddAbove` | `⟨b, by rintro _ ⟨n, rfl⟩; exact h n⟩ : BddAbove (Set.range lo)` | compare terms with the sup/inf (`le_ciSup` needs `BddAbove`) | H062, H064 |
| `le_of_tendsto'`, `ge_of_tendsto'` | `le_of_tendsto' ((hf.tendsto r).comp tlo) fun n => …` | pass `∀ n, u n ≤ b` to the limit (sign of `f` at the root) | H062 |
| continuity and limits | `(hf.tendsto r).comp h`, `hc.tendsto.comp tg` | `u → r` gives `f ∘ u → f r` | H062, H064 |
| `Real.norm_eq_abs` | `rw [Real.norm_eq_abs]` | `‖r‖ = \|r\|` on ℝ (norms appear in limits, MVT and Gershgorin radii); `norm_neg` | M107, M108, M120, H071 |
| `fun_prop (disch := …)` | `unfold babylon; fun_prop (disch := exact hL0.ne')` | `ContinuousAt` with a side goal like `L ≠ 0`; unfold user defs first | H064 |
| `tendsto_nhds_unique` | `tendsto_nhds_unique tb tg1 : babylon a L = L` | two limits of one sequence agree: identify the limit as a fixed point | H064 |
| index shift | `rw [← tendsto_add_atTop_iff_nat 1]`, `tg.comp (tendsto_add_atTop_nat 1)` | `(fun n => u (n + k)) → l ↔ u → l` | H063, H064 |
| blow-up | `(tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const (abs_pos.mpr hy)` | `1 < r → rⁿ → ∞`; times a positive constant still goes to `∞` | M118, H075 |

### Exp, sqrt, powers

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Real.exp_bound` | `Real.exp_bound (x := 1 / 2) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)` | `\|x\| ≤ 1 → 0 < n → \|exp x - ∑ m ∈ range n, x^m/m!\| ≤ \|x\|^n * (n.succ / (n! * n))` | M112 |
| expand small sums | `norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢` | unroll `∑ m ∈ range 3` and `3!` into numerals | M112 |
| `Real.add_one_le_exp`, `Real.exp_nat_mul` | `calc (1 + a) ^ n ≤ Real.exp a ^ n := by gcongr; linarith [Real.add_one_le_exp a]` | `x + 1 ≤ eˣ`; `exp (n * x) = exp x ^ n` | M118, M119, H072, H073 |
| `Real.abs_exp_sub_one_sub_id_le`, `Real.abs_exp`, `Real.exp_le_exp` | `Real.abs_exp_sub_one_sub_id_le hxn` | `\|x\| ≤ 1 → \|eˣ - 1 - x\| ≤ x²`; `\|eˣ\| = eˣ`; `exp` is monotone | H073 |
| `abs_pow_sub_pow_le` | `abs_pow_sub_pow_le a b n` | `\|aⁿ - bⁿ\| ≤ \|a - b\| * n * max \|a\| \|b\| ^ (n-1)` (telescoping) | H073 |
| sqrt facts | `Real.sq_sqrt ha`, `Real.sqrt_nonneg a`, `Real.sqrt_sq ha`, `Real.mul_self_sqrt ha`, `Real.sqrt_pos`, `Real.sqrt_eq_zero'` | `√a² = a`, `0 ≤ √a`, `√(a²) = a`, `√a * √a = a` (each needs `0 ≤ a`); `0 < √x ↔ 0 < x`; `√a = 0 ↔ a ≤ 0` | M109, M124, M125, H063, H064 |
| power bounds | `one_lt_pow₀ (by norm_num) (by omega)`, `pow_le_one₀`, `pow_le_pow_left₀`, `inv_le_one_of_one_le₀`, `inv_lt_one_of_one_lt₀` | `1 < a → n ≠ 0 → 1 < aⁿ`; `0 ≤ a ≤ 1 → aⁿ ≤ 1`; `0 ≤ a ≤ b → aⁿ ≤ bⁿ`; `1 ≤ a → a⁻¹ ≤ 1` | M110, M123, H073 |
| `div_pow`, `pow_succ` + `div_div`, `pow_mul` | `rw [pow_succ, div_div]` | `(a/b)ⁿ = aⁿ/bⁿ`; `w / 2ⁿ / 2 = w / 2ⁿ⁺¹`; `a^(m*n) = (a^m)^n` (squaring errors) | M106, M110, H065 |

### Recurrences, ODE and PDE schemes, stability

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| closed form by induction | `induction n with \| zero => simp [euler] \| succ n ih => rw [euler, ih, pow_succ]; ring` | `yₙ = (1 + hλ)ⁿ y₀` for forward Euler; `(1 - hλ)⁻¹ⁿ y₀` for backward Euler (`field_simp` instead of `ring`) | M118, M123, H073 |
| amplification factor | `rw [euler_closed_form, abs_mul, abs_pow]` then `\|1 + h * lam\| ≤ 1` via `abs_le` + `nlinarith` | stability is `\|R(hλ)\| ≤ 1`; `\|R\| > 1` with `y₀ ≠ 0` blows up | M118, M123, H075 |
| implicit step check | `simp only [beuler]; field_simp; ring` | the solved formula satisfies `yₙ₊₁ = yₙ + hλyₙ₊₁` | M123 |
| discrete Gronwall | `have key : ∀ n, e n ≤ (1 + a) ^ n * (e 0 + n * b) := by intro n; induction n with …` | `eₙ₊₁ ≤ (1+a)eₙ + b ⇒ eₙ ≤ e^{na}(e₀ + nb)`; induct on the `(1+a)ⁿ` form, add `exp` at the end | M119, H072 |
| local + propagated error | `\|y (t + h) - y t - h * y' t\| ≤ M * h ^ 2` | Euler's error recursion: local error `≤ Mh²` by the MVT, then the old error is amplified by `1 + hL` (Lipschitz `F`) | H072 |
| `0 ≤ M` from a Lipschitz hypothesis | `have h1 : (0 : ℝ) ≤ M * \|1 - 0\| := (abs_nonneg _).trans (hlip 1 0)` | the constant's sign is not assumed; get it at two distinct points | H065, H072 |
| exact error multiplication | `linear_combination (-(n + 1 : ℝ)) * ih` | `Jₙ - Iₙ = (-1)ⁿ n! (J₀ - I₀)`: start errors grow like `n!` (forward-unstable recurrence) | M117 |
| energy identities | `simp only [eulerHO]; linear_combination (1 + h ^ 2 * ω ^ 2) * ih` | explicit Euler scales `p² + ω²q²` by `1 + h²ω²` each step; symplectic Euler keeps `p² + ω²q² - hω²qp` | M122 |
| grid functions `ℤ → ℝ` | `induction n generalizing j with \| zero => exact hu j \| succ n ih => …` | an IH for every grid point `j`; `abs_add_three` for the 3-point stencil | H075 |
| checkerboard mode | `rw [zpow_sub_one₀ (by norm_num), zpow_add_one₀ (by norm_num), pow_succ]` | `(-1)ʲ ε` is an eigenvector of the heat step with factor `1 - 4r` | H075 |
| Lax: stability + consistency | `have hb := step_bound r hr0 hr _ (n * τ) ih j` | global error `≤ n τ`, from `step_bound` applied to the old error | H075 |

### Matrices and numerical linear algebra

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| unfold `*ᵥ` | `simp only [mulVec, dotProduct, Pi.zero_apply] at this` | `(A *ᵥ v) i = ∑ j, A i j * v j` holds by `rfl`; `congrFun h i` takes one row of `A *ᵥ v = 0` | H070, H071 |
| `Finset.add_sum_erase`, `Finset.sum_erase_eq_sub` | `rw [← add_sum_erase _ _ (mem_univ i)] at this` | split off the diagonal term `A i i * v i` | M120, H070, H071 |
| `Fin.sum_univ_succ`, `fin_cases` | `fin_cases k <;> simp [A, Finset.sum_erase_eq_sub, Fin.sum_univ_succ] at hk` | evaluate sums and entries of a concrete matrix, one goal per row | M120 |
| `eigenvalue_mem_ball`, `Metric.mem_closedBall` | `obtain ⟨k, hk⟩ := eigenvalue_mem_ball hμ` | Gershgorin: `μ ∈ closedBall (A k k) (∑ j ∈ univ.erase k, ‖A k j‖)` for some `k`; `y ∈ closedBall x r ↔ dist y x ≤ r` | M120 |
| `Matrix.exists_mulVec_eq_zero_iff` | `Matrix.exists_mulVec_eq_zero_iff.mpr hdet` | `(∃ v, v ≠ 0 ∧ M *ᵥ v = 0) ↔ M.det = 0` | H070 |
| `Finset.exists_max_image` | `exists_max_image univ (fun j => \|v j\|) hne` | index of the largest coordinate (needs `univ.Nonempty`) | H070 |
| `Matrix.linfty_opNorm_mulVec` | `hx ▸ Matrix.linfty_opNorm_mulVec _ _` | `‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖` in the ∞-norm (`open scoped Matrix.Norms.Operator`) | M121 |
| `*ᵥ` algebra | `rw [← hx, ← hx', ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]` | `mulVec_add`, `mulVec_sub`, `mulVec_smul`, `mulVec_mulVec` (`M *ᵥ N *ᵥ v = (M * N) *ᵥ v`), `one_mulVec`, `mulVec_zero` | M121, H063, H074 |
| sup-norm coordinates | `rw [pi_norm_le_iff_of_nonneg (by positivity)]` | `0 ≤ r → (‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r)`; `norm_le_pi_norm x i : ‖x i‖ ≤ ‖x‖` | H071 |
| `norm_pos_iff` | `norm_pos_iff.mpr hb : 0 < ‖b‖` | `0 < ‖a‖ ↔ a ≠ 0` | M121 |
| dot-product linearity | `simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]` | distribute `⬝ᵥ` over `+` and `•`; `smul_smul`, `Pi.smul_apply` for scalars | H063, H070, H074 |
| move `A` across `⬝ᵥ` | `rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]` | `v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w`, `Aᵀ *ᵥ x = x ᵥ* A`, `dotProduct_comm`; symmetric `A` gives `u ⬝ A v = A u ⬝ v` | H063, H074 |
| `dotProduct_self_eq_zero`, `dotProduct_self_star_nonneg` | `simpa using dotProduct_self_star_nonneg v` | `v ⬝ᵥ v = 0 ↔ v = 0`; `0 ≤ v ⬝ᵥ v` (`star v = v` on ℝ); `‖v‖²` is written `v ⬝ᵥ v` | H074 |
| `Function.Injective A.mulVec` | `exact (hA h1).symm` | independent columns: `A *ᵥ v = A *ᵥ w → v = w` | H074 |
| `abel` | `show A *ᵥ x + A *ᵥ d - b = (A *ᵥ x - b) + A *ᵥ d by abel` | rearrange in an additive group (vectors), where `ring` does not apply | H074 |
| normalization | `Real.mul_self_sqrt h.le`, `Real.sqrt_eq_zero'.mpr h`, `mul_self_pos.mpr` | `(√(y⬝y))⁻¹ • y` is a unit vector or `0` | H063 |

### Inequality toolkit (used throughout)

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| absolute values | `rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]` | `abs_mul`, `abs_div`, `abs_inv`, `abs_pow`, `abs_neg`, `abs_two`, `abs_of_pos`, `abs_of_nonneg`, `abs_of_neg` | M103, M110, M123, M124 |
| triangle inequalities | `abs_add_le a b`, `abs_sub a b`, `abs_sub_le a b c`, `abs_add_three a b c`, `abs_sub_comm` | `\|a+b\| ≤ \|a\|+\|b\|`; `\|a-b\| ≤ \|a\|+\|b\|`; `\|a-c\| ≤ \|a-b\|+\|b-c\|`; three terms | M104, M107, M110, H075 |
| `abs_le`, `abs_pos`, `abs_nonpos_iff` | `constructor <;> linarith [abs_le.mp hk]` | `\|a\| ≤ b ↔ -b ≤ a ∧ a ≤ b`; `0 < \|a\| ↔ a ≠ 0`; `\|a\| ≤ 0 ↔ a = 0` | M112, M118, M120, H070 |
| clear a positive denominator | `div_le_iff₀ hc`, `le_div_iff₀ hc`, `div_lt_iff₀ hc`, `div_le_one hc` | `0 < c → (b / c ≤ a ↔ b ≤ a * c)` and its variants | M103, M107, M109, M121 |
| cancellations | `div_mul_cancel₀ _ hb`, `mul_div_cancel₀ _ hb`, `mul_div_cancel_left₀`, `div_mul_eq_mul_div` | `a / b * b = a`, `b * (a / b) = a`; more predictable than `field_simp` | H067, H072, M107, M122 |
| scale inequalities | `mul_le_mul_of_nonneg_left h (abs_nonneg _)`, `mul_lt_mul_of_pos_right`, `le_of_mul_le_mul_right h hpos` | multiply both sides by a nonnegative/positive factor, or cancel one | H070, M119 |
| sums | `Finset.abs_sum_le_sum_abs`, `Finset.sum_sub_distrib`, `Finset.sum_mul`, `gcongr with k` | triangle inequality for sums; split sums; bound a sum term by term; `∑ _k ∈ range n, c = n * c` by `simp` | M116, H070, H071 |

### Tactic idioms in this area

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `linear_combination` | `linear_combination (3 / 2 : ℝ) * (h3 - (x₁ + x₂) * h2 + (x₁ * x₂) * h1)` | closes `lhs = rhs` when `lhs - rhs - Σ eᵢ(hᵢ.lhs - hᵢ.rhs)` is `0` by `ring`; coefficients may be expressions | M111, M117, M122, M124, M125 |
| `field_simp` then `ring` / `linear_combination` | `field_simp; linear_combination 2 * hξ` | clear denominators that are `≠ 0` (facts in context), then finish | M109, M110, M123, M124 |
| `nlinarith [hints]` | `nlinarith [mul_nonneg hc (sq_nonneg (ω * q - p))]` | linear arithmetic plus products of hypotheses and hints | M105, M109, M122 |
| `gcongr` | `calc _ ≤ 2 ^ p * (K * (h ^ q / 2 ^ q)) + K * h ^ q := by gcongr` | monotone congruence; may leave side goals like `0 ≤ …` | M104, M110, M118 |
| `set … with` | `set u := D (h / 2) - (A + c * (h / 2) ^ p) with hu` | name a subterm everywhere (`hu : u = …`); `set φ := fun t => …` then `simp only [φ]` | M110, M122, H067 |
| `generalize` | `generalize √(b ^ 2 - 4 * a * c) = s at hs hsn ⊢` | replace a term by a fresh variable in the goal and the named hypotheses | M124 |
| `conv_lhs => rw [h]` | `conv_lhs => rw [Lagrange.eq_interpolate hv hp]` | rewrite only the left side | M115, H071 |
| `split_ifs with h` | `simp only [bisect, step]; split_ifs with hm` | one goal per `if` branch; then `simp only` reduces `(x, y).1` | M106 |
| strengthen before induction | `have inv : ∀ n, lo ≤ hi ∧ a ≤ lo ∧ hi ≤ b := by intro n; induction n with …` | when the statement mentions `n + 1` it is not its own IH | M106, M119 |
| `let` in a goal | `intro x₁; simp only [x₁]` | enter and unfold a `let`; `simp only [f]` also unfolds a recursive def one step, `let` included | M122, M124 |
| specialise a bounded `∀` | `have h2 := hexact 2 (by norm_num)` | `h : ∀ k ≤ 3, P k` gives `P 2` | M125 |
| `simp_rw` | `simp_rw [euler_closed_form, abs_mul, abs_pow]` | rewrite under binders (inside `fun n => …`) | M118, H075 |
| casts of step indices | `example (n : ℕ) (b : ℝ) : ((n + 1 : ℕ) : ℝ) * b = n * b + b := by push_cast; ring` | `push_cast` / `Nat.cast_succ` tidy `t₀ + ↑(k+1) * h` and partition points `a + ↑k * h`; `exact_mod_cast` gives `(0 : ℝ) < n` from `0 < n` | M116, M119, H072, H073 |

### Gotchas

- `deriv f x` is `0` when `f` is not differentiable at `x`, and `√a = 0` for `a < 0`. Facts about them need differentiability or `0 ≤ a`. (E105, M109)
- `⌊·⌋` rounds toward -∞ (`⌊-2.5⌋ = -3`). Mathlib's `round` sends ties up (`round 0.5 = 1`); IEEE rounds half to even. Decimals like `3.7` are exact rationals to `norm_num`. (E108)
- Derivative rules give unsimplified expressions such as `↑3 * a ^ (3 - 1) + 2 * 1`. Fix the shape with `.congr_deriv (by ring)` or `(by norm_num)`. (E105, H067)
- `simp` cannot integrate `m * x`. `simp only [intervalIntegral.integral_const_mul]` leaves `∫ c₁ * x` alone because the bare `x` does not match `c * f x`, so use `rw`. `c₀ + c₁x + c₂x² + c₃x³` is left-associated, so split the last `+` first. (E106, M113)
- `fun_prop` proves `Continuous`, not `IntervalIntegrable`. Wrap it as `Continuous.intervalIntegrable (by fun_prop) a b`. (E106)
- A plain `rw [Lagrange.eq_interpolate hv hp]` also rewrites the `p` inside `p.eval (v i)` on the right. Use `conv_lhs`. (M115)
- ORDER in Taylor proofs: first rewrite every coefficient `iteratedDerivWithin k f (uIcc ..) x` to `iteratedDeriv k f x` (k = 1: `deriv f x`), then run `norm_num [Nat.factorial] at hξ`. If `norm_num` runs first, it turns k = 1 into `derivWithin`. If you skip the rewrite, the `x + h` and `x - h` expansions do not cancel. (H065, H066)
- Taylor's `hξ` shows `↑(1 + 1).factorial`. `m !` notation needs `open Nat`; otherwise write `m.factorial`. (M112, H065)
- `field_simp` also rewrites inside `√(…)`, so `generalize` the root away first. (M124)
- On `|a| * |x| ≤ |a| * |y|`, `gcongr` descends into `|·|` and asks for `0 ≤ x`. Use `mul_le_mul_of_nonneg_left h (abs_nonneg _)` instead. `gcongr` can also leave nonnegativity side goals; close them by hand, for example `le_trans (abs_nonneg _) hθ`. (H070, M104)
- `Fin 0` is empty, so `univ` may be empty. Get nonemptiness from `v ≠ 0` before you take a maximum. (H070)
- `n - 1 : ℕ` truncates. Cast with `Nat.cast_sub (by omega)`. (H073)
- `Polynomial.Chebyshev.T` is indexed by `ℤ`, so `T ℝ n` with `n : ℕ` carries a cast; `push_cast` tidies it. `(-1 : ℝ) ^ j` with `j : ℤ` is a zpow, so use `zpow_add_one₀` and `zpow_sub_one₀`. (M125, H075)
- Version-specific names: at this Mathlib, `abs_sub : |a - b| ≤ |a| + |b|`, and `Polynomial.eval_finsetSum` replaces the deprecated `eval_finset_sum`. (M110, M124, M115)
- `positivity` cannot use `a ≠ 0` hypotheses on compound terms. Use `mul_self_pos.mpr` or `pow_ne_zero`. (H063)
- `refine` needs `?_` for proof holes, not `_`. (M106)
- The M104 product model rounds the last factor `xₙ * 1` too, so it makes `n` roundings where hardware makes `n - 1`. (M104)
- Banned names, so the exercise is not a one-liner:
  - M107: `ContractingWith` and Mathlib's `apriori_`/`aposteriori_dist_iterate_fixedPoint_le`, `tendsto_iterate_fixedPoint`.
  - M112: the `exp_one_*_d9`, `exp_one_near_*` and `exp_half` shortcuts.
  - M114: `eq_interpolate*`, `funEquivDegreeLT` and the `eq_of_degree*` family.
  - H068: `trapezoidal_error_le*` and the related `trapezoidal_*` defs.
  - H070: `det_ne_zero_of_sum_row_lt_diag`, `eigenvalue_mem_ball`, `exact?`.
  - H073: the `tendsto_one_add_div_pow_exp` family.
  - M106, M109, M122, M123: `grind` / `try?`, because `grind [def]` closes the algebra.
  - M118: `try?`, because it closes the closed form.

## Quantum computing and information (Mathlib matrices + QuantumInfo)

Two layers. **Mathlib** gives raw linear algebra: a gate is `Matrix n n ℂ`, a state vector is `n → ℂ`,
a multi-qubit index is a product type (`Fin 2 × Fin 2`). **QuantumInfo** (physlib's quantum library)
bundles these into types that carry their invariants: `Ket d` (unit vector), `MState d` (density matrix),
`𝐔[d]` (unitary), `POVM`, `CPTPMap`, `Sᵥₙ`, `TrDistance`. Each QuantumInfo object has a projection to the raw
Mathlib object (`ψ.vec`, `ρ.m`, `U.val`); most proofs go: unwrap, compute entrywise, rewrap.
Conventions: `d` is a finite index type (`[Fintype d] [DecidableEq d]`), `n = Fintype.card d`.

### Imports and scopes

| Import / open | Gives | IDs |
|---|---|---|
| `import Mathlib` | matrices, Kronecker, `unitaryGroup`, `NormedSpace.exp`, roots of unity | E109, E110, M126, H083 |
| `import QuantumInfo.States.Pure.Braket` | `Ket`, `Bra`, `〈ξ‖ψ〉`, `⊗ᵠ`, `Ket.MES`, `IsProd`/`IsEntangled` | E112, M131, M137, M143, H080 |
| `import QuantumInfo.States.Mixed.MState` | `MState`, `pure`, `traceLeft`/`traceRight`, `uniform`, `purity` | E113, M134, M136, M138, H076, H078 |
| `import QuantumInfo.Operators.Unitary` | `𝐔[d]` notation (= `Matrix.unitaryGroup d ℂ`) | M133, M147, H079 |
| `QuantumInfo.Measurements.POVM` / `.Channels.CPTP` / `.States.Mixed.TraceDistance` | `POVM`, `CPTPMap`, `TrDistance` | M135, M146, M147, H082 |
| `QuantumInfo.Entropy.VonNeumann` + `QuantumInfo.States.Entanglement` | `Sᵥₙ`, `qMutualInfo` | M139 |
| `QuantumInfo.ForMathlib.Matrix` | `Matrix.traceLeft` / `traceRight` on raw matrices | M145 |
| `open Matrix Complex` | write `mulVec`, `I`, `exp` unqualified | E109, M126, H084 |
| `open scoped Kronecker` | the `⊗ₖ` notation | E111, E114, M129 |
| `open Braket` | the `〈ξ‖ψ〉` notation (copy the brackets from the spec) | E112, H079, H080 |
| `open ComplexConjugate` | `conj` for `starRingEnd ℂ` | E113 |
| `open scoped ComplexOrder` | partial order `≤` on ℂ (needed to state `PosSemidef`, `0 ≤ det`) | M135, M136, M144, M149 |

### Notation decoder

| Lean | Math | IDs |
|---|---|---|
| `!![a, b; c, d]` | 2×2 matrix literal, rows split by `;` | E109, M126 |
| `Matrix.of fun p q => …` | matrix from an entry function | E114, M130, H084 |
| `M *ᵥ v` / `v ᵥ* M` | matrix·column vector / row vector·matrix | E114, M128, M133 |
| `x ⬝ᵥ y` | `∑ i, x i * y i` (no conjugation) | M133, M149 |
| `star v ⬝ᵥ w` | ⟨v, w⟩ = `∑ i, conj (v i) * w i` (physics inner product) | M128, M133, H077 |
| `star v ⬝ᵥ (M *ᵥ v)` | ⟨v\|M\|v⟩, expectation value | M143, H077, H081 |
| `Mᴴ` (`\^H`), `star M` | conjugate transpose M†; `Mᴴ i j = conj (M j i)` | E110, M145 |
| `starRingEnd ℂ z`, `conj z`, `star z` | complex conjugate (all the same on ℂ) | E113, M127, H084 |
| `A ⊗ₖ B` (`\otimes\_k`) | Kronecker product `kroneckerMap (· * ·) A B`, indexed by pairs | E111, E114 |
| `ψ ⊗ᵠ φ` | `Ket.prod ψ φ`, tensor product of kets | M137, H079 |
| `〈ξ‖ψ〉` | `Braket.dot ↑ξ ψ` = `∑ x, conj (ξ x) * ψ x` | E112, H079 |
| `𝐔[d]` | `Matrix.unitaryGroup d ℂ` (a submonoid; `U.val` the matrix) | M133, H079 |
| `cexp` | `Complex.exp` | M127, H088 |
| `Complex.normSq z` | \|z\|² as a real (Born probability) | E113, M130 |
| `ρ.m`, `ρ.M`, `A.mat` | raw `Matrix d d ℂ` / `HermitianMat d ℂ` / unwrap a `HermitianMat` | E113, M135, M138 |
| `Sᵥₙ ρ`, `Hₛ p` | von Neumann entropy −tr ρ log ρ / Shannon entropy | M139 |
| `Prob` | `{p : ℝ // 0 ≤ p ∧ p ≤ 1}`; `(p : ℝ)` the number | H078 |

### 2×2 gates: literals and entrywise proofs

| API | Example | Gloss | IDs |
|---|---|---|---|
| `simp [defs]` on literals | `theorem X_sq : X * X = 1 := by simp [X, Matrix.one_fin_two]` | simp multiplies, negates, scales `!![..]` | E109, M129 |
| `Matrix.one_fin_two` | `(1 : Matrix (Fin 2) (Fin 2) α) = !![1, 0; 0, 1]` | simp never turns `1` into a literal itself | E109, M127 |
| `Matrix.mul_fin_two` | `simp only [Rz, Matrix.mul_fin_two, ← Complex.exp_add]` | product of two literals | E109, M127, H087 |
| `c • M` | `example : (2 : ℂ) • !![1, 0; 0, (1 : ℂ)] = !![2, 0; 0, 2] := by simp` | scalar multiple, entrywise | E109, M126 |
| `Complex.I_mul_I` | `I * I = -1` (simp uses it unprompted) | `I` is `Complex.I` | E109 |
| entrywise | `ext i j; fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]` | the default for anything with `ᴴ`, `√2`, `exp` | E110, M126, M127 |
| `Matrix.mul_apply`, `Fin.sum_univ_two` | `(M * N) i k = ∑ j, M i j * N j k`; `∑ i : Fin 2, f i = f 0 + f 1` | open a product into a sum, then into two terms | E110, M126 |
| `Matrix.eta_fin_two` | `rw [Matrix.eta_fin_two U]` | `A = !![A 0 0, A 0 1; A 1 0, A 1 1]` | H087 |
| `Matrix.smul_of` | `r • Matrix.of f = Matrix.of (r • f)` | push a scalar into a literal | H087 |
| `Matrix.det_fin_two`, `Matrix.trace_fin_two` | `rw [Matrix.det_fin_two, h10, Complex.nonneg_iff] at hdet` | `det = a d − b c`, `tr = a + d` | M131, M136, H076 |
| `Matrix.diagonal`, `diagonal_apply`, `diagonal_mul` | `def P (i : Fin 2) := Matrix.diagonal (Pi.single i 1)` | projector \|i⟩⟨i\| | M135, M146 |
| read off entries | `have e := congrFun (congrFun h 1) 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at e` | entry (1,0) of a matrix equation `h` | H087 |
| `ring_nf <;> rw [h] <;> ring` | `… <;> simp [H, …] <;> ring_nf <;> rw [h] <;> ring` | after simp, normalise and plug `(√2⁻¹)^2 = 1/2` | M126 |

### Adjoints, Hermitian and unitary matrices

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Matrix.mem_unitaryGroup_iff` / `'` | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` | `A ∈ unitaryGroup ↔ A * star A = 1` (`'`: `star A * A = 1`) | E110, M126, M127, H084 |
| `Matrix.star_eq_conjTranspose` | `rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hU` | `star M = Mᴴ` | E110 |
| `Submonoid.mul_mem` | `Submonoid.mul_mem _ X_unitary Z_unitary` | unitaries closed under product | E110 |
| `Matrix.UnitaryGroup.star_mul_self` | `star U.val * U.val = 1` for `U : 𝐔[d]` | unitarity of a bundled `U` | M133, H079 |
| `Matrix.conjTranspose_apply` | `simp [H, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.conj_ofReal]` | entry of `Mᴴ` | M126, M131 |
| `Matrix.conjTranspose_mul` / `_smul` / `_one` / `_kronecker` | `rw [conjTranspose_smul, hH.eq, ← neg_smul]` | `(MN)ᴴ = NᴴMᴴ`, `(c•M)ᴴ = star c • Mᴴ`, `(A⊗B)ᴴ = Aᴴ⊗Bᴴ` | M131, H081, H088 |
| `Matrix.IsHermitian.eq` | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hH.eq] at hU` | `hA : A.IsHermitian` gives `Aᴴ = A` | M128, H077 |
| `Matrix.IsHermitian.apply` | `(ρ.Hermitian.apply 1 0).symm : ρ.m 1 0 = star (ρ.m 0 1)` | `star (A j i) = A i j` | M136, H076 |
| real diagonal | `have := congrArg Complex.im (ρ.Hermitian.apply 0 0); simp at this; linarith` | `(ρ.m 0 0).im = 0` | M136, H076 |
| `Matrix.det_of_mem_unitary` + `CStarRing.norm_of_mem_unitary` | `CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU) : ‖U.det‖ = 1` | \|det U\| = 1 | H087 |
| `Matrix.kronecker_mem_unitary` | `Matrix.kronecker_mem_unitary hU (one_mem _)` | `U ⊗ₖ 1` unitary | H082 |
| `Complex.conj_ofReal`, `map_ofNat` | `simp [Rz, …, ← Complex.exp_conj, ← Complex.exp_add, map_ofNat]` | conj of a real cast / numeral is itself | M126, M127 |

### Vectors and inner products (adjoint moves)

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Matrix.mulVec`, `dotProduct` | `simp [CNOT, H, ket, tensor, bell, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]` | unfold `M *ᵥ v` into sums | E114, M130 |
| `Matrix.star_mulVec` | `star (M *ᵥ v) = star v ᵥ* Mᴴ` | ⟨Mv\| = ⟨v\|M† | M128, M133, H077 |
| `Matrix.dotProduct_mulVec` | `v ⬝ᵥ (A *ᵥ w) = (v ᵥ* A) ⬝ᵥ w` | move a matrix across `⬝ᵥ` | M128, M133 |
| Hermitian move | `rw [Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]` | ⟨x, Ay⟩ = ⟨Ax, y⟩ | M128, H077 |
| unitary move | `rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]` | ⟨Ux, Uy⟩ = ⟨x, y⟩ | M133, H079 |
| `Matrix.mulVec_mulVec`, `one_mulVec`, `mulVec_smul`, `neg_mulVec` | `rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]` | `M *ᵥ (N *ᵥ v) = (M*N) *ᵥ v` etc. | M128, M129 |
| `Matrix.vecMul_vecMul`, `vecMul_one` | `v ᵥ* M ᵥ* N = v ᵥ* (M * N)` | row-vector side | M133, H079, H081 |
| `mulVec_add`, `add_mulVec`, `sub_mulVec`; `dotProduct_add/sub/neg` | `simp only [chsh, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, mes_expect]` | linearity; the `dotProduct_*` ones have no `Matrix.` prefix | M140, M143, H081 |
| `congrArg (· *ᵥ v) h` | `have h := congrArg (· *ᵥ v) mermin_identity` | apply a matrix identity to a vector | M129 |
| `smul_eq_zero` | `rcases smul_eq_zero.mp h2 with h3 \| h3` | `r • v = 0 ↔ r = 0 ∨ v = 0`; eigenvalue argument with `v ≠ 0` | M128, M129 |
| `Pi.single i 1`, `Pi.single_apply` | `def ket (b : Fin 2) : Fin 2 → ℂ := Pi.single b 1` | basis vector \|b⟩; `Pi.single i x i' = if i' = i then x else 0` | E114, M140, H083 |
| `exists_pair_ne` | `obtain ⟨i, j, hij⟩ := exists_pair_ne d` | two distinct basis labels from `[Nontrivial d]` | M140 |
| Cauchy–Schwarz via ℓ² | `norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 x : EuclideanSpace ℂ n) (WithLp.toLp 2 y)` | `‖⟪x,y⟫‖ ≤ ‖x‖‖y‖` for plain vectors | H077, H081 |
| `EuclideanSpace.inner_eq_star_dotProduct`, `norm_sq_eq_re_inner` | `rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]` | bridge ⟪·,·⟫ and ‖·‖ back to `star x ⬝ᵥ y` | H077, H081 |
| `Complex.conj_eq_iff_re`, `Complex.abs_re_le_norm` | `apply Complex.conj_eq_iff_re.mp` | ⟨A⟩ real for Hermitian A; `\|z.re\| ≤ ‖z‖` | H077, H081 |

### Multi-qubit systems: product indices and Kronecker products

| API | Example | Gloss | IDs |
|---|---|---|---|
| pair-indexed states | `def tensor (u v : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun p => u p.1 * v p.2` | \|ab⟩ is index `(a, b)` | E114, M130, M140 |
| nested projections | `p.1` (q₀), `p.2.1` (q₁), `p.2.2.1` (q₂), `p.2.2.2` (R) | `Fin 2 × Fin 2 × Fin 2 × R` associates right | M132, M148 |
| `ext ⟨a, b⟩` / `ext ⟨a, b⟩ ⟨c, d⟩` | `ext ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [...]` | entrywise on vectors / matrices over pairs | E114, M145, M149 |
| `funext ⟨c, r⟩` | `funext ⟨c, r⟩` | function ext with a pair pattern | M132, M148 |
| `Fintype.sum_prod_type` | `∑ x : α × β, f x = ∑ a, ∑ b, f (a, b)` | sum over pairs = double sum | E114, M132, M143 |
| Fin 2 XOR | `example : (1 : Fin 2) + 1 = 0 := rfl` | bit flips: CNOT `b + a`, oracle `y + f x` | E114, M130, M132, H083 |
| `Matrix.kroneckerMap_apply` | `(A ⊗ₖ B) (i, k) (j, l) = A i j * B k l` | simp applies it by itself | E111, E114, M143 |
| `Matrix.mul_kronecker_mul` (use `←`) | `rw [← Matrix.mul_kronecker_mul, hA, hB, Matrix.one_kronecker_one]` | `(A⊗B)(C⊗D) = AC ⊗ BD` | E111, M129, M131, M145 |
| `Matrix.one_kronecker_one` | `1 ⊗ₖ 1 = 1` | identity on the joint system | E111, M145 |
| `Matrix.smul_kronecker`, `kronecker_smul`, `neg_one_smul` | `rw [Matrix.smul_kronecker, Matrix.kronecker_smul, neg_one_smul]` | pull scalars out of `⊗ₖ` | M129 |
| Pauli strings | `def P3 (P Q R : Matrix (Fin 2) (Fin 2) ℂ) := P ⊗ₖ (Q ⊗ₖ R)` | three-qubit operator | M129 |
| partial transpose | `Matrix.of fun p q => M (p.1, q.2) (q.1, p.2)` | `M^{T_B}`; on products `ρ ⊗ₖ σᵀ` | M149 |
| `Fintype.sum_equiv (Equiv.prodComm d d) _ _ fun _ => rfl` | `exact Fintype.sum_equiv (Equiv.prodComm d d) _ _ fun _ => rfl` | reindex a sum over `d × d` by swapping | H080 |
| `Finset.sum_mul_sum` | `simp only [Braket.dot, Fintype.sum_prod_type, Finset.sum_mul_sum]` | product of sums = double sum (factor ⟨ψ⊗ψ'\|φ⊗φ'⟩) | H079, H080 |

### Complex numbers, phases, √ casts

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Complex.mul_conj` | `rw [MState.pure_apply, Complex.mul_conj]` | `z * conj z = ↑(normSq z)` | E113, H076, H087 |
| `Complex.conj_mul'` | `simp [dotProduct, Complex.conj_mul']` | `conj z * z = ↑‖z‖ ^ 2`; bridges `∑ ‖vᵢ‖²` and `star v ⬝ᵥ v` | M133, M134 |
| `Complex.conj_conj`, `map_mul`, `map_inv₀`, `map_pow` | `rw [MState.pure_apply, MState.pure_apply, map_mul, Complex.conj_conj, mul_comm]` | push `conj` through | E113, H084 |
| `Complex.normSq_apply` / `_mul` / `_add` | `rw [Complex.normSq_apply]` | `re² + im²`; multiplicative; `\|z+w\|² = … + 2 Re(z conj w)` | M130, M132, H080 |
| `Complex.normSq_eq_conj_mul_self`, `Complex.sq_norm`, `Complex.normSq_eq_norm_sq` | `rw [Complex.sq_norm]` | `↑(normSq z) = conj z * z`; `‖z‖ ^ 2 = normSq z` | H080, H087 |
| `Complex.re_sum`, `Complex.mul_re` | `rw [← Complex.re_sum]` | `(∑ f).re = ∑ (f i).re` | M136, H080 |
| `Complex.nonneg_iff` | `norm_num [Complex.nonneg_iff] at h1` | `0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im` (ComplexOrder) | M136, M149 |
| take real/imag parts | `simpa using congrArg Complex.re h` | from `z = 1` to `z.re = 1` | M136, H076 |
| `exp_add`, `exp_neg`, `exp_pi_mul_I`, `exp_conj` | `rw [show -(2 * (Real.pi : ℂ) / 2) * I = -(Real.pi * I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]` | e^{iπ} = −1; `cexp (conj x) = conj (cexp x)` | M127, H087 |
| conj of a phase | `rw [← Complex.exp_conj, ← Complex.exp_neg]` | conj ω = ω⁻¹ | H084, H085 |
| `Complex.exp_mul_I`, `exp_nat_mul` | `cexp (x * I) = cos x + sin x * I`; `exp (n * x) = exp x ^ n` | Euler; phase powers | H084, H088 |
| `Complex.norm_mul_exp_arg_mul_I` | `‖x‖ * cexp (x.arg * I) = x` | polar form, valid at `x = 0` | H087 |
| `push_cast; ring_nf` | `simp only [Rz, Matrix.mul_fin_two, ← Complex.exp_add]; push_cast; ring_nf` | move ℝ→ℂ casts out, then match exponents | M127 |
| (√2)⁻² | `rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num` | `((√2)⁻¹ : ℂ)^2 = 1/2` | M126, M130, H083, H084 |
| (√n)⁻¹(√n)⁻¹ | `rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp` | `= (n : ℂ)⁻¹` | M131, M132, M138, H080 |
| √2² via `linear_combination` | `rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp` then `linear_combination (-4) * h2` | after `field_simp` | M143, M149 |
| `exact_mod_cast` | `simp only [MState.pure_apply, Complex.mul_conj]; exact_mod_cast ψ.normalized` | ℝ sum ↔ ℂ sum | E113, M133, M134 |

### Kets and bra-kets (physlib `Ket`)

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Ket d` | `⟨fun _ => ((Real.sqrt 2)⁻¹ : ℂ), by simp⟩ : Ket (Fin 2)` | fields `vec : d → ℂ`, `normalized' : ∑ x, ‖vec x‖ ^ 2 = 1` | E112, H076 |
| `where` syntax | `noncomputable def singlet : Ket (Fin 2 × Fin 2) where vec := …; normalized' := by …` | define field by field | M137 |
| `Ket.apply` | `ψ i = ψ.vec i` (unfold with `simp [Ket.apply]`) | coercion to a function | E112, M137 |
| `Ket.normalized'` / `Ket.normalized` | `exact_mod_cast ψ.normalized` | `∑ ‖ψ.vec x‖^2 = 1` / `∑ normSq (ψ x) = 1` | E113, M133, H080 |
| `Ket.basis i` | `〈Ket.basis i‖Ket.basis j〉 = if i = j then 1 else 0` | `vec = fun j => if i = j then 1 else 0` | E112, H076 |
| `〈ξ‖ψ〉`, `Braket.dot` | `simp [Braket.dot, Ket.basis, Ket.to_bra, Ket.apply, Bra.apply]` | unfold a bra-ket into a sum | E112, H079 |
| `Ket.to_bra` | `(ψ : Ket d) : Bra d` | coercion Ket → Bra, conjugates entries | E112 |
| `Braket.dot_eq_dotProduct` | `dot ψ φ = ⇑ψ ⬝ᵥ ⇑φ` | bra-ket as `⬝ᵥ` | H079 |
| `Braket.dot_self_eq_one` | `rw [Braket.dot_self_eq_one] at key` | 〈ψ‖ψ〉 = 1 | H079 |
| `ψ ⊗ᵠ φ` (`Ket.prod`) | `example (i j : Fin 2) : (ξ ⊗ᵠ φ) (i, j) = ξ i * φ j := rfl` | product ket | M137, H079 |
| `Ket.IsProd`, `Ket.IsEntangled` | `ψ.IsProd ↔ ∃ ξ φ, ψ = ξ ⊗ᵠ φ := Iff.rfl`; `IsEntangled = ¬ IsProd` | separability of a pure state | M137, H078 |
| refute a product | `rintro ⟨ξ, φ, h⟩; have h01 := congrArg (fun ψ : Ket _ => ψ (0, 1)) h` | evaluate a ket equation at an index | M137 |
| `Ket.IsProd_iff_mul_eq_mul` | `ψ.IsProd ↔ ∀ i₁ i₂ j₁ j₂, ψ (i₁,j₁) * ψ (i₂,j₂) = ψ (i₁,j₂) * ψ (i₂,j₁)` | product iff 2×2 minors vanish | H078 |
| `Ket.MES d` | `(Ket.MES d).vec (i, j) = if i = j then ((Real.sqrt (Fintype.card d) : ℂ))⁻¹ else 0 := by simp [Ket.MES]` | Φ = (1/√n) ∑ᵢ \|i,i⟩; needs `[Nonempty d]` | M131, M138, M143 |
| raw-vector access | `star (Ket.MES d).vec ⬝ᵥ ((A ⊗ₖ B) *ᵥ (Ket.MES d).vec)` | ⟨Φ\|A⊗B\|Φ⟩ = (1/n) ∑ᵢⱼ Aᵢⱼ Bᵢⱼ | M131, M143 |

### Density matrices (physlib `MState`) and `HermitianMat`

| API | Example | Gloss | IDs |
|---|---|---|---|
| `MState d`, `ρ.m`, `ρ.M` | `example (ρ : MState (Fin 2)) : ρ.m = ρ.M.mat := rfl` | state; raw matrix; `HermitianMat` wrapper | E113, M135, M138 |
| `MState.pure ψ`, `MState.pure_apply` | `(MState.pure ψ).m i j = ψ i * conj (ψ j)` | \|ψ⟩⟨ψ\| | E113, M134, H076 |
| `ρ.psd`, `ρ.Hermitian`, `ρ.tr'` | `have hdet := ρ.psd.det_nonneg` | `ρ.m.PosSemidef`, `.IsHermitian`, `ρ.m.trace = 1` | M136, H076 |
| `MState.ext_m` | `apply MState.ext_m; ext i j` | equal raw matrices give equal states | M138, M146, H076 |
| `HermitianMat` unwrap | `show (MState.pure (Ket.MES d)).traceLeft.M.mat i j = (MState.uniform : MState d).M.mat i j` | restate `ρ.m` as `ρ.M.mat` so lemmas match | M138, H078 |
| `MState.traceLeft_M`, `HermitianMat.traceLeft_mat`, `MState.mat_M` | `rw [MState.traceLeft_M, HermitianMat.traceLeft_mat, MState.mat_M]` | peel MState → HermitianMat → Matrix (same for `traceRight`) | M138, H078 |
| `Matrix.traceLeft` / `traceRight` | `simp only [Matrix.traceLeft, Matrix.of_apply, MState.pure_apply]` | Tr_A: `∑ k, M (k, i) (k, j)`; Tr_B: `∑ k, M (i, k) (j, k)` | M138, M145, H078, H082 |
| `ρ.traceLeft : MState d₂`, `ρ.traceRight : MState d₁` | `(MState.pure ψ).traceRight` | reduced states ρ_B, ρ_A | M138, M139, H078 |
| `MState.uniform`, `coe_ofClassical`, `HermitianMat.diagonal_mat` | `rw [MState.uniform, MState.coe_ofClassical, HermitianMat.diagonal_mat, Matrix.diagonal_apply]` | I/d as `ofClassical` of the uniform distribution | M138 |
| `HermitianMat.diagonal ℂ f`, `zero_le_iff`, `mat_finset_sum`, `ext1` | `rw [HermitianMat.zero_le_iff, zMats, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]` | build Hermitian matrices; `0 ≤ A ↔ A.mat.PosSemidef` | M135 |
| `HermitianMat.inner_eq_re_trace` | `inner ℝ A B = re (A.mat * B.mat).trace` | Hilbert–Schmidt inner product | M135, H078 |
| `MState.purity`, `MState.val_inner`, `Prob.coe_one` | `rw [Subtype.ext_iff, Prob.coe_one, reduced_purity]` | `purity : Prob` is tr ρ²; `p = 1 ↔ (p : ℝ) = 1` | H078 |
| `ρ.uConj U`, `HermitianMat.conj_apply_mat` | `simp only [TrDistance, MState.uConj, MState.m, HermitianMat.conj_apply_mat]` | U ρ U†, matrix `B * A.mat * Bᴴ` | M147 |
| Bloch coordinates | `def blochX (ρ : MState (Fin 2)) : ℝ := 2 * (ρ.m 0 1).re` | ρ = ½(I + xX + yY + zZ) | M136, H076 |
| `Fin.forall_fin_two` | `simp only [Fin.forall_fin_two]` | split `∀ i j : Fin 2` without `⟨0, _⟩` indices | H076 |

### Measurements, channels, positivity

| API | Example | Gloss | IDs |
|---|---|---|---|
| `POVM X d` | `(⟨zMats, zMats_nonneg, zMats_sum⟩ : POVM d d)` | `⟨mats, nonneg, normalized⟩`: effects ≥ 0 summing to 1 | M135 |
| `POVM.measure` | `(Λ.measure ρ i : ℝ) = inner ℝ (Λ.mats i) ρ.M := rfl` | Born rule, a `ProbDistribution X` | M135 |
| Kraus map (raw) | `def kraus K ρ := ∑ i, K i * ρ * (K i)ᴴ` with `∑ i, (K i)ᴴ * K i = 1` | channel in Kraus form | M144, M145 |
| `Matrix.trace_sum`, `trace_mul_cycle` | `simp_rw [trace_mul_cycle (K _) ρ]` | `(A*B*C).trace = (C*A*B).trace` under the sum | M144 |
| `CPTPMap.of_kraus_CPTPMap` | `CPTPMap.of_kraus_CPTPMap P dephase_tp : CPTPMap (Fin 2) (Fin 2) ℂ` | bundle Kraus ops into a channel; `Λ ρ : MState _` | M146 |
| `CPTPMap.mat_coe_eq_apply_mat` | `rw [CPTPMap.mat_coe_eq_apply_mat]; rfl` | output matrix is the Kraus sum (by `rfl`) | M146 |
| `Matrix.posSemidef_iff_dotProduct_mulVec` | `rw [posSemidef_iff_dotProduct_mulVec] at *` | PSD ↔ Hermitian ∧ ∀ x, 0 ≤ ⟨x, Mx⟩ | M144 |
| `Matrix.isHermitian_mul_mul_conjTranspose` | `isHermitian_mul_mul_conjTranspose B hρ.1` | `B A Bᴴ` Hermitian | M144 |
| `Matrix.posSemidef_sum` | `posSemidef_sum _ fun i _ => conj_psd (K i) ρ hρ` | finite sums of PSD are PSD | M144, M149 |
| `PosSemidef.kronecker` / `.transpose` / `.smul` | `((hρ k).kronecker (hσ k).transpose).smul (hp k)` | closure; `.smul` takes a real `0 ≤ a` | M149 |
| `PosSemidef.dotProduct_mulVec_nonneg` | `have h1 := h.dotProduct_mulVec_nonneg v` | test PSD on a witness vector | M149 |
| `PosSemidef.det_nonneg`, `posSemidef_diagonal_iff` | `ρ.psd.det_nonneg : 0 ≤ ρ.m.det` | 2×2 positivity; diagonal PSD iff entries ≥ 0 | M135, M136 |
| `Matrix.vecMulVec v (star v)` | `¬ (ptB (vecMulVec bell (star bell))).PosSemidef` | projector \|v⟩⟨v\| | M149 |

### Entropy and distance measures

| API | Example | Gloss | IDs |
|---|---|---|---|
| `qMutualInfo` | `rw [qMutualInfo]` | `Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight − Sᵥₙ ρ` on `MState (dA × dB)` | M139 |
| named implicits | `qMutualInfo (dA := d) (dB := d)` | fix the implicit index types | M139 |
| `Sᵥₙ_of_partial_eq`, `Sᵥₙ_of_pure_zero`, `Sᵥₙ_nonneg`, `Sᵥₙ_le_log_d` | `have hA := Sᵥₙ_le_log_d ρ.traceLeft` | pure marginals equal; S(pure) = 0; 0 ≤ S ≤ log d | M139 |
| `traceRight_pure_MES`, `Sᵥₙ_ofClassical`, `Hₛ_uniform` | `rw [qMutualInfo, Sᵥₙ_of_partial_eq, traceRight_pure_MES, Sᵥₙ_of_pure_zero, MState.uniform, Sᵥₙ_ofClassical, Hₛ_uniform, Finset.card_univ]` | I(Φ) = 2 log d | M139 |
| `Finset.card_univ` | `rw [Finset.card_univ] at hA hB` | entropy bounds use `Finset.univ.card` | M139 |
| `IsGreatest s a` | `refine ⟨⟨_, MES_mutual_info⟩, ?_⟩; rintro _ ⟨ρ, rfl⟩` | `a ∈ s ∧ ∀ x ∈ s, x ≤ a` | M139, H082 |
| `TrDistance` | `unfold TrDistance` | `1 / 2 * (ρ.m - σ.m).traceNorm` | M147, H082 |
| `Matrix.traceNorm_nonneg` / `_zero_iff` / `_add_le` | `have := traceNorm_add_le (ρ.m - σ.m) (σ.m - τ.m)` | ‖·‖₁ (sum of singular values) is a norm | M147 |
| `Matrix.traceNorm_unitary_conj` | `classical; have := traceNorm_unitary_conj (A := A) (U := ⟨U.val, by convert U.2 <;> rfl⟩); simpa using this` | unitary invariance (classical-instance idiom) | M147 |
| `Matrix.traceNorm_eq_max_re_tr_U` | `obtain ⟨⟨U, hU⟩, hUeq⟩ := (Matrix.traceNorm_eq_max_re_tr_U A).1` | ‖A‖₁ = max over unitaries of Re tr(UA) | H082 |
| `Matrix.traceRight_sub` | `rw [Matrix.traceRight_sub]` | partial trace is linear | H082 |
| instance clash | `obtain rfl : i1 = i2 := Subsingleton.elim _ _` | identify two `DecidableEq` instances | H082 |

### Algorithms: roots of unity, Fourier and Hadamard sums

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Complex.isPrimitiveRoot_exp` | `Complex.isPrimitiveRoot_exp N hN : IsPrimitiveRoot (exp (2 * π * I / N)) N` | ω = e^{2πi/N} | H084, H085 |
| `IsPrimitiveRoot.pow_eq_one` / `.pow_inj` / `.ne_zero` | `Fin.ext (hprim.pow_inj j.isLt l.isLt this)` | ω^N = 1; ω^i = ω^j with i, j < N ⇒ i = j; ω ≠ 0 | H084, H085 |
| `geom_sum_eq` | `rw [geom_sum_eq hr1, hrN, sub_self, zero_div]` | `x ≠ 1 → ∑ i ∈ range n, x^i = (x^n − 1)/(x − 1)` | H084, H085 |
| `Fin.sum_univ_eq_sum_range` | `rw [Fin.sum_univ_eq_sum_range (fun k => r ^ k)]` | `∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i` | H084 |
| `ZMod d` index, `[NeZero d]` | `obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)` | then `exact Fin.sum_univ_eq_sum_range f (n + 1)` | H085 |
| `ZMod.val_injective`, `ZMod.val_lt` | `ZMod.val_injective _ (hp.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h1)` | `b.val : ℕ` the representative in [0, d) | H085 |
| `Equiv.sum_comp (Equiv.subLeft i)` | `exact Equiv.sum_comp (Equiv.subLeft i) (fun j => ρ j j)` | reindex by `j ↦ i − j` | H085 |
| `Matrix.smul_apply`, `Matrix.sum_apply` | `simp only [Matrix.smul_apply, Matrix.sum_apply, …]` | entries of `c • M`, `∑ M`; qualify them under `open Matrix` | H085, M145 |
| `Fintype.prod_sum` | `rw [← Fintype.prod_sum (fun i (b : Fin 2) => (-1 : ℂ) ^ ((x i).val * b.val))]` | ∏ᵢ ∑ⱼ = ∑ over functions; character sum over bit strings | H083 |
| `Finset.prod_pow_eq_pow_sum`, `prod_mul_distrib`, `prod_eq_zero` | `simp_rw [dot, ← Finset.prod_pow_eq_pow_sum]` | (−1)^{x·y} as a product of per-bit signs | H083 |
| `Finset.sum_filter_add_sum_filter_not` | `rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = 0)]` | split a sum by a predicate (balanced f) | H083 |
| Grover trig | `rw [Real.sin_add, Real.sin_two_mul, Real.cos_two_mul, hs, hc]; field_simp` | `sin_arcsin`, `cos_arcsin`, `sqrt_div`; finish `linear_combination c * h1` | H086 |
| `Real.cos_arccos`, `Real.sin_arccos` | `⟨Real.cos_arccos (by linarith) h1, Real.sin_arccos r⟩` | angles from a modulus (ZYZ) | H087 |

### Sums with `if` (collapse) and sum algebra

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Finset.sum_ite_eq` / `sum_ite_eq'` | `simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]` | `∑ j, (if i = j then f j else 0) = f i` (`'`: `x = a` order) | M131, M143, M145, H083 |
| `apply_ite`, `mul_ite`, `ite_mul` | `simp only [apply_ite star, star_zero, …]` | push functions/products into `if` first | M131, M143, H085 |
| `Finset.sum_comm` | `rw [Finset.sum_comm]` | swap two sums | M145, M148, H082, H083 |
| `Finset.mul_sum`, `sum_mul`, `Matrix.mul_sum`, `Finset.sum_smul` | `rw [← traceLeft_sum, ← Matrix.mul_sum]` | constants through sums | M134, M141, M145, M148 |
| `Finset.sum_apply`, `Pi.smul_apply` | `simp only [decode, err, proj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]` | pointwise sums/scalings of functions | M140, M148 |
| `Finset.sum_congr rfl fun i _ => …` | `refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` | termwise equality of (double) sums | M131, M143, H079 |
| `simp_rw [h]` | `simp_rw [Matrix.mul_assoc, traceLeft_cyc, …]` | rewrite under `∑` binders | M144, M145, M148 |
| no `sum_kronecker` | `ext ⟨a, b⟩ ⟨c, e⟩; simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]` | prove `∑ i, A i ⊗ₖ 1 = (∑ i, A i) ⊗ₖ 1` entrywise | M145 |
| `rcases e with _ \| e` then `fin_cases e` | `rcases e with _ \| e; all_goals (try fin_cases e)` | case split on `Option (Fin 3)` (no error / which qubit) | M148 |

### Noncommutative algebra (CHSH) and the matrix exponential

| API | Example | Gloss | IDs |
|---|---|---|---|
| `noncomm_ring` | `example {R : Type} [Ring R] (a b : R) : (a + b) * (a - b) = a * a - a * b + b * a - b * b := by noncomm_ring` | ring identities without commutativity; ignores hypotheses | M142 |
| `abel` | `simp only [sq, add_mul, mul_add, sub_mul, mul_sub, mul_assoc, sw h₀₀, sq1 hA₀, mul_one]; abel` | close once products are atoms | M142, H077, H081 |
| right-nested helpers | `have sw : ∀ {a b : R}, a * b = b * a → ∀ x, b * (a * x) = a * (b * x)` | lets simp use commutations inside `x * (B * (A * y))` | M142, H081 |
| matrix numerals | `rw [show (4 : Matrix n n ℂ) = 1 + 1 + 1 + 1 by norm_num]` | so `abel` can match `4` | M142, H081 |
| shift observables | `simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]; abel` | `[A − a, B − b] = [A, B]` | H077 |
| `NormedSpace.exp` | `NormedSpace.exp ((-(θ / 2 : ℂ) * I) • X) = Rx θ` | matrix exponential ∑ Aᵏ/k! | H088 |
| `Matrix.exp_units_conj` | `rw [diag_conj, Matrix.exp_units_conj, exp_diag]` | `exp (U A U⁻¹) = U exp A U⁻¹`, `U : (Matrix m m 𝔸)ˣ` | H088 |
| units literal | `⟨1, 1, mul_one 1, mul_one 1⟩ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ` | `⟨val, inv, val*inv=1, inv*val=1⟩` | H088 |
| `Matrix.exp_diagonal`, `Pi.exp_def`, `Complex.exp_eq_exp_ℂ` | `rw [Matrix.exp_diagonal, Pi.exp_def]; simp only [← Complex.exp_eq_exp_ℂ]` | exp of a diagonal is entrywise; recover `cexp` | H088 |
| `Matrix.exp_conjTranspose`, `exp_add_of_commute` | `rw [← exp_conjTranspose, star_gen H hH t, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((-(t : ℂ) * I) • H)).neg_right), add_neg_cancel, NormedSpace.exp_zero]` | e^{−itH} unitary | H088 |

### Gotchas

- `simp` multiplies `!![..]` literals but never turns `1` into a literal: add `Matrix.one_fin_two`. It does not compute `!![..]ᴴ` either, so prove those entrywise (`ext i j; fin_cases i <;> fin_cases j`). (E109, E110)
- `((Real.sqrt 2 : ℝ) : ℂ)` is a cast and `simp` cannot square it. Use the `inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt` or `← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt` idioms. (M126, M132)
- Mathlib has `smul_kronecker` but no `neg_kronecker`, so write a sign as `(-1 : ℂ) • X`, not `-X`. There is no `sum_kronecker` in v4.32.0 either. (M129, M145)
- `Matrix.mul_kronecker_mul` is stated as split-the-product. Rewrite with `←` to merge `(A ⊗ₖ B) * (C ⊗ₖ D)`. (E111)
- `dotProduct_add`, `dotProduct_sub` and `dotProduct_neg` live in the root namespace, with no `Matrix.` prefix. Under `open Matrix`, `smul_apply`/`sum_apply` are ambiguous: write `Matrix.smul_apply`. (M143, H085)
- `ρ.m` is `ρ.M.mat` by definition, but the rewrite lemmas (`traceLeft_M`, `traceLeft_mat`, `mat_M`) only match the `.M.mat` form. `show … .M.mat i j = _` first. (M138, H078)
- Several QuantumInfo lemmas (`traceNorm_unitary_conj`, `traceNorm_eq_max_re_tr_U`) are stated under `open Classical`, so their `unitaryGroup` carries a different `DecidableEq`. Rebuild `U` with `⟨U.val, by convert U.2 <;> rfl⟩`, or use `Subsingleton.elim` on the instances. (M147, H082)
- `fin_cases` leaves indices as `⟨0, _⟩`, which `rw` with `ψ 0` lemmas does not see. Prefer `simp only [Fin.forall_fin_two]` or pass `show (1 + 1 : Fin 2) = 0 from rfl` to `simp`. (H076, H083)
- `ZMod d` for a variable `d` is not `Fin d`. Substitute `d = n + 1` first, then `Fin.sum_univ_eq_sum_range` closes by `exact` (definitional), not by `rw`. (H085)
- `ring` fails on noncommutative `R` and on matrices. `noncomm_ring` cannot use hypotheses like `A * A = 1` and cannot match the matrix numeral `4`. Expand with `simp only [add_mul, mul_add, mul_assoc, helpers]`, then use `abel`. (M142, H081)
- Use `Matrix.exp_add_of_commute`. The generic `NormedSpace.exp_add_of_commute` does not rewrite on matrices. `(Commute.refl A).neg_right` needs `A` written in full, because `_` fails to synthesize `HasDistribNeg`. (H088)
- `norm_sq_eq_re_inner` needs `(𝕜 := ℂ)` or `@norm_sq_eq_re_inner ℂ`, or `rw` gets stuck. (H081)
- `PosSemidef` is defined through `Finsupp`. Use `dotProduct_mulVec_nonneg` / `posSemidef_iff_dotProduct_mulVec` rather than unfolding it. (M144, M149)
- After `set ζ := …`, earlier lemmas stated with the unfolded expression no longer match syntactically: restate them in terms of `ζ`. (H084)
- Banned shortcuts (each card's `BANNED:` line) include `MState.pure_mul_self`, the `vecMulVec` product lemmas (M134), `Ket.IsProd_iff_mul_eq_mul` (M137 only; allowed in H078), `traceRight_pure_MES` (M138; allowed in M139), physlib `no_cloning` (H079), `dft_dft` (H084), and `try?` in M128/M134/M144.
- `CPTPMap` coerces to `MState dIn → MState dOut`. Its output matrix equals the Kraus sum only after `CPTPMap.mat_coe_eq_apply_mat`, then `rfl`. (M146)

## Condensed matter and statistical mechanics (physlib + Mathlib)

Problems E115–E121, M150–M173, H089–H102. physlib's statistical-mechanics API is `CanonicalEnsemble`.
Its tight-binding API is `CondensedMatter.TightBindingChain`. The Ising and Hubbard problems use plain
Mathlib (`Bool` spins, `Matrix`). Notation used below:
- `𝓒` (typed `\MCC`) is the usual name for an ensemble.
- `ℝ≥0` is `NNReal`, the nonnegative reals, and `↑x` / `(x : ℝ)` is its cast to ℝ.
- `kB` is Boltzmann's constant (`open Constants`).
- "β-real" means physlib's family of definitions that take a plain real `b` as the inverse temperature, in units with kB = 1.

### Imports and opens

| Import / open | Gives | IDs |
|---|---|---|
| `import Physlib.Thermodynamics.Temperature.Basic` | `Temperature`, `T.β`, `β_toReal` | E115 |
| `import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite` | finite ensembles, the β-real API (`probabilityBetaReal`, …), `fluctuation_dissipation_theorem_finite`, `sum_probability_eq_one`, `+` of ensembles | E117, E120, M150–M154, M160, M173, H089–H092 |
| `import Physlib.StatisticalMechanics.CanonicalEnsemble.TwoState` | `twoState E₀ E₁` and the finite API | E116, M155–M157, M161 |
| `import Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | `meanEnergy_eq_ratio_of_integrals`, `partitionFunction_def`, `mathematicalPartitionFunction_eq_integral` (non-finite ensembles on ℝ or ℕ) | H093, H094 |
| `import Physlib.CondensedMatter.TightBindingChain.Basic` | `TightBindingChain`, `localizedState`, `hamiltonian`, `energyEigenstate`, `QuantaWaveNumber` | E119, E121, M167–M171, H099, H100 |
| `import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp` | `Real.hasDerivAt_sinh`/`cosh`; physlib does not import it | M155 |
| `…Log.NegMulLog`, `Mathlib.Analysis.MeanInequalities`, `…Gaussian.GaussianIntegral` + `Mathlib.MeasureTheory.Integral.Gamma`, `Mathlib.RingTheory.RootsOfUnity.Complex` | `negMulLog`; Hölder; Gaussian/Gamma integrals; `Complex.isPrimitiveRoot_exp` | H090, H092; H091; H093; H099 |
| `open CanonicalEnsemble Constants Real` / `open CondensedMatter TightBindingChain InnerProductSpace` / `open Filter Topology` / `open Matrix` | short names; `kB`; `⟪x, y⟫_ℂ`; `𝓝`, `atTop`; `*ᵥ`, `⬝ᵥ` | all |

### Temperature and inverse temperature

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Temperature` (one field `val : ℝ≥0`) | `example (T : Temperature) : (T.val : ℝ) = T.toReal := rfl` | `T.toReal` is `T.val` cast to ℝ | E115, M157, H093 |
| `0 < T.val` → ℝ by defeq | `have hT' : (0 : ℝ) < T.toReal := hT` | move a positivity fact from `ℝ≥0` to ℝ | E115, H093 |
| `T.β : ℝ≥0`, `Temperature.β_toReal` | `rw [Temperature.β_toReal]` | `(T.β : ℝ) = 1 / (kB * T.toReal)`; after the rewrite it is ℝ algebra | E115, M155, H093 |
| `Constants.kB_pos` | `have hk := kB_pos` | `0 < kB`; must be in context for `positivity` and `field_simp` | E115, E120, H093 |
| `Temperature.beta_pos` | `have hβ : 0 < (T.β : ℝ) := Temperature.beta_pos T hT` | `0 < T.val → 0 < ↑T.β` (banned in E115) | H093, H094 |
| `gcongr` on reciprocals | `rw [Temperature.β_toReal, Temperature.β_toReal]; gcongr` | hotter means smaller β, using the `have`s in context | E115 |

### `CanonicalEnsemble`: the Temperature API

`CanonicalEnsemble ι` is a structure with fields `energy : ι → ℝ`, `dof : ℕ`, `phaseSpaceunit` (default 1),
`energy_measurable`, `μ : Measure ι` (default `volume`). `[𝓒.IsFinite]` holds when `μ = count`, `dof = 0` and the phase-space unit is 1.
Physical quantities take `T : Temperature`, and the Boltzmann weight is `exp (-↑T.β * E i)`.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `partitionFunction_of_fintype` | `rw [partitionFunction_of_fintype, Fin.sum_univ_two]` | `[IsFinite]`: `Z T = ∑ i, exp (-↑T.β * 𝓒.energy i)` (defined as an integral) | E116, M157, M173 |
| `mathematicalPartitionFunction_of_fintype` | `simp [probability, mathematicalPartitionFunction_of_fintype, Fin.sum_univ_two]` | the same sum for the `Z` in `probability`'s denominator | M155, M161, M173 |
| `probability` | `(twoState (-h) h).probability T 0` | `exp (-↑T.β * E i) / 𝓒.mathematicalPartitionFunction T` | M155, M161, M173 |
| `meanEnergy_of_fintype` | `rw [meanEnergy_of_fintype, Fintype.sum_prod_type]` | `U T = ∑ i, 𝓒.energy i * 𝓒.probability T i` | M173 |
| `sum_probability_eq_one` | `have h1 := sum_probability_eq_one 𝓒 T` | `∑ i, 𝓒.probability T i = 1` (finite, nonempty) | M173 |
| `twoState E₀ E₁ : CanonicalEnsemble (Fin 2)`, `twoState_energy_fst`/`_snd` | `rw [twoState_energy_fst, twoState_energy_snd]` | two-level system: energy 0 ↦ `E₀`, 1 ↦ `E₁`; its `IsFinite` instance is found automatically | E116, M155–M157, M161 |
| `nsmul N 𝓒`, `partitionFunction_nsmul` | `rw [partitionFunction_nsmul, partitionFunction_of_fintype]` | N distinguishable non-interacting copies (states `Fin N → ι`); `Z ^ N` | M157 |
| `helmholtzFreeEnergy` (def) | `rw [helmholtzFreeEnergy, paramagnet_Z, Real.log_pow]` | `F = -kB * T.val * log Z`; unfold by `rw` | M157 |
| `thermodynamicEntropy_eq_shannonEntropy`, `shannonEntropy` | `rw [thermodynamicEntropy_eq_shannonEntropy, shannonEntropy]` | finite: `S = -kB * ∑ i, p i * log (p i)` | M161 |
| `heatCapacity`, `fluctuation_dissipation_theorem_finite` | `rw [fluctuation_dissipation_theorem_finite 𝓒 T hT]` | `C = energyVariance T / (kB * ↑T.val ^ 2)`; no derivatives needed | E120 |
| `energyVariance` | `exact div_nonneg (MeasureTheory.integral_nonneg fun _ => sq_nonneg _) (by positivity)` | `∫ i, (E i - U) ^ 2 ∂(𝓒.μProd T)`: an integral of squares | E120 |
| `𝓒 + 𝓒'`, `energy_add_apply` | `rw [energy_add_apply, mul_add, Real.exp_add]` | product system on `ι × ι'`, energies add | M173 |
| `meanEnergy_eq_ratio_of_integrals` | `rw [meanEnergy_eq_ratio_of_integrals]` | `⟨E⟩ = (∫ E e^{-βE} dμ) / ∫ e^{-βE} dμ`, no hypotheses (continuous or ℕ-valued states) | H093, H094 |
| `partitionFunction_def`, `mathematicalPartitionFunction_eq_integral` | `rw [partitionFunction_def, mathematicalPartitionFunction_eq_integral, show (qho ε).dof = 0 from rfl, pow_zero, div_one]` | `Z = Z_math / phaseSpaceunit ^ dof`, `Z_math = ∫ e^{-βE} dμ` | H094 |

### The β-real API (kB = 1, `b : ℝ`)

These are plain finite sums, so they work for `b ≤ 0` too. Unfold them with `unfold`, `simp only [...]` or `rw`.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `mathematicalPartitionFunctionBetaReal` | `simp [mathematicalPartitionFunctionBetaReal, h]` | `Z(b) = ∑ i, exp (-b * 𝓒.energy i)` | E117, M150–M154, H089–H091 |
| `mathematicalPartitionFunctionBetaReal_pos` | `have hZ := 𝓒.mathematicalPartitionFunctionBetaReal_pos b` | `[Nonempty ι] : 0 < Z(b)`; use `hZ.ne'` for `div_self` and `field_simp` | M150–M154, H089–H092 |
| `probabilityBetaReal` | `refine ⟨fun i => by unfold probabilityBetaReal; positivity, ?_⟩` | `p b i = exp (-b * E i) / Z(b)` | M150–M154, H089, H090, H092 |
| `∑ p = 1` by hand | `simp only [probabilityBetaReal, ← Finset.sum_div]; exact div_self hZ.ne'` | the library lemma is banned; this two-liner recurs | M150, M152, M153, H090, H092 |
| `meanEnergyBetaReal` | `unfold meanEnergyBetaReal` | `U(b) = ∑ i, E i * p b i` | M152, M153, M156, M160, H089 |
| Boltzmann ratio | `rw [div_div_div_cancel_right₀ hZ, ← Real.exp_sub]; ring_nf` | `p j / p i = exp (-b (E j - E i))`: Z cancels | M151 |
| `haveI : Nonempty ι := ⟨i₀⟩` | `haveI : Nonempty ι := ⟨i₀⟩` | provide the instance `_pos` needs when you only have a witness | H092 |

### Building and modifying ensembles

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| structure update | `{ 𝓒 with energy := fun i => 𝓒.energy i + c, energy_measurable := by fun_prop }` | copy `𝓒`, replacing fields; proof fields must be supplied again | M153 |
| field by `rfl` | `have hE : (shift 𝓒 c).energy i = 𝓒.energy i + c := rfl` | read a field of your own definition | M153, H094 |
| ensemble on ℝ via `where` | `noncomputable def harmonic (κ : ℝ) : CanonicalEnsemble ℝ where energy x := κ * x ^ 2 / 2; dof := 1; energy_measurable := by fun_prop` | `μ` defaults to Lebesgue `volume` | H093 |
| ensemble on ℕ | `μ := Measure.count` (with `dof := 0`) | discrete quantum spectrum | H094 |
| unfold a field equation | `show (qho ε).dof = 0 from rfl` inside `rw [...]` | rewrite with a definitional fact | H094 |

### Derivatives (`HasDerivAt` plumbing)

`HasDerivAt f f' x` means f is differentiable at x with derivative f'. Build it with dot notation and fix the
derivative's form with `.congr_deriv`.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `HasDerivAt.fun_sum` | `apply HasDerivAt.fun_sum; intro i _` | termwise derivative of `fun y => ∑ i ∈ u, A i y` | M160, H089 |
| `.neg.mul_const`, `.exp` | `((hasDerivAt_id' b).neg.mul_const (𝓒.energy i)).exp` | d/db `exp (-b E)` | M160, H089 |
| `.const_mul` | `simpa using (hasDerivAt_id (0 : ℝ)).const_mul (T.β : ℝ)` | derivative of `c * y` | M155, H098 |
| `.log` | `(hd.log hZ.ne').congr_deriv ?_` | `HasDerivAt (log ∘ f) (f' / f x)`; needs `f x ≠ 0` | M160 |
| `.comp` | `(Real.hasDerivAt_sinh ((T.β : ℝ) * 0)).comp 0 hl` | chain rule `(f ∘ g)' = f' (g x) * g'` | M155 |
| `.div` | `(hs.div hc (Real.cosh_pos _).ne').congr_deriv (by simp)` | quotient rule, value `(c' d - c d') / d ^ 2` | M155, H089 |
| `.mul`, `.sub`, `.const_add`, `.const_sub` | `exact ((h1.mul h2).sub h3).congr_deriv (by ring)` | product/difference rules | H098 |
| `HasDerivAt.congr_deriv` | `….congr_deriv (by simp; ring)` | `f' = g'` → swap the derivative expression | M155, M160, H089, H098 |
| `HasDerivAt.deriv`, `.differentiableAt` | `rw [(hasDerivAt_meanEnergy 𝓒 b).deriv, neg_nonpos]` | turn `HasDerivAt` into a `deriv` value or differentiability | H089, H098 |
| `antitone_of_deriv_nonpos` | `apply antitone_of_deriv_nonpos` | `Differentiable ℝ f → (∀ x, deriv f x ≤ 0) → Antitone f` | H089 |
| `strictMonoOn_of_deriv_pos` | `apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)` | positive derivative on `interior D` gives strict monotonicity; `rw [interior_Ici] at hx` | H098 |

### Limits (`Filter.Tendsto`)

- `Tendsto f (𝓝 a) (𝓝 L)` means f x → L as x → a.
- `Tendsto f atTop (𝓝 L)` means f b → L as b → ∞.
- `atBot` means → −∞.
- `f =ᶠ[atTop] g` means f N = g N for all large N.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Continuous.tendsto`, `Continuous.div`, `fun_prop` | `exact Continuous.div (by fun_prop) (by fun_prop) (fun b => (𝓒.mathematicalPartitionFunctionBetaReal_pos b).ne')` | a continuous function's limit is its value; `simpa [...] using hc.tendsto 0` | M154, H098 |
| `Real.tendsto_exp_atTop` / `_atBot` | `(Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hε)).atTop_add tendsto_const_nhds` | `exp → ∞` / `→ 0`; `hg.comp hf` composes | M156, M162, H092 |
| `Tendsto.atTop_mul_const`, `.atTop_mul_neg`, `.atBot_mul_const`, `tendsto_neg_atTop_atBot` | `tendsto_id.atTop_mul_neg (by linarith) tendsto_const_nhds` | `b * c → ±∞` from the sign of c | M156, M162, H092 |
| `.div_atTop`, `.add_const`, `.const_add`, `.div`, `.sub`, `.log` | `apply Tendsto.div_atTop tendsto_const_nhds` | limit algebra (`.div` needs a nonzero limit of the denominator, `.log` a nonzero limit) | M156, M162, H092, H102 |
| `tendsto_finsetSum` | `tendsto_finsetSum Finset.univ fun i _ => (Real.continuous_negMulLog.tendsto _).comp (hlim i)` | termwise limits of a finite sum | H092 |
| `tendsto_of_tendsto_of_tendsto_of_le_of_le` | `tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (Real.tendsto_exp_atBot.comp hlin) h₁ h₂` | squeeze theorem | H092 |
| `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, `tendsto_natCast_atTop_atTop` | `(hlim.div_atTop tendsto_natCast_atTop_atTop).const_add (Real.log lp)` | `r^N → 0`; `(N : ℝ) → ∞` | H102 |
| `Tendsto.congr'` + `filter_upwards` | `refine h2.congr' ?_; filter_upwards [eventually_ge_atTop 1] with N hN` | change a sequence on a tail (avoids `x / 0 = 0` junk at N = 0) | H102 |
| `intermediate_value_Icc'` | `obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc' hm₀1 hcont ⟨hg1, hg0⟩` | IVT for a sign change from + to −: `Icc (f b) (f a) ⊆ f '' Icc a b` | H098 |

### Entropy, convexity, inequalities

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Real.negMulLog`, `negMulLog_def`, `continuous_negMulLog` | `simp only [Real.negMulLog]` | `x ↦ -x log x`, the Gibbs entropy summand; 0 at 0 and 1 | M158, H090, H092 |
| `Real.concaveOn_negMulLog` + `ConcaveOn.le_map_sum` | `Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := fun _ => 1 / n) (p := p) h₀ h₁ hmem` | Jensen with uniform weights; fill implicits by name | M158 |
| `Real.log_le_sub_one_of_pos` | `have h1 := Real.log_le_sub_one_of_pos (div_pos hy hx')` | `log x ≤ x - 1`: Gibbs' inequality | H090 |
| `rcases h.eq_or_lt with rfl \| h'` | `rcases hx.eq_or_lt with rfl \| hx'` | split `0 ≤ x` into `x = 0` or `0 < x` (the `0 · log 0 = 0` case) | H090, H091 |
| `ConvexOn ℝ Set.univ f` | `refine ⟨convex_univ, fun x _ y _ a c ha hc hac => ?_⟩; simp only [smul_eq_mul]` | unfold convexity by hand | H091 |
| `Real.inner_le_Lp_mul_Lq_of_nonneg`, `Real.holderConjugate_iff` | `Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) (f := …) (g := …) hpq hf hg` | finite Hölder `∑ f g ≤ (∑ f^p)^(1/p) (∑ g^q)^(1/q)`; `p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1` | H091 |
| rpow (`x ^ (y : ℝ)`) | `rw [Real.log_mul (rpow_pos_of_pos (hZ x) a).ne' (rpow_pos_of_pos (hZ y) c).ne', Real.log_rpow (hZ x)]` | `Real.exp_mul : exp (x*y) = exp x ^ y`, `log_rpow`, `rpow_pos_of_pos`, `one_div_one_div` | H091, H093 |
| `Finset.single_le_sum`, `Finset.add_sum_erase` | `rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h1` | one term ≤ a sum of nonnegatives; split off term `i₀` (`classical`) | H092 |

### Integrals and series

- `∫ x, f x ∂μ` is the Bochner integral.
- `∑' n, f n` is `tsum`. It is 0 unless `Summable f`.
- `μ.real s` is a measure as a real number.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `integral_gaussian` | `rw [integral_gaussian]; positivity` | `∫ x, exp (-b * x ^ 2) = √(π / b)` | H093 |
| `integral_comp_abs`, `integral_rpow_mul_exp_neg_mul_rpow` | `rw [h1, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) ha, integral_gaussian]` | even integrand ↦ `2 ∫_{Ioi 0}`; Gamma moment formula (real powers) | H093 |
| `Real.Gamma_add_one`, `Real.Gamma_one_half_eq` | `rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]` | `Γ(s+1) = s Γ(s)`, `Γ(1/2) = √π` | H093 |
| `Real.rpow_two`, `rpow_add`, `rpow_neg`, `sqrt_eq_rpow` | `simp only [Real.rpow_two, sq_abs]` | bridge `x ^ (2 : ℝ)` and `x ^ 2`, `√` | H093 |
| `integral_const_mul` | `rw [integrand_eq, weight_eq, integral_const_mul]` | pull a constant out (match the integrand as a lambda first) | H093 |
| `integral_countable` + `integrable_count_iff` | `rw [integral_countable (integrable_count_iff.mpr ?_)]; · simp [Measure.real]` | `∫ ∂count = ∑'` (count.real {n} = 1) | H094 |
| `tsum_geometric_of_lt_one`, `summable_geometric_of_lt_one` | `rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr1]` | `∑' rⁿ = (1 - r)⁻¹` | H094 |
| `tsum_coe_mul_geometric_of_norm_lt_one`, `summable_pow_mul_geometric_of_norm_lt_one` | `simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnr` | `∑' n rⁿ = r/(1-r)²` | H094 |
| `Summable.tsum_add`, `tsum_mul_left`, `.mul_left` | `(hs1.mul_left _).tsum_add (hs0.mul_left _)` | linearity of `tsum` | H094 |

### Ising models on `Bool`

The convention is `def spin (b : Bool) : ℝ := if b then 1 else -1`. A configuration is `σ : Fin (n + 1) → Bool`.
For `i : Fin n`, the bond `i` joins sites `i.castSucc` and `i.succ`, and `Fin.last n` is the top site.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| Bool case split | `cases a <;> cases b <;> simp [bond, spin]` | check all spin values; `!a` flips | E118, M164, H095 |
| `IsLeast`/`IsGreatest` + `Set.range` | `refine ⟨⟨fun _ => true, by simp [energy, spin]⟩, ?_⟩; rintro _ ⟨σ, rfl⟩` | attained + bound; elements of a range | M164, M167 |
| `Equiv` by hand + `Equiv.sum_comp` | `⟨fun σ i => !σ i, fun σ i => !σ i, fun σ => by funext i; simp, fun σ => by funext i; simp⟩` | global spin flip; `Equiv.coe_fn_mk` lets simp evaluate it | M165 |
| `Fin.consEquiv` + `Fintype.sum_prod_type` | `rw [Z, ← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]` | sum out the first spin; `Fin.cons_zero`, `Fin.cons_succ` | H095, H097 |
| `Fin.snocEquiv` | `rw [← (Fin.snocEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]` | sum out the last spin; `Fin.snoc_castSucc`, `Fin.snoc_last`, `Fin.succ_last` | H096 |
| `← Fin.succ_castSucc` | `simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]` | reindex bonds after `cons`/`snoc` | H095–H097 |
| `Fin.sum_univ_succ` / `_castSucc` | `simp only [energy, Fin.sum_univ_castSucc]` | peel the first or last term of a `Fin (n+1)` sum | H095–H097 |
| `Nat.le_induction` | `induction n, hr using Nat.le_induction with \| base => _ \| succ n hrn ih => _` | induction on `n ≥ r` carrying `r ≤ n` | H096 |
| transfer matrix `Matrix.of`, path sums | `Matrix.of fun a b => Real.exp (β * (J * (spin a * spin b) + h * (spin a + spin b) / 2))` | `Matrix Bool Bool ℝ`; `Matrix.mul_apply`, `Matrix.one_apply`, `Matrix.trace`/`diag` (rfl) | H097 |
| `Real.exp_sum`, `Finset.sum_eq_single`, `ite_and`, `Equiv.funUnique` | `simp only [transfer, Matrix.of_apply, ← Real.exp_sum, ← Real.exp_add, ringEnergy, field_split]` | product of Boltzmann factors; collapse a sum; `Fin 1 → Bool ≃ Bool` | H097 |
| 2×2 transfer matrix power | `fin_cases i <;> fin_cases j <;> simp [T0, Matrix.mul_apply, Fin.sum_univ_two, Real.cosh_eq, Real.sinh_eq, pow_succ] <;> ring` | induct on the whole matrix `T0 K ^ n`, then `Matrix.trace_fin_two` | M166, H102 |

### Counting microstates

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Finset.card_nbij'` | `refine Finset.card_nbij' (fun σ => Finset.univ.filter fun i => σ i = true) (fun s i => decide (i ∈ s)) ?_ ?_ ?_ ?_` | card equality from mutually inverse maps (4 goals) | M159, M163 |
| `Finset.card_powersetCard`, `mem_powersetCard` | `simp [Finset.card_powersetCard]` | k-subsets: `N.choose k` | M159 |
| `Finset.sum_fiberwise_of_maps_to` | `rw [← Finset.sum_fiberwise_of_maps_to (g := nUp) (t := Finset.range (N + 1))]` | group a sum over states by energy level (density of states) | M159 |
| `Sym.equivNatSumOfFintype`, `Sym.card_sym_eq_choose` | `rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin N) q), Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]` | stars and bars: `Ω_N(q) = C(N+q-1, q)` | M163 |
| `Finset.Nat.antidiagonalTuple`, `Nat.card_eq_finsetCard`, `Equiv.subtypeEquivRight` | `exact Nat.card_congr (Equiv.subtypeEquivRight fun f => Finset.Nat.mem_antidiagonalTuple.symm)` | turn a subtype count into a `Finset.card` | M163 |
| `Finset.card_eq_sum_card_fiberwise`, `Finset.card_product`, `Fin.append` | `exact Prod.ext (funext (Fin.append_left _ _)) (funext (Fin.append_right _ _))` | split `Fin (a+b)` states into A × B | M163 |

### Tight-binding chain (physlib `CondensedMatter.TightBindingChain`)

A `T : TightBindingChain` has fields `N` (with `[NeZero N]`), `a` (and `a_pos : 0 < a`), `E0` and `t`.
`T.HilbertSpace` is `ℂ^N`. `localizedState : OrthonormalBasis (Fin T.N) ℂ T.HilbertSpace` is the site
basis, which the cards write `|n⟩`. `localizedComp m n` prints as `|m⟩⟨n|` and sends ψ to `⟪|n⟩, ψ⟫ • |m⟩`.
`⟪x, y⟫_ℂ` is conjugate-linear in `x`, and `conj` prints as `starRingEnd ℂ`.

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `energyEigenvalue` | `unfold TightBindingChain.energyEigenvalue` | `E(k) = E0 - 2 * t * cos (↑k * a)` | E119, M167, H099 |
| `QuantaWaveNumber : Set ℝ` | `refine ⟨⟨T.N / 2, by have := NeZero.pos T.N; omega⟩, ?_⟩` | `{x \| ∃ n : Fin N, 2π/(a N) * (n - ⌊N/2⌋) = x}`; `k` is a subtype element `⟨x, ⟨n, proof⟩⟩` | M167, M170, H099 |
| `Set.ncard_range_of_injective` | `rw [hset, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]` | count the N wavenumbers | M170, H100 |
| `hamiltonian_hermitian` | `have h := T.hamiltonian_hermitian ψ ψ` | `⟪H ψ, φ⟫_ℂ = ⟪ψ, H φ⟫_ℂ` | E121, M169, H100 |
| `inner_conj_symm`, `Complex.conj_eq_iff_im` | `rw [← inner_conj_symm] at h; exact Complex.conj_eq_iff_im.mp h` | ⟨ψ, Hψ⟩ is real | E121, M169 |
| `inner_smul_left`/`_right`, `inner_self_ne_zero`, `mul_right_cancel₀` | `rw [hE, inner_smul_left, inner_smul_right] at h` | eigenvalues of a Hermitian H are real | M169, H100 |
| `energyEigenstate`, `localizedState_orthonormal_eq_ite`, `inner_sum`, `sum_inner` | `simp only [TightBindingChain.energyEigenstate, sum_inner, inner_sum, inner_smul_left, inner_smul_right, localizedState_orthonormal_eq_ite]` | `ψ_k = ∑ n, exp (I k n a) • \|n⟩`; `⟪\|m⟩, \|n⟩⟫ = if m = n then 1 else 0` | M168, H100 |
| `Complex.norm_exp`, `Complex.exp_conj` | `simp [← Complex.exp_conj, ← Complex.exp_add, Complex.conj_ofReal]` | `‖exp z‖ = exp z.re`; `⟪ψ_k, ψ_k⟫ = N` | M168, H100 |
| `hamiltonian_apply_localizedState`, `localizedComp_apply_localizedState` | `simp [translation, localizedComp_apply_localizedState]` | `H\|n⟩ = E0•\|n⟩ - t•(\|n+1⟩ + \|n-1⟩)`; `\|m⟩⟨n\| \|p⟩ = if n = p then \|m⟩ else 0` | M171 |
| `Module.Basis.ext` via `toBasis` | `apply (localizedState (T := T)).toBasis.ext` | linear maps equal on a basis (`OrthonormalBasis.coe_toBasis`) | M171 |
| `Equiv.subRight`, `quantaWaveNumber_exp_sub_one` | `rw [← (Equiv.subRight (1 : Fin T.N)).sum_comp]` | reindex `n ↦ n - 1`; `exp (I k (n-1) a) = exp (I k n a) * exp (-I k a)` | M171 |
| `hamiltonian_energyEigenstate`, `energyEigenstate_orthogonal` | `apply linearIndependent_of_ne_zero_of_inner_eq_zero _ T.energyEigenstate_orthogonal` | `H ψ_k = E(k) • ψ_k`; Bloch states are pairwise orthogonal | H100 |
| dimension count | `rw [Module.finrank_eq_card_basis (localizedState (T := T)).toBasis, Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, card_wavenumbers]` | with `LinearIndependent.span_eq_top_of_card_eq_finrank'`; `haveI : Fintype T.QuantaWaveNumber := hfin.fintype` | H100 |
| `Submodule.span_induction` | `induction hφ using Submodule.span_induction with \| mem x hx => … \| zero => simp \| add x y _ _ hx hy => … \| smul c x _ hx => …` | push a property through a span | H100 |
| roots of unity | `have hω := Complex.isPrimitiveRoot_exp N hN0` | `IsPrimitiveRoot (exp (2πI/N)) N`; `.pow_eq_one_iff_dvd`, `geom_sum_mul` | H099 |
| cos sums as `Re` of exp sums | `rw [Complex.re_sum]; simp only [Complex.exp_ofReal_mul_I_re]` | with `Fin.sum_univ_eq_sum_range`, `Complex.exp_nat_mul`, `Real.cos_sq` | H099 |
| cos bounds | `exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)` | `Real.cos_le_one`, `neg_one_le_cos`, `cos_pi`, `cos_neg`; `abs_mul`, `abs_neg`, `abs_two` | E119, M167 |

### Small Hamiltonians as matrices

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `!![…]`, `![…]` literals | `!![U, 0, -t, -t; 0, U, -t, -t; -t, -t, 0, 0; -t, -t, 0, 0]` | `Matrix (Fin 4) (Fin 4) ℝ`; vector `Fin 4 → ℝ` | M166, M172, H101 |
| `M *ᵥ v`, `v ⬝ᵥ w` (open Matrix) | `fin_cases i <;> simp [H, mulVec, dotProduct, Fin.sum_univ_four]` | matrix·vector, dot product; `x ⬝ᵥ (H *ᵥ x)` = ⟨x, Hx⟩ | M172, H101 |
| `congrFun hv i` | `have h0 := congrFun hv 0` | read one component of `H *ᵥ v = E • v` | M172 |
| `linear_combination` | `linear_combination (-E) * h0 + (-E) * h1 + (2 * t) * h2 + (2 * t) * h3` | eliminate components into the characteristic equation | M161, M172, H101 |
| `by_contra hne; apply hv0` | `by_contra hne; apply hv0` | prove an equation by showing that otherwise `v = 0` | M172 |
| `Real.sq_sqrt`, `sqrt_lt_sqrt`, `sqrt_sq_eq_abs`, `abs_cases` | `constructor <;> cases abs_cases U <;> linarith` | handle `√(U² + 16t²)` | H101 |
| `mul_nonneg_iff_of_pos_left` | `rw [← mul_nonneg_iff_of_pos_left hUE, key]; positivity` | strip a positive factor after completing the square | H101 |
| `le_div_iff₀`, `div_le_iff₀`, `pow_le_pow_left₀` | `rw [le_div_iff₀ hU]; nlinarith` | clear a positive denominator; square a nonnegative inequality | M172, H098 |

### exp, log and hyperbolic functions

| API | Example | Gloss | IDs |
|---|---|---|---|
| `Real.exp_add`, `exp_sub`, `exp_neg`, `exp_le_exp`, `exp_nat_mul` | `rw [hE, show -b * (𝓒.energy i + c) = -b * c + -b * 𝓒.energy i by ring, Real.exp_add]` | split or merge exponents | M151, M153, M162, H094 |
| `Real.log_div`, `log_exp`, `log_pow`, `log_mul`, `log_le_log` | `rw [Real.log_div (exp_pos _).ne' hZ.ne', Real.log_exp]` | `log p_i = -b E_i - log Z` | M157, M161, H090, H102 |
| `Real.cosh_eq`, `sinh_eq`, `tanh_eq`, `tanh_eq_sinh_div_cosh` | `simp [Fin.sum_univ_two, Real.cosh_eq]` | exp forms; `2 cosh` sums of two Boltzmann factors | M155, M157, M166, H095–H098 |
| `Real.cosh_pos`, `cosh_sq`, `cosh_sq_sub_sinh_sq`, `tanh_lt_one` | `have hc : 0 < Real.cosh (β * J) := Real.cosh_pos _` | facts for `field_simp` and bounds | M155, H096, H098, H102 |
| `Real.add_one_le_exp`, `add_one_lt_exp` | `Real.add_one_lt_exp (by positivity)` | `x + 1 ≤ exp x` (strict if x ≠ 0) | H094, H098 |
| `div_lt_one`, `div_le_div_iff_of_pos_right`, `div_le_div_iff₀`, `div_le_div_of_nonneg_right` | `rw [div_le_div_iff_of_pos_right hZ, Real.exp_le_exp]` | compare fractions | M151, M162, H090, H098 |
| `Finset.sum_div`, `mul_sum`, `sum_add_distrib`, `sum_mul_sum`, `sum_comm`, `sum_le_sum`, `sum_neg_distrib` | `simp only [prob_mul, energy_add_apply, add_mul, Finset.sum_add_distrib]` | move constants and split sums | M150–M153, M160, M164, M165, M173 |

### Gotchas

- `positivity`, `field_simp` and `gcongr` only see facts in the context. Add `0 < T.toReal`, `kB_pos`, `hZ`, `Real.exp_pos _` and `Real.cosh_pos _` with `have` first. (E115, M162, M167, H096)
- Mathlib has no `hasDerivAt_tanh` and no `Real.continuous_tanh`. Rewrite tanh as `sinh / cosh` with `funext Real.tanh_eq_sinh_div_cosh`. With physlib you also need `import …Trigonometric.DerivHyp`. (M155, H098)
- `probabilityBetaReal` and the other β-real definitions come from `CanonicalEnsemble.Finite`, not `Lemmas`. (H092)
- Never name the anonymous `IsFinite` instances, such as those for `twoState` and `𝓒 + 𝓒'`. Let instance search fill `[...]` arguments. (E116, E120, M173)
- `rw` and `simp_rw` with `h : ∀ b, U b = …` cannot rewrite a bare, unapplied `U`. Use `rw [show U = fun b => … from funext h]`. (M156)
- `gcongr` on `exp (-b * E j) / Z ≤ exp (-b * E i) / Z` picks the wrong pattern and asks for `0 ≤ -b`. Use `div_le_div_iff_of_pos_right` plus `Real.exp_le_exp` instead. (M151)
- Prefer `HasDerivAt.congr_deriv` over `convert … using 1`, which leaves an instance-equality side goal. (M160, H089)
- Before `field_simp`, name the big sums with `generalize e = Z at *`, or it rewrites inside them. Prefer `generalize` to `set`, because `ring` treats a `set` variable and the original term as different atoms. (M161, H089)
- simp writes `-(β*ε)` where a spec has `-β*ε`. Unify the two with `show … by ring` before `generalize`, or `generalize` misses some occurrences. (M161)
- ℕ division `T.N / 2` rounds down. Rewrite it (`omega`) before you cast `T.N` to ℝ. Do not rewrite `N` as `Fintype.card (Fin N)` everywhere, because `rw` also changes the `N` inside `Fin N`. (M159, M167, M170)
- `Set.ncard` is 0 for infinite sets. `QuantaWaveNumber` is a `Set ℝ`, so `haveI : Fintype ↥s := hfin.fintype` before you count dimensions. (M170, H100)
- `Fin T.N` arithmetic wraps mod N: `m + 1 - 1 = m` needs `add_sub_cancel_right`. (M171)
- `Fin.snocEquiv` and `Fin.consEquiv` applied to a pair unfold to `Fin.snoc τ b` or `Fin.cons a σ` only by `show`. (H095, H096)
- `log 0 = 0` and `x / 0 = 0` in Lean. A zero-probability state drops out of `p log p`, and `(log Z_N) / N` is junk at N = 0, which you handle with `Tendsto.congr'`. (H090, H102)
- `x ^ (y : ℝ)` (rpow) and `x ^ (n : ℕ)` are different functions. Gamma-integral formulas use rpow, so bridge them with `Real.rpow_two`. (H091, H093)
- `ring` does not fail when it cannot close a goal. It falls back to `ring_nf`, so inside `first | ring1 | linear_combination hq` use `ring1`, which does fail. (H101)
- `trace (T ^ (n+1))` is not a function of `trace (T ^ n)`. Induct on the whole matrix power. (M166, H102)
- Banned shortcuts are physlib's own versions of the results, such as `twoState_partitionFunction_apply`, `sum_probability_eq_one` (M150), `deriv_*BetaReal`, `fluctuation_dissipation_theorem_finite` (H089), `*_add` (M173) and the `Hₛ`/`Sᵥₙ` max-entropy lemmas (M158). `try?` is banned in M157, M158, M173 and H089 because it runs for minutes.

## Physics with PhysLean (physlib)

physlib (formerly PhysLean) on top of Mathlib. Every problem imports one physlib module rather than
`import Mathlib`; import the module named on the card (below) and `open` the namespaces it lists, or the
notation will not parse. Physics conventions: `c = 1` in relativity, signature (+,−,−,−), indices
`Sum.inl 0` = time and `Sum.inr i` = space axis `i`.

### Imports, opens, notation

| Module (`import Physlib.…`) | Opens | Gives | IDs |
|---|---|---|---|
| `Relativity.Special.ProperTime` | `Lorentz Vector` | `SpaceTime d`, `⟪p, q⟫ₘ`, `SpaceTime.properTime` | E122, M177 |
| `Relativity.Tensors.RealTensor.Vector.Causality.Basic` / `.Vector.MinkowskiProduct` / `.Velocity.Basic` | `Lorentz Vector` | `causalCharacter`; `timeComponent`, `spatialPart`; `Velocity d` | M176, H107, M180 |
| `Relativity.Special.TwinParadox.Basic` | `Lorentz Vector SpecialRelativity` | `InstantaneousTwinParadox`, `causallyFollows` | H108 |
| `Relativity.LorentzGroup.Basic` / `.Boosts.Basic` / `.Boosts.Apply` / `.Orthochronous.Basic` | `LorentzGroup Matrix minkowskiMatrix` (+ `Lorentz Vector` for `•` on vectors) | `LorentzGroup d`, `minkowskiMatrix`, `boost`, `γ`, `IsOrthochronous` | M174, M175, M178, M179, H103–H105 |
| `SpaceAndTime.Space.Derivatives.{Div, Curl, Laplacian}`, `SpaceAndTime.Space.CrossProduct` | `Space` (+ `Matrix` for `⨯ₑ₃`, `InnerProductSpace` for `⟪·,·⟫_ℝ`) | `Space d`, `∂[i]`, `∇`, `∇ ⬝`, `∇ ⨯`, `Δ`, `⨯ₑ₃` | E127, M181–M184, H109 |
| `ClassicalMechanics.HarmonicOscillator.{Basic, Solution}`, `.DampedHarmonicOscillator.Basic`, `.WaveEquation.Basic` | `ClassicalMechanics HarmonicOscillator Time ContDiff InnerProductSpace` | oscillator structures, `Time`, `∂ₜ`, `planeWave` | E123, M185, M192, H110–H113 |
| `Electromagnetism.ThreeDimension.Basic` | `Electromagnetism ElectromagneticPotential Space Time ContDiff` | `ElectromagneticPotential`, `electricField`, `magneticField` | M186, H106 |
| `QuantumMechanics.HarmonicOscillator.OneDimension.TISE` | `QuantumMechanics OneDimension HarmonicOscillator Constants` | QHO, `ℏ`, `eigenValue`, `eigenfunction`, `schrodingerOperator` | E124, H114 |
| `Mathematics.SpecialFunctions.PhysHermite` | `Polynomial` | `physHermite n : ℤ[X]` | M187 |
| `Units.WithDim.Speed` | `Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim WithDim` | `WithDim`, `M𝓭 L𝓭 T𝓭`, `scaleUnit`, `SI`, `SIPrimed` | E125, M188, M189 |
| `Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.{Basic, HyperCharge, BMinusL}` | `SMνCharges SMνACCs SMRHN` | `SMνCharges n`, `PlusU1 n`, `acc*`, `Y`, `BL` | E126, M190, M191, H115 |

| Notation | Means | IDs |
|---|---|---|
| `⟪p, q⟫ₘ` | Minkowski product `p⁰q⁰ − ∑ᵢ pⁱqⁱ` (a bilinear map: `minkowskiProduct p q`) | E122, M176 |
| `⟪x, y⟫_ℝ` / `inner ℝ x y` | real inner (dot) product on `EuclideanSpace ℝ (Fin n)` or `Space d` | M181, M185 |
| `√x` | `Real.sqrt x`, which is `0` for `x < 0` | E122, M177 |
| `∂[i] f x` | `Space.deriv i f x`, partial derivative ∂f/∂xᵢ at `x` | E127, M183 |
| `∇ f`, `∇ ⬝ F`, `∇ ⨯ F` | `Space.grad f`, `Space.div F`, `Space.curl F` | E127, M182 |
| `Δ f`, `Δᵥ F` | scalar Laplacian `Space.laplacian`; vector Laplacian `Space.laplacianVec` (componentwise) | M183, H110 |
| `∂ₜ f t` | `Time.deriv f t = fderiv ℝ f t 1`, d/dt of `f : Time → _` | M185, M192, H111 |
| `a ⨯ₑ₃ b` | cross product on `EuclideanSpace ℝ (Fin 3)` (Mathlib's `⨯₃` lives on `Fin 3 → ℝ`) | M181, M184 |
| `↿f` | uncurried `f`: `fun (t, x) => f t x` | M186 |
| `M *ᵥ v`, `Λ • p` | matrix times vector; Lorentz action on a 4-vector | H103 |
| `ℏ` | `Constants.ℏ : {x : ℝ // 0 < x}`; prints `↑ℏ` in ℝ, `↑↑ℏ` in ℂ | E124, H114 |
| `M𝓭 L𝓭 T𝓭` | the mass, length, time `Dimension`s | E125 |
| `![a, b, …]` | a vector literal `Fin n → α` | E126, M191 |

### Special relativity: 4-vectors

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Lorentz.Vector d`, `SpaceTime d` | `def p : SpaceTime 3 := fun \| Sum.inl 0 => 5 \| Sum.inr 0 => 3 \| Sum.inr _ => 0` | `Fin 1 ⊕ Fin d → ℝ`; `SpaceTime d` is the same type | E122, M175 |
| `minkowskiProduct_toCoord` | `rw [minkowskiProduct_toCoord]; simp [p, Fin.sum_univ_three]` | `⟪p, q⟫ₘ = p (inl 0) * q (inl 0) - ∑ i, p (inr i) * q (inr i)` | E122, M177 |
| `p.timeComponent`, `p.spatialPart` | `example (u : Lorentz.Vector d) : u.timeComponent = u (Sum.inl 0) := rfl` | `p⁰ : ℝ` and `p⃗ : EuclideanSpace ℝ (Fin d)` | M180, H107, H108 |
| `minkowskiProduct_eq_timeComponent_spatialPart`, `…_self_eq_…` | `rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at hu` | `⟪p,q⟫ₘ = p⁰q⁰ − inner ℝ p⃗ q⃗`; `⟪p,p⟫ₘ = ‖p⁰‖^2 − ‖p⃗‖^2` | M180, H107, H108 |
| bilinearity: `map_smul`, `map_add`, `map_sub`, `minkowskiProduct_symm` | `simp [map_add, minkowskiProduct_symm v u]; ring` | pull scalars, expand `⟪u+v, u+v⟫ₘ`; `symm : ⟪p, q⟫ₘ = ⟪q, p⟫ₘ` | M176, M180, H108 |
| `(r • q).spatialPart = r • q.spatialPart` | `change p.spatialPart = (a / b) • q.spatialPart` | holds by `rfl`; time part is `r * q.timeComponent` | H107 |
| 4-vector extensionality | `funext μ; match μ with \| Sum.inl 0 => exact h0 \| Sum.inr i => exact congrArg (· i) hs` | prove `p = q` by components | M180, H107 |
| `causalCharacter p` | `unfold causalCharacter; rw [h]; by_cases h0 : ⟪p, p⟫ₘ = 0` | `if ⟪p,p⟫ₘ = 0 then .lightLike else if 0 < ⟪p,p⟫ₘ then .timeLike else .spaceLike` | M176 |
| `timeLike_iff_norm_sq_pos`, `lightLike_iff_norm_sq_zero` | `((timeLike_iff_norm_sq_pos _).mp h1).le` | causal character as the sign of `⟪p, p⟫ₘ` | H108 |
| `causallyFollows p q` | `rcases h with ⟨h1, h2⟩ \| ⟨h1, h2⟩` | `q − p` timelike with `0 < (q−p)⁰`, or lightlike with `0 ≤ (q−p)⁰` | H108 |
| `SpaceTime.properTime q p` | `rw [SpaceTime.properTime, sub_zero, minkowski_p]` | `√⟪p - q, p - q⟫ₘ` (unfold with `rw`/`unfold`) | E122, M177, H108 |
| `InstantaneousTwinParadox`, `.ageGap`, `.properTimeTwinA/B` | `unfold InstantaneousTwinParadox.ageGap InstantaneousTwinParadox.properTimeTwinA …` | fields `startPoint`, `twinBMid`, `endPoint`, causality proofs `twinBMid_causallyFollows_startPoint` | H108 |
| `Velocity d`, `Velocity.ext` | `ext1; exact sub_eq_zero.mp hw` | a `Set (Lorentz.Vector d)` with `⟪u,u⟫ₘ = 1`, `u⁰ > 0`; `u.1` is the vector; `simp` proves `⟪u.1, u.1⟫ₘ = 1` | M180 |

### Lorentz group and boosts

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `LorentzGroup d`, `Λ.1` | `Λ.1 (Sum.inl 0) (Sum.inl 0)` | subtype of matrices over `Fin 1 ⊕ Fin d`; `Λ.1` is the matrix, `Λ⁰₀` the entry above | M178, M179 |
| `transpose_mul_minkowskiMatrix_mul_self`, `mul_minkowskiMatrix_mul_transpose` | `congrArg Matrix.det (transpose_mul_minkowskiMatrix_mul_self (Λ := Λ))` | `Λᵀ η Λ = η`, `Λ η Λᵀ = η`; `Λ` is implicit | M178, M179, H105 |
| `minkowskiMatrix.det_eq_neg_one_pow_d`, `Matrix.det_mul`, `Matrix.det_transpose` | `simp only [det_mul, det_transpose, det_eq_neg_one_pow_d] at h` | `det η = (-1)^d` | M178 |
| `minkowskiMatrix.as_diagonal` + `Matrix.diagonal_apply`, `Matrix.mul_apply`, `Fintype.sum_sum_type` | `simp [Matrix.mul_apply, Fintype.sum_sum_type, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply] at hc` | expand an entry of a product over `Fin 1 ⊕ Fin d`; `η = diagonal (Sum.elim 1 (-1))` | M179, H105 |
| entry of a matrix equation | `congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)` | `M = N → M i j = N i j` | M179, H104 |
| `lorentzGroupIsGroup_mul_coe` | `simp only [lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type]` | coercion of `Λ * Λ'` is the matrix product | H104, H105 |
| `LorentzGroup.boost i β hβ` | `boost i β hβ • p` | boost along spatial axis `i` at speed `β`, needs `hβ : \|β\| < 1` | M174, M175, H103 |
| `LorentzGroup.γ`, `γ_sq`, `γ_det_not_zero` | `unfold γ`; `rw [γ_sq β hβ]; field_simp` | `γ β = 1 / √(1 - β ^ 2)`; `γ β ^ 2 = 1 / (1 - β ^ 2)`; `1 - β ^ 2 ≠ 0` | M174, M175, H103 |
| `boost_inl_0_inl_0` | `rw [boost_inl_0_inl_0]` | `Λ⁰₀` of a boost is `γ β` | M174 |
| `Lorentz.Vector.boost_time_eq`, `boost_inr_self_eq` | `rw [boost_time_eq, boost_inr_self_eq]; ring` | `(Λp)⁰ = γ(t − βxᵢ)`, `(Λp)ⁱ = γ(xᵢ − βt)` | M175 |
| `Lorentz.Vector.boost_toCoord_eq` | `rw [boost_toCoord_eq, boost_toCoord_eq, boost_toCoord_eq]` | full coordinate formula as a `match` with an `if j = i` | H103 |
| `LorentzGroup.eq_of_mulVec_eq`, `Lorentz.Vector.smul_eq_mulVec` | `apply eq_of_mulVec_eq; intro x; rw [← Lorentz.Vector.smul_eq_mulVec]` | two Lorentz matrices agree if they agree on all vectors; `Λ • p = Λ.1 *ᵥ p` | H103 |
| `SemigroupAction.mul_smul` | `SemigroupAction.mul_smul _ _ _` | `(Λ * Λ') • p = Λ • Λ' • p` | H103 |
| `boost_transpose_matrix_eq_self` | `congrFun (congrFun (boost_transpose_matrix_eq_self k hβ) (Sum.inr i)) (Sum.inr j)` | pure boosts are symmetric matrices | H104 |
| `boost_inr_other_inr`, `boost_inr_self_inr_other`, `boost_inr_other_inl_0` | `simp [boost_inr_other_inr h₂ hij, hij]` | off-axis rows are the identity's; the `(inl 0, ·)`/`(·, inl 0)` entries on axis `i` are `@[simp]` | H104 |
| `IsOrthochronous Λ` | `unfold IsOrthochronous at *` | `0 ≤ Λ.1 (Sum.inl 0) (Sum.inl 0)` | H105 |

### Vector calculus on `Space`

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Space d` (`Space` = `Space 3`), `x.val i` / `x i`, `basis.repr y` | `(∇ ⬝ (fun y : Space d => basis.repr y)) x = d` | a point; `basis.repr y : EuclideanSpace ℝ (Fin d)` is `y` as a vector ("x ↦ x") | E127, M184, H109 |
| `Space.basis_repr_apply` | `simp only [Space.basis_repr_apply, Space.deriv_component, if_true]` | `(basis.repr p) i = p.val i` | E127, M184 |
| `Space.div` | `rw [Space.div]` / `unfold Space.div` | `(∇ ⬝ F) x = ∑ i, ∂[i] (fun y => F y i) x` (rfl) | E127, H106, H109 |
| `Space.curl`, `Space.grad` | `unfold Space.curl Space.grad; ext i` / `simp [curl, cross_apply]` | `(∇ ⨯ F) x 0 = ∂[1] (fun y => F y 2) x - ∂[2] (fun y => F y 1) x`; indices wrap mod 3 | M182, M184, H106 |
| `Space.laplacian_eq_sum_snd_deriv` | `rw [laplacian_eq_sum_snd_deriv]` | `Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x`; `Δᵥ F x j = Δ (fun y => F y j) x` (rfl) | M183, H110 |
| `Space.deriv_eq`, `Space.deriv_eq_fderiv_fun` | `rw [Space.deriv_eq, fderiv_const_mul (by fun_prop)]; simp [← Space.deriv_eq]` | `∂[μ] f x = fderiv ℝ f x (basis μ)`; the `fun` form lets `fun_prop` see a partial derivative | M183, M184, H106 |
| `Space.deriv_component`, `deriv_component_same` | `∂[ν] (fun x => x.val μ) x = if ν = μ then 1 else 0` | derivative of a coordinate; `= 1` on the diagonal | E127, M183, H109 |
| `Space.deriv_norm_sq`, `Space.norm_sq_eq` | `exact deriv_norm_sq y i` | `∂[i] (‖·‖^2) x = 2 * x.val i`; `‖p‖ ^ 2 = ∑ i, p i ^ 2` | M183, H109, H110 |
| `Space.deriv_smul` | `change ∂[i] ((fun y => (‖y‖ ^ 3)⁻¹) • fun y => y i) x = _; rw [Space.deriv_smul hc hf]` | product rule `∂[u](c • f) = c • ∂[u] f + ∂[u] c • f` | H109 |
| `Space.deriv_euclid` | `exact Space.deriv_euclid hF y` | `Differentiable f → ∂[ν] (fun x => f x μ) x = ∂[ν] f x μ` | H110 |
| `Space.deriv_commute` | `rw [deriv_commute _ (hc 0)]` | Schwarz: `ContDiff ℝ 2 f → ∂[u] (∂[v] f) = ∂[v] (∂[u] f)` (banned in M182) | H106 |
| `IsSymmSndFDerivAt`, `fderiv_clm_apply` | `(hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _` | Mathlib symmetry of the 2nd Fréchet derivative; prove Schwarz for `∂[i]` yourself | M182 |
| `contDiff_euclidean` | `contDiff_euclidean.mp hf w` | `ContDiff ℝ n F ↔ ∀ i, ContDiff ℝ n (fun x => F x i)` | H106 |
| `Space.curl_of_grad_eq_zero`, `fun_curl_sub`, `fun_curl_neg` | `rw [fun_curl_sub, fun_curl_neg, curl_of_grad_eq_zero]` | `curl (∇ f) = 0` (C²); curl is linear (Differentiable side goals) | M186 |
| `a ⨯ₑ₃ b`, `cross_apply` | `simp [Fin.sum_univ_three, cross_apply]` | `a ⨯₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]` | M181, M184 |
| `PiLp.inner_apply` + `Fin.sum_univ_three` | `simp only [PiLp.inner_apply]` | dot product on ℝ³ as a sum of components | M181 |
| vector equation by components | `ext i; fin_cases i <;> simp [curl, cross_apply, basis_repr_apply] <;> ring` | split `EuclideanSpace ℝ (Fin 3)` goals into `i = 0, 1, 2` | M182, M184 |

### Derivative toolkit (Mathlib, as used here)

| API | Example | Gloss | IDs |
|---|---|---|---|
| `fderiv_const_mul`, `fderiv_fun_sub`, `fderiv_fun_add`, `fderiv_fun_const_smul` | `rw [fderiv_fun_sub (by fun_prop) (by fun_prop), fderiv_const_mul (by fun_prop)]` | linearity of `fderiv` on lambdas (`DifferentiableAt` side goals) | M183, M184, H106, H111 |
| `_root_.sub_apply`, `_root_.smul_apply`, `_root_.add_apply` | `simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]` | evaluate a sum/difference of linear maps | M184, H111 |
| `fderiv_comp` + `change … (g ∘ fun τ => …) …` | `change fderiv ℝ (g ∘ fun τ : Time => a - c * τ.val) t 1 = _` | chain rule; the function must literally be a composition | H110, M192 |
| `fderiv_eq_smul_deriv`, `fderiv_apply_one_eq_deriv` | `rw [← fderiv_apply_one_eq_deriv]` | `fderiv ℝ f x y = y • deriv f x`; `fderiv 𝕜 f x 1 = deriv f x` | H110, M192 |
| `fderiv_inner_apply ℝ` | `fderiv_inner_apply ℝ hd hd` | product rule for `t ↦ ⟪f t, g t⟫` (`ℝ` explicit) | H110, H111 |
| `ContinuousLinearEquiv.fderiv` | `rw [fderiv_comp _ (hE _) Time.toRealCLE.symm.differentiableAt, ContinuousLinearEquiv.fderiv]` | `fderiv e x = e` | M192 |
| `hasStrictFDerivAt_norm_sq`, `HasFDerivAt.sqrt`, `HasFDerivAt.fderiv` | `(hasStrictFDerivAt_norm_sq x).hasFDerivAt` | fderiv of `‖·‖^2` is `(2 : ℕ) • innerSL ℝ x`; `.fderiv` turns a fact into a rewrite | H109 |
| `HasDerivAt.comp_hasFDerivAt`, `HasDerivAt.fun_inv`, `hasDerivAt_pow` | `hg.comp_hasFDerivAt x hd.hasFDerivAt` | scalar `g : ℝ → ℝ` after `f : Space → ℝ`; state the composite as a lambda | H109 |
| `DifferentiableAt.norm` | `DifferentiableAt.norm ℝ differentiableAt_id hx` | `‖·‖` is differentiable at `x ≠ 0` (`𝕜` explicit) | H109 |
| `iteratedDeriv_succ`, `iteratedDeriv_one`, `ContDiff.differentiable_iteratedDeriv` | `rw [iteratedDeriv_succ, iteratedDeriv_one]` | `iteratedDeriv 2 f = deriv (deriv f)` | H110 |
| `deriv_comp`, `Complex.deriv_exp`, `Complex.deriv_ofReal` | `rw [show (fun x : ℝ => Complex.exp (g x)) = Complex.exp ∘ g from rfl, deriv_comp _ (by fun_prop) (by fun_prop)]` | chain rule for `ℝ → ℂ`; `deriv (↑) x = 1` | H114 |
| `deriv_const_mul_field'`, `deriv_fun_mul`, `deriv_div_const`, `deriv.fun_neg'` | `rw [deriv_const_mul_field']; dsimp only` | pull constants, product rule, peel `/ c` and `-` | H114 |
| `is_const_of_fderiv_eq_zero (𝕜 := ℝ)` | `apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (by fun_prop)` | zero derivative everywhere ⇒ constant | H111 |
| `antitone_of_deriv_nonpos` | `antitone_of_deriv_nonpos hg hderiv ((Time.le_def _ _).mp ht)` | `f : ℝ → ℝ`, differentiable, `deriv ≤ 0` ⇒ `Antitone f` | M192 |
| `fun_prop` | `all_goals fun_prop` | discharges `Differentiable`/`ContDiff`/`DifferentiableAt` side goals | M183, M186, H106 |

### Time and classical mechanics

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `Time`, `t.val`, `Time.le_def`, `Time.eq_one_smul` | `rw [p.eq_one_smul, map_smul, ← Time.deriv_eq]` | structure over one real; `t = t.val • 1`, so a linear map on `Time` is fixed by its value at `1` | M192, H111 |
| `Time.deriv_eq` | `rw [Time.deriv_eq]` | `∂ₜ f t = fderiv ℝ f t 1` (rfl) | M192, H110, H112 |
| `Time.toRealCLE` | `let g : ℝ → ℝ := S.energy x ∘ Time.toRealCLE.symm` | `Time ≃L[ℝ] ℝ`; carry a `Time` function to `ℝ → ℝ` | M192 |
| `Time.deriv_smul`, `Time.deriv_differentiable_of_contDiff` | `Time.deriv_differentiable_of_contDiff x hx` | pull a scalar out of `∂ₜ`; smooth ⇒ `∂ₜ x` differentiable | H110, H111, H112 |
| `ClassicalMechanics.HarmonicOscillator` | `rw [HarmonicOscillator.ω_sq]; field_simp [S.m_ne_zero]` | fields `S.m S.k`, `S.m_pos`, `S.k_pos`; `S.ω = √(S.k / S.m)`; `ω_sq`, `ω_pos`, `ω_ne_zero`, `m_ne_zero`, `k_ne_zero` | E123, M185, H113 |
| `energy`, `kineticEnergy`, `potentialEnergy` (+ `_eq`, `_differentiable`) | `simp only [energy, kineticEnergy, potentialEnergy]` | `½ m ⟪ẋ,ẋ⟫_ℝ + (1/2) • k • ⟪x,x⟫_ℝ` on `x : Time → EuclideanSpace ℝ (Fin 1)` | M185, H111, H112 |
| `equationOfMotion_iff_newtons_2nd_law`, `force_eq_linear` | `rw [S.equationOfMotion_iff_newtons_2nd_law _ hx] at h` | for smooth `x`, variational EOM ↔ `∀ t, S.m • ∂ₜ (∂ₜ x) t = S.force (x t)`; `S.force x = -S.k • x` | H111, H112 |
| `energy_conservation_of_equationOfMotion'` | `rw [S.energy_conservation_of_equationOfMotion' y (hx.sub hT) hEOM]` | smooth + EOM ⇒ `S.energy x t = S.energy x 0` (banned in H111) | H112 |
| `InitialConditions`, `trajectory_eq`, `trajectory_velocity`, `trajectory_equationOfMotion` | `rw [InitialConditions.trajectory_velocity]` | `IC.x₀`, `IC.v₀`; `x(t) = cos(ωt)•x₀ + (sin(ωt)/ω)•v₀`, velocity `-ω•sin(ωt)•x₀ + cos(ωt)•v₀` | M185, H112, H113 |
| `DampedHarmonicOscillator` | `S.energy_dissipation_rate x _ h hx` | adds `S.γ`, `S.γ_nonneg`; `∂ₜ (S.energy x) t = -S.γ * ⟪∂ₜ x t, ∂ₜ x t⟫_ℝ` | M192 |
| `planeWave`, `planeWave_eq`, `WaveEquation`, `Direction` | `rw [WaveEquation, laplacianVec_planeWave …, sub_self]` | `planeWave f₀ c s t x = f₀ (⟪x, s.unit⟫_ℝ - c * t.val)`; `WaveEquation f t x c ↔ c ^ 2 • Δᵥ (f t) x - ∂ₜ (∂ₜ f) = 0`; `s.norm : ‖s.unit‖ = 1` | H110 |
| inner-product algebra | `simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm IC.x₀ IC.v₀]` | expand `⟪a • x + b • y, …⟫_ℝ`; then `real_inner_self_eq_norm_sq` | M181, M185, H113 |
| `real_inner_self_nonneg`, `real_inner_self_pos`, `inner_self_eq_zero` | `real_inner_self_pos.mpr h` | `0 ≤ ⟪x,x⟫_ℝ`; `0 < ⟪x,x⟫_ℝ ↔ x ≠ 0` | M192, H112, H113 |
| `Real.cos_eq_one_iff`, `Real.sin_int_mul_pi`, `Real.sin_sq_add_cos_sq` | `linear_combination (‖v₀‖ ^ 2 + ω ^ 2 * ‖x₀‖ ^ 2) * Real.sin_sq_add_cos_sq (S.ω * t.val)` | `cos x = 1 ↔ ∃ n : ℤ, ↑n * (2π) = x`; `sin (n π) = 0` | M185, H113 |

### Electromagnetism

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `ElectromagneticPotential`, `SpeedOfLight` | `(c : SpeedOfLight) (V : ElectromagneticPotential) (hV : ContDiff ℝ ∞ V)` | a 4-potential `(φ, A)` on spacetime; `c` a positive constant | M186, H106 |
| `V.electricField c t`, `V.magneticField c t` | `(∇ ⨯ V.electricField c t) x` | fields `Space → EuclideanSpace ℝ (Fin 3)` at time `t` | M186, H106 |
| `ThreeDimension.electricField_eq_3D`, `magneticField_eq_3D` | `rw [ThreeDimension.magneticField_eq_3D]` | `E = -∇φ - ∂ₜA`, `B = ∇ × A` as rewrites | M186, H106 |
| `Space.time_deriv_curl_commute` | `rw [time_deriv_curl_commute]` | `ContDiff ℝ 2 ↿fₜ → ∂ₜ` commutes with `curl` | M186 |
| Lorentz force | `rw [real_inner_smul_right, inner_add_right, h, add_zero]` | `⟪v, v ⨯ₑ₃ B⟫_ℝ = 0`, so `v · F = q (v · E)` | M181 |

### Quantum mechanics

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `QuantumMechanics.OneDimension.HarmonicOscillator` | `unfold HarmonicOscillator.eigenValue; push_cast; ring` | `Q.m`, `Q.ω`; `Q.eigenValue n = (n + 1/2) * ℏ * Q.ω` | E124, H114 |
| `Q.ξ`, `ξ_sq`, `ξ_ne_zero`, `ℏ_ne_zero` | `rw [← Complex.ofReal_pow, ξ_sq]; push_cast` | length scale `ξ = √(ℏ / (m ω))`, `ξ² = ℏ / (m ω)` | H114 |
| `eigenfunction_zero` | `rw [eigenfunction_zero]` | `ψ₀ = fun x => 1/√(√π * ξ) * Complex.exp (-x^2/(2 * ξ^2))`, `ψ : ℝ → ℂ` | H114 |
| `schrodingerOperator_eq_ξ` | `rw [schrodingerOperator_eq_ξ]; simp only` | `H ψ x = ℏ²/(2m) * (-ψ'' x + (1/ξ²)² x² ψ x)` | H114 |
| `Complex.ofReal_ne_zero` | `have hm := Complex.ofReal_ne_zero.mpr Q.m_ne_zero` | `≠ 0` facts in ℂ for `field_simp` | H114 |
| `Polynomial.physHermite`, `physHermite_succ`, `physHermite_one` | `rw [physHermite_succ (n + 1), derivative_sub, derivative_mul, ih, physHermite_succ n]` | `H_{n+1} = 2 • X * H_n - derivative H_n` in `ℤ[X]` | M187 |
| `derivative_mul`, `derivative_sub`, `derivative_X`, `nsmul_eq_mul` | `simp; ring` | formal derivative rules; `simp` kills derivatives of numerals/casts | M187 |

### Units and dimensions

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `WithDim d ℝ`, `x.1`/`x.val`, `⟨a⟩`, `WithDim.cast` | `p = cast (m * v)` | a real tagged with a dimension; `cast` retypes between equal dimensions (`M𝓭 * (L𝓭 * T𝓭⁻¹)` to `M𝓭 * L𝓭 * T𝓭⁻¹`) | E125, M189 |
| `scaleUnit u1 u2 x`, `LTMCTUnitChoices`, `SI`, `SIPrimed` | `use SI, SIPrimed, ⟨1⟩, ⟨1⟩, ⟨c⟩` | convert `x` from unit system `u1` to `u2`; `SIPrimed` scales length, time, mass by 2, 3, 5 | E125, M189 |
| `IsDimensionallyCorrect f`, `isDimensionallyCorrect_fun_iff` | `rw [isDimensionallyCorrect_fun_iff]; intro u1 u2 m; funext v p` | `∀ u1 u2, scaleUnit u1 u2 f = f`; `_fun_iff` peels off one argument | E125, M188, M189 |
| `scaleUnit_apply_fun(_left)`, `DMul.hMul_scaleUnit`, `WithDim.cast_scaleUnit`, `scaleUnit_injective` | `rw [DMul.hMul_scaleUnit, cast_scaleUnit, scaleUnit_injective]` | move rescaling through application, `*`, `cast`, `=` (`_left`: codomain not rescaled, e.g. `Prop`) | E125 |
| `WithDim.scaleUnit_val`, `withDim_hMul_val`, `dimScale`, `dimScale_pos`, `dimScale_apply` | `simp only [WithDim.scaleUnit_val, WithDim.withDim_hMul_val, map_mul, map_inv, NNReal.smul_def, NNReal.coe_mul, NNReal.coe_inv]` | `(scaleUnit u1 u2 m).val = u1.dimScale u2 d • m.val`; `dimScale : Dimension →* NNReal` | M188, M189 |
| raw-number relation | `simp [funext_iff, KineticEnergy]` then `field_simp at h; linear_combination h / 2` | when the relation is on `.1` values, track the scale factors yourself | M188 |

### Anomaly cancellation (SM + right-handed neutrinos)

| Construct / API | Example | Gloss | IDs |
|---|---|---|---|
| `(SMνCharges n).Charges`, `toSpecies j`, `Q S i` | `def Y : (SMνCharges 1).Charges := ![1, -4, 2, -3, 6, 0]` | rational charges of 6 species `Q U D L E N` × `n` families; `Q = toSpecies 0`, …, `N = toSpecies 5` | E126 |
| `accGrav`, `accSU2`, `accSU3`, `accYY`, `accQuad`, `accCube` + `_decomp` | `rw [accGrav_decomp]; simp only [sum_one, toSpecies_one]; simp [Y]` | the six ACCs as sums over families per species | E126, M190, M191 |
| `SMνCharges.sum_one`, `toSpecies_one` | `simp only [sum_one, toSpecies_one] at hG h2 h3 hY` | one family: collapse a family sum to the plain entry `S j` | E126, M190 |
| `PlusU1 n`, `LinSols`, `QuadSols`, `Sols`, `IsSolution` | `refine ⟨PlusU1.chargeToAF S ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩` | `IsSolution χ T := ∃ sol : χ.Sols, sol.val = T`; `chargeToAF` takes six ACC proofs | M190, M191, H115 |
| `PlusU1.gravSol`, `SU2Sol`, `SU3Sol`, `YYsol`, `quadSol`, `cubeSol`, `linearToAF` | `PlusU1.linearToAF (a • S.1.1 + b • (PlusU1.Y n).1.1) ?_ ?_` | ACC facts carried by a solution; `S.1.1 : LinSols`; build `Sols` from `LinSols` + quad + cube | M190, H115 |
| `PlusU1.Y₁`, `BL₁`, `PlusU1.Y n`, `Y_val`, `familyUniversal` | `rw [quadBiLin_decomp, accYY_decomp, PlusU1.Y_val]` | one-family `Y = (1,−4,2,−3,6,0)`, `B−L = (1,−1,−1,−3,3,3)`; `Y n` copies `Y₁` to every family | M190, H115 |
| `toSpeciesEquiv.symm g`, `toSMSpecies_toSpecies_inv` | `simp only [leptonFlavour, toSMSpecies_toSpecies_inv]` | build a charge vector from `g j f`; `toSpecies j (toSpeciesEquiv.symm g) = g j` | M191 |
| `quadBiLin`, `cubeTriLin`, `toHomogeneousQuad_add`, `toCubic_add` | `change quadBiLin.toHomogeneousQuad (a • S + b • Y) = 0; rw [BiLinearSymm.toHomogeneousQuad_add]` | `accQuad = quadBiLin.toHomogeneousQuad`; `q(S+T) = qS + qT + 2B(S,T)`; cubic: `+ 3τSST + 3τTTS` | H115 |
| `HomogeneousQuadratic.map_smul`, `HomogeneousCubic.map_smul`, `BiLinearSymm.map_smul₁/₂`, `swap`, `TriLinearSymm.map_smul₁/₂/₃`, `swap₃` | `rw [TriLinearSymm.swap₃ cubeTriLin S S]` | `f (a • S) = a^2 * f S` / `a^3 * f S`; scalars out of a slot; symmetry | H115 |
| `sum_familyUniversal_two`, `_three` | `repeat rw [sum_familyUniversal_two]` | pull a family-universal factor out of a sum over families | H115 |
| entrywise vector proof | `funext j; match j with \| ⟨0, _⟩ => change S.val (0 : Fin 6) = (…) * 1 + (…) * 1; linarith` | `change` exposes concrete entries of `Y₁`, `BL₁` | M190 |

### Gotchas

- `⟪p, q⟫ₘ` needs `open Lorentz Vector`, and that `open` makes `mul_smul`, `smul_eq_mulVec` ambiguous: write
  `SemigroupAction.mul_smul`, `Lorentz.Vector.smul_eq_mulVec`, or use `smul_smul`. (H103, H107)
- `open minkowskiMatrix` makes bare `sq` mean `minkowskiMatrix.sq` (`η * η = 1`); `simp only [sq]` then makes no
  progress. Write `_root_.sq` or `pow_two`. (M179, H105)
- Reading off a concrete 4-vector: `rw [minkowskiProduct_toCoord]` first, then `simp [p, …]`; `norm_num [p]`
  sticks on `p`'s `match`. (E122)
- `√` of a negative is `0`: time dilation needs `0 < Δt`, not `0 ≤`, else spacelike separation gives
  `√(negative) = 0 = Δt`. (M177)
- `_self_` Minkowski lemma writes `p⁰²` as `‖p⁰‖ ^ 2`; clear with `simp only [Real.norm_eq_abs, sq_abs] at h`. (M180, H107)
- `transpose_mul_minkowskiMatrix_mul_self` has `Λ` implicit: pass `(Λ := Λ)` in a `have`. (M178, M179)
- Boost entries: unfolding `simp [boost, …]` leaves nested `if`s whose shape depends on `hij` vs
  `Ne.symm hij`; use `boost_inr_other_inr` and friends. Run `simp only [if_true]` before `linear_combination`. (H103, H104)
- Two `HarmonicOscillator`s: `ClassicalMechanics.HarmonicOscillator` (E123, M185, H111–H113) and
  `QuantumMechanics.OneDimension.HarmonicOscillator` (E124, H114); the `open` line decides which one you get.
- `ℏ` is a subtype: it shows as `↑ℏ` in ℝ and `↑↑ℏ` in ℂ; `push_cast` before `ring`/`field_simp`. (E124, H114)
- Rewrite `∂ₜ (IC.trajectory S)` with `trajectory_velocity` before unfolding `IC.trajectory S` with
  `trajectory_eq`, or the derivative no longer matches. (M185)
- `antitone_of_deriv_nonpos` wants `ℝ → ℝ`; a `Time` function goes through `Time.toRealCLE.symm`, and
  `Time.toRealCLE.symm 1 = 1` is proved by `ext; simp [Time.toRealCLE, Time.one_val]`, not `rfl`. (M192)
- `potentialEnergy` uses `•` on reals: `simp only [potentialEnergy_eq, smul_eq_mul, ← mul_assoc]` before
  `fderiv_const_mul` will match. (H111)
- Chain rules need the literal shape: `change … (g ∘ fun τ => …) …` before `fderiv_comp` (H110); state the
  composite as a lambda for `comp_hasFDerivAt` (H109); `show (fun x => exp (g x)) = exp ∘ g from rfl` before
  `deriv_comp` (H114). Use `fderiv_fun_const_smul`, not `fderiv_const_smul`, on a lambda (H110).
- In `hasStrictFDerivAt_norm_sq` the `2` is a ℕ-scalar: write `(2 : ℕ) • innerSL ℝ x`. (H109)
- `rw [h]` with a conditional `h : P → a = b` leaves `P` as a later goal: rewrite first, then
  `all_goals fun_prop`. (M186)
- Anomaly charges: the index type of `(PlusU1 1).Charges` / `(SMνCharges 1).Charges` has no numerals, so
  `Y 0` fails; write `S.val (0 : Fin 6)`. Apply `sum_one`, `toSpecies_one` before `simp [Y]` (unfolding
  `Y` first blocks them). (E126, M190)
- The `_decomp` sums run over `Fin (SMνSpecies n).numberCharges`, which is `Fin n` only after unfolding:
  restate `hx` with `have hx' : ∑ f : Fin (SMνSpecies n).numberCharges, x f = 0 := hx`. (M191)
- `(PlusU1 n).Charges` is a synonym of `(SMνCharges n).Charges` that `rw` and `+` do not see through: state
  helper lemmas over `(SMνCharges n).Charges`, and `change` the goal into `toHomogeneousQuad`/`toCubic` form. (H115)
- Many cards ban the physlib lemma that states the result outright (e.g. `curl_of_grad_eq_zero`,
  `deriv_commute` in M182; `trajectory_energy` in M185; `planeWave_waveEquation` in H110), along with
  `exact?`/`apply?`/`try?`: the point is to do the calculation.

## Cheatsheet

The items used most across all 434 Lean problems. The full rows are in the sections above.

### Core tactics

| Write | Does | IDs |
|---|---|---|
| `intro h` / `exact h` / `apply h` | assume; close the goal with a term; work backwards (one goal per premise) | E003 |
| `constructor` / `⟨hp, hq⟩` / `use 3` (core: `exists 3`) / `left`, `right` | build `∧`, `↔`, `∃`, `∨` | E004–E007 |
| `obtain ⟨r, rfl⟩ := h` / `rintro (⟨hp, hq⟩ \| ⟨hp, hr⟩)` | take apart `∧ ∃ ∨`; the `rfl` pattern substitutes | E005, E006, E025 |
| `refine ⟨?_, ?_⟩ <;> simp [h]` / `all_goals t` / `first \| rfl \| omega` | each `?_` becomes a goal; run a tactic on every goal | E031 |
| `have h : T := …` / `suffices hs : … by omega` / `show T'` / `calc a < b := h1` then `_ ≤ c := h2` | intermediate fact (write its type); prove the goal from `hs` first; restate the goal up to defeq; chain relations | E020, E021 |
| `rw [h, ← h'] at h1 ⊢` / `nth_rw 1 [h]` | rewrite left to right / right to left, in hypotheses; only the k-th match | E009, E061 |
| `simp only [l]` / `simp [f] at h` / `simp_all` / `simpa using h` | simplify with exactly `l` / also unfold `f` / everywhere / simplify, then close with `h` | E010, E050, E059 |
| `unfold f at *` / `split` / `split at h` | expose a `def`; one goal per `if`/`match` arm in the goal / in `h` | E012, E030, M034 |
| `conv in _ * 1 => rw [Nat.mul_one]` / `simp_rw [h]` | rewrite under binders (`fun`, `∀`, `∑`), where `rw` fails | E061, E064 |
| `funext x` / `ext i j` / `congr` | function, set or matrix equality pointwise; split `f a = f b` into argument equations | E022, E074 |
| `rfl` / `decide` | closed computation; well-founded defs do not reduce, so use `simp [f]` / `rw [f]` | E001, E026, E079 |
| `omega` | linear ℕ/ℤ arithmetic, including truncated `-` and `/`, `%` by literals; `x*y` and `2^n` are atoms | E011 |
| `grind` | congruence, linear arithmetic, ring normalisation, `if` splits; no induction | E028 |
| `by_cases h : p` / `Classical.byContradiction` / `by_contra! h` / `contrapose! h` | classical case split; proof by contradiction (`!` pushes the negation in) | E013, E058, E065 |
| `exact?` / `apply?` | search the library; paste the printed `Try this:` | E033 |

### Induction, recursion, inductive relations

| Write | Does | IDs |
|---|---|---|
| `induction n generalizing acc with \| zero => … \| succ k ih => …` | IH that holds for every accumulator | E014, E085 |
| `induction n, hn using Nat.le_induction` / `induction q using Nat.strong_induction_on with \| _ q ih => …` | induction from a base `n₀ ≤ n` / strong induction (infinite descent) | E089, H030 |
| `fun_induction f x with \| case1 … \| case2 n ih => …` | induction that follows `f`'s recursion, one IH per recursive call | E084 |
| `termination_by xs.length` + `decreasing_by simp only [List.length_cons]; omega` | well-founded recursion; unfold it with `rw [f]` / `f.eq_2` | E026, M017 |
| `induction h with \| refl e => … \| step s _ ih => …` | rule induction on an inductive Prop, one case per constructor | M004, H001 |
| `cases h` | inversion: only rules whose conclusion unifies survive; if none survive, the goal closes | M004, H020 |
| `generalize hw : Com.while b c = w at h` | turn a non-variable index into a variable before `induction h` | M045, H021 |
| `induction h1 generalizing e2 <;> cases h2 <;> simp_all` | determinism of an inductive relation | M040, H021 |
| `induction a using h.induction with \| _ a ih => …` | well-founded induction for `h : WellFounded r` | H004 |

### Mathlib automation

| Write | Does | IDs |
|---|---|---|
| `ring` / `ring_nf` / `abel` / `group` | commutative ring / additive group / any group identities; they ignore hypotheses | E034, E093 |
| `linarith [sq_nonneg (a - b)]` / `nlinarith [..]` | linear consequences of the hypotheses plus hints; `nlinarith` also multiplies pairs | E035, E068 |
| `linear_combination e * h` | equation that is a ring combination of hypotheses; no order needed (works in ℂ) | E067, M117 |
| `norm_num` | numerals: `⁻¹`, `%`, `Nat.Prime 97`, `(6 : ℤ) ∣ 42` | E036, E043 |
| `positivity` | only `0 < e`, `0 ≤ e`, `e ≠ 0`, read off the syntax of `e` | E037 |
| `gcongr` / `gcongr with i hi` | `f a ≤ f b` from `a ≤ b`, also term by term in `∑`/`∏` | E044, E071 |
| `field_simp` then `ring` | clear denominators; needs the `≠ 0` facts in context; `generalize √D = s` first | E045, M124 |
| `push_cast` / `exact_mod_cast h` / `zify [h]` / `lift x to ℕ using hx` | move between ℕ, ℤ, ℝ; `h : b ≤ a` makes `↑(a - b) = ↑a - ↑b` | E063, E092 |
| `fin_cases i <;> simp` / `interval_cases n <;> norm_num` | one goal per value of `i : Fin n` / per value between bounds | E072, E094 |
| `fun_prop (disch := norm_num)` | `Continuous`, `Differentiable`, integrability side goals | E075, M186 |
| `choose g hg using h` | turn `∀ x, ∃ y, P x y` into a function `g` and `hg : ∀ x, P x (g x)` | E090 |
| `tauto` / `aesop (add norm Set.subset_def)` | propositional tautologies / general search | E091 |

### Terms and syntax

| Write | Does | IDs |
|---|---|---|
| `fun ⟨hp, hq⟩ => ⟨hq, hp⟩` / `h.1`, `h.mp` / `h1.trans h2` | anonymous constructor; projections; dot notation (`h.f` = `T.f h`) | E004, E046 |
| `congrArg f h` / `congrFun h a` / `h ▸ e` / `h.symm` | apply to both sides; specialise a function equality; transport along `=` | E046, E051 |
| `funext fun x => propext (h x)` | equal predicates from a pointwise `↔` | M011, H003 |
| `Quotient.lift₂ f (by …)` / `Quotient.sound` / `Quotient.exact` | functions and equalities on a quotient (must respect `≈`) | E081, H007 |
| `open X in` / `open scoped Kronecker` / `_root_.sq` | local open; scoped notation; escape a shadowing name | E056, E111, H105 |

### Library APIs by domain

| Domain | Write | Does |
|---|---|---|
| Programs | `mvcgen [f] invariants · ⇓⟨cur, s⟩ => ⌜s = cur.prefix.sum⌝` then `all_goals grind` | Hoare triple for a `for` loop (`import Std.Tactic.Do`) |
| Number theory | `rw [Finset.sum_range_succ, ih]; ring` | induction step for `∑ i ∈ range n` |
| Number theory | `rcases hp.dvd_mul.mp h with h \| h` | Euclid's lemma for a prime `p` |
| Number theory | `haveI := Fact.mk hp`; `revert x; decide` | `ZMod p` lemmas need `[Fact p.Prime]`; check every residue |
| Analysis | `obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)`; `refine ⟨max N1 N2, fun n hn => ?_⟩` | Archimedes; supply the `N` of an ε-N proof |
| Analysis | `rw [abs_lt] at h ⊢; constructor <;> linarith` | `\|x\| < ε` as two linear facts |
| Analysis | `filter_upwards [h] with ω hω` | prove an `∀ᶠ` / `∀ᵐ` / `=ᵐ` goal pointwise |
| Numerics | `rw [tendsto_iff_norm_sub_tendsto_zero]; exact squeeze_zero (fun _ => norm_nonneg _) hb h0` | convergence from an error bound that tends to 0 |
| Numerics | `tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1` / `Function.iterate_succ_apply'` | `K^n → 0` for `0 ≤ K < 1`; `f^[n+1] x = f (f^[n] x)` |
| Numerics | `(hf.add hg).congr_deriv (by ring)`; `h.deriv` | build a `HasDerivAt` fact, fix the derivative's form, read off `deriv f x` |
| Probability | `open MeasureTheory ProbabilityTheory` | required for `μ[X]`, `Var[X; μ]`, `X ⟂ᵢ[μ] Y`, `μ[B \| A]` to parse |
| Probability | `rw [integral_add (hX.const_mul a) (integrable_const b), integral_const_mul]` | linearity of expectation |
| Probability | `rw [variance_eq_sub hL2]`; `hX.integrable_sq` | `Var X = μ[X^2] - μ[X]^2`, from `MemLp X 2 μ` |
| Quantum | `ext i j; fin_cases i <;> fin_cases j <;> simp [defs, Matrix.mul_apply, Fin.sum_univ_two]` | 2×2 gate identity entrywise |
| Quantum | `rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]` / `rw [← Matrix.mul_kronecker_mul]` | unitarity as `U * Uᴴ = 1`; `(A ⊗ₖ B)(C ⊗ₖ D) = AC ⊗ₖ BD` |
| Quantum | `simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]` | collapse sums against Kronecker deltas |
| Stat mech | `rw [Temperature.β_toReal]`; `rw [partitionFunction_of_fintype, Fin.sum_univ_two]` | `β = 1 / (kB T)`; finite `Z = ∑ i, exp (-β Eᵢ)` |
| PhysLean | `rw [minkowskiProduct_toCoord]` (after `open Lorentz Vector`) | `⟪p, q⟫ₘ = p⁰q⁰ - ∑ i, pⁱqⁱ` |

**Five traps.** ℕ subtraction truncates (`3 - 5 = 0`). `x / 0 = 0` and `√(-4) = 0`, so the honest lemmas carry side conditions. `ring`, `abel` and `group` ignore hypotheses (`linear_combination` uses them). `rfl` and `decide` do not unfold well-founded definitions. Without `generalizing`, the IH is stuck on the original accumulator or index.
