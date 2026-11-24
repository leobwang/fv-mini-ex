# H108 · Twin paradox: the travelling twin is younger: cheatsheet

Exercise: [`problem.lean`](problem.lean).
Lean companion: [`guide.lean`](guide.lean). Entry **Rn** here is
example **Rn** there. Put the cursor after each tactic to see the same before and after states in the
infoview. Generic tactics are in [`TACTIC_STATES.md`](../../../TACTIC_STATES.md).

**Assumed:** Lean basics (easy tier E001–E033): `intro`, `exact`, `rw`, `simp`, `have`, `refine`,
`ring`, `norm_num`, anonymous constructors `⟨_, _⟩`, dot notation `h.1`, `h.2`, `h.mp`. **New here:**
Mathlib's real square root `√`, norms `‖·‖`, the real inner product `inner ℝ`, `EuclideanSpace`, and the
tactics `rcases`/`obtain`, `set`, `simpa`, `linarith`, `nlinarith`, `abel`; physlib's Lorentz vectors
`Lorentz.Vector d` (= `SpaceTime d`), the Minkowski product `⟪·, ·⟫ₘ`, causal characters,
`causallyFollows`, `SpaceTime.properTime` and the `InstantaneousTwinParadox` structure.

**The physics, in symbols.** Units with $c = 1$. An event is $p = (p^0, \vec p) \in \mathbb R^{1+d}$: time
$p^0$, position $\vec p \in \mathbb R^d$. The Minkowski product (signature $+-\cdots-$) is
$\langle p, q\rangle_m = p^0 q^0 - \vec p\cdot\vec q$. A displacement $w$ is *future causal* when
$\langle w, w\rangle_m \ge 0$ and $w^0 \ge 0$, equivalently $\|\vec w\| \le w^0$ (inside or on the future
light cone). The proper time of a straight worldline from $q$ to $p$ is
$\tau(q, p) = \sqrt{\langle p - q, p - q\rangle_m}$. With $s, m, e$ the start, middle (twin B's turning
point) and end events, put $u = m - s$ and $v = e - m$, so $u + v = e - s$. Then
$$\texttt{ageGap} = \tau(s, e) - \bigl(\tau(s, m) + \tau(m, e)\bigr)
= \sqrt{\langle u+v, u+v\rangle_m} - \sqrt{\langle u,u\rangle_m} - \sqrt{\langle v,v\rangle_m},$$
and the claim $\texttt{ageGap} \ge 0$ is the **reverse triangle inequality** for future-causal $u, v$.
Squaring reduces it to the **reverse Cauchy–Schwarz inequality**
$\sqrt{\langle u,u\rangle_m}\sqrt{\langle v,v\rangle_m} \le \langle u, v\rangle_m$. With
$a = u^0,\ b = v^0,\ c = \|\vec u\|,\ e = \|\vec v\|$ (so $0 \le c \le a$, $0 \le e \le b$):
$\langle u,u\rangle_m = a^2 - c^2$, $\langle v,v\rangle_m = b^2 - e^2$, and Euclidean Cauchy–Schwarz
$\vec u\cdot\vec v \le ce$ gives $\langle u,v\rangle_m \ge ab - ce \ge 0$. Finally
$(ab - ce)^2 - (a^2 - c^2)(b^2 - e^2) = (ae - bc)^2 \ge 0$.

The milestones are exactly these steps: causal ⇒ in the cone (Part 1), reverse Cauchy–Schwarz
(Part 2), reverse triangle (Part 3); Part 4 unfolds the twin paradox and applies them.

## How to read an entry

Each entry is one tactic or one lemma used with `rw`/`simp`/`have`. It says what changes (**goal**,
**context**, or **goal list**), lists the placeholders with their types, then shows the proof state
before and after.

- `Γ ⊢ G` is a proof state: hypotheses `Γ`, goal `G`. A cell shows only the hypotheses that change.
- `P` is "the rest of your goal" (`P : ℝ → Prop`). The step changes only the part inside `P (…)`,
  wherever it sits in a larger goal. `G : Prop` is an arbitrary goal; a hypothesis `g : … → G` is only
  there to close the example after a fact was added to the context.
- Placeholders are written as Lean binders. `{d : ℕ}` is the number of space dimensions (the twin
  paradox uses `d = 3`). `{E : Type} [NormedAddCommGroup E]` is any type with `+`, `-`, `0` and a norm
  `‖·‖` (`ℝ` and `EuclideanSpace ℝ (Fin d)` qualify); `[AddCommGroup E]` only asks for `+`, `-`, `0`
  (`Lorentz.Vector d` qualifies).
- Every `⊢` cell is a state Lean reaches in the companion file; `tools/guide_sync.py` checks that.

## Reading the goals

| You see | It means |
|---|---|
| `Lorentz.Vector d`, `SpaceTime d` | the same type: functions `Fin 1 ⊕ Fin d → ℝ`, i.e. vectors of $\mathbb R^{1+d}$ |
| `Fin 1 ⊕ Fin d` | the disjoint union (`Sum`) of one time index and `d` space indices; its elements are `Sum.inl i` and `Sum.inr i` |
| `Sum.inl 0`, `Sum.inr i` | the time index, and the `i`-th space index |
| `p.timeComponent`, `timeComponent p`, `p (Sum.inl 0)` | the time component $p^0$; all three are the same term (`timeComponent` is an `abbrev`) |
| `p.spatialPart`, `spatialPart p` | the spatial part $\vec p$, a vector of `EuclideanSpace ℝ (Fin d)` ($\mathbb R^d$ with the Euclidean norm) |
| `‖x‖` | the norm; for a real `x` it is the absolute value `abs x` (R7) |
| `\|x\|` | `abs x`, the absolute value of a real `x` (R7) |
| `inner ℝ x y` | the Euclidean dot product $\vec x\cdot\vec y$ |
| `(minkowskiProduct p) q` | $\langle p, q\rangle_m = p^0q^0 - \vec p\cdot\vec q$. You type it `⟪p, q⟫ₘ` (scoped notation, needs `open Lorentz Vector`); the infoview prints the long form |
| `minkowskiProduct u + minkowskiProduct v` | a sum of linear maps; applied to `w` it is `⟪u, w⟫ₘ + ⟪v, w⟫ₘ` (R22) |
| `√x` | `Real.sqrt x`; it is `0` when `x < 0`, so its lemmas need `0 ≤ x` |
| `p.causalCharacter`, `CausalCharacter.timeLike` | the causal character of `p`, one of three values: `.timeLike` ($\langle p,p\rangle_m > 0$), `.lightLike` ($= 0$), `.spaceLike` ($< 0$) |
| `causallyFollows p q` | `q` is in the causal future of `p`: `q - p` timelike with `0 < (q - p)⁰`, or lightlike with `0 ≤ (q - p)⁰` |
| `T : InstantaneousTwinParadox` | a structure: events `T.startPoint`, `T.twinBMid`, `T.endPoint : SpaceTime 3` and three causal facts (R27) |
| `T.ageGap`, `T.properTimeTwinA`, `T.properTimeTwinB` | $\tau_A - \tau_B$, $\tau(s, e)$, $\tau(s, m) + \tau(m, e)$ |
| `q.properTime p` | `SpaceTime.properTime q p` $= \sqrt{\langle p - q, p - q\rangle_m}$, from `q` to `p` |
| `a : ℝ := e` | a local definition made by `set` (R11) |
| `case inl`, `case inr` | the two goals of an `∨` split: left and right alternative |

---

## Part 1 · `future_causal` (milestone 1)

Statement: from `h : causallyFollows p q`, prove `‖(q - p).spatialPart‖ ≤ (q - p).timeComponent`: the
displacement lies in the closed future cone.

**R1 · `rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩`** changes the **goal list and the context**. `h` is an `∨` of
two `∧`s (after unfolding `causallyFollows` and the two cone sets, which `rcases` does by itself): `|`
splits the `∨` into two goals, `⟨h1, h2⟩` splits each `∧`. Placeholders: `{d : ℕ} (p q : SpaceTime d) (G : Prop)`.
Note that `h2` prints with `(q - p) (Sum.inl 0)`, which is `timeComponent (q - p)`.

| Before | After |
|---|---|
| `h : causallyFollows p q ⊢ G` | `h1 : (q - p).causalCharacter = CausalCharacter.timeLike, h2 : 0 < (q - p) (Sum.inl 0) ⊢ G` |
| | `h1 : (q - p).causalCharacter = CausalCharacter.lightLike, h2 : 0 ≤ (q - p) (Sum.inl 0) ⊢ G` |

**R2 · `(timeLike_iff_norm_sq_pos p).mp h`** changes the **context** (here via `have h' := …`). The lemma
is `causalCharacter p = .timeLike ↔ 0 < ⟪p, p⟫ₘ`; `.mp` is its `→` half. Placeholders:
`{d : ℕ} (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `h : p.causalCharacter = CausalCharacter.timeLike ⊢ G` | `h' : 0 < (minkowskiProduct p) p ⊢ G` |

**R3 · `(lightLike_iff_norm_sq_zero p).mp h`** changes the **context**. The lemma is
`causalCharacter p = .lightLike ↔ ⟪p, p⟫ₘ = 0`. Placeholders: as R2.

| Before | After |
|---|---|
| `h : p.causalCharacter = CausalCharacter.lightLike ⊢ G` | `h' : (minkowskiProduct p) p = 0 ⊢ G` |

**R4 · `hlt.le`, `heq.ge`** change the **context**. `LT.lt.le : a < b → a ≤ b`; `Eq.ge : a = b → b ≤ a`.
So R2 followed by `.le`, and R3 followed by `.ge`, both give `0 ≤ ⟪p, p⟫ₘ`. Placeholders: `(x y : ℝ)`.

| Before | After `have h1 := hlt.le` | After `have h2 := heq.ge` |
|---|---|---|
| `hlt : x < y, heq : x = y ⊢ G` | `h1 : x ≤ y ⊢ G` | `h2 : y ≤ x ⊢ G` |

**R5 · `obtain ⟨h1, h2⟩ := h`** changes the **context**: a conjunction hypothesis becomes its two halves.
Placeholders: `(A B G : Prop)`.

| Before | After |
|---|---|
| `h : A ∧ B ⊢ G` | `h1 : A, h2 : B ⊢ G` |

**R6 · `rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at h`** changes the **context**. The lemma
is `⟪p, p⟫ₘ = ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2`, i.e. $\langle p,p\rangle_m = (p^0)^2 - \|\vec p\|^2$
with a norm around the real $p^0$. `at h` rewrites `h` instead of the goal. Placeholders:
`{d : ℕ} (p : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `h : 0 ≤ (minkowskiProduct p) p ⊢ G` | `h : 0 ≤ ‖p.timeComponent‖ ^ 2 - ‖p.spatialPart‖ ^ 2 ⊢ G` |

**R7 · `Real.norm_eq_abs`, then `sq_abs`** change the **goal**: `‖x‖ = |x|` for a real `x`, and
`|a| ^ 2 = a ^ 2`. Together they remove the norm around the time component. `simp` uses `Real.norm_eq_abs`
by itself; `sq_abs` must be named. Placeholders: `(x : ℝ)`.

```lean-goal
⊢ P (‖x‖ ^ 2)
⊢ P (|x| ^ 2)
⊢ P (x ^ 2)
```

**R8 · `sub_nonneg`** changes the **goal** or, with `at h`, the **context**: `0 ≤ a - b ↔ b ≤ a`. `simp`
uses it by itself. Placeholders: `(a b : ℝ)`.

| Before | After `rw [sub_nonneg] at h` |
|---|---|
| `h : 0 ≤ a - b ⊢ G` | `h : b ≤ a ⊢ G` |

**R9 · `simpa [lemmas] using h`** **closes** the goal: it simplifies both `h` and the goal with `simp`
plus `lemmas`, then closes the goal with the simplified `h`. Here `simp` does R7 and R8 on `h`.
Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `h : 0 ≤ ‖x‖ ^ 2 - y ⊢ y ≤ x ^ 2` | closed by `simpa [sq_abs] using h` |

**R10 · `abs_le_of_sq_le_sq'`** changes the **context**. The lemma is
`a ^ 2 ≤ b ^ 2 → 0 ≤ b → -b ≤ a ∧ a ≤ b`; `.2` takes `a ≤ b`. Placeholders: `(a b : ℝ)`.

| Before | After `have h' := abs_le_of_sq_le_sq' h hb` |
|---|---|
| `h : a ^ 2 ≤ b ^ 2, hb : 0 ≤ b ⊢ G` | `h' : -b ≤ a ∧ a ≤ b ⊢ G` |

---

## Part 2 · `reverse_cauchy_schwarz` (milestone 2)

Statement: for `u v` with `‖u⃗‖ ≤ u⁰` and `‖v⃗‖ ≤ v⁰`, `√⟪u, u⟫ₘ * √⟪v, v⟫ₘ ≤ ⟪u, v⟫ₘ`.

**R11 · `set a := e`** changes the **goal and the context**: the context gains the local definition
`a : ℝ := e`, and every `e` in the goal **and in the hypotheses** becomes `a`. `simp only [a]` or
`simp [a, …]` unfolds it again. Placeholders: `{d : ℕ} (u : Lorentz.Vector d)`, `e := u.timeComponent`.

| Before | After `set a := u.timeComponent` | After `simp only [a]` |
|---|---|---|
| `h : P u.timeComponent ⊢ P u.timeComponent` | `a : ℝ := u.timeComponent, h : P a ⊢ P a` | `h : P a ⊢ P u.timeComponent` |

**R12 · `norm_nonneg x`** changes the **context**: `0 ≤ ‖x‖`. Placeholders: `{E : Type} [NormedAddCommGroup E] (x : E)`.

| Before | After `have h' := norm_nonneg x` |
|---|---|
| `⊢ G` | `h' : 0 ≤ ‖x‖ ⊢ G` |

**R13 · `minkowskiProduct_eq_timeComponent_spatialPart`** changes the **goal**: the lemma is
`⟪p, q⟫ₘ = p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart`. Placeholders:
`{d : ℕ} (p q : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P ((minkowskiProduct p) q)` | `⊢ P (p.timeComponent * q.timeComponent - inner ℝ p.spatialPart q.spatialPart)` |

**R14 · `real_inner_le_norm x y`** changes the **context**: Cauchy–Schwarz `inner ℝ x y ≤ ‖x‖ * ‖y‖`.
Placeholders: `{d : ℕ} (x y : EuclideanSpace ℝ (Fin d))` (any real inner product space works).

| Before | After `have h' := real_inner_le_norm x y` |
|---|---|
| `⊢ G` | `h' : inner ℝ x y ≤ ‖x‖ * ‖y‖ ⊢ G` |

**R15 · `linarith [t₁, …]`** **closes** a goal `≤`, `<`, `=` that follows *linearly* from the hypotheses
plus the extra facts `tᵢ`. Products of unknowns count as single atoms: it treats `c * e` or `√x` as one
unknown. Placeholders: `(f : ℝ → ℝ) (a b : ℝ)`.

| Before | After |
|---|---|
| `hb : b = 2 - f a ⊢ 1 ≤ b` (with `hf : ∀ x, f x ≤ 1`) | closed by `linarith [hf a]` |

**R16 · `nlinarith [t₁, …]`** **closes** a polynomial (in)equality. Like `linarith`, but it first adds the
pairwise products of the hypotheses and the hints `tᵢ` (here `(a - c) * (b - e) ≥ 0`-type products).
It is incomplete: when it fails, give it the right square as a hint (R20). Placeholders: `(a b c e : ℝ)`.

| Before | After |
|---|---|
| `hc : 0 ≤ c, he : 0 ≤ e, hca : c ≤ a, heb : e ≤ b ⊢ c * e ≤ a * b` | closed by `nlinarith` |

**R17 · `rw [← Real.sqrt_mul hx]`** changes the **goal**. The lemma is `0 ≤ x → √(x * y) = √x * √y`;
right to left it merges two roots. Write `(by nlinarith)` in place of `hx` to prove `0 ≤ x` on the spot.
Placeholders: `(x y : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x * √y)` | `⊢ P √(x * y)` |

**R18 · `refine le_trans ?_ h`** changes the **goal**. `le_trans : a ≤ b → b ≤ c → a ≤ c`: given
`h : b ≤ c`, the goal `a ≤ c` becomes `a ≤ b`. Placeholders: `(a b c : ℝ)`.

| Before | After |
|---|---|
| `h : b ≤ c ⊢ a ≤ c` | `h : b ≤ c ⊢ a ≤ b` |

**R19 · `rw [Real.sqrt_le_left hy]`** changes the **goal**. The lemma is `0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`;
it removes the root by squaring. Placeholders: `(x y : ℝ) (hy : 0 ≤ y)`.

| Before | After |
|---|---|
| `⊢ √x ≤ y` | `⊢ x ≤ y ^ 2` |

**R20 · `sq_nonneg a`** changes the **context**: `0 ≤ a ^ 2`. Pass it as a hint, `nlinarith [sq_nonneg t]`,
when the inequality is "a square is nonnegative" in disguise. Placeholders: `(a b : ℝ)`.

| Before | After `have h' := sq_nonneg (a - b)` |
|---|---|
| `⊢ G` | `h' : 0 ≤ (a - b) ^ 2 ⊢ G` |

---

## Part 3 · `reverse_triangle` (milestone 3)

Statement: for `u v` in the closed future cone, `√⟪u, u⟫ₘ + √⟪v, v⟫ₘ ≤ √⟪u + v, u + v⟫ₘ`.

**R21 · `apply Real.le_sqrt_of_sq_le`** changes the **goal**. The lemma is `x ^ 2 ≤ y → x ≤ √y`, so it
squares the left side and needs no sign condition. Placeholders: `(x y : ℝ)`.

| Before | After |
|---|---|
| `⊢ x ≤ √y` | `⊢ x ^ 2 ≤ y` |

**R22 · `map_add`** changes the **goal**. `minkowskiProduct` is a linear map into linear maps, so
`map_add : f (a + b) = f a + f b` splits the first slot into a sum of maps, and plain `simp` applies that
sum to `w` (and splits the second slot too). Placeholders: `{d : ℕ} (u v w : Lorentz.Vector d)`.

| Before | After `simp only [map_add]` | After `simp` |
|---|---|---|
| `⊢ P ((minkowskiProduct (u + v)) w)` | `⊢ P ((minkowskiProduct u + minkowskiProduct v) w)` | `⊢ P ((minkowskiProduct u) w + (minkowskiProduct v) w)` |

**R23 · `rw [minkowskiProduct_symm q p]`** changes the **goal**. The lemma is `⟪p, q⟫ₘ = ⟪q, p⟫ₘ`. With the
arguments given, it turns around only `⟪q, p⟫ₘ`, so `⟪u, v⟫ₘ` and `⟪v, u⟫ₘ` become the same atom for
`ring`. `simp [map_add, minkowskiProduct_symm v u]` followed by `ring` expands `⟪u + v, u + v⟫ₘ`.
Placeholders: `{d : ℕ} (p q : Lorentz.Vector d)`.

| Before | After |
|---|---|
| `⊢ P ((minkowskiProduct p) q + (minkowskiProduct q) p)` | `⊢ P ((minkowskiProduct p) q + (minkowskiProduct p) q)` |

**R24 · `rw [add_sq]`** changes the **goal**: `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2`. Placeholders:
`(a b : ℝ)` (any commutative semiring).

| Before | After |
|---|---|
| `⊢ P ((a + b) ^ 2)` | `⊢ P (a ^ 2 + 2 * a * b + b ^ 2)` |

**R25 · `rw [Real.sq_sqrt hx]`** changes the **goal**: `0 ≤ x → √x ^ 2 = x`. Placeholders: `(x : ℝ) (hx : 0 ≤ x)`.

| Before | After |
|---|---|
| `⊢ P (√x ^ 2)` | `⊢ P x` |

---

## Part 4 · `ageGap_nonneg`

Statement: `0 ≤ T.ageGap` for every `T : InstantaneousTwinParadox`.

**R26 · `unfold`** changes the **goal**: it replaces a defined name by its definition. Three layers:
`ageGap`, then the two proper times of the twins, then `SpaceTime.properTime`. One
`unfold A B C D` does all of them at once. Placeholders: `(T : InstantaneousTwinParadox)`.

| Before | After `unfold InstantaneousTwinParadox.ageGap` | After `unfold InstantaneousTwinParadox.properTimeTwinA InstantaneousTwinParadox.properTimeTwinB` |
|---|---|---|
| `⊢ P T.ageGap` | `⊢ P (T.properTimeTwinA - T.properTimeTwinB)` | `⊢ P (T.startPoint.properTime T.endPoint - (T.startPoint.properTime T.twinBMid + T.twinBMid.properTime T.endPoint))` |

After `unfold SpaceTime.properTime` (one goal, printed over three lines in the infoview):

```lean-goal
⊢ P (√((minkowskiProduct (T.endPoint - T.startPoint)) (T.endPoint - T.startPoint)) - (√((minkowskiProduct (T.twinBMid - T.startPoint)) (T.twinBMid - T.startPoint)) + √((minkowskiProduct (T.endPoint - T.twinBMid)) (T.endPoint - T.twinBMid))))
```

**R27 · a structure field** changes the **context**: `T.twinBMid_causallyFollows_startPoint` is the proof
stored in `T` that the middle event follows the start. The other two fields are
`T.endPoint_causallyFollows_twinBMid` and `T.endPoint_causallyFollows_startPoint`. Placeholders:
`(T : InstantaneousTwinParadox)`.

| Before | After `have h' := T.twinBMid_causallyFollows_startPoint` |
|---|---|
| `⊢ G` | `h' : causallyFollows T.startPoint T.twinBMid ⊢ G` |

**R28 · `abel`** **closes** an identity in a commutative additive group: only `+`, `-`, `0` and integer
multiples. Use it for vector identities such as `y - x + (z - y) = z - x`, where `ring` does not apply
(vectors cannot be multiplied). Placeholders: `{E : Type} [AddCommGroup E] (x y : E)`.

**R29 · `rw [show t = t' by tac] at h`** changes the **context**: `show t = t' by tac` is a one-off
equation proved on the spot (here by R28), and `rw … at h` uses it on `h`. Placeholders:
`{E : Type} [AddCommGroup E] (x y z : E)`.

| Before | After `rw [show y - x + (z - y) = z - x by abel] at h` |
|---|---|
| `h : P (y - x + (z - y)) ⊢ P (z - x)` | `h : P (z - x) ⊢ P (z - x)` |

### Worked combinations (W1–W3, on objects that are not the exercise's)

**W1: AM–GM, the shape of milestone 2's end game.** `√x * √y ≤ (x + y) / 2` for `0 ≤ x, y`: R17, then R19
with `(by linarith)` for the sign, then R16 with the hint `sq_nonneg (x - y)` (R20):

```lean-goal
⊢ √x * √y ≤ (x + y) / 2
⊢ √(x * y) ≤ (x + y) / 2
⊢ x * y ≤ ((x + y) / 2) ^ 2
```

**W2: square, expand, remove the roots.** `√x + √y ≤ √(2 * (x + y))`: R21, then one `rw` with R24 and
R25 twice, then `nlinarith [sq_nonneg (√x - √y), Real.sq_sqrt hx, Real.sq_sqrt hy]`:

```lean-goal
⊢ √x + √y ≤ √(2 * (x + y))
⊢ (√x + √y) ^ 2 ≤ 2 * (x + y)
⊢ x + 2 * √x * √y + y ≤ 2 * (x + y)
```

**W3: expanding a Minkowski square.** `⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`:
`simp [map_sub, minkowskiProduct_symm v u]` (R22's `map_sub` twin, R23) leaves a goal `ring` closes:

```lean-goal
⊢ (minkowskiProduct u) u - (minkowskiProduct u) v - ((minkowskiProduct u) v - (minkowskiProduct v) v) = (minkowskiProduct u) u - 2 * (minkowskiProduct u) v + (minkowskiProduct v) v
```

---

## Traps

- You type `⟪u, v⟫ₘ`, the infoview prints `(minkowskiProduct u) v`. Both are the same term.
- `√x = 0` for `x < 0`, so `Real.sqrt_mul`, `Real.sq_sqrt`, `Real.sqrt_le_left` all need a sign
  hypothesis. Prove `0 ≤ ⟪u, u⟫ₘ` and `0 ≤ ⟪v, v⟫ₘ` from the cone hypotheses first (R6, R7, then R16
  with `norm_nonneg`).
- R6 leaves `‖p.timeComponent‖ ^ 2`, a norm around a real number. Remove it with R7 (`sq_abs` must be
  named; `simp` alone stops at `|x| ^ 2`).
- `set` also rewrites the hypotheses: after `set a := u.timeComponent`, `hu` reads `‖u.spatialPart‖ ≤ a`.
- `set` renames only what is there when you call it. A term produced later (by R6 inside `huu`, say)
  prints as `u.timeComponent` again: the goal is `‖u.timeComponent‖ ^ 2 - ‖u.spatialPart‖ ^ 2 = a ^ 2 - c ^ 2`.
  `simp [a, c, sq_abs]` unfolds `a`, `c` on the right so both sides match.
- `simp [minkowskiProduct_symm]` without arguments may order the two products differently from what you
  want; give the arguments (`minkowskiProduct_symm v u`) so `⟪v, u⟫ₘ` becomes `⟪u, v⟫ₘ`.
- `SpaceTime.properTime q p` is the proper time **from `q` to `p`**: `√⟪p - q, p - q⟫ₘ`.
- `abs_le_of_sq_le_sq'` gives a conjunction `-b ≤ a ∧ a ≤ b`; take `.2`.
- `nlinarith` does not find the identity $(ab - ce)^2 - (a^2 - c^2)(b^2 - e^2) = (ae - bc)^2$ by itself:
  give it `sq_nonneg (a * e - b * c)`.
- `ring` cannot prove the vector identity `u + v = end - start`; use `abel` (R28).
- `rcases` on `causallyFollows` gives `h2 : 0 < (q - p) (Sum.inl 0)`: that is `0 < timeComponent (q - p)`
  by definition, so `h2.le` fits a goal written with `timeComponent`.

## Cheatsheet

| Need | Write | Entry |
|---|---|---|
| split `causallyFollows p q` | `rcases h with ⟨h1, h2⟩ \| ⟨h1, h2⟩` | R1 |
| causal character → sign of `⟪p, p⟫ₘ` | `(timeLike_iff_norm_sq_pos _).mp h`, `(lightLike_iff_norm_sq_zero _).mp h` | R2, R3 |
| `<` or `=` → `≤` | `h.le`, `h.ge` | R4 |
| split `h : A ∧ B` | `obtain ⟨h1, h2⟩ := h` | R5 |
| `⟪p, p⟫ₘ` in components | `minkowskiProduct_self_eq_timeComponent_spatialPart` | R6 |
| `⟪p, q⟫ₘ` in components | `minkowskiProduct_eq_timeComponent_spatialPart` | R13 |
| `‖x‖ ^ 2 → x ^ 2` for real `x` | `simp [sq_abs]` (`Real.norm_eq_abs`, `sq_abs`) | R7 |
| `0 ≤ a - b ↔ b ≤ a` | `sub_nonneg` | R8 |
| simplify a fact into the goal | `simpa [lemmas] using h` | R9 |
| `a ^ 2 ≤ b ^ 2, 0 ≤ b → a ≤ b` | `(abs_le_of_sq_le_sq' h hb).2` | R10 |
| name a subterm | `set a := e` | R11 |
| `0 ≤ ‖x‖` | `norm_nonneg _` | R12 |
| Cauchy–Schwarz | `real_inner_le_norm x y` | R14 |
| linear / polynomial arithmetic | `linarith [facts]` / `nlinarith [facts]` | R15, R16 |
| `√x * √y → √(x * y)` | `rw [← Real.sqrt_mul (by nlinarith)]` | R17 |
| go through an intermediate bound | `refine le_trans ?_ h` | R18 |
| `√x ≤ y` → `x ≤ y ^ 2` | `rw [Real.sqrt_le_left hy]` | R19 |
| square hint | `sq_nonneg t` | R20 |
| `x ≤ √y` → `x ^ 2 ≤ y` | `apply Real.le_sqrt_of_sq_le` | R21 |
| expand `⟪u + v, u + v⟫ₘ` | `simp [map_add, minkowskiProduct_symm v u]; ring` | R22, R23 |
| `(a + b) ^ 2`, `√x ^ 2` | `rw [add_sq, Real.sq_sqrt hx]` | R24, R25 |
| open up `T.ageGap` | `unfold InstantaneousTwinParadox.ageGap … SpaceTime.properTime` | R26 |
| the twin paradox's causal facts | `T.twinBMid_causallyFollows_startPoint`, `T.endPoint_causallyFollows_twinBMid` | R27 |
| vector identity | `abel`; in a hypothesis `rw [show t = t' by abel] at h` | R28, R29 |
| see the state | infoview | |
