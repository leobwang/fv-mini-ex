# Lean syllabus

How the Lean track is laid out and a suggested route through it. Every problem, with its time and tags, is in `INDEX.md`; the APIs each one teaches are in `REFERENCE.md`.

| Tier | IDs | Layout |
|---|---|---|
| easy | E001–E127 | flat in `easy/`: E001–E094 syntax and tactics tour, E095–E127 domain warm-ups |
| medium | M001–M192 | topic folders `medium/01_…`–`medium/10_…`, numbered topic by topic |
| hard | H001–H115 | topic folders `hard/01_…`–`hard/10_…`, numbered topic by topic |

**Where to start.** Do the easy tour in order up to about E033 (core Lean), then E034–E045 and E063–E075 if you will use Mathlib. Before a domain topic (06–10), do its five or six warm-ups. Within a topic, mediums come before hards and are numbered in teaching order; each area below suggests a route.

**Dependencies between topics.** 01–03 need only core Lean. 04–05 need the Mathlib easies. 06 (probability) and 07 (numerics) build on 05 (limits, sups, derivatives). 08 (quantum) needs the matrix and complex-number easies (E072–E074). 09 (condensed matter) uses 06-style sums and expectations and 08-style matrices. 10 (PhysLean) uses 05's calculus.

## Core syntax and tactics (E001–E094)

This area covers E001-E094, the Lean 4 basics needed for everything later. It has four parts: commands and definitions (def/theorem, pattern matching, structures, inductives, instances, coercions, sections, universes, notation, macros); proof tactics and term-mode proofs for the logical connectives and quantifiers; rewriting, simplification and decision procedures (rw, simp, conv, omega, decide, grind); and Mathlib's automation (ring, linarith, nlinarith, linear_combination, norm_num, positivity, gcongr, field_simp, casts, abel/group, fun_prop, fin_cases, interval_cases). E001-E033, E046-E062 and E076-E086 use core Lean only. E034-E045, E063-E075 and E087-E094 need `import Mathlib`, and they bring in math notation the learner should be able to read: ∑/∏ over Finset, `![..]` vectors, `!![..]` matrices, ℂ's re/im/conj/normSq, Set.Icc, ZMod, ∣, and ↑ casts. Nothing comes before this area; it is the entry point. Suggested path: start with computation and logic (E001-E008, then E046-E047 and E057-E058 for term-mode proofs and classical logic). Next, rewriting and automation (E009-E011, E027-E028, E031, E033, E061-E062). Then data and definitions (E012-E013, E016-E019, E029-E030, E032, E052-E056, E059-E060, E078, E081-E083, E086). Then induction and recursion (E014-E015, E024-E026, E048-E050, E079-E080, E084-E085). Then proof structure (E020-E023, E051, E076-E077). Finally the Mathlib block, in this order: E034-E037 and E067-E068 (arithmetic tactics), E038-E041, E065-E066 and E087-E091 (logic and quantifiers), E042-E045, E063-E064, E069-E075 and E092-E094 (domain notation and specialized tactics).

## Logic and types, verified programs, semantics (topics 01–03)

This area covers Lean 4 as a programming language and a logic. **Logic and types** (M001-M014, H001-H009) is about inductive predicates and rule induction, dependent types (`Fin`, subtypes, indexed families, type-level functions, `Σ`, `HEq`, `▸`), and type classes with laws, including a hand-built `Monad` and `LawfulMonad`. It also covers decidability instances, extensionality and the axioms (`funext`, `propext`, `cast`, `#print axioms`), well-founded relations (`Acc`, `Prod.Lex`, `InvImage`, `Subrelation`), quotients, and proof by reflection.

**Verified programs** (M015-M037, H010-H018) covers accumulator invariants, `termination_by`/`decreasing_by`, `fun_induction`, and Std.Do Hoare triples with `mvcgen`. It works with the core `List` library (Perm, Pairwise, Sublist, prefix/infix/suffix, count) and with `Array` swaps, on trees, heaps and queues.

**Semantics** (M038-M050, H019-H028) covers evaluators and compilers, small-step, big-step and fuel semantics for IMP, and Hoare logic with weakest preconditions. It also covers abstract interpretation, and de Bruijn STLC with renaming and substitution, Tait reducibility and Church-Rosser through parallel reduction.

Everything is core Lean 4.32 plus `Std.Tactic.Do`; Mathlib is never needed, and several problems forbid imports. Prerequisites are the easy track: E003-E031 for the core tactics, E026 for `termination_by`, E046-E051 for term-mode and `subst`/`congrArg`, E059 for list indexing, E081 for quotients, E084 for `fun_induction`. A good path:
- M001-M005, then M006-M010.
- M015-M018, then M020-M024 and M017/M025-M031.
- M019, M034, M035, M037.
- M036, then H012.
- M038-M043, then M044/M050, M045, M046-M049.

After that, the hard problems:
- H019-H021 first, then H001, H004-H006, H007, H008, H009.
- H010/H011, H013-H018.
- H022-H025, and last H026-H028.

## Algebra, number theory, analysis and sets (topics 04–05)

This area covers medium and hard topics 04-05 (M051–M078, H029–H049), all built on Mathlib. Algebra and number theory covers Finset sums, products and counting, divisibility, primes and gcd, `Nat.ModEq`/`Int.ModEq` congruences, `ZMod` with `Fact`, groups, homomorphisms and subgroups built as structure instances, polynomials over ℚ/ℂ, and the Gaussian integers. Analysis and sets covers images, preimages and the Cantor/Knaster–Tarski/Schröder–Bernstein constructions, hand-written ε-N and ε-δ proofs, `sSup` completeness arguments, and then Mathlib's own filters, metric spaces, `HasDerivAt` and interval integrals (H045–H049). You need the Mathlib tactic problems E034–E045 (ring, linarith, norm_num, positivity, gcongr, field_simp, push Not, Finset sums, primes, set ext) and the induction patterns from E014, M001 and M003 (structural, generalizing, strong induction). Suggested algebra path: M051 → M052 → M056 (sums), M055 → M057 → M053 (primes, factoring, ZMod by decide), M054 → M059 → M060 → M063 (groups), M058 → M061 → M064 → M065 (congruences, casts), M062 (polynomials); then H029 → H030 → H031 → H032 → H033 → H034 → H035 → H036 → H037 → H038. Suggested analysis path: M069 → M070 → M071 → M077 (sets), M066 → M072 (inequalities), M067 → M068 → M073 → M076 → M078 (ε-N/ε-δ), M074 → M075 (suprema); then H039 → H040, H041 → H042 → H043 → H044 (completeness without topology), H045 → H046 → H047 (filters, metric spaces), H049 → H048 (calculus, integrals).

## Probability and statistics (E095–E103, topic 06)

This area is Mathlib's measure-theoretic probability (`import Mathlib`, `open MeasureTheory ProbabilityTheory`). A random variable is a function `X : Ω → ℝ`, an event is a `MeasurableSet`, and a distribution is a `Measure`. It covers measures of events and `ℝ≥0∞` arithmetic, conditional probability and independence, expectation as an integral (`μ[X]`), variance, the classical inequalities (Markov, Chebyshev, Jensen, Cauchy–Schwarz, Chernoff, Hoeffding), named laws (PMF, Gaussian, binomial, Poisson, geometric, exponential, `HasLaw`), and limit theorems (WLLN, Borel–Cantelli, SLLN, CLT). It ends with conditional expectation, martingales and 2-state Markov chains. No physlib is used. Prerequisites: sets and `ext` (E040), Finset sums (E042), `ring`/`linarith`/`norm_num`/`positivity`/`field_simp` (E034–E045), `nlinarith` and casts (M066, M067), and filters/`Tendsto` for the hard limit problems. Suggested path: E095 → E096 → E097 → E098 → E099 → E100 → E101 → E102 → E103 (one notation each). Then events: M079, M080, M081, M082. Then expectation algebra: M084, M085, M087, M088, M089, M090, M091, M092, M093. Then laws: M083, M101, M086, M094, M095, M096, M099. Then chains and statistics: M097, M098. Then conditional expectation: M100. Hard: H052 and H051 (event algebra); H053, H054, H055 (laws plus linearity); H056 and H057 (inequalities); H050 and H058 (laws of large numbers); H059 (chains); H060 and H061 (condExp and martingales).

## Numerical analysis (E104–E108, topic 07)

Numerical analysis (E104–E108, M102–M125, H062–H075) proves what numerical methods guarantee: polynomial evaluation and interpolation, rounding and floating-point error models, root-finding and fixed-point iteration, finite differences and Taylor remainders, quadrature, ODE and PDE time-stepping, and linear systems.

It uses Mathlib only:
- `Polynomial` and `Lagrange` for polynomials and interpolation
- `HasDerivAt`, `iteratedDeriv`, `taylorWithinEval` and `intervalIntegral` for analysis
- `Filter.Tendsto` with `ciSup`/`ciInf` for limits
- `Matrix` with `*ᵥ`/`⬝ᵥ`, the sup norm and Gershgorin for linear algebra
- `Real.exp`/`Real.sqrt` bounds

**Prerequisites:**
- the Mathlib automation easies E034–E045 (`ring`, `linarith`, `norm_num`, `positivity`, `gcongr`, `field_simp`) and E042 (Finset sums)
- the analysis mediums (around M066–M078: limits, sup, `exists_nat_gt`)
- H049 (Rolle from scratch) as background for H067

**Suggested path:**
1. Vocabulary: E104 (polynomials), E105 (derivatives), E106 (integrals), E107 (contractions), E108 (floor/round).
2. Floating point: M102 (Horner), then M103, M104, M105.
3. Iteration: M106, M107, M108, M109.
4. Approximation: M110, M111, M112.
5. Quadrature and interpolation: M113, M114, M115, M116.
6. Recurrences and ODE methods: M117, M118, M119, M122, M123.
7. Conditioning and nodes: M120, M121, M124, M125.

**Hard problems**, each after the mediums it builds on:
- H062 after M106; H064 after M109
- H065 and H066 after M111
- H067 and H068 after M113/M116
- H069 after M104
- H070 and H071 after M120/M121
- H072 after M119; H073 after M118
- H063, H074 and H075 last

## Quantum computing and information (E109–E114, topic 08)

This area turns finite-dimensional quantum mechanics into Lean. It works in two layers. Mathlib gives raw linear algebra: gates as `Matrix n n ℂ`, states as `n → ℂ`, Kronecker products, `unitaryGroup` and `NormedSpace.exp`. physlib's QuantumInfo gives bundled objects that carry their invariants: `Ket`, `MState`, `𝐔[d]`, `POVM`, `CPTPMap`, `Sᵥₙ` and `TrDistance`. Prerequisites are the core tactics and rewriting (E001-E033) plus the Mathlib automation and casts problems (E034-E045: `ring`, `linarith`, `norm_num`, `field_simp`, `push_cast`/`exact_mod_cast`). Finset sums from E042 and complex numbers help. The easy cards teach the six building blocks in order: Pauli literals (E109), the unitary group (E110), Kronecker products (E111), physlib kets and bra-kets (E112), density matrices (E113), and two-qubit indexing with CNOT (E114). Suggested medium path:
- Single-qubit gates: M126, M127, M128.
- Multi-qubit circuits: M129, M130, M132, M131.
- Bundled states: M133, M134, M137, M136.
- Measurement, reduced states and entropy: M135, M138, M139.
- No-go theorems and Bell tests: M140, M141, M142, M143.
- Channels and distances: M144, M145, M146, M147.
- Error correction and the PPT criterion: M148, M149.

The hard problems build on these:
- State geometry and entanglement: H076, H078.
- Inner-product arguments: H079, H080, H077, H081 (H081 reuses M142's identity and H077's Cauchy-Schwarz).
- Algorithms and Fourier sums: H083, H084, H085, H086.
- Gate synthesis and dynamics: H087, H088.
- Trace distance under partial trace: H082, which follows M147.

## Condensed matter and statistical mechanics (E115–E121, topic 09)

This area covers equilibrium statistical mechanics and simple lattice models.

**Statistical mechanics (physlib).** Most problems use physlib's `CanonicalEnsemble`: partition function, Boltzmann probabilities, mean energy, free energy, entropy and heat capacity. They use two interfaces:
- the Temperature-based one: `T.β`, `kB`, `partitionFunction_of_fintype`, `twoState`, `nsmul`, `+`;
- the β-real one, with kB = 1: `mathematicalPartitionFunctionBetaReal`, `probabilityBetaReal`, `meanEnergyBetaReal`.

**Tight-binding chain (physlib).** `CondensedMatter.TightBindingChain` covers bands, Hermiticity, Bloch states and the spectrum.

**Plain Mathlib.** The Ising chains and rings use `Bool` spins, `Fin.cons`/`Fin.snoc` reindexing and transfer matrices. The Hubbard dimer uses `Matrix`, `*ᵥ` and `⬝ᵥ`. The combinatorics of microstates uses `card_nbij'`, `powersetCard` and stars and bars.

**Prerequisites.**
- The Mathlib tactic layer: E034–E045 (`ring`, `linarith`, `positivity`, `gcongr`, `field_simp`) and `Finset` sums (E042).
- The matrix literals from E109/M097.
- The real-analysis, calculus and limit material from the earlier analysis and probability areas (`HasDerivAt`, `Tendsto`, integrals; e.g. M091–M099). The hard problems use all of these heavily.

**Suggested path.**
1. Easy warm-ups: E115 (Temperature/β), E116–E117 (Z), E120 (heat capacity), E118 (Ising bond), E119 and E121 (tight-binding).
2. The β-real core: M150 → M151 → M152 → M153 → M154. Then the Temperature API: M155, M157, M161, M173.
3. Limits and derivatives: M156, M160, M162.
4. Entropy and counting: M158, M159, M163.
5. Ising: M164 → M165 → M166.
6. Tight-binding: M167 → M170 → M168 → M169 → M171. Then the Hubbard dimer, M172.
7. Hard, thermodynamics: H089 (dU/db = −Var), H090 (Gibbs variational principle), H091 (log Z convex), H092 (third law), H093 (equipartition), H094 (Planck oscillator).
8. Hard, Ising: H095 → H096 → H097 → H102, plus H098 (Curie–Weiss).
9. Hard, tight-binding: H099 → H100, plus H101 (Hubbard ground state).

## Physics with PhysLean (E122–E127, topic 10)

This area proves textbook physics facts against the real definitions in physlib (formerly PhysLean), which sits on top of Mathlib v4.32.0. Each problem imports a single physlib module rather than `import Mathlib`. It covers six strands. Special relativity: `Lorentz.Vector`, `⟪·,·⟫ₘ`, proper time, causal character, the Lorentz group, boosts and `γ`, orthochronous maps and the twin paradox. Vector calculus on `Space`: `∂[i]`, grad, div, curl, Laplacian and the cross product. Classical mechanics on `Time`: the harmonic oscillator, its explicit trajectory, energy, the damped oscillator and plane waves. Electromagnetism from potentials. The quantum harmonic oscillator, with `ℏ`, its eigenvalues, the ground state and Hermite polynomials. Units and dimensions (`WithDim`, `scaleUnit`), and Standard Model anomaly cancellation (`SMνCharges`, `PlusU1`). Prerequisites from earlier IDs are field_simp, push_cast, nlinarith and linear_combination (E034–E045, M066–M072), Finset sums (E042), Real.sqrt (E035–E045), Mathlib derivatives and limits (M107–M108, H089) and matrix and inner-product algebra (E110, H101). A suggested path: E122, E123, E124, E127, E125, E126 to learn the API surface. Then the relativity medium problems M174–M180, followed by M181–M184 (vector calculus), M185 and M192 (oscillator), M186 (EM), M187 (Hermite), M188–M189 (units) and M190–M191 (anomalies). After that come the hard problems by strand: H103–H105 and H107–H108 for Lorentz, H106, H109 and H110 for vector calculus and waves, H111–H113 for the oscillator, H114 for the QHO and H115 for anomalies.
