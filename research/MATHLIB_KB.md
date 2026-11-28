# Mathlib Knowledge Base for Odd Perfect Numbers

This knowledge base indexes proven theorems, definitions, and proof tactics in the
repository's pinned Mathlib checkout (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, Lean `v4.36.0`)
and cross-references them against `OddPerfect/`.

## Quick Lookup Workflow (Carbon & Neon Agents)

Before proving any general lemma on divisors, valuations, cyclotomics, orders, squares,
or inequalities from scratch, query the local SQLite/FTS5 index:

```sh
# Search Mathlib declarations by name, type signature, or docstring
python3 research/tools/mathlib_kb.py search "cyclotomic orderOf" --scope mathlib

# Search within Mathlib.NumberTheory specifically
python3 research/tools/mathlib_kb.py search "abundancyIndex" --module Mathlib.NumberTheory

# Search existing project theorems so workers reuse OddPerfect lemmas instead of duplicating
python3 research/tools/mathlib_kb.py search "component_index" --scope project

# Audit underused Mathlib modules & potential duplicate helpers
python3 research/tools/mathlib_kb.py overlap
```

## Index Snapshot

- **Pinned Mathlib files indexed**: `8,799`
- **Pinned Mathlib declarations indexed**: `230,753`
- **Project structural declarations (`OddPerfect/`)**: `4,991`
- **Project generated certificate declarations**: `41,648`

---

## Domain Map of Proven Mathlib Machinery

### 1. Divisors, Perfection, Abundancy & Factorisation Properties

Core predicates (`Nat.Perfect`, `Nat.Abundant`, `Nat.Deficient`, `Nat.Pseudoperfect`, `Nat.abundancyIndex`), proper/antidiagonal divisor sums, monotonicity of abundancy under divisibility (`Abundant.of_dvd`, `abundancyIndex_le_of_dvd`), and Euclid-Euler even perfect numbers.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.NumberTheory.Divisors` | 125 | 2 |
| `Mathlib.NumberTheory.FactorisationProperties` | 39 | 4 |
| `Mathlib.Data.Nat.Factorization.Divisors` | 8 | 1 |
| `Archive.Wiedijk100Theorems.PerfectNumbers` | 7 | 2 |

**Representative Mathlib declarations:**
- `Nat.perfect_iff_sum_properDivisors` (`Mathlib.NumberTheory.Divisors`): `(h : 0 < n) : Perfect n ↔ ∑ i ∈ properDivisors n, i = n`
- `Nat.perfect_iff_sum_divisors_eq_two_mul` (`Mathlib.NumberTheory.Divisors`): `(h : 0 < n) : Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n`
- `Nat.Perfect` (`Mathlib.NumberTheory.Divisors`): `(n : ℕ) : Prop`
- `Nat.Perfect.pseudoperfect` (`Mathlib.NumberTheory.FactorisationProperties`): `(h : Perfect n) : Pseudoperfect n`
- `Nat.perfect_iff_not_abundant_and_not_deficient` (`Mathlib.NumberTheory.FactorisationProperties`): `(hn : 0 ≠ n) : Perfect n ↔ ¬ Abundant n ∧ ¬ Deficient n`
- `Nat.deficient_or_perfect_or_abundant` (`Mathlib.NumberTheory.FactorisationProperties`): `(hn : 0 ≠ n) : Deficient n ∨ Abundant n ∨ Perfect n`
- `Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime` (`Archive.Wiedijk100Theorems.PerfectNumbers`): `(k : ℕ) (pr : (mersenne (k + 1)).Prime) : Nat.Perfect (2 ^ k * mersenne (k + 1))`
- `Theorems100.Nat.even_and_perfect_iff` (`Archive.Wiedijk100Theorems.PerfectNumbers`): `{n : ℕ} : Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1)`

### 2. Arithmetic Functions (`σ`, `ω`, `Ω`, `ζ`, `μ`) & Multiplicativity

Dirichlet ring of arithmetic functions, multiplicativity of `σ k` (`isMultiplicative_sigma`), prime-power evaluation (`sigma_one_apply_prime_pow`), factorization expansions (`multiplicative_factorization`), `cardFactors` (`Ω`), `cardDistinctFactors` (`ω`), and `prodPrimeFactors`.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.NumberTheory.ArithmeticFunction.Misc` | 66 | 28 |
| `Mathlib.NumberTheory.ArithmeticFunction.Defs` | 60 | 3 |
| `Mathlib.NumberTheory.ArithmeticFunction.Zeta` | 32 | 1 |
| `Mathlib.NumberTheory.ArithmeticFunction.Moebius` | 35 | 2 |
| `Mathlib.NumberTheory.ArithmeticFunction.Carmichael` | 19 | 2 |

**Representative Mathlib declarations:**
- `sigma_one_apply` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `(n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d`
- `sigma_one_apply_prime_pow` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `{p i : ℕ} (hp : p.Prime) : σ 1 (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k`
- `isMultiplicative_sigma` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `{k : ℕ} : IsMultiplicative (σ k)`
- `cardFactors_zero` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `: Ω 0 = 0`
- `cardFactors_one` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `: Ω 1 = 0`
- `cardFactors_apply` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `{n : ℕ} : Ω n = n.primeFactorsList.length`
- `ArithmeticFunction.moebius_apply_of_squarefree` (`Mathlib.NumberTheory.ArithmeticFunction.Moebius`): `{n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n`
- `ArithmeticFunction.IsMultiplicative.prodPrimeFactors` (`Mathlib.NumberTheory.ArithmeticFunction.Misc`): `[CommMonoidWithZero R] (f : ℕ → R) : IsMultiplicative (prodPrimeFactors f)`

### 3. Prime Factorization, Exact Prime Powers (`ordProj` / `ordCompl`) & Valuations

Exact component extraction (`ordProj[p] n`, `ordCompl[p] n`), `Nat.factorization`, `IsPrimePow`, `padicValNat`, coprime splitting (`ordProj_mul_ordCompl_eq_self`), square characterizations (`Nat.isSquare_iff_even_factorization`), and LCM/GCD valuations.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.Data.Nat.Factorization.Basic` | 77 | 18 |
| `Mathlib.Data.Nat.Factorization.Defs` | 43 | 5 |
| `Mathlib.Data.Nat.Factorization.PrimePow` | 19 | 4 |
| `Mathlib.Data.Nat.Factorization.LCM` | 10 | 1 |
| `Mathlib.Algebra.IsPrimePow` | 20 | 2 |
| `Mathlib.NumberTheory.Padics.PadicVal.Basic` | 84 | 3 |
| `Mathlib.NumberTheory.Multiplicity` | 25 | 5 |

**Representative Mathlib declarations:**
- `Nat.ordCompl_dvd` (`Mathlib.Data.Nat.Factorization.Basic`): `(n p : ℕ) : ordCompl[p] n ∣ n`
- `Nat.ordCompl_le` (`Mathlib.Data.Nat.Factorization.Basic`): `(n p : ℕ) : ordCompl[p] n ≤ n`
- `Nat.ordCompl_mul` (`Mathlib.Data.Nat.Factorization.Basic`): `(a b p : ℕ) : ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b`
- `IsPrimePow.exists_ordCompl_eq_one` (`Mathlib.Data.Nat.Factorization.PrimePow`): `{n : ℕ} (h : IsPrimePow n) : ∃ p : ℕ, p.Prime ∧ ordCompl[p] n = 1`
- `exists_ordCompl_eq_one_iff_isPrimePow` (`Mathlib.Data.Nat.Factorization.PrimePow`): `{n : ℕ} (hn : n ≠ 1) : IsPrimePow n ↔ ∃ p : ℕ, p.Prime ∧ ordCompl[p] n = 1`
- `Nat.ordProj_pos` (`Mathlib.Data.Nat.Factorization.Basic`): `(n p : ℕ) : 0 < ordProj[p] n`
- `Nat.ordProj_of_not_prime` (`Mathlib.Data.Nat.Factorization.Basic`): `(n p : ℕ) (hp : ¬p.Prime) : ordProj[p] n = 1`
- `Nat.ordProj_mul_ordCompl_eq_self` (`Mathlib.Data.Nat.Factorization.Basic`): `(n p : ℕ) : ordProj[p] n * ordCompl[p] n = n`

### 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders

Bang-Zsigmondy / primitive prime divisor machinery, `Polynomial.cyclotomic` roots modulo `r` (`isRoot_cyclotomic_prime_pow_mul_iff_of_charP`), prime divisors of `Φ_n(a)`, lower bounds `(b - 1)^φ(d) < |Φ_d(b)|`, `orderOf` in `(ZMod r)ˣ`, and primes congruent to `1 mod n`.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` | 58 | 1 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` | 15 | 2 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Expand` | 9 | 2 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization` | 5 | 1 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Roots` | 18 | 1 |
| `Mathlib.Algebra.Ring.GeomSum` | 54 | 13 |
| `Mathlib.GroupTheory.OrderOfElement` | 170 | 7 |
| `Mathlib.NumberTheory.PrimesCongruentOne` | 3 | 1 |

**Representative Mathlib declarations:**
- `cyclotomic_two` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`): `(R : Type*) [Ring R] : cyclotomic 2 R = X + 1`
- `cyclotomic'_splits` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`): `(n : ℕ) : Splits (cyclotomic' n K)`
- `cyclotomic_three` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`): `(R : Type*) [Ring R] : cyclotomic 3 R = X ^ 2 + X + 1`
- `Polynomial.cyclotomic_eval_le_add_one_pow_totient` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Eval`): `{q : ℝ} (hq' : 1 < q) : ∀ n, (cyclotomic n ℝ).eval q ≤ (q + 1) ^ totient n`
- `Polynomial.cyclotomic_eval_lt_add_one_pow_totient` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Eval`): `{n : ℕ} {q : ℝ} (hn' : 3 ≤ n) (hq' : 1 < q) : (cyclotomic n ℝ).eval q < (q + 1) ^ totient n`
- `Polynomial.cyclotomic_pos` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Eval`): `{n : ℕ} (hn : 2 < n) {R} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) : 0 < eval x (cycloto...`
- `Polynomial.cyclotomic_six` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Expand`): `(R : Type*) [Ring R] : cyclotomic 6 R = X ^ 2 - X + 1`
- `Polynomial.cyclotomic_irreducible_of_irreducible_pow` (`Mathlib.RingTheory.Polynomial.Cyclotomic.Expand`): `{p : ℕ} (hp : Nat.Prime p) {R} [CommRing R] [IsDomain R] {n : ℕ} (hn : n ≠ 0) (h : Irreducible (cyclotomic ...`

### 5. Quadratic Reciprocity, Legendre/Jacobi Symbols & Finite Fields

Direction constraints on prime-forcing edges (`3 mod 4` reciprocity), Euler's criterion, quadratic characters mod `4` and `8`, Jacobi symbol evaluation without primality, and finite-field multiplicative group structure.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` | 10 | 9 |
| `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol` | 50 | 4 |
| `Mathlib.NumberTheory.LegendreSymbol.Basic` | 30 | 1 |
| `Mathlib.FieldTheory.Finite.Basic` | 80 | 52 |
| `Mathlib.Algebra.Field.ZMod` | 0 | 3 |

**Representative Mathlib declarations:**
- `legendreSym.at_two` (`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`): `(hp : p ≠ 2) : legendreSym p 2 = χ₈ p`
- `legendreSym.at_neg_two` (`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`): `(hp : p ≠ 2) : legendreSym p (-2) = χ₈' p`
- `legendreSym.quadratic_reciprocity_one_mod_four` (`Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity`): `(hp : p % 4 = 1) (hq : q ≠ 2) : legendreSym q p = legendreSym p q`
- `jacobiSym.legendreSym.to_jacobiSym` (`Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`): `(p : ℕ) [fp : Fact p.Prime] (a : ℤ) : legendreSym p a = J(a \| p)`
- `jacobiSym` (`Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`): `(a : ℤ) (b : ℕ) : ℤ`
- `jacobiSym.zero_right` (`Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`): `(a : ℤ) : J(a \| 0) = 1`
- `legendreSym.at_neg_one` (`Mathlib.NumberTheory.LegendreSymbol.Basic`): `(hp : p ≠ 2) : legendreSym p (-1) = χ₄ p`
- `legendreSym.at_zero` (`Mathlib.NumberTheory.LegendreSymbol.Basic`): `: legendreSym p 0 = 0`

### 6. Pell Equations, `Zsqrtd`, Squares & Exponential Diophantine Tools

Ljunggren / Nagell-Ljunggren reductions, Pell solution groups (`Pell.Solution1`), norm-one elements in `ℤ[√d]` (also used in Brillhart-Lehmer-Selfridge quadratic primality certificates), and Lucas-Lehmer / primality proving tactics.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.NumberTheory.Pell` | 59 | 2 |
| `Mathlib.NumberTheory.PellMatiyasevic` | 81 | 1 |
| `Mathlib.NumberTheory.Zsqrtd.Basic` | 107 | 5 |
| `Mathlib.NumberTheory.LucasLehmer` | 75 | 1 |
| `Mathlib.Tactic.Primality` | 3 | 26 |
| `Mathlib.Tactic.NormNum.Prime` | 19 | 3 |

**Representative Mathlib declarations:**
- `Pell.dnsq` (`Mathlib.NumberTheory.PellMatiyasevic`): `(a1 : 1 < a) : Zsqrtd.Nonsquare (d a)`
- `Zsqrtd.dmuld` (`Mathlib.NumberTheory.Zsqrtd.Basic`): `: sqrtd (d`
- `Zsqrtd.re_zero` (`Mathlib.NumberTheory.Zsqrtd.Basic`): `: (0 : ℤ√d).re = 0`
- `Zsqrtd.im_zero` (`Mathlib.NumberTheory.Zsqrtd.Basic`): `: (0 : ℤ√d).im = 0`
- `lucas_lehmer_sufficiency` (`Mathlib.NumberTheory.LucasLehmer`): `(p : ℕ) (w : 1 < p) : LucasLehmerTest p → (mersenne p).Prime`
- `lucas_lehmer_necessity` (`Mathlib.NumberTheory.LucasLehmer`): `(p : ℕ) (w : 3 ≤ p) (hp : (mersenne p).Prime) : LucasLehmerTest p`

### 7. Logarithmic, Prime-Reciprocal & Rational Envelope Inequalities

Underutilized analytical bridge for formalizing Zelinsky (2025) prime-reciprocal bounds (`∑ 1/p < log 2 - ...`), subexponential index envelopes `(1 + 1/K)^j`, and sharp abundancy-product upper bounds via `Real.log`.

| Mathlib Module | Public Decls | `OddPerfect` Imports |
| --- | ---: | ---: |
| `Mathlib.Analysis.SpecialFunctions.Log.Basic` | 110 | 3 |
| `Mathlib.Analysis.SpecialFunctions.Log.Sum` | 7 | 1 |
| `Mathlib.Analysis.SpecialFunctions.Log.Monotone` | 5 | 1 |
| `Mathlib.NumberTheory.SumPrimeReciprocals` | 8 | 1 |
| `Mathlib.NumberTheory.PrimeCounting` | 57 | 2 |

**Representative Mathlib declarations:**
- `Real.lt_log_one_add_of_pos` (`Mathlib.Analysis.SpecialFunctions.Log.Basic`): `{x : ℝ} (hx : 0 < x) : 2 * x / (x + 2) < log (1 + x)`
- `Real.le_log_one_add_of_nonneg` (`Mathlib.Analysis.SpecialFunctions.Log.Basic`): `{x : ℝ} (hx : 0 ≤ x) : 2 * x / (x + 2) ≤ log (1 + x)`
- `Complex.summable_log_one_add_of_summable` (`Mathlib.Analysis.SpecialFunctions.Log.Summable`): `{f : ι → ℂ} (hf : Summable f) : Summable (fun i ↦ log (1 + f i))`
- `Real.summable_log_one_add_of_summable` (`Mathlib.Analysis.SpecialFunctions.Log.Summable`): `(hf : Summable f) : Summable (fun i ↦ log (1 + f i))`
- `Real.log_prod` (`Mathlib.Analysis.SpecialFunctions.Log.Basic`): `{α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ x ∈ s, f x ≠ 0) : log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i)`
- `Finsupp.log_prod` (`Mathlib.Analysis.SpecialFunctions.Log.Basic`): `{α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → ℝ) (hg : ∀ a, g a (f a) = 0 → f a = 0) : log (f.prod g) = ...`

---

## High-Value Underutilized Mathlib Modules (Strategic Opportunities)

These modules are already compiled in `.lake/build` on the pinned commit, contain
relevant number-theoretic or analytic lemmas, and currently have **≤ 2** imports across
structural `OddPerfect/` modules:

| Module | Domain | Public Decls | Current Imports |
| --- | --- | ---: | ---: |
| `Mathlib.NumberTheory.Divisors` | 1. Divisors, Perfection, Abundancy & Factorisation Properties | 125 | 2 |
| `Mathlib.Data.Nat.Factorization.Divisors` | 1. Divisors, Perfection, Abundancy & Factorisation Properties | 8 | 1 |
| `Archive.Wiedijk100Theorems.PerfectNumbers` | 1. Divisors, Perfection, Abundancy & Factorisation Properties | 7 | 2 |
| `Mathlib.NumberTheory.ArithmeticFunction.Zeta` | 2. Arithmetic Functions (`σ`, `ω`, `Ω`, `ζ`, `μ`) & Multiplicativity | 32 | 1 |
| `Mathlib.NumberTheory.ArithmeticFunction.Moebius` | 2. Arithmetic Functions (`σ`, `ω`, `Ω`, `ζ`, `μ`) & Multiplicativity | 35 | 2 |
| `Mathlib.NumberTheory.ArithmeticFunction.Carmichael` | 2. Arithmetic Functions (`σ`, `ω`, `Ω`, `ζ`, `μ`) & Multiplicativity | 19 | 2 |
| `Mathlib.Data.Nat.Factorization.LCM` | 3. Prime Factorization, Exact Prime Powers (`ordProj` / `ordCompl`) & Valuations | 10 | 1 |
| `Mathlib.Algebra.IsPrimePow` | 3. Prime Factorization, Exact Prime Powers (`ordProj` / `ordCompl`) & Valuations | 20 | 2 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` | 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders | 58 | 1 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Eval` | 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders | 15 | 2 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Expand` | 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders | 9 | 2 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization` | 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders | 5 | 1 |
| `Mathlib.RingTheory.Polynomial.Cyclotomic.Roots` | 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders | 18 | 1 |
| `Mathlib.NumberTheory.PrimesCongruentOne` | 4. Cyclotomic Polynomials, Geometric Sums & Multiplicative Orders | 3 | 1 |
| `Mathlib.NumberTheory.LegendreSymbol.Basic` | 5. Quadratic Reciprocity, Legendre/Jacobi Symbols & Finite Fields | 30 | 1 |
| `Mathlib.NumberTheory.Pell` | 6. Pell Equations, `Zsqrtd`, Squares & Exponential Diophantine Tools | 59 | 2 |
| `Mathlib.NumberTheory.PellMatiyasevic` | 6. Pell Equations, `Zsqrtd`, Squares & Exponential Diophantine Tools | 81 | 1 |
| `Mathlib.NumberTheory.LucasLehmer` | 6. Pell Equations, `Zsqrtd`, Squares & Exponential Diophantine Tools | 75 | 1 |
| `Mathlib.Analysis.SpecialFunctions.Log.Sum` | 7. Logarithmic, Prime-Reciprocal & Rational Envelope Inequalities | 7 | 1 |
| `Mathlib.Analysis.SpecialFunctions.Log.Monotone` | 7. Logarithmic, Prime-Reciprocal & Rational Envelope Inequalities | 5 | 1 |
| `Mathlib.NumberTheory.SumPrimeReciprocals` | 7. Logarithmic, Prime-Reciprocal & Rational Envelope Inequalities | 8 | 1 |
| `Mathlib.NumberTheory.PrimeCounting` | 7. Logarithmic, Prime-Reciprocal & Rational Envelope Inequalities | 57 | 2 |

## Lean 4 / Mathlib Proof Automation Checklist for Neon Workers

- **Arithmetic & linear/integer goals**: `omega`, `lia`, `grind`, `norm_num`, `positivity`, `gcongr`.
- **Ring / field identities**: `ring`, `linear_combination`, `field_simp`.
- **Finite residue / small exponent exhaustion**: `interval_cases`, `fin_cases`, `decide`, `decide +kernel`.
- **Primality certificates**: `norm_num` (`Mathlib.Tactic.NormNum.Prime`), Pratt/Lucas (`Mathlib.Tactic.Primality`), or project Pocklington/BLS checkers (`OddPerfect.LargeOrderPrime`, `OddPerfect.LargeOrderCube`, `OddPerfect.LargeOrderQuadratic`).
- **Interactive lemma discovery inside temporary scratch checks**: `exact?`, `apply?`, `rw?`.
