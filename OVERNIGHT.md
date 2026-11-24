# Overnight proof report

The existence of an odd perfect number remains open. This report tracks verified milestones during the run scheduled through November 24, 2026 at 7:00 a.m. Chicago time.

## Strongest unconditional count theorem at this checkpoint

For **every** odd perfect N, `18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 31`. This is Ochem and Rao's published Theorem 1. Its local proof covers both the presence and absence of 3 and has received independent review against the paper. The exact declaration is `OddPerfect.ochem_rao_prime_factor_count`. [Lean proof](OddPerfect/OchemRao.lean) · [Ochem–Rao, §3](https://www.lirmm.fr/~ochem/opn/opnf.pdf)

Every odd perfect number N satisfies **Ω(N) ≥ 37** and **N > 10⁵⁰**. The first theorem counts prime factors with multiplicity and reproduces Iannucci and Sorli’s bound. The second reproduces Hagis’s 1973 bound using a fresh exact-exponent proof. Both declarations quantify over every odd perfect natural number. The count certificate uses 101 reusable subtree proofs covering two roots and an analytic bound for the complement. The size proof handles least primes 3, 5 and 7, followed by a separate bound for the complement. [Count declaration and certificate](research/COUNT_CHAIN.md) · [Size declaration](OddPerfect/SizeBound50.lean) · [Size certificate](research/ABSOLUTE_SIZE.md)

## Structural theorem

The project also proves Dickson's finiteness theorem. For each k, the set of odd perfect natural numbers with at most k distinct prime divisors is finite. The declaration `OddPerfect.dickson_finite` has received independent review. Its proof gives an explicit recursive upper bound depending on k. The bounds vary with k. [Lean proof](OddPerfect/Dickson.lean) · [Mathematical argument](research/DICKSON.md)

A kernel-checked finite sieve forces a prime divisor greater than 257. It yields Sylvester's distinct-prime bounds of five in general and eight when 3 is absent. Excluding all seven odd primes through 19 raises the checked lower bound to 115. [Support certificate](research/SUPPORT.md) · [Cardinality proofs](research/SIEVE.md)

For **every** exact prime-power component qᵃ of an odd perfect N, the integral quotient σ(N/qᵃ)/qᵃ is greater than five. The declaration `OddPerfect.five_lt_divisor_sum_component_index` proves Dris and Luca's Theorem 1.1. An independent worker checked the universal hypotheses, the Euler and nonspecial cases, and each finite endpoint. [Lean proof](OddPerfect/DrisLuca.lean) · [Argument and source](research/RECIPROCAL.md)

The same paper's Theorem 1.2 is checked as `OddPerfect.finite_of_bounded_component_index`. For every real K, only finitely many odd perfect numbers have an exact component of index below K. The project gives an explicit bound, using Dickson finiteness and a count of exceptional components with multiplicity. [Lean proof](OddPerfect/BoundedIndex.lean)

Every component index is composite. Every exact component index also differs from every prime square. The Euler component index has at least three prime factors counted with multiplicity and is at least 165. There are additional restrictions on index primes that are 3 modulo 4 and occur to odd valuation. [Index lower bound](OddPerfect/IndexBound165.lean) · [Square-class bounds](research/EULER_SQUARE_CLASS.md)

For an Euler prime q and any positive exponent e, σ(qᵉ) is never square. For an odd perfect number in Euler form with a > 1, the index σ(m²)/qᵃ is also never square. Hirakawa’s stronger prime-times-square claim is checked for the branches q ≢ 1 modulo 16, or any of 3, 5, 7, 11 and 13 dividing (a+1)/2. [Exact results and sources](research/HIRAKAWA.md)

When the Euler exponent is one, the index is at least 22,971. For a > 1, a prime-times-square index forces (a+1)/2 to be a prime s or its square. In the square case s must divide q−1. The proof counts how many primes have odd valuation in the geometric blocks of the index. [Exponent-one proof](OddPerfect/ExponentOneIndex.lean) · [Half-length argument](research/HALF_LENGTH_SUPPORT.md)

For each prime divisor q, `OddPerfect.prime_cube_lt_three_mul` proves q³ < 3N. The separate rank theorem `OddPerfect.prime_rank_bound` gives 2t^(2j) < 3N when j of the prime divisors are at least t > 0. [Sources and proofs](research/PRIME_SIZES.md)

For every odd perfect natural number N, there are distinct prime divisors p and q such that p and its exponent are both 1 modulo 4, while the exponent of q is even and at least four. This proves Steuerwald's 1937 theorem. Its Lean declaration is `OddPerfect.steuerwald`. The proof covers both possibilities for 3 dividing N. [Declaration](OddPerfect/Steuerwald.lean) · [Source and independent case review](research/STEUERWALD.md)

It follows that Ω(N) ≥ 2ω(N)+1. Here Ω counts prime factors with multiplicity and ω counts distinct primes. The declaration is `OddPerfect.steuerwald_prime_factor_count`. [Prime counts](OddPerfect/Counts.lean)

## Published works and checked examples

The project contains checked proofs of Euler form, Sylvester's exclusion of multiples of 105, Touchard's congruence, Roberts's refinement, the exact-square chain steps at 3 and 13 from Iannucci–Sorli, and Steuerwald's fourth-power result. It also checks five even perfect numbers using mathlib's Euclid–Euler theorem. The corpus records the sources and the outstanding work for stronger published bounds. [Literature corpus](research/CORPUS.md) · [Euler replay](research/EULER.md)

For every perfect N divisible by 13, the 13-component forces 7, 61, or a different prime of at least 23, with a witness in the remaining even exponent classes. The endpoint identity for a single coprime spoof base holds for a genuine perfect number exactly when that base is prime. Lean computes Descartes's actual divisor sum as 426,027,470,778. Its value passes the Euler, Touchard and 105 tests and fails the fourth-power test. [Exponents at 13](OddPerfect/ThirteenRemainder.lean) · [Spoof calculation](OddPerfect/Spoof.lean) · [Candidate sets](OddPerfect/CandidateSets.lean)

Dittmer's Lemma 7.1 and Corollaries 7.2–7.3 and the BYU group's positive finiteness Corollary 4.3 are checked. Every hypothetical odd perfect number has a normalized formally balanced factorization with prime lengths and a single linear entry whose base is a prime. The canonical refinement preserves the actual divisor sum. For any fixed number of entries there are only finitely many positive odd spoof-perfect factorizations, even allowing repeated bases and the base one. [Normalization and inclusion](OddPerfect/QuasiFactors.lean) · [Finiteness](research/DICKSON.md)

The normalized candidate set also requires a genuine prime fourth power. This rules out Descartes’s integer in every allowed normalized representation, including alternatives to its historical factorization. The proof uses the uniquely prescribed linear entry and splits on whether its base also occurs as a square entry. [Checked theorem](OddPerfect/FourthPowerSpoof.lean) · [Case analysis](research/SPOOFS.md)

The related quasiperfect equation σ(N)=2N+1 is equivalent to omitting the proper divisor one. The project proves Cattaneo’s odd-square restriction, deficiency of every proper divisor, and the restriction to residues 1 or 3 modulo 8 for every divisor of σ(N). These conditions apply to a different equation and its own candidate set. [Quasiperfect proofs](OddPerfect/Quasiperfect.lean) · [Hagis–Cohen, properties A–C](https://doi.org/10.1017/S1446788700018401)

## Reproduce

On the research branch with Elan installed, run these commands from the repository root.

```sh
lake build
lake lean research/Audit.lean
```

Lean is pinned to v4.36.0 and mathlib to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The audit checks the imported project declarations and prints the types and axiom dependencies of the named theorems. Each proof uses only standard foundations. [Audit](research/Audit.lean)

## Remaining question and next assignment

The general existence question remains open. A nonspecial fourth power, Ω ≥ 37, and N > 10⁵⁰ are now necessary. The next numerical assignment is to replay the eight prime-index seed families for Brent and Cohen’s 10¹⁶⁰ bound and prove that their complements are covered. A separate structural track tests whether the remaining prime or prime-square half-lengths can give a prime-times-square Euler index. [Branch ledger](research/LEDGER.md) · [Size results and reproduction](research/ABSOLUTE_SIZE.md)
