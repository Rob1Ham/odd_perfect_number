# Overnight proof report

The existence of an odd perfect number remains open. This report tracks verified milestones during the run scheduled through November 24, 2026 at 7:00 a.m. Chicago time.

## Strongest unconditional count theorem at this checkpoint

For **every** odd perfect N, `18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 31`. This is Ochem and Rao's published Theorem 1. Its local proof covers both the presence and absence of 3 and has received independent review against the paper. The exact declaration is `OddPerfect.ochem_rao_prime_factor_count`. [Lean proof](OddPerfect/OchemRao.lean) · [Ochem–Rao, §3](https://www.lirmm.fr/~ochem/opn/opnf.pdf)

The absolute lower bound is now **Ω(N) ≥ 25**, where Ω counts prime factors with multiplicity. The declaration `OddPerfect.twenty_five_le_total_prime_factor_count` uses a kernel-checked tree of 5,336 nodes to exclude every case with Ω ≤ 23, together with the fact that Ω is odd. [Lean theorem](OddPerfect/CountBound25.lean) · [Certificate and reproduction](research/COUNT_CHAIN.md)

## Structural theorem

The project also proves Dickson's finiteness theorem. For each k, the set of odd perfect natural numbers with at most k distinct prime divisors is finite. The declaration `OddPerfect.dickson_finite` has received independent review. Its proof gives an explicit recursive upper bound depending on k. The bounds vary with k. [Lean proof](OddPerfect/Dickson.lean) · [Mathematical argument](research/DICKSON.md)

A kernel-checked finite sieve forces a prime divisor greater than 257. It yields Sylvester's distinct-prime bounds of five in general and eight when 3 is absent. Excluding all seven odd primes through 19 raises the checked lower bound to 115. [Support certificate](research/SUPPORT.md) · [Cardinality proofs](research/SIEVE.md)

For **every** exact prime-power component qᵃ of an odd perfect N, the integral quotient σ(N/qᵃ)/qᵃ is greater than five. The declaration `OddPerfect.five_lt_divisor_sum_component_index` proves Dris and Luca's Theorem 1.1. An independent worker checked the universal hypotheses, the Euler and nonspecial cases, and each finite endpoint. [Lean proof](OddPerfect/DrisLuca.lean) · [Argument and source](research/RECIPROCAL.md)

The same paper's Theorem 1.2 is checked as `OddPerfect.finite_of_bounded_component_index`. For every real K, only finitely many odd perfect numbers have an exact component of index below K. The project gives an explicit bound, using Dickson finiteness and a count of exceptional components with multiplicity. [Lean proof](OddPerfect/BoundedIndex.lean)

Every component index is composite. For the Euler component specifically, the checked lower bound is 21. There are additional restrictions on index primes that are 3 modulo 4 and occur to odd valuation. [Index lower bound](OddPerfect/FermatIndexSupport.lean) · [Square-class bounds](research/EULER_SQUARE_CLASS.md)

For each prime divisor q, `OddPerfect.prime_cube_lt_three_mul` proves q³ < 3N. The separate rank theorem `OddPerfect.prime_rank_bound` gives 2t^(2j) < 3N when j of the prime divisors are at least t > 0. [Sources and proofs](research/PRIME_SIZES.md)

For every odd perfect natural number N, there are distinct prime divisors p and q such that p and its exponent are both 1 modulo 4, while the exponent of q is even and at least four. This proves Steuerwald's 1937 theorem. Its Lean declaration is `OddPerfect.steuerwald`. The proof covers both possibilities for 3 dividing N. [Declaration](OddPerfect/Steuerwald.lean) · [Source and independent case review](research/STEUERWALD.md)

It follows that Ω(N) ≥ 2ω(N)+1. Here Ω counts prime factors with multiplicity and ω counts distinct primes. The declaration is `OddPerfect.steuerwald_prime_factor_count`. [Prime counts](OddPerfect/Counts.lean)

## Published works and checked examples

The project contains checked proofs of Euler form, Sylvester's exclusion of multiples of 105, Touchard's congruence, Roberts's refinement, the exact-square chain steps at 3 and 13 from Iannucci–Sorli, and Steuerwald's fourth-power result. It also checks five even perfect numbers using mathlib's Euclid–Euler theorem. The corpus records the sources and the outstanding work for stronger published bounds. [Literature corpus](research/CORPUS.md) · [Euler replay](research/EULER.md)

For every perfect N divisible by 13, the 13-component forces 7, 61, or a different prime of at least 23, with a witness in the remaining even exponent classes. The endpoint identity for a single coprime spoof base holds for a genuine perfect number exactly when that base is prime. Lean computes Descartes's actual divisor sum as 426,027,470,778. Its value passes the Euler, Touchard and 105 tests and fails the fourth-power test. [Exponents at 13](OddPerfect/ThirteenRemainder.lean) · [Spoof calculation](OddPerfect/Spoof.lean) · [Candidate sets](OddPerfect/CandidateSets.lean)

Dittmer's Lemma 7.1 and Corollaries 7.2–7.3 and the BYU group's positive finiteness Corollary 4.3 are checked. Every hypothetical odd perfect number has a normalized formally balanced factorization with prime lengths and a single linear entry whose base is a prime. The canonical refinement preserves the actual divisor sum. For any fixed number of entries there are only finitely many positive odd spoof-perfect factorizations, even allowing repeated bases and the base one. [Normalization and inclusion](OddPerfect/QuasiFactors.lean) · [Finiteness](research/DICKSON.md)

## Reproduce

On the research branch with Elan installed, run these commands from the repository root.

```sh
lake build
lake lean research/Audit.lean
```

Lean is pinned to v4.36.0 and mathlib to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The audit checks the imported project declarations and prints the types and axiom dependencies of the named theorems. Each proof uses only standard foundations. [Audit](research/Audit.lean)

## Remaining question and next assignment

Candidates with a nonspecial fourth power and Ω ≥ 25 survive. Distinct multiplicative orders force distinct primes for a fixed source, while different sources can reuse the same prime. The next assignment is to close the trees with Ω ≤ 27 by bounding the smallest unassigned prime from its required abundancy whenever factoring a forced divisor sum stalls. This would raise the unconditional bound to 29. [Branch ledger](research/LEDGER.md) · [Certificate method](research/COUNT_CHAIN.md)
