# Prime-factor counts

Write Ω for the number of prime factors of N counted with multiplicity and ω for the number of distinct prime factors. In mathlib these reduce to `N.primeFactorsList.length` and `N.primeFactors.card`. The project proves the following statements in `OddPerfect/Counts.lean`.

| Declaration | Scope and conclusion |
| --- | --- |
| `prime_factor_count_excess` | For any N with a prime factor p and even exponents at all other primes, Ω + 1 − 2ω is the sum of the special exponent minus one and the excess of each ordinary exponent over two. The Lean statement is an additive identity in the naturals. |
| `euler_prime_factor_count` | For every odd perfect N, 2ω ≤ Ω + 1. |
| `prime_factor_count_of_fourth_power` | If a prime fourth power divides an odd perfect N, then 2ω + 1 ≤ Ω. |
| `steuerwald_prime_factor_count` | For every odd perfect N, 2ω + 1 ≤ Ω, using Steuerwald’s nonspecial prime. |

The exact identity explains equality in Euler's bound. Each ordinary exponent on the support is even and positive, so contributes a nonnegative excess. Equality requires special exponent one and ordinary exponent two at every other prime. An ordinary prime of exponent at least four contributes at least two to the excess. These are counts on the exact factorization and require no finite search bound.

## Published bounds and their inputs

| Authors | Theorem | What its replay would require |
| --- | --- | --- |
| Ochem and Rao (2012) | Ω ≥ 101, N > 10¹⁵⁰⁰ | Certificate coverage for the authors' branching calculation, including exponent limits, arithmetic leaves and bounds for unfactored cofactors. [Published paper](https://doi.org/10.1090/S0025-5718-2012-02563-4) |
| Ochem and Rao (2014), Theorems 1 and 2 | 7Ω ≥ 18ω − 31 and Ω ≥ 2ω + 51 | The first proof is analytic. Its remaining combinatorial inputs include injectivity of a normalized quadratic divisor sum and a count of the multiplicities contributed by exact-square components (§3). The second uses a factor-chain computation (§4). [Published paper](https://doi.org/10.1090/S0025-5718-2013-02776-7) |
| Nielsen (2015) | ω ≥ 10 | The argument combines an upper bound, estimates for common prime factors of two component sums, and two computations. [Published paper](https://doi.org/10.1090/S0025-5718-2015-02941-X) |
| Zelinsky (2021), Theorem 2 | 113Ω ≥ 302ω − 286 if 3 is absent, and 25Ω ≥ 66ω − 125 if it is present | Bounds on the numbers of primes in the paper's partition of square components. [Published paper](https://math.colgate.edu/~integers/v76/v76.pdf) |
| Clayton and Hansen (2023), Theorems 1.3–1.4 | 37Ω ≥ 99ω − 187, strengthened to 19Ω ≥ 51ω − 46 when 3 is absent | Restrictions on factorizations of cyclotomic values, a classification of source primes, and verification of every inequality before linear optimization. [Published paper](https://math.colgate.edu/~integers/x79/x79.pdf) |

Ochem's project page reports further computations giving Ω ≥ 121 and Ω ≥ 2ω + 55. These are later figures attributed to the authors' project page. The certificates needed for a Lean replay of those computations are outside the present build. [Authors' research page](https://www.lirmm.fr/~ochem/opn/)

Ochem and Zelinsky's July 2026 preprint treats the narrower hypothesis that exactly one nonspecial exponent exceeds two. It reports divisibility by 3 raised to 23 billion. The hypothesis permits more than one nonspecial prime and constrains how many exponents are large. Its large numerical conclusion has no proof or certificate in this checkout. [Preprint](https://arxiv.org/abs/2607.19746)

## External Lean evidence

Google DeepMind's Formal Conjectures source contains `PerfectNumbers.odd_perfect_number.lower_bound`. Its statement includes Ω ≥ 101, but the proof body is a placeholder. The same source links a separate AlphaProof script for Euler form. The umpolungfish Euler and Touchard proofs and the local replay are documented in `research/EULER.md`. Neither external project supplied a completed proof of a modern prime-count bound in the inspected source. [Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/PerfectNumbers.lean) · [Linked AlphaProof script](https://github.com/mzhorvath1/formal-conjectures/blob/7deed78f7babe2ae9ea13969a8dfa26854982407/FormalConjectures/Wikipedia/PerfectNumbers.lean) · [Euler and Touchard source](https://github.com/umpolungfish/odd-perfect-numbers/blob/8819676aa1ce20652f5898a369250a048ff35c76/OddPerfectNumbers.lean)
