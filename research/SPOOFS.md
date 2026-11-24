# What Descartes's example rules out

For coprime positive integers `m,w` with `w > 1`, consider the equation

```text
σ(m) (w + 1) = 2mw.
```

`OddPerfect.perfect_iff_prime_of_spoof_balance` proves that, under these hypotheses, `mw` is perfect exactly when `w` is prime. The genuine divisor sum of `mw` is `σ(m)σ(w)`. For a prime, `σ(w) = w+1`. A composite integer greater than one has an additional positive divisor. Consequently `σ(w) > w+1`.

The Lean predicate `OddPerfect.SingleCompositeSpoof m w` requires both factors odd, coprimality, the displayed equation, and a composite `w > 1`. Its theorems `true_sigma_gt`, `abundant` and `not_perfect` apply to every such pair. Oddness of a natural number implies positivity. The local proof of the strict inequality uses mathlib's characterization of primes by a proper-divisor sum of one.

## Descartes's factorization

| Quantity | Checked value |
| --- | ---: |
| Ordinary part `m = (3 · 7 · 11 · 13)²` | 9,018,009 |
| Distinguished base `w = 19² · 61` | 22,021 |
| Product `mw` | 198,585,576,189 |
| True `σ(m)` | 18,035,199 |
| Substituted `σ(m)(w+1) = 2mw` | 397,171,152,378 |
| True `σ(mw)` | 426,027,470,778 |

`descartes_singleCompositeSpoof` checks membership. `descartes_true_sigma` checks the actual sum after separating the four smaller coprime prime powers of `m` and the coprime factors 361 and 61 of `w`. All computations run in Lean's kernel. The largest individual divisor set in these calculations comes from 361.

## Coverage in the literature

- Banks, Güloğlu, Nevans and Saidak study the single distinguished base equation. In a later clarification Banks explained that their definition omits a coprimality requirement. The local theorem explicitly requires coprimality to evaluate the true divisor sum multiplicatively. [Published chapter](https://doi.org/10.1090/crmp/046/12) · [Banks's clarification reproduced by J. A. B. Dris](https://math.stackexchange.com/questions/1178386/about-descartes-numbers)
- Dittmer allows positive quasi-prime bases at least two. Bases may be composite, repeated or have common factors. His classification with fewer than seven quasi-prime factors uses that definition. [Definitions 1.1, 1.3 and 1.4](https://www.ams.org/journals/mcom/2014-83-289/S0025-5718-2013-02793-7/S0025-5718-2013-02793-7.pdf)
- The BYU Computational Number Theory Group allows integer bases and positive exponents. Its formal divisor sum multiplies the geometric sums associated to the specified factorization. Genuine perfect numbers in their ordinary prime factorization satisfy the formal equation. Voight's example has a negative base. Other examples in the paper use repeated bases. The classification of 21 cases concerns nontrivial, primitive, odd factorizations with fewer than seven bases. These are published results outside the scope of the local Lean certificates. [Definition 1.1 and Examples 1.2–1.4](https://mathdept.byu.edu/~pace/Spoof_web.pdf) · [arXiv record](https://arxiv.org/abs/2006.10697)

## Consequence for a search

A search that checks only the relaxed equation can retain the displayed composite-base pair. Verifying primality at each use of the prime-power divisor-sum formula removes this false positive. With coprime factors and the displayed equation, a hypothetical genuine solution would have to lie in the prime branch. There is no theorem here producing a composite distinguished base for every hypothetical odd perfect number. Such a coverage theorem, together with the strict inequality, would imply nonexistence. Removing this one class leaves the original existence question open.

Reproduce the local results with `lake build OddPerfect.Spoof`.

## Positive factorizations with several bases

For a finite collection of positive bases `bᵢ > 1` with exponents `eᵢ > 0`, let `F` be the product of the geometric sums `1 + bᵢ + ⋯ + bᵢ^eᵢ` and `N` the product of the stated powers. The following two tests apply to any number of bases and any positive exponents.

| Hypotheses | Comparison | Consequence when `F = 2N` |
| --- | --- | --- |
| Pairwise coprime bases, all prime | `F = σ(N)` | Genuine perfection |
| Pairwise coprime bases, some composite | `F < σ(N)` | Abundance |
| All prime bases, some repeated | `σ(N) < F` | Deficiency |
| Positive bases with a composite and a common factor | No general comparison proved here | Open in this analysis |

The first two rows exhaust the pairwise coprime class. For a composite base its smallest prime divisor lies strictly between 1 and the base. It divides every positive power and is missing from the geometric progression. Coprimality then multiplies the inequalities. The equivalence `formalSigma_eq_iff_prime` and the abundance conclusion `abundant_of_formalSigma_eq_two_mul_of_composite` are in `OddPerfect/SpoofFactors.lean`.

The third row follows from a collision among divisor pairs. Each divisor of `ab` is a product of a divisor of `a` and a divisor of `b`. If `d > 1` divides both, the ordered pairs `(d,1)` and `(1,d)` contribute the same divisor to that product. This gives strict submultiplicativity of the true divisor sum for positive inputs with a common factor. The theorem `deficient_of_repeated_prime_spoof` in `OddPerfect/RepeatedPrimes.lean` applies it at a repeated prime. Signed bases and unit bases lie outside all four rows. A genuine odd perfect number would enter the first row via its ordinary prime factorization.

## Normalized factorizations and the fourth-power test

Dittmer refines a prime power by factoring its length e+1 into prime blocks. The integer and its geometric sum are preserved at each split. Starting from the genuine prime factorization and putting the only block of length two first in its component yields exactly one linear entry with prime base. The order matters. Refining 5⁵ with block lengths 3,2 gives (5,2),(125,1), while lengths 2,3 give (5,1),(25,2). Both products and formal sums agree. For the actual prime factorization of any positive N the resulting formal balance is equivalent to perfection. [Dittmer, §7](https://doi.org/10.1090/S0025-5718-2013-02793-7) · [Proofs](../OddPerfect/QuasiFactors.lean)

The set `normalizedSpoofCandidates` allows any factorization satisfying the prime-power base condition, prime lengths, formal balance, and the single linear prime condition. Every odd perfect number lies in it. Whether it contains additional integers remains open. For every member N, `exists_prime_fourth_of_normalized_spoof` proves that some genuine prime fourth power divides N. Assume otherwise. Each nonlinear entry has even exponent at least two and a base that is a power of a prime, so it must be exactly (p,2). Write q for the base of the single linear entry. If (q,2) is absent, no primes repeat and the formal sum equals the true divisor sum. Perfection would then force a fourth power by Steuerwald. If (q,2) is present, every prime divisor p of N has a square entry, so p²+p+1 divides N. Some such factor forces 3 into N, directly or through a prime congruent to one modulo three. Iterating the quadratic at 3, 13, 61 and 97 puts 13, 61, 97 and 3169 in N. These four separate square entries each supply another factor of 3 to the formal sum, forcing 81 to divide N. An independent review checked both branches, the previously absent-3 case, and multiplicities of the four entries. [Fourth-power proof](../OddPerfect/FourthPowerSpoof.lean)

Descartes’s integer is cube-free, so it is excluded from every normalized representation. Its historical composite-base representation still balances. When all other components have been fixed, there is at most one positive final base and exponent. If U is the prefix formal sum and V twice its represented integer, reduce V/U to S/P. A possible final value must be P=bᵉ and have geometric sum S. Thus b=1+(P−1)/(S−P) and e is the integer logarithm of P to base b. Applied to Descartes’s four squared bases this recovers exactly (22021,1). [Cube-free exclusion](../OddPerfect/CubeFreeSpoof.lean) · [Completion formula](../OddPerfect/SpoofCompletion.lean)

The unique linear prime also fixes the squarefree part of every normalized candidate. Its value satisfies N=q·s², even if q divides s. Consequently these candidates are nonsquare. Every odd near-perfect number with one redundant divisor is square, so the two classes are disjoint. In particular Johnson’s example fails every normalized representation. [Shape and disjointness](../OddPerfect/NormalizedShape.lean)

## Least number of positive odd entries

Five is the exact minimum for a formally perfect list of entries with odd bases greater than one and positive exponents. The list may repeat a base or use composite bases with common factors. Descartes’s list supplies the upper bound. The lower bound covers each possible location of the exceptional Euler exponent at lengths one through four. The empty list has formal sum and value both one and cannot balance. A permutation sorting the bases preserves both products. [Exact minimum](../OddPerfect/SpoofBelowFive.lean) · [Ordering lemma](../OddPerfect/SpoofOrdering.lean)

The interval checker splits a base or exponent and proves that every balanced point goes into one of the two children. A terminal box closes by a strict rational abundancy comparison, incompatible endpoints, or the exact last-component formula. Each supplied offset must lead to proofs of both children. Python chooses the cuts and prints the tables. Lean checks the endpoints, inequalities and coverage. To regenerate the published modules, run `python3 research/spoof_certificate.py --four-project --chunk 23 --output OddPerfect/SpoofBelowFive`. Dittmer’s full positive classification through six entries also requires the cases of five and six entries. [Checker](../OddPerfect/SpoofCover.lean) · [Certificate generator](spoof_certificate.py) · [Dittmer, §6](https://doi.org/10.1090/S0025-5718-2013-02793-7)
