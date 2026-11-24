# Overnight research ledger

The target is `∃ n : ℕ, Odd n ∧ Nat.Perfect n`. The scheduled cutoff is November 24, 2026 at 7:00 a.m. America/Chicago (13:00 UTC). Until then, the coordinator assigns regular rounds of independent subagent proof work and review, with up to three workers at a time. Integrated milestones receive a statement and axiom check, a commit, and a push to the research branch.

## Round one

| Owner | Deliverable | Coverage |
| --- | --- | --- |
| Euler worker | Replay and audit a published Euler-form proof | Every hypothetical odd perfect number |
| Forcing worker | Factor forcing and the implication from exact exponent two at 3 | Every perfect number satisfying the indicated hypotheses |
| Review worker | Challenge the hypotheses and formalize the link from 13 to 61 | Exact exponent two at 13 initially |
| Coordinator | Pin dependencies, integrate proofs, inspect axioms and choose the next round | The full existence question remains open |

## Exact-power forcing

An exact exponent `e` means `p^e ∣ N` and `¬p^(e+1) ∣ N`. Every positive integer has one exact exponent at each prime. An odd divisor of the divisor sum of a coprime component of a perfect number divides the number itself. The exact exponent makes the prime-power component coprime to its cofactor.

| Parent case | Condition | Conclusion |
| --- | --- | --- |
| Perfect, exact exponent at 3 | `e = 2` | 13 divides the number |
| Perfect, exact exponent at 13 | `e % 6 = 2` | 61 divides the number |
| Same | `e % 6 = 1` or `3` | 7 divides the number |
| Same | `e % 6 = 5` | Both 7 and 61 divide the number |
| Same | `e % 6 = 0` or `4` | For `e > 0`, the component supplies a prime at least 23 different from 61. The bound is attained locally at `e = 10`. Other components could supply 7 or 61. |

The six possible remainders exhaust the exact exponents, including zero. The conclusion at 3 gives divisibility by 13 but leaves its exponent unknown. The congruence tests in `OddPerfect/Thirteen.lean` are equivalences for the local divisor sum and implications for the full number.

The literature track will cover published necessary conditions, factor-chain methods, computational bounds, formal proofs and spoof constructions. The coordinator records the status of each result and assigns further formalizations from the cited papers.

## Verified exclusions and open cases

- Euler form holds for every candidate. The port and the historical replay pass the standard-axiom audit. [Source and replay](EULER.md)
- Sylvester's exclusion eliminates all multiples of 105. If 3, 5 and 7 divide an odd perfect number, 3² and 7² also divide it, so its divisor 2205 is abundant. Every candidate either is a multiple of 105 or survives this exclusion.
- For perfect numbers containing 13, the final line of the residue table supplies a witness even with an unknown exponent. [Proof and counterexamples to weaker hypotheses](REVIEW.md)
- Steuerwald's 1937 theorem now eliminates candidates whose every nonspecial prime has exact exponent two. Both branches of the split on 3 dividing N passed independent review and the integrated audit. As a consequence Ω(N) ≥ 2ω(N)+1. Candidates with a nonspecial fourth power remain open. [Proof coverage](STEUERWALD.md) · [Counting corollaries](COUNTS.md)
- Descartes's positive composite-base spoof passes Euler form, Touchard's congruence and the 105 exclusion simultaneously. Its true prime factorization contains no fourth power, so it witnesses the strict containment proved by `fourthPowerCandidates_ssubset`. Every genuine odd perfect number lies in the smaller set. Its emptiness remains open. [Spoof calculation](SPOOFS.md)
- Active rounds address Ochem–Rao's prime-count inequality, primitive divisors of geometric sums and the extension of the spoof comparison to finite factorizations.

## Ochem–Rao's first count bound

The integrated project proves `18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 31` from exactly `Odd N` and `Nat.Perfect N`. The proof counts exact-square components other than 3, proves injectivity of the normalized quadratic divisor sum on the relevant primes, and bounds their transferred multiplicities by the true prime exponents. A separate worker checked the partition and the transfer against equations (1)–(8) in the paper. [Ochem–Rao, §3](https://www.lirmm.fr/~ochem/opn/opnf.pdf) · [Local counting argument](../OddPerfect/OchemRao.lean)

Two cases exhaust the sharper local conclusion. If 3 is absent then `18ω ≤ 7Ω + 15`. If 3 is present then `18ω + v₃(N) ≤ 7Ω + 33`. Neither case excludes all candidates. The separate bound `Ω ≥ 2ω + 51` in §4 still needs a computational proof.

For each true component exponent e of an odd perfect number, every divisor d>1 of e+1 occurs as an exact multiplicative order at another prime of the support. This bounds the divisor count of e+1 by ω(N). A second constraint requires every nonempty proper subset of the support to send an edge outside it. Within the finite support, paths may return to primes already visited. [Order theorem](../OddPerfect/CyclotomicOrders.lean) · [Cut theorem and remaining obstruction](CUTS.md)

## Bound on the prime support

The support cannot lie among the primes up to and including 257. A kernel-checked certificate eliminates the initial 54 odd primes in eight rounds. For each genuine exponent e, a prime divisor of e+1 must occur among the indices tested in its row. A surviving sub-sum can retain a base, so a conservative test cannot falsely remove a genuine component. A separate worker checked the preservation argument, both endpoints and the empty terminal state. [Certificate](SUPPORT.md)

Every odd perfect number has at least five distinct prime factors. If 3 is absent it has at least eight. If the seven odd primes through 19 are absent, it has at least 115 distinct prime factors and Ω ≥ 2ω+65. The last two numerical statements apply only to that seven-prime exclusion. [Abundancy and case coverage](SIEVE.md)

For every k, Dickson's theorem gives finiteness of the set of odd perfect numbers with ω ≤ k. The project proves a uniform recursive upper bound by controlling the numerator and denominator of the partial divisor product, including the case where every prime is known but some exact exponents remain unknown. Independent re-elaboration and review found standard axioms and verified termination with tied labels. A single k bounding all candidates remains unknown. [Proof and reproduction](DICKSON.md)

Every exact component has index greater than five. For any fixed real threshold, only finitely many odd perfect numbers have even one exact component with index below that threshold. These independently reviewed proofs give both theorems in Dris and Luca's paper. Their effective bound combines the local support cover with Dickson's theorem. [Arithmetic and case analysis](RECIPROCAL.md)

Every supported prime q satisfies q³ < 3N. Any j supported primes all at least t > 0 satisfy 2t^(2j) < 3N. The incoming-edge argument covers proper subsets, and Steuerwald covers the whole support. For primes that are 3 mod 4, quadratic reciprocity permits only one direction between a pair. The actual local divisor-sum cycle on 3, 11 and 7 shows why this direction restriction alone cannot eliminate all cycles. [Prime sizes](PRIME_SIZES.md) · [Reciprocity](RECIPROCITY.md)

Two finite trees close all cases with Ω ≤ 23. Each exact-exponent split is exhaustive under the assumed budget. The 3-present tree visits 3,350 nodes. The 3-absent branch forces 5 and its tree visits 1,986. The parity of Ω then gives Ω ≥ 25. [Checker, counts and sources](COUNT_CHAIN.md)

For every exact component the index is composite. In Euler form the checked lower bound is 21. The primes that are 3 modulo 4 with odd valuation in the Euler component index are at least as numerous as those in (a+1)/2, with one additional prime required when q is 5 modulo 8. A larger index can satisfy these conditions. [Index restrictions](RECIPROCAL.md) · [Square classes](EULER_SQUARE_CLASS.md)

Every odd perfect number belongs to the set of normalized spoof candidates in Dittmer's Corollary 7.2. Refining the true prime factorization gives formal balance precisely for perfect inputs. Descartes's chosen factorization balances, while the refinement of its true prime factorization gives 426,027,470,778. An independent reviewer checked the direction of the inclusion, its hypotheses, and the role of ordering the blocks within each component. Whether the candidate set is empty remains open. [Candidate inclusion](../OddPerfect/QuasiFactors.lean) · [Dittmer, §7](https://doi.org/10.1090/S0025-5718-2013-02793-7)

The factor-budget branches through Ω ≤ 27 have closed, verifying Ω ≥ 29. The branch without any of 3, 5, 7 or 11 already gives Ω ≥ 105. The remaining four seed branches for the published Ω ≥ 101 bound are open above the verified budget. [Count certificates](COUNT_CHAIN.md)

The square of any prime is excluded as the index of every exact component. The Euler index additionally excludes a product of two distinct primes, so its Ω is at least three and its value at least 27. For an Euler prime q with q−1 a power of two, the exact incoming q-adic valuation bounds its exponent by the number of edges among supported primes equal to one modulo q. Quadratic reciprocity strengthens that count. The local pair 61 and 131 sends edges both ways when the common length is five. [Index proof](RECIPROCAL.md) · [Fermat Euler-prime counting theorem](FERMAT_EULER.md)

Every normalized spoof candidate requires a genuine prime fourth power. Even permitting every normalized representation cannot rescue Descartes’s cube-free integer. Candidates having a fourth power and a normalized representation remain open. [Definitions and case review](SPOOFS.md)
