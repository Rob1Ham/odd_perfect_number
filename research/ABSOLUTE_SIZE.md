# Factor-chain certificates for an absolute size bound

Peter Hagis proved in 1973 that every odd perfect number exceeds 10⁵⁰. His paper divides the problem into five cases, gives representative branches and identifies a deposited UMT case study containing the full computation. Ochem and Rao later proved the stronger published bound 10¹⁵⁰⁰. The local size certificates use newly generated exact-exponent branches. [Hagis, Theorem and case-study description](https://doi.org/10.1090/S0025-5718-1973-0325507-9) · [Ochem and Rao, Theorem 1](https://doi.org/10.1090/S0025-5718-2012-02563-4)

At a node write N = Dm, where D and m are coprime, A = σ(D), and s = Ω(D). The forced divisor K = A / gcd(A,2D) divides m. If N ≤ X, this requires DK ≤ X. The verifier computes a lower bound a on every prime of m from the oddness of N, the absence of specified primes, and coprimality with D. It takes the least eligible prime below 43, using 43 if none is eligible. Since m is the product of its prime factors with multiplicity,

```text
a^Ω(m) ≤ m ≤ ⌊X/D⌋.
```

If Ω(N) ≥ L, then D·a^max(0,L−s) ≤ X. Conversely the upper bound on m gives the local count budget s + ⌊logₐ(⌊X/D⌋)⌋. Assigning a forced prime p checks every exact exponent up to both this residual count budget and ⌊logₚ(⌊X/D⌋)⌋. `SizeChain.lean` proves both directions of the pruning argument and verifies each remaining choice using the factor-count rules.

For X = 10⁵⁰ the numeric certificate uses L = 37 and lower support counts 5, 8 and 15 in the mutually exclusive least-prime cases 3, 5 and 7. The 3-seed search visited 20,774 nodes, the 5-seed search visited 5,863, and the 7-seed search visited 1,216, including nodes immediately closed by the size tests. For the complementary case, the existing count estimates give at least 69 prime factors, each at least 11. The distinct-prime product below strengthens this case to N > 10¹⁰⁶. The certificate occupies 80,905 source bytes. Its three size replays are checked by `decide +kernel` in `OddPerfect/SizeChain50.lean`.

`python3 research/count_chain.py 50 --size --output <path>` generates a fresh size certificate. Factoring choices may vary with the configured timeout. `lake build OddPerfect.SizeBound50` verifies the stored numeric certificates and the unconditional theorem `OddPerfect.ten_pow_fifty_lt_of_odd_perfect` without running the search program. Its axiom report contains `propext`, `Classical.choice` and `Quot.sound`.

## The complement of each seed family

Suppose all supported primes are at least a, at least k+1 distinct primes occur, and Ω(N) ≥ M. Euler's form supplies k distinct nonspecial primes, each occurring at least twice. Let P be the product of the first k primes at least a. Their product minimizes the product of any k permitted prime bases. After removing the corresponding k squares, the remaining prime factors are all at least a. Lean proves P²·a^(M−2k) ≤ N in `OddPerfect/SizeSeeds.lean`.

| Excluded primes | a | k | M | Last prime in P | Checked lower bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3, 5 | 7 | 14 | 37 | 59 | N > 10⁴⁷ |
| 3, 5, 7 | 11 | 26 | 69 | 113 | N > 10¹⁰⁶ |
| 3, 5, 7, 11 | 13 | 40 | 105 | 197 | N > 10¹⁸⁰ |

The finite interval products, cardinalities and integer inequalities are all evaluated by the kernel.
