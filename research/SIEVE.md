# The branch with every prime factor at least 23

Ochem and Rao's 2014 proof of Theorem 2 branches on the primes 3, 5, 7, 11, 13, 17 and 19. If none divides N, the last paragraph of §4 derives at least 115 distinct prime factors from an abundancy estimate. The other branches of §4 use a separate computation. [Published paper, p. 2438](https://doi.org/10.1090/S0025-5718-2013-02776-7)

For every component pᵉ of a perfect N, the geometric-sum identity gives σ(pᵉ)(p−1) + 1 = p^(e+1). Multiplying the corresponding strict inequalities over the nonempty prime support, using multiplicativity, and cancelling the positive N gives

```text
2 × product(p−1 : p prime dividing N) < product(p : p prime dividing N).
```

Consequently the product of p/(p−1) over all prime factors exceeds 2. These two forms are `perfect_support_product_bound` and `two_lt_prod_primeAbundancyLimit` in `OddPerfect/AbundancyLimit.lean`.

Take T to be every prime in the closed interval [23,673]. The certificate uses exactly `(Finset.Icc 23 673).filter Nat.Prime`. Lean evaluates its cardinality and the inequality between integer products with `decide +kernel`. It finds 114 elements and verifies ∏p < 2∏(p−1). This proves the strict comparison with two using integer arithmetic throughout the numerical check.

The finite comparison permits an arbitrary unbounded prime support S. If it has at most 114 members, every member of S outside T exceeds 673 and contributes at most 673/672. Every missing member of T contributes at least 673/672. There are at least as many missing members as extra ones. Multiplying those bounds and the factors present in both sets bounds the product for S by that for T. The excluded primes and oddness account for every prime smaller than 23.

The numerical declaration `prime_interval_23_673_certificate` and the result `prime_factor_count_avoiding_primes_below_23` are in `OddPerfect/SmallestPrime.lean`. The 3-free form of the count inequality gives 7Ω ≥ 18ω − 15. With ω ≥ 115 this yields Ω − 2ω ≥ 64, and oddness of Ω raises the bound to 65. The declaration `total_prime_factor_count_avoiding_primes_below_23` proves this terminal consequence. It leaves the seven branches in which one of the specified small primes divides N open in this sieve.

## Five distinct primes, or eight when 3 is absent

Sylvester published the five-prime bound in the *Comptes rendus*, vol. 106 (1888), pp. 522–526, and the 3-free eight-prime bound on pp. 403–405. The five-prime paper is reproduced in English in Gimbel and Jaroma's historical study. The proof in `OddPerfect/FewPrimes.lean` uses the repository's certified large-prime sieve. [Original paper on divisibility by 3](https://rcin.org.pl/impan/Content/122671/PDF/WA35_145312_11371-4_Art55.pdf) · [English translation of the five-prime paper, appendix](https://math.colgate.edu/~integers/d16/d16.pdf)

Suppose that ω ≤ 4. Choose a prime R > 257 dividing N. After removing R, at most three primes remain. If 3 were absent, the maximal product of the other three limiting abundancies would come from 5, 7 and 11. If 5 were absent, it would come from 3, 7 and 11. Both products, even multiplied by 257/256, fall short of two. Thus 3 and 5 are present. Since 105 does not divide an odd perfect number, 7 is absent. If both 11 and 13 were absent, 3, 5 and 17 would maximize the remaining product, and even this gives only 65535/32768 after multiplication by 257/256. This leaves exactly the supports {3,5,11,R} and {3,5,13,R}.

For either possible third prime s, exact exponent one at 5 would cap the abundancy below two because (6/5)(3/2)(11/10)(257/256) < 2. Therefore 25 divides N. The prime 11 occurs to even exponent by Euler's theorem. If s = 13 had exact exponent one, it would force 7, which has already been excluded. Thus s² divides N in both cases. If 81 divides N, the divisor 81·25·s² is abundant for either value of s. This leaves exact exponent two at 3. That exponent caps the abundancy below two by (13/9)(5/4)(11/10)(257/256) < 2. These contradictions prove `five_le_distinct_prime_factor_count`.

When 3 is absent, the six smallest permitted primes are 5, 7, 11, 13, 17 and 19. Multiplying their limiting abundancies and 41/40 still gives less than two. A prime R > 257 is available, so a support with at most seven primes cannot achieve perfection. The result is `eight_le_distinct_prime_factor_count_of_three_free`.

The Prove2Me entry for the branch with q₂ = 5 and q₃ = 11 uses four primes in the square cofactor m² and a distinct special prime of exponent one. Its displayed statement supplies hypotheses on m² that our four-prime support does not have. Its public statement ends with a placeholder. Our proof and numerical comparisons were developed locally; no Prove2Me code is used. [Displayed Prove2Me statement](https://beta.prove2.me/theorems/2449de12-9f5f-494d-a237-61c98b710473)
