# Review of the 3 → 13 → 61 chain

Iannucci and Sorli give the exact-square steps at 3 and 13 in §4, p. 2081. Their §2 proves the factor-forcing principle from multiplicativity of the divisor sum and perfection. Fletcher, Nielsen and Ochem use divisibility of the exponent plus one to force cyclotomic factors in §2 of their sieve paper. These published results give the mathematical provenance of the chain. [Iannucci and Sorli (2003)](https://doi.org/10.1090/S0025-5718-03-01522-9) · [Fletcher, Nielsen and Ochem](https://mathdept.byu.edu/~pace/OPNSieves_web.pdf)

## Hypothesis checks

| Change | Result |
| --- | --- |
| Allow an odd composite divisor of a component's divisor sum | The proof still works. Mathlib's coprimality cancellation removes the factor 2 from `2*N`. See `OddPerfect.odd_dvd_perfect_of_dvd_sum_divisors`. |
| Allow an even perfect number | The factor-forcing and exact-power proofs already cover it. |
| Drop coprimality of the factors | The perfect number 28 equals 2 × 14. The divisor sum of 2 is 3 and 3 does not divide 28. |
| Drop perfection | The number 9 has exact 3-adic exponent two and 13 does not divide it. |
| Use an arbitrary power dividing the number as the full local component | 9 divides 81, but σ(81) = 121 is indivisible by 13. Likewise 169 divides 13⁴, but σ(13⁴) = 30941 is indivisible by 61. These examples refute the local divisor-sum inference. Whether some *other* argument forces 13 or 61 for perfect numbers with these weakened hypotheses remains open here. |
| Allow an even divisor of the component's divisor sum | Multiplicativity gives divisibility of `2*N`. The cancellation used for odd divisors requires coprimality with 2. |

The Lean proof uses `Nat.Perfect`, `Nat.perfect_iff_sum_divisors_eq_two_mul`, `Nat.Coprime.sum_divisors_mul` and `Nat.sum_divisors_prime_pow`. The counterexamples in the table were checked with Lean's kernel decision procedure.

## What 13 forces with an unknown exponent

Write `e = N.factorization 13`. For a perfect number divisible by 13, positivity and unique factorization give `e ≥ 1`, `13^e ∣ N` and `¬13^(e+1) ∣ N`. The divisor sum of this exact component has `e+1` geometric terms. A block of three contributes a multiple of (1+13+13^2=183), leaving only its remainder of zero, one or two terms to check modulo 61. A block of two contributes a multiple of 14.

| Exact exponent modulo 6 | Factors contributed by this component |
| --- | --- |
| 1 or 3 | 7 |
| 2 | 61 |
| 5 | 7 and 61 |
| 0 or 4 | Every prime divisor of σ(13ᵉ) is at least 23 and differs from 61. At least one such prime divides N. |

Every exponent has one of these six remainders. The two congruence tests in `OddPerfect/Thirteen.lean` characterize divisibility of the **local** divisor sum. Thus forcing 61 specifically from the 13-component requires proving `e % 3 = 2`. To force 61 in either remaining even residue class, one would need an argument about another component or a contradiction excluding that class.

`OddPerfect.thirteen_factor_alternatives` in `OddPerfect/ThirteenRemainder.lean` proves the exhaustive disjunction for every perfect number divisible by 13. The statement includes a prime witness dividing both σ(13ᵉ) and N in the final branch. The proof considers every prime below 23, and Lean verifies each geometric-sum period and each proper prefix used in the finite checks. At `e = 10` the local divisor sum is divisible by 23, so this method gives a sharp lower bound over the remaining exponents. The witness does not assert that any perfect number has this exponent.

Reproduce these declarations with `lake build OddPerfect.ThirteenRemainder`. The project-wide axiom audit is `lake env lean research/Audit.lean`.
