# Sixth powers and small prime divisors

Fletcher, Nielsen and Ochem proved that an odd perfect number divisible by 5 must have a prime sixth power divisor. Their paper also treats a larger class in which every nonspecial component length is divisible by 3 or 5. The local theorem proves the sixth-power assertion and covers every odd perfect number N with a divisor q satisfying 2 ≤ q < 53. The full least-prime bound of the paper remains a further result. [Fletcher–Nielsen–Ochem, §§5–6](https://mathdept.byu.edu/~pace/OPNSieves_web.pdf) · [Lean statements](../OddPerfect/SixthPowerSieve.lean)

Assume no prime sixth power divides N. Then each prime divisor has an exact exponent in {1,2,3,4,5}. At any assigned prefix D the checker retains its coprime cofactor m and the equality N = Dm. Put S = σ(D) and F = S/gcd(S,2D). Perfectness gives F dividing m. Four dividing S contradicts oddness, S > 2D contradicts perfectness, and any nontrivial gcd(D,F) contradicts coprimality. A positive divisor of F smaller than the assumed least prime gives another terminal contradiction when the divisor exceeds one. Every interior node checks the primality and divisibility of its proposed next base and covers all five possible exponents. [Prefix identities](../OddPerfect/FactorBudget.lean) · [Checker and coverage](../OddPerfect/SixthPowerChain.lean)

The least-prime trees at 3 and 5 have 123 and 90 splits respectively, including their roots. The tree at 3 closes with 493 arithmetic terminals. At 5 it has 270 arithmetic terminals and 91 smaller-divisor terminals. A divisor q < 53 forces the least prime to be at most q. Lean enumerates all odd prime values below 53 and applies the corresponding tree. An independent review checked the passage from a least-prime exclusion to an exclusion for every multiple of 5.

Regenerate any tree by supplying the prime and its directory. GNU coreutils supplies the factor command used to discover factors. Each factor used in the proof is checked on replay. [Generator](sixth_power.py)

```sh
python3 research/sixth_power.py 5 --output OddPerfect/SixthLeast5
lake build OddPerfect.SixthPowerSieve
```
