# The nine exceptional branches in the 1991 size proof

Brent, Cohen and te Riele obtained their 10³⁰⁰ bound by extending their earlier factor-chain method. Their §4 isolates nine branches where they used estimates from §2 to avoid factoring a large divisor sum. The line numbers below refer to the extracts in the published paper. The authors also distribute a revised machine-readable tree with 12,644 leaves. [Published paper, §4](https://maths-people.anu.edu.au/~brent/pd/rpb116.pdf) · [Author's archive and revised appendix](https://maths-people.anu.edu.au/~brent/pub/pub116.html)

Each corresponding divisor sum now has a publicly reported complete factorization. Lean has checked all nine product identities and the primality of all 20 listed factors. It verifies the eight direct bounds shown below and the additional valuation argument for case viii. Together these close all nine exceptional branches under their stated hypotheses. The full 10³⁰⁰ theorem additionally needs exhaustive coverage of the prime-index branches. The 10¹⁶⁰ replay has its own certificates. [Nine verified branch proofs](../OddPerfect/BrentHistorical.lean) · [Prime-index certificate method](BRENT_SIZE.md)

| §4 case | Published line | Source power | Preceding selected powers used | Decimal exponent reached by rounding |
|---|---:|---:|---|---:|
| i | 7,343 | 3221^42 | None | 370 |
| ii | 7,163 | 7^172 | None | 339 |
| iii | 7,985 | 612067^22 | None | 300 |
| iv | 8,866 | 3169^36 | None | 328 |
| v | 4,479 | 467^46 | 7^4, 2801^1 | 375 |
| vi | 9,527 | 191^46 | 13^4, 30941^1 | 325 |
| vii | 11,343 | 36389^22 | 3^18, 363889^1 | 319 |
| viii | 9,526 | 191^42 | 13^4, 30941^1 | 298 |
| ix | 12,201 | 3^240 | None | 343 |

The bound in the last column is derived from U = lcm(D, σ(D)/gcd(σ(D), 2)), where D is the product of the listed powers. Each reported prime divides U to odd valuation. If no special prime has been selected, the largest reported factor congruent to one modulo four accounts for the sole possible odd valuation in N. With a known special prime outside the reported factors, every such valuation must rise. Removing the actual special prime gives a divisor of N. Removing the largest possible special prime gives a lower bound on that divisor. These arguments require the selected component lengths to divide the actual component lengths. [Component and valuation proofs](../OddPerfect/IndexRounding.lean)

For case viii the rounded lower bound L has 299 digits and satisfies 53L < 10³⁰⁰ < 54L. The special prime is 30,941 and its successor is 2·3⁴·191. Hence the true valuation of 3 is even and at least four. Exact valuation four forces 11 through σ(3⁴)=121, and 11 was eliminated earlier in this branch. Exact valuation six forces 1,093 through σ(3⁶)=1,093, which is coprime to L. Valuation at least eight supplies an additional factor of 81, since 3 has valuation four in L. Each case exceeds the size target or encounters the forbidden 11. [Lean theorem `size_viii`](../OddPerfect/BrentHistorical.lean) · [Original antecedents, Figure 2](https://maths-people.anu.edu.au/~brent/pd/rpb116.pdf)

## Factor records

**i.** The factors of σ(3221^42) have 72, 77 decimal digits. [FactorDB record 1100000000125911585](https://factordb.com/index.php?id=1100000000125911585)

- `138380262291250937488089581658960972202922697970747808890189599600370673`
- `15655651531940748110478789695839379295612322863079251957505662002537883633911`

**ii.** The factors of σ(7^172) have 49, 97 decimal digits. [FactorDB record 1000000000043578197](https://factordb.com/index.php?id=1000000000043578197)

- `9491935586594867440367391646466925926211879363793`
- `2795470346154518601095703317279482175240316831812233463788382148771684556965122038863701628739457`

**iii.** The factors of σ(612067^22) have 47, 82 decimal digits. [FactorDB record 1100000000127495017](https://factordb.com/index.php?id=1100000000127495017)

- `19646107790168407038221172121977104941258765589`
- `1038248742632101482564989131468295652419856857036517004815396175149317316827547313`

**iv.** The factors of σ(3169^36) have 32, 45, 50 decimal digits. [FactorDB record 1100000000161417154](https://factordb.com/index.php?id=1100000000161417154)

- `31744233262482561015455983738381`
- `924347763164985110217631744828987973503604101`
- `36799120636249118806979649347305792642377421012261`

**v.** The factors of σ(467^46) have 30, 42, 52 decimal digits. [FactorDB record 1100000000007437254](https://factordb.com/index.php?id=1100000000007437254)

- `107904371296112724878570673929`
- `678305068508062949122512002362273110362327`
- `8414791682134527238127200279472177729343785794299499`

**vi.** The factors of σ(191^46) have 34, 72 decimal digits. [FactorDB record 1100000000007362263](https://factordb.com/index.php?id=1100000000007362263)

- `5730395978260105084320676489373993`
- `148467031893746524227485026611653806025492334017387237830406481156482009`

**vii.** The factors of σ(36389^22) have 37, 65 decimal digits. [FactorDB record 1100000000126810744](https://factordb.com/index.php?id=1100000000126810744)

- `1544162265349605884331755125640208251`
- `14212211472699543013587080904252097825957437375827305902242030561`

**viii.** The factors of σ(191^42) have 46, 51 decimal digits. [FactorDB record 1100000000007362225](https://factordb.com/index.php?id=1100000000007362225)

- `5519538714644097832143693263994602098520609053`
- `115818625571197592034031211634645997677055792367221`

**ix.** The factors of σ(3^240) have 36, 79 decimal digits. [FactorDB record 1000000000043566265](https://factordb.com/index.php?id=1000000000043566265)

- `553788718707122198751861425724478919`
- `8746781693759220836960579574321515651597080180989131549946798109975686695403479`

The Cunningham tables independently give factors for powers of small bases. Brent’s indexed file also covers many larger bases below 10,000. For example, its entry for 3169 raised to length 37 provides two divisors of the original 127-digit composite, and division supplies its remaining factor. [Cunningham, third edition, main tables](https://homes.cerias.purdue.edu/~ssw/cun/third/pmain901) · [Brent’s factor tables and indexed file](https://maths-people.anu.edu.au/~brent/factors.html)

## Abundant divisors in the replay

An additional terminal test takes small prime powers whose product B divides the odd perfect number. A supplied power pᵉ is admissible if it divides U. The checker can also raise a forced valuation from e−1 to even e when p is known to be nonspecial. The recurrence multiplies the geometric sums of distinct bases, so the resulting numerator is exactly σ(B). If σ(B)>2B, the branch would give an abundant divisor of a perfect number. The 1991 paper describes this test by reference to the S-test in the earlier work. [Brent and Cohen, §2](https://maths-people.anu.edu.au/brent/pd/rpb100.pdf)

The numerical search used primes through 257 for this test. On the seed-7 discovery tree it eliminated 10,053 of 12,998 explicit nodes. On seed 19 it eliminated 6,224 of 7,424. The resulting eight numerical trees contain 6,977 distinct proposed prime witnesses before later witness replacement. The standalone certificate must additionally verify every primality witness and every child state, including omitted branches. [Generator](../research/index_size.py)

A second integer traversal enumerated every admissible exponent from the size bound, including exponent one at every split. For these eight discovery trees it found 4,266 prime-index splits, 16,917 direct contradictions, 2,592 valuation bounds and 1,209 abundant divisors. It checked the divisibility and abundance inequalities with full integer products. These figures describe the discovery trees before replacement of unavailable primality witnesses.

The complementary case already has a Lean proof. If none of the eight seeds divides N, the first 100 permitted prime abundancy limits have product below two. The support therefore has at least 101 primes. The 3-free count inequality and odd parity of Ω give at least 259 factors with multiplicity. Assigning two copies to each of 100 nonspecial primes and a factor of at least 17 to each remaining place gives N > 10⁵³⁶. For finite coverage the checker gives a small proper divisor of each excluded composite in the tested interval. [Eight-seed complement](../OddPerfect/BrentSeeds.lean)

## Prime certificates from partial factorizations

The large-order test can certify a prime candidate n from a factored divisor F of n−1 with n < (F+1)². Its certificate supplies an integer b with b^F congruent to 1 modulo n. For every prime q dividing F, it checks that b^(F/q)−1 is coprime to n. Reduction modulo the least prime divisor r of n preserves all these tests, so the order of b modulo r is F. Consequently F divides r−1. A composite n would have r² ≤ n, contradicting the certified inequality. The Lean checker accepts the order and modular data directly. This is a large-order version of the method Pocklington presented in 1914. [Lean proof](../OddPerfect/LargeOrderPrime.lean) · [Pocklington, *Proceedings of the Cambridge Philosophical Society* 18, pp. 29–30](https://upload.wikimedia.org/wikipedia/commons/e/eb/Proceedings_-_Cambridge_Philosophical_Society_%28IA_proceedingscambr18camb%29.pdf)

The cubic test uses n < F³. A composite n would then be a product of two primes 1+Fa and 1+Fb. Writing R=(n−1)/F gives R=a+b+Fab. The size bound forces ab<F and a+b≤F, so the least positive residue of R modulo F gives a+b, and another division gives ab. The computed discriminant must equal (a−b)². Lean checks that this square is impossible. This specialization uses a stricter cubic cutoff than Theorem 5 of Brillhart, Lehmer and Selfridge. [Cubic certificate](../OddPerfect/LargeOrderCube.lean) · [Brillhart, Lehmer and Selfridge, 1975](https://doi.org/10.1090/S0025-5718-1975-0384673-1)

The quadratic test uses a norm-one element x+y√D. For every odd prime r dividing n, the r-th power fixes this element or sends it to its conjugate. Its certified order G therefore divides r−1 or r+1. A second test combines this restriction with a multiplicative order F dividing r−1. The two residue classes give a lower bound on r that is checked against the least prime factor of n. Both verifiers use modular exponentiation and gcd computations on the supplied integers. [Quadratic and mixed order proofs](../OddPerfect/LargeOrderQuadratic.lean) · [Brillhart, Lehmer and Selfridge, 1975](https://doi.org/10.1090/S0025-5718-1975-0384673-1)
