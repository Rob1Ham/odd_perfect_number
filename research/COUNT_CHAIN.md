# A checked finite tree for the total prime-factor count

The local certificate excludes every odd perfect number with Ω ≤ 19. Euler's form makes Ω odd, so the resulting lower bound is 21. Here Ω counts the prime factors with multiplicity and ω counts distinct prime factors.

Iannucci and Sorli describe branching on the exact power of a forced prime, usually choosing the smallest available prime. Their §4 begins with 3², its divisor sum 13, and the alternatives at 13. They prove Ω ≥ 37 using additional results and a different collection of cases. Ochem and Rao's 2012 paper uses exact and non-exact components, forced primes, abundance contradictions and lower bounds on the number of remaining factors to prove Ω ≥ 101. Our certificate uses fresh case data and the exact-exponent rule throughout. [Iannucci and Sorli, §§4–5](https://opus.lib.uts.edu.au/bitstream/10453/5651/1/2003000441.pdf) · [Ochem and Rao, §4](https://doi.org/10.1090/S0025-5718-2012-02563-4)

## The two initial cases

When 3 is present, Sylvester's five-prime theorem gives ω ≥ 5. When 3 is absent, the local Sylvester theorem gives ω ≥ 8. If 5 is also absent, every prime divisor is at least 7. Lean checks that the first fourteen such primes, from 7 through 59 inclusive, have product of limiting abundancies below two. Since an odd perfect number's product exceeds two, at least fifteen distinct primes are required. The local Steuerwald count then gives Ω ≥ 31. Hence 5 is present in every remaining candidate with Ω ≤ 19. These statements are in `OddPerfect/CountSeeds.lean`.

## What is checked at a node

Write N = Dm with gcd(D,m) = 1, and set A = σ(D). The node records D, A, the sum s of its assigned exponents and their number c. The root represents D = A = 1. Since Aσ(m) = 2Dm, the integer K = A / gcd(A,2D) divides m. In particular gcd(D,K) = 1.

A split supplies a prime p with p dividing K, or with p supplied by the initial seed and coprime to D. Thus p divides m. The next node assigns e = vₚ(m) to D and replaces m by m/pᵉ. The checker iterates over every e from 1 through B−s, inclusive, where B is the hypothesized upper bound on Ω. It recomputes the component and its divisor sum. Failure to find a necessary hint or exhaustion of recursion fuel rejects that certificate.

An assigned divisor sum divisible by four cannot divide 2N. An assigned component with A > 2D contradicts Aσ(m) = 2Dm because σ(m) ≥ m. If at most one prime factor remains and A < 2D, a candidate cofactor must be prime. Its divisor sum m+1 then forces (2D−A)m = A. Failure of divisibility closes this case.

Suppose that w is the initial lower bound on ω and that K has k mutually coprime divisors greater than one. Then ω(m) ≥ max(k,w−c). With at most one Euler prime, 2ω(m) ≤ Ω(m)+1. If s is odd the residual count is even, so the right-hand side can be reduced by one. Together these give

```text
s + 2 max(k, w−c) + (s mod 2) ≤ B + 1.
```

This leaf accepts lists of coprime composite divisors. Each divisor contributes at least one distinct prime to m. The checker verifies their product divides K and verifies each coprimality requirement. For split primes above 1023, the file supplies Lucas primality witnesses which mathlib verifies inside Lean.

## Replay

`OddPerfect/FactorBudget.lean` proves preservation under every exact split and proves the leaf inequalities. `OddPerfect/CountChain.lean` proves the Boolean replay correct for arbitrary seed, counting budget, support lower bound, finite hint table and recursion fuel. The keys in `OddPerfect/CountChain19.lean` show the assigned prime powers, so an individual branch can be read directly from the Lean source. The 3-seed tree visits 1,192 nodes, of which 155 split. The 5-seed tree visits 597 nodes, of which 58 split. Every accepted numerical certificate is discharged by `decide +kernel`.

Run `lake build OddPerfect.CountBound` to replay both trees and their corollary `OddPerfect.twenty_one_le_total_prime_factor_count`. The proof uses the checked global Sylvester and Steuerwald results in this checkout. The stronger historical and current published lower bounds require further checked branches. [Iannucci and Sorli, introduction](https://opus.lib.uts.edu.au/handle/10453/5651) · [Ochem and Rao, Theorem 2](https://doi.org/10.1090/S0025-5718-2012-02563-4)

## Budget 23

The same rules exclude Ω ≤ 23. The 3-seed replay checks 3,350 nodes and the 5-seed replay checks 1,986. The proof `OddPerfect.twenty_five_le_total_prime_factor_count` gives Ω ≥ 25. It therefore includes the historical Ω ≥ 23 bound credited to Cohen's 1982 thesis. Iannucci and Sorli credit Sayers's 1986 thesis with Ω ≥ 29. [Iannucci and Sorli, pp. 2077 and 2084](https://opus.lib.uts.edu.au/bitstream/10453/5651/1/2003000441.pdf)

Run `lake build OddPerfect.CountBound25` to verify this certificate. The independent search program `research/count_chain.py` takes a budget and can emit a fresh Lean hint module with `--output`. It uses GNU `factor` or `gfactor` for candidate discovery. Factorization timeouts can change the hints selected on a machine. The checked module stores the numeric divisions, coprimality tests and Lucas witnesses needed for replay, so Lean verification requires no external factoring program.

## Budget 27 and larger seed-free cases

`OddPerfect/CountBound29.lean` reaches the Ω ≥ 29 result credited to Sayers. The 3-seed certificate visits 9,569 nodes, the 5-seed certificate visits 1,938, and the second certificate uses 3 ∤ N. Their checked proof follows the factor-chain method with an additional branch for a presently unknown prime. [Iannucci and Sorli, introduction and §4](https://opus.lib.uts.edu.au/bitstream/10453/5651/1/2003000441.pdf)

Suppose at most k distinct primes divide the remaining cofactor m. An integer g > 1 dividing K and coprime to (L−1)! guarantees that at least one such prime is at least L. If all the remaining primes were at least a, their limiting abundancy product would be at most

```text
[L/(L−1)] · [a/(a−1)]^(k−1).
```

The actual abundancy of m is 2D/A and falls strictly below the limiting product. A verified comparison with 2D/A therefore forces a prime below a. The tree checks every eligible prime below a and all its possible positive exponents. It omits primes dividing D and primes known absent from N. A cutoff with no eligible primes closes immediately. When L ≤ a, the same reasoning uses any prime dividing m without supplying g. These statements are proved in `OddPerfect/ChainAbundancy.lean` and `OddPerfect/ChainPlan.lean`.

Run `lake build OddPerfect.CountBound29` for the proof and `python3 research/count_chain.py 27 --cutoffs` for a fresh search. The verified result uses the stored certificate in `OddPerfect/CountChain27.lean`.

The bigger seed-free cases in `OddPerfect/HigherCountSeeds.lean` use the 3-free Ochem–Rao estimate 18ω ≤ 7Ω + 15. Without 3 and 5 it gives Ω ≥ 37. Without 3, 5 and 7, bounding the product on the first 26 allowed primes gives ω ≥ 27 and Ω ≥ 69. Without 3, 5, 7 and 11, the first 40 allowed primes give ω ≥ 41 and Ω ≥ 105. Thus the complementary case outside the four seeds of Ochem and Rao's 2012 Theorem 2 already exceeds its target 101 in this development. [Ochem and Rao, 2012, §4](https://doi.org/10.1090/S0025-5718-2012-02563-4) · [Ochem and Rao, 2014, §3](https://doi.org/10.1090/S0025-5718-2013-02776-7)

## Budget 35

`OddPerfect.thirty_seven_le_total_prime_factor_count` reaches Iannucci and Sorli's Ω ≥ 37 theorem. The two stored seed searches visit 70,757 and 14,654 nodes. `OddPerfect/ChainScript.lean` indexes children by prime case and exponent. `OddPerfect/ChainGroupBounds.lean` also permits an abundance contradiction from pairwise coprime divisors of the residual and an upper bound on their number from the Ochem–Rao inequality. [Iannucci and Sorli, Theorem 1](https://opus.lib.uts.edu.au/bitstream/10453/5651/1/2003000441.pdf)

`OddPerfect/ChainCheckpoint.lean` splits the numeric verification into subtrees. A parent accepts a handoff only when all four fields of the current node equal those of an earlier proved subtree. Each subtree theorem covers every possible cofactor realizing its start state. The 3 and 5 root splits hand off each nontrivial exact exponent separately. Larger branches divide again. Every omitted case must pass the arithmetic tests or a checked handoff.

`OddPerfect/CountChain35/Primes.lean` verifies 510 split primes. The 101 subtree theorems occupy `Part01.lean` through `Part19.lean` in the same directory. `OddPerfect/CountChain35.lean` gives the two seed exclusions, and `OddPerfect/CountBound37.lean` handles parity and the case outside both seeds. Run `lake build OddPerfect.CountBound37` to check the complete result. `python3 research/count_chain.py 35 --partition --output OddPerfect/CountChain35.lean` generates a new certificate using the same proof rules.

The stored witness modules, including their entry file and prime table, total 1,548,917 source bytes. The largest subtree module is 89,408 bytes. A cold replay of these targets against built dependencies took 841.3 seconds on the shared machine. Half-second sampling of the target IR and Lean output paths recorded 37,122,048 peak allocated bytes (35,010,957 logical bytes), including Lake setup files. The build's maximum child resident set was 3,061,530,624 bytes. An earlier 4,452,576-byte monolithic representation was stopped before completion when system disk space declined during concurrent builds.

## Excess over twice the distinct count

The verified lower bound Ω ≥ 37 and the unconditional inequality 18ω ≤ 7Ω + 31 imply Ω ≥ 2ω + 5. Indeed, 9(Ω−2ω) ≥ 2Ω−31 ≥ 43. If 3 is absent, replacing 31 with 15 gives Ω ≥ 2ω + 7. Ochem and Rao proved the stronger unconditional bound Ω ≥ 2ω + 51 in their 2014 paper using an additional factor-chain argument. [Lean corollaries](../OddPerfect/CountExcess.lean) · [Published paper, Theorem 2](https://doi.org/10.1090/S0025-5718-2013-02776-7)

The final count certificate gives Ω≥2ω+7 unconditionally. If 3 is absent, the linear inequalities suffice. If 3 divides N, oddness of Ω, the absolute lower bound 37, and 18ω≤7Ω+31 reduce a possible counterexample to Ω=37 and ω=16. A 354-hint certificate excludes that case. Its Lean source embeds the numerical witness. The absolute bound Ω≥47 and stronger additive bounds remain pending. [Unconditional +7 certificate](../OddPerfect/CountExcessSeven.lean)
