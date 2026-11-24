# Divisor counts for odd integers

Cohen and Sorli's 2010 paper proves three estimates for the number τ(n) of positive divisors of an odd integer. The second and third estimates in the paper are stated beyond 10⁶ and 9·10¹⁷, respectively. The proof gives the sharp endpoints below. These estimates apply to every odd integer in the stated range, so they are also available for odd perfect and odd harmonic integers. [Cohen–Sorli, *Odd harmonic numbers exceed 10²⁴*, Theorems 1–3](https://doi.org/10.1090/S0025-5718-10-02337-9)

| Checked conclusion | Exact range | Endpoint evidence |
| --- | --- | --- |
| τ(n)² ≤ n | Odd n other than 3 and 15 | Both exceptions violate the inequality. The statement includes n = 1. |
| τ(n)³ ≤ n | Odd n > 883575 | τ(883575) = 96, and 96³ = 884736. |
| τ(n)⁴ ≤ n | Odd n > 883086389887727025 | The divisor count at the endpoint is 30720 and its fourth power is 890604418498560000. |

The three theorem declarations and the checked endpoint violations are in the public module. [Lean declarations](../OddPerfect/CohenSorli.lean)

## Certificate

At a node, n = Dm, τ(n) = Tτ(m), and every prime factor of m is at least a. An exact-exponent split at p includes zero and every positive exponent. The last branch covers all e ≥ H. The closure proof bounds the product of local ratios (e+1)ᵏ/pˢᵉ. A comparison of successive ratios controls all exponents past the finite maximum. A separate terminal rule checks the possibility m = 1, where no remaining prime can supply a decrease. The proof uses rational inequalities throughout. The degree-two, degree-three and degree-four trees have 2, 24 and 107 split nodes, respectively. [Local ratio proofs](../OddPerfect/DivisorMoments.lean) · [Coverage and closure](../OddPerfect/DivisorCountBounds.lean)

The scripts emit Lean declarations. The checker does not need Python to replay the committed proofs.

```sh
python3 research/divisor_count.py 2 16 --output OddPerfect/DivisorCount2
python3 research/divisor_count.py 3 883576 --output OddPerfect/DivisorCount3
python3 research/divisor_count.py 4 883086389887727026 --output OddPerfect/DivisorCount4
lake build OddPerfect.CohenSorli
```

For any harmonic N and any positive prime power pᵃ dividing it, (pᵃ)² < Nτ(N). A divisor-count bound τ(N)ᵈ ≤ N therefore gives (pᵃ)²ᵈ < Nᵈ⁺¹. The paper's unconditional numeric lower bound N > 10²⁴ for odd harmonic N also requires excluding the remaining harmonic candidates. [Prime-power inequalities](../OddPerfect/HarmonicSize.lean)
