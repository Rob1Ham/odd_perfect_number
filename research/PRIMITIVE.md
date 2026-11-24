# Forced primes of prescribed multiplicative order

`OddPerfect.exists_prime_order_prime_pow` proves the odd prime-power case of the Bang–Zsigmondy primitive divisor theorem. For any natural `b > 1`, odd prime `l`, and `k ≥ 0`, some prime `r` satisfies `orderOf (b : ZMod r) = l^(k+1)` and `l^(k+1) ∣ r-1`. Thus `r` divides `b^(l^(k+1)) - 1` and first divides a positive-exponent difference at precisely this exponent. The local proof uses mathlib's valuation-one formula for an odd-prime-length geometric sum. [K. Zsigmondy, *Zur Theorie der Potenzreste* (1892), original article](https://doi.org/10.1007/BF01692444)

Write `x = b^(l^k)`. The geometric sum `1 + x + ⋯ + x^(l-1)` exceeds `l`. If `l` divides this sum, Fermat's theorem gives `x ≡ 1 (mod l)` and lifting the exponent shows `l²` cannot divide it. A prime factor `r` other than `l` therefore exists whether or not `l` occurs. Modulo `r`, the sum vanishes, `x^l = 1`, and `x ≠ 1` because otherwise the sum would be `l`. This proves the claimed order of `b`.

`OddPerfect.exists_forced_prime_order_prime_pow` transfers this result to every perfect number. At exact exponent `e = N.factorization p`, each odd prime power dividing `e+1` forces a different prime divisor of `N` for that base `p`. The theorem `OddPerfect.odd_length_factor_count_bound` counts all these orders. If `N` is also odd, Euler's theorem covers the only available even prime-power length. More explicitly, `2 ∣ e+1` puts `p` at the Euler prime, with `e ≡ p ≡ 1 (mod 4)`, so the only power of two dividing `e+1` is `2`. A prime factor of `(p+1)/2` is odd and produces order `2`. This yields `OddPerfect.exists_forced_order_of_prime_pow_length` without an oddness restriction on the index prime.

`OddPerfect.length_factor_count_bound` formalizes the resulting inequality for every prime `p` in an odd perfect `N`, where `e = N.factorization p`:

```lean
(e + 1).primeFactorsList.length ≤ (N.primeFactors.erase p).card
```

The argument maps pairs `(l,k)` with `0 ≤ k < (e+1).factorization l` injectively into the set of realized orders by `(l,k) ↦ l^(k+1)`. Uniqueness of prime-power bases and positive exponents gives injectivity. Counting orders cannot exceed the number of eligible primes. The same divisor of `N` may serve more than one base, so these counts cannot simply be added across components.

`lake build OddPerfect.Primitive` passed on the pinned toolchain. `#print axioms` for the five public primitive-order and counting declarations then present returned `[propext, Classical.choice, Quot.sound]`.

## All lengths and exact exponents on a fixed support

`OddPerfect.exists_forced_order_of_length` in `OddPerfect/CyclotomicOrders.lean` extends the prime-power result to every divisor `d > 1` of `e+1`, where `e = N.factorization p` and `N` is odd and perfect. Some `r ∈ N.primeFactors.erase p` has `orderOf (p : ZMod r) = d` and `d ∣ r-1`. Taking `d = e+1` shows that, for a known support and `p` in that support, all possible exponents occur in the finite list `orderOf (p : ZMod r) - 1` as `r` ranges over the other primes. It does not assert each value in the list is possible. Taking all the divisors at once yields `OddPerfect.component_length_divisor_count`, namely `τ(e+1) ≤ ω(N)`.

The proof divides `d > 1` into a prime power and a number with at least two distinct prime factors. The first case is proved in `Primitive.lean`. In the second case `OddPerfect.exists_prime_order_mixed` proves primitive-prime existence for every natural base `b ≥ 3`. Every prime divisor `r` of `|Φ_d(b)|` sees `b` with multiplicative order equal to the factor of `d` left after removing the entire `r`-power. Thus a divisor of `|Φ_d(b)|` that also divides `d` must be the largest prime in `d`. If all divisors were of that kind, they would all equal this one prime `r`. The cyclotomic evaluation bound gives `|Φ_d(b)| > r`, so `r²` would divide it. The geometric sum of length `r` and base `b^(d/r)` is divisible by `|Φ_d(b)|`. Since `r` is odd, lifting the exponent excludes `r²` in this sum. The largest prime `r` is odd here because `d` has at least two distinct prime factors.

The exceptional lengths of the general Bang–Zsigmondy theorem are accounted for directly. The case `d = 1` is excluded by the statement. The base-two, length-six exception cannot occur at the full prime-power component of an odd number. If `d = 2`, then the Euler prime is `1` modulo four and `(p+1)/2` is an odd integer greater than one, so `p+1` cannot be a power of two. A Lean 4 formalization of the broader two-base theorem was proposed in mathlib PR 28895, which closed without merging. The local proof uses the cyclotomic polynomial, its evaluation bounds and root classification already present at this repository's mathlib pin. [Mathlib PR 28895](https://github.com/leanprover-community/mathlib4/pull/28895) · [Original article](https://doi.org/10.1007/BF01692444)

A finite list of possible exponents for each fixed support leaves unboundedly many supports. Combining counts across distinct bases would also require controlling when different bases have the same primitive prime divisor.
