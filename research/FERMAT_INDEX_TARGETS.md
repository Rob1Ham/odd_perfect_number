# Non-Fermat prime divisors in component indices

Write an odd perfect number as $N=q^a b$, with $q$ prime and $q\nmid b$. Its index at $q$ is the integer $i$ given by $\sigma(b)=q^a i$. Say that a prime $p$ is non-Fermat here when $p-1$ has an odd prime divisor. This excludes $2$ as well as primes of the form $1+2^k$.

Suppose the Euler prime is $r\ne q$ and its exponent is $e\equiv1\pmod4$. Set $d=(e+1)/2$. The number of distinct non-Fermat prime divisors of $i$ satisfies

$$\#\{p\mid i : p\text{ prime},\ p-1\text{ has an odd prime divisor}\}\ \ge\ 2\tau(d)-3.$$

For each divisor $n$ of $e+1=2d$ other than $1,2$, the existing primitive-divisor theorems supply a prime $p$ with $\operatorname{ord}_p(r)=n$. Then $p$ divides $\sigma(r^e)$ and hence $q^a i$. Since $n$ has an odd prime factor and $n\mid p-1$, the prime $p$ is non-Fermat. Different orders need different primes. There are $2\tau(d)-2$ orders to represent and at most one witness can equal $q$. The counting lemma requires only an odd integer with the stated factorization and divisor-sum equation. [`euler_length_divisors_le_nonfermat_targets` and `nonspecial_index_nonfermat_prime_count`](../OddPerfect/FermatIndexTargets.lean)

In particular, if the Euler exponent is greater than one, **every component index** has a non-Fermat prime divisor. At the Euler component this follows from the earlier odd-index theorem. At any other component, $d>1$ gives $\tau(d)\ge2$. Consequently a component with an index supported entirely on primes with power-of-two predecessor could occur only if the Euler exponent were one. [`exists_nonfermat_index_prime_of_large_euler_exponent`](../OddPerfect/FermatIndexTargets.lean) · [Odd-index argument](FERMAT_INDEX_OBSTRUCTION.md)

The earlier structural reduction for a fully Fermat-supported component also proves that its prime $q$ is nonspecial and non-Fermat, its exponent $a$ is even and at least four, its index is $2\bmod4$, and $\omega(N)\le a+2$. These are conditional restrictions on a hypothetical odd perfect number. [`fermat_supported_component_structure`](../OddPerfect/FermatIndexNonspecial.lean)
