# The Euler prime at a fixed index

Let $N=q^a m^2$ be odd and perfect in Euler form, and let $i=\sigma(m^2)/q^a$. The theorem `OddPerfect.IndexSieve.euler_prime_mem_candidates` proves that $q$ belongs to a finite set computed entirely from $i$. Its inputs are oddness, perfection and the Euler form. The bound neither fixes the integer $N$ nor assumes an external lower bound for its prime count. [Lean proof](../OddPerfect/IndexEulerSource.lean)

## A source dividing the index

The odd index divides $m^2$. For every $p\mid i$, let $e_p=2v_p(m)$ and $U_p=\sigma(p^{e_p})$. The component product $\prod_{p\mid i} U_p$ divides $q^a i$. It strictly exceeds $i$, because $U_p>p^{e_p}\ge p^{v_p(i)}$ for every factor and $i>1$. Consequently, at least one $p\mid i$ satisfies $q\mid U_p$. Since $q\nmid i$, the residual $U_p/\gcd(U_p,i)$ still contains $q$. In fact it is a positive power of $q$. [Source theorem](../OddPerfect/IndexEulerSource.lean) · [Residual calculation](../OddPerfect/IndexSieveResiduals.lean)

## Computing the candidate set

Write $B=\omega(i)+\Omega(i)$, counting distinct primes in the first term and multiplicities in the second. The weight estimate applied at threshold $B+1$ gives $\tau(a+1)/2\le B$. This holds at every index because $2^{B+1}>2B+1$. For each $p\mid i$, the finite set `fullLengths i p B` contains $e_p+1$. For each listed $d$, compute $U=(p^d-1)/(p-1)$, remove $\gcd(U,i)$, and take the positive prime divisors of the quotient. The union over the listed lengths and all $p\mid i$ is `eulerPrimeCandidates i`. The actual source proved above places $q$ in that union. The set can be large, and the theorem makes no assertion that any of its members extends to an odd perfect number. [Exact-length proof](../OddPerfect/IndexSieveExactLengths.lean) · [Computable definition](../OddPerfect/IndexEulerSource.lean)

## Pure prime-power sources

If $p$ is odd prime, $e>0$ is even, and $\sigma(p^e)$ divides a power of a single prime $q$, then $e+1$ is prime. The full length occurs as a multiplicative order at some prime divisor of $\sigma(p^e)$, so it occurs at $q$. If a prime $d$ divides $e+1$, then $\sigma(p^{d-1})$ also divides the same power of $q$. Its order witness requires $\operatorname{ord}_q(p)=d$, forcing $d=e+1$. This uses the repository's primitive-divisor theorem. [Lean proof](../OddPerfect/IndexPowerLength.lean) · [Primitive-order ingredients](../OddPerfect/IndexSieveCore.lean)

At an Euler index $i=p^j$, the true source at $p$ cannot spend a factor of its own base. Its entire sum is $q^\beta$. The exponent $e=2v_p(m)$ therefore satisfies $j\le e\le j+\lfloor\tau(a+1)/2\rfloor$, and $e+1$ is prime. In particular, $i=p^7$ forces $e\ge10$, since the even candidate 8 has composite successor 9. Chen and Chen obtain the same local restriction in their proof of Corollary 1.4, p. 48, using Ljunggren's square classification. Their complete exclusion of seventh-power Euler indices also uses other components and a lower bound on the number of primes of $N$. [Chen and Chen, Corollary 1.4](https://www.impan.pl/shop/en/publication/transaction/download/product/88031) · [Prime-power constraints](../OddPerfect/IndexPowerLength.lean)
