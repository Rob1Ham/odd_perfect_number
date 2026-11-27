# An exponent bound for a component index that is a prime power

Let $p^j$ be the index of any exact prime-power component of an odd perfect number, with $p$ prime and $j>0$. Then $j\ge256$. For odd $j$, the existing local obstruction gives $j\ge36207$. The proof below handles the even exponents $j=2u$. The cofactor equations are $N=q(p^u s)^2$, $q=\sigma(p^j)$, $q+1=2s^2$ and $\sigma(s^2)=p^j$. Here $q,p$ and the prime divisors of $s$ are distinct. [Full component statement](../OddPerfect/EvenIndexExponent256.lean) · [Odd exponent obstruction](../OddPerfect/OddIndexExponentScreen.lean)

## Small bases and the branch at three modulo four

The length $j+1$ is prime. For $p\equiv1\pmod4$, the existing restrictions $16\mid j$ and $j\ge66$ leave $96,112,192,240$ below 256. For all remaining combinations with $p<61$, the integer $(G(p,j+1)+1)/2$ lies strictly between two consecutive squares. Twelve integer Newton steps supply an integer candidate, and both square inequalities are checked directly in the kernel for all 505 pairs. [Small-base proof](../OddPerfect/EvenIndexSmallBase.lean)

For $p\equiv3\pmod4$, every prime divisor of $s$ is $1\pmod4$. At any $r\in\{5,13,17\}$ dividing $s$, the multiplicative-order condition implies $r\mid u+1$. Since $u+1\le128$, at least one of these three primes is missing. The valuation budget gives $3\omega(s)\le2u+2\omega(u+1)$ with $\omega(u+1)\le3$. Thus the support outside $p$ contains at most 90 primes and they are all $1\pmod4$. Use the first 90 primes in that residue class excluding the missing prime, the largest being 1117. In each case their product of limiting abundancies $r/(r-1)$, times $61/60$, is less than two. An odd perfect number would need the product of the limiting abundancies of its primes to exceed two. [Three-modulo-four branch](../OddPerfect/EvenIndexThreeModFour.lean)

## Charging each remaining source to its multiplicity

At each prime $r\mid s$, write $\sigma(r^{2v_r(s)})=p^{\beta_r}$. Every $\beta_r$ is odd and $\sum_r\beta_r=j$. For $K>0$, the condition $K\le\beta_r(r-1)$ gives
$$\frac r{r-1}\le1+\frac{\beta_r}{K}\le(1+1/K)^{\beta_r}.$$
For each of the four exponents, all primes outside the stated exceptional set satisfy this condition. [General local and product inequalities](../OddPerfect/EvenIndexEnvelope.lean)

| $j$ | $K$ | Exceptional primes |
|---:|---:|---|
| 96 | 400 | 7, 11, 19 |
| 112 | 2400 | 3, 11, 19, 23, 43 |
| 192 | 400 | 11, 19, 43, 97 |
| 240 | 510 | 11, 19, 29 |

At a cofactor prime let $x=p\bmod r$. Then $x^{\beta_r}=1$, $x^{j+1}+x=2$, and $x=1$ implies $r\mid j+2$. Below $r=245$ the finite residue and multiplicity ranges certify the cost directly. Above that cutoff $x\ne1$, so $\beta_r\ge3$. For $j=112$ the stronger bound $\beta_r\ge11$ follows by four polynomial identities. A common root with $\beta=3,5,7,9$ would force $r$ to divide $3,11,2,171$, respectively. [Large-prime identities](../OddPerfect/EvenIndexCostTail.lean) · [Cost certificates](../OddPerfect/EvenIndexCostTables.lean)

Since $p\ge61$ and $q\ge p^2\ge3721$, the full product of limiting abundancies is bounded by
$$\frac{61}{60}\frac{3721}{3720}\prod_{r\in E}\frac r{r-1}\,(1+1/K)^j.$$
Each of the four rational numbers is strictly below two, including the case whose value is approximately 1.9863. This excludes the remaining candidates for $j<256$. [Rational comparisons and component reduction](../OddPerfect/EvenIndexExponent256.lean)
