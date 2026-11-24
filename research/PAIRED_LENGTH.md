# Prime factors of the half-length and the squarefree part of the Euler index

For an odd perfect number in Euler form $N=q^a m^2$, put $d=(a+1)/2$, $I=\sigma(m^2)/q^a$, and let $O(I)$ be the primes whose valuations in $I$ are odd. The checked bound is
$$\Omega(d)\;\le\;\#\{r\in O(I):r>\operatorname{minFac}(d)\},$$
where $\Omega$ counts primes with multiplicity. At $d=1$, its left side is zero. For instance, any half-length divisible by $17^4$ requires at least four different odd-valuation primes in the Euler index, and at $d=17^4$ all four exceed 17. This improves the previous bound $\Omega(d)\le2|O(I)|$. [Length and index proof](../OddPerfect/PairedLength.lean) · [Earlier bounds](HALF_LENGTH_SUPPORT.md)

Let $G(x,s)=(x^s-1)/(x-1)$ and $C(x,s)=(x^s+1)/(x+1)$ for odd $s$. Grouping successive terms of a geometric sum gives $G(x^2,s)=G(x,s)C(x,s)$. For $x=q^D$ with $q$ an Euler prime, both factors are nonsquare when $s$ is an odd prime. The first follows from the positive prime-power base theorem and the second from the negative-base result. They are coprime because a common prime would divide $x^s-1$ and $x^s+1$, whereas $G(x,s)$ is odd. Thus at least one of their odd-valuation primes $r$ differs from $s$. The order of $x^2$ modulo $r$ is then exactly $s$, giving $r>s$. [Positive bases](../OddPerfect/GeometricPrimePower.lean) · [Alternating sums](ALTERNATING_PELL.md)

Adjoin the prime factors of $d$ in descending order, repeating every factor to its multiplicity. Appending $s$ to the accumulated length $D$ multiplies $G(q,2D)$ by $G(q^{2D},s)$. A prime common to the old and new terms must equal $s$, since reduction at that prime makes the last sum congruent to $s$. The selected $r>s$ is therefore new. Each previous selected prime already exceeds $s$, so it retains its odd valuation. Induction gives one separate prime per occurrence in the length, including repetitions. Finally $\sigma(q^a)I=2m^2$ transfers each selected odd-prime valuation to $I$. Run `lake build OddPerfect.PairedLength` to replay the result.

## An extra contribution away from the neighboring integers

If $s\mid d$ and $s\nmid q^2-1$, each occurrence of $s$ supplies a second odd-valuation prime. Writing $v_s(d)$ for the exponent of $s$, the checked inequality becomes
$$\Omega(d)+\sum_{s\mid d,\ s\text{ prime},\ s\nmid q^2-1}v_s(d)
\;\le\;\#\{r\in O(I):r>\operatorname{minFac}(d)\}.$$
In particular, if $\gcd(d,q^2-1)=1$, all $\Omega(d)$ occurrences contribute twice. To see why, at the step adjoining $s$ the accumulated length $D$ has no prime factor smaller than $s$. If $s\mid G(q^{2D},s)$, reduction modulo $s$ and Fermat's theorem imply $(q^2)^D\equiv1\pmod s$. The order of $q^2$ then divides both $D$ and $s-1$, so it is one. This contradicts $s\nmid q^2-1$. Both coprime signed factors must therefore supply separate odd-valuation primes strictly above $s$. [Weighted bound](../OddPerfect/WeightedLength.lean)

## Simultaneous assignment and divisibility

There is a subset $T\subseteq\{r\in O(I):r>\operatorname{minFac}(d)\}$ and an assignment $f:T\to\mathbb N$ with $f(r)\mid r-1$. For each prime $s$, exactly $v_s(d)$ members of $T$ have label $s$ if $s\mid q^2-1$, and exactly $2v_s(d)$ have label $s$ otherwise. The formal fiber count also vanishes for nonprimes. The selected target primes are distinct across all length factors. At each induction step a subset of the required cardinality is drawn from the new witnesses. All its labels are the new length prime and its intersection with the previous targets is empty. [Exact simultaneous assignment](../OddPerfect/LengthMatching.lean)

Let $d_0$ be the product of all prime powers $s^{v_s(d)}$ with $s\nmid q^2-1$. The same witnesses give the arithmetic divisibility
$$d\,d_0\ \mid\ \prod_{r\in O(I),\ r>\operatorname{minFac}(d)}(r-1).$$
For $d=1$ the divisor is one and the assignment may use an empty set. Run `lake build OddPerfect.LengthMatching` to replay both results. [Product theorem](../OddPerfect/LengthMatching.lean)
