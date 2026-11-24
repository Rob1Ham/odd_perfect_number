# Odd prime powers as component indices

Let $N=q^a m^2$ be odd and perfect in Euler form. Suppose its Euler index $i=\sigma(m^2)/q^a$ equals $p^j$ with $p$ prime and $j$ odd. The hypotheses lead to the following exact system. Write $d=(a+1)/2$. Then $a>1$, $d$ is prime with $d\equiv1\pmod8$, and $q\equiv1\pmod{16}$. In addition,

- $2v_p(m)=j+1$, $16\mid j+1$, and $j+2$ is prime.
- $p\equiv1\pmod8$, $\operatorname{ord}_p(q)=d$, and $d\mid p-1$.
- $d\mid j+3$ and $\sigma(p^{j+1})=q^d$.

The project derives these restrictions without an external bound on the number of primes or the size of $N$. Hirakawa's published theorem excludes every prime-times-square Euler index when $a>1$ using a generalized Fermat theorem. The arguments here give an independent formal deduction for the prime-power subfamily from the exceptional shape verified in this project. [Hirakawa, Theorem 1.1](https://arxiv.org/pdf/2309.17084v3) · [Exceptional shape](../OddPerfect/ExceptionalLength.lean) · [Prime-power restrictions](../OddPerfect/OddPrimePowerIndex.lean) · [Return equation](../OddPerfect/OddPrimePowerReturn.lean)

## Recovering the two exponents

At $a=1$ a single-prime index has even exponent. At $a>1$, the exceptional shape forces $d$ to be prime and $(q+1)/2=d w^2$. Thus $\tau(a+1)=\tau(2d)=4$. The pure-component bound at $p$ says $j\le e=2v_p(m)\le j+2$. Since $e$ is even and $j$ is odd, $e=j+1$. The primitive-divisor argument forces $e+1$ to be prime. Write $\sigma(p^e)=q^\beta$. [Exponent-one identity](../OddPerfect/IndexPrimeReturn.lean) · [Pure components](../OddPerfect/IndexPowerLength.lean)

Chen and Luo's square-part divisor-sum congruence gives $i\equiv1\pmod8$, since $q$, $(q+1)/2$ and $(a+1)/2$ are all one modulo eight. Odd $j$ forces $p\equiv1\pmod8$. Reducing $\sigma(p^e)=q^\beta$ first modulo eight gives $8\mid e$. For $p\equiv1\pmod8$ each block of four consecutive powers starting at an exponent divisible by four sums to four modulo sixteen. Therefore $q^\beta\equiv e+1\pmod{16}$, giving $16\mid e$. [Index residue](../OddPerfect/ExceptionalIndexResidue.lean) · [Four-term calculation](../OddPerfect/OddPrimePowerIndex.lean)

Hirakawa's geometric nonsquare theorem at the base $p\equiv1\pmod4$ makes $\beta$ odd. The return identity at $p$ gives $v_p(\sigma(q^a))=e-j=1$. The order of $q$ modulo $p$ divides both $\beta$ and $2d$. It cannot be one, since that would give $p\mid2d$, $p=d$, and $p\mid(q+1)-(q-1)=2$. It equals $d$. Now $d\mid\beta$ and $0<\beta\le a=2d-1$, so $\beta=d$. Finally $p\equiv1\pmod d$ and $q\equiv-1\pmod d$ give $j+2\equiv q^d\equiv-1\pmod d$. [Geometric nonsquare theorem](../OddPerfect/GeometricNonSquare.lean) · [Return-order proof](../OddPerfect/OddPrimePowerReturn.lean)

## First possible exponent

The arithmetic conditions $16\mid j+1$, primality of $j+2$, and $d\mid j+3$ for a prime $d\equiv1\pmod8$ have no solution with $j<191$. At $j=191$, the pair $j+2=193$ and $d=97$ passes these three tests. This is an arithmetic candidate. The equations for $p,q,m,N$ still apply. The least possible $d$ is 17, and $8d\mid p-1$, so $p\ge137$ and $i>10^{408}$. [Kernel-checked finite screen](../OddPerfect/OddPrimePowerBound.lean)

The resulting exclusion applies to **every exact component** of an odd perfect integer. A prime index itself is impossible. A higher power of two would make the return identity divisible by four, whereas twice the odd cofactor has only one factor of two. An odd prime-power index identifies the Euler component, so its exponent must pass the screen above. In particular the index of an exact component cannot be a prime cube. [All-component theorem](../OddPerfect/OddPrimePowerBound.lean) · [Euler component identification](../OddPerfect/ChenChenIndex.lean)

## Support for general prime-times-square indices

For an Euler index $i=\ell t^2$ at $a>1$, every $r\mid m$ outside $i$ must supply a factor of $i$. If its divisor sum were a pure power of $q$, return divisibility would give $r^{2v_r(m)-1}\mid 2d$. Since $r$ is odd and $d$ is prime, $r=d$ and $2v_r(m)=2$. Then $\sigma(r^2)\equiv3\pmod4$, while every power of $q$ is one modulo four. The product of the index parts spent by any set of sources divides $i$. Hence the number of primes in $m$ outside $i$ is at most $\Omega(i)$ and $\omega(N)\le\omega(i)+\Omega(i)+1$. [Local and global source bounds](../OddPerfect/ExceptionalIndexSources.lean)
