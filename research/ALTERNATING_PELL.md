# Alternating geometric squares and the Euler half-length

For all naturals $x>1$ and odd $n>1$, the integer
$$C(x,n)=\frac{x^n+1}{x+1}$$
is nonsquare. This is the negative-base odd-length case of Ljunggren's Theorem 1, applied to the base $-x$. At $x=1$ or $n=1$, the quotient equals one. The proof below uses integral Pell coordinates and binomial valuations. The positive-base solutions $(3,5)$ and $(7,4)$ in Ljunggren's full classification fall outside this statement. [Lean theorem](../OddPerfect/AlternatingPell.lean) · [Ljunggren, *Noen setninger om ubestemte likninger av formen* $(x^n-1)/(x-1)=y^q$, Norsk Matematisk Tidsskrift 25 (1943)](https://msleziak.com/temp/Ljunggren.pdf)

## Descent and valuations

Write $n=2h+1$. If $C(x,n)=y^2$, then $(x+1)y^2-xz^2=1$ with $z=x^h$. For any integer $x>0$, every positive solution $(y,z)$ arises from $(1,1)$ by iterating the integral matrix
$$T=\begin{pmatrix}2x+1&2x\\2(x+1)&2x+1\end{pmatrix}.$$
When $z>1$, applying its inverse leaves both coordinates positive and strictly decreases $z$. The second coordinate $Z_j$ of $T^j(1,1)$ satisfies $Z_j>2j+1$ for $j>0$. [Checked descent and growth](../OddPerfect/PellCoordinates.lean)

For a prime $p\ge5$ dividing $x$, every $p^k\mid Z_j$ divides $m=2j+1$. Set $D=x(x+1)$ and expand $(x+1+\sqrt D)^m$. Its imaginary coefficient is $(x+1)^jZ_j$. Modulo $p^{v_p(m)+1}$ only the linear binomial term $m(x+1)^{m-1}$ survives. At each higher odd index $2i+1$, the binomial coefficient identity gives $v_p(m)\le v_p(2i+1)+v_p(\binom m{2i+1})$, while $v_p(2i+1)<i$ and $p^i\mid D^i$. If all prime divisors of $x$ are at least five, this gives $x^h\mid m$, contradicting $Z_j>m$.

The two small primes require separate arguments. Every $Z_j$ is odd. If $x$ is odd and $3\mid x$, reduction of the recurrence gives $Z_j\equiv2j+1\pmod3$. Thus $Z_j=x^h$ forces $j\equiv1\pmod3$. The same recurrence, now modulo $4x+3$, has $Z_{j+3}\equiv Z_j$ and $Z_1=4x+3$. Consequently $4x+3\mid x^h$, and every prime factor of $4x+3$ must divide three. But $4x+3\equiv7\pmod8$ has no such prime factorization. [Binomial congruence and exceptional-prime arguments](../OddPerfect/AlternatingPell.lean)

## Consequences for odd perfect numbers

Let $N=q^a m^2$ be an odd perfect number in Euler form, $a>1$, $d=(a+1)/2$, and $I=\sigma(m^2)/q^a$. If $I=\ell t^2$ for $\ell=1$ or prime, the checked reductions force all of
$$d\text{ prime},\qquad d\equiv1\pmod8,\qquad q\equiv1\pmod{16},\qquad \frac{q+1}{2}=d w^2.$$
The previous factor-count bounds left $d=s$ or $s^2$, with $s\mid q-1$ necessary in the square case. In the latter case $s\nmid q^s+1$. The nonsquare alternating factor at base $q^s$ then gives a nonsquare second Euler half-block, contradicting the index hypothesis. In the prime case, the alternating factor at $q$ leaves only $s\equiv1\pmod8$ and $s\mid q+1$. Lifting the exponent shows the valuation of $(q+1)/2$ is odd at $s$ and even at every other prime. For a fixed Euler prime, the restriction determines at most one possible exponent greater than one through the squarefree part of $(q+1)/2$. [Euler reduction](../OddPerfect/ExceptionalLength.lean) · [Earlier quantitative bounds](HALF_LENGTH_SUPPORT.md) · [Valuation equality](HALF_BLOCKS.md)

The remaining Diophantine equation is $q^d+1=2y^2$. On paper, Bennett and Skinner's Theorem 1.1, specialized to $C=2$ and $(x,y)=(q,1)$, excludes it for these prime exponents $d\ge17$. The coprimality with the square root follows since $q\mid y$ is incompatible with $q^d+1=2y^2$. The classical cubic solution $23^3+1=2\cdot78^2$ falls outside the Euler residue class for $q$. Hirakawa’s Lemma 2.5 cites Bruin for exponent five and Ivorra’s Theorem 2(b) for prime exponents at least seven. The latter applies to the primitive positive triple $(q,1,y)$ and is the published input for all remaining prime half-lengths here. The Lean reduction stops at the displayed necessary shape, and Gallardo's square-index exclusion is independently checked without any remaining length restriction. [Bennett and Skinner, Theorem 1.1](https://doi.org/10.4153/CJM-2004-002-2) · [Hirakawa, Theorem 1.1 and Lemma 2.5](https://arxiv.org/pdf/2309.17084v3) · [Ivorra, Theorem 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82637) · [Exact checked index results](HIRAKAWA.md)

Run `lake build OddPerfect.ExceptionalLength` from the project root to replay the descent, the binomial argument and the Euler reduction.
