# Nonsquare geometric sums and the Euler component index

For every prime $q\equiv1\pmod4$ and every integer $e\ge1$, the divisor sum $\sigma(q^e)$ is nonsquare. This is Hirakawa's Theorem 2.3, with no hypothesis about a perfect number. The length version has $d=e+1>1$. At length one the geometric sum is 1. At base one it equals the length and can be a square. The congruence on the prime is substantive: $1+3+3^2+3^3+3^4=11^2$ and $1+7+7^2+7^3=20^2$. [Local proof](../OddPerfect/GeometricNonSquare.lean) · [Hirakawa, v3, Theorem 2.3](https://arxiv.org/pdf/2309.17084v3)

## Explicit division in the quadratic order

Set $D=1-q$, $w=1+\sqrt D$, so $w$ has norm $q$. A hypothetical square $G(q,d)=y^2$ gives $z=1+y\sqrt D$ of norm $q^d$. For any $u+v\sqrt D$, divisibility by $w$ is equivalent to $q\mid v-u$. In the reverse direction write $v-u=qt$ and multiply $w$ by $(v-t)+t\sqrt D$. If a norm is divisible by $q$, primality and the factorization of $u^2-v^2$ show that $w$ divides the element or its conjugate. Both alternatives for $z$ would give $q\mid2$, so one orientation persists through each successive division. After $d$ divisions the quotient has norm one. Since $D\le-4$, the only norm-one elements are $1$ and $-1$. Hence the real coefficient of $w^d$ would have to be $1$ or $-1$.

The formal proof excludes both values by doubling. Write $D=4c$. For each positive even exponent $m$, the coordinates of $w^m$ have the form
$$\left(1+4cR(1+2A),\;2RB\right),\qquad R>0.$$
The initial case is $w^2$. Odd powers preserve the form, and squaring replaces $R$ by $2R$. These steps cover every positive even exponent. Multiplying an even power by $w$ replaces $A$ in the real coordinate by $A+B$, which also handles odd exponents greater than one. The real coordinate differs from 1 and is 1 modulo 4, excluding $-1$.

Hirakawa's original proof uses prime ideals in a quadratic order and a two-adic valuation of a binomial sum. The checked argument uses integer coordinates in mathlib's `Zsqrtd` and the doubling identities above. Neither proof needs the full Nagell–Ljunggren classification for arbitrary bases. [Hirakawa, proof of Theorem 2.1 and Remark 2.4](https://arxiv.org/pdf/2309.17084v3)

## Consequences for the index

Write an odd perfect number as $N=q^a m^2$ in Euler form. Put $I=\sigma(m^2)/q^a$, $d=(a+1)/2$, $A=G(q,d)$ and $B=(q^d+1)/2$. Then $m^2=ABI$, with $A$ and $B$ coprime. For $a>1$, some prime has odd valuation in $A$. It has the same odd valuation parity in $I$, so $I$ cannot be square. Gallardo's Proposition 2 states this using $\gcd(m^2,\sigma(m^2))$ as the index. The two definitions agree. [Gallardo, Integers 22 (2022), A58, Proposition 2](https://math.colgate.edu/~integers/w58/w58.pdf) · [Local Euler half-blocks](../OddPerfect/EulerSquareClass.lean)

The first-block argument also proves Hirakawa's full Theorem 2.1, independently of a hypothetical perfect number: for every prime $q\equiv1\pmod4$ and $a>1$, $\sigma(q^a)$ cannot equal twice a square. An equality would force $a$ odd, give $AB=n^2$, and make $A$ a square.

To exclude $I=\ell t^2$ for a prime $\ell$, a second odd-valuation prime suffices. If $q\not\equiv1\pmod{16}$, a square $B$ would force $q^d\equiv1\pmod{16}$. Raising to the odd power $d$ again and using $d^2\equiv1\pmod4$ would give $q\equiv1\pmod{16}$. For all Euler primes the cubic and quintic arguments also exclude square $B$ when $3\mid d$ or $5\mid d$. These conditions leave a possible prime-times-square index only when $q\equiv1\pmod{16}$ and $\gcd(d,15)=1$. Hirakawa excludes that branch in full using results on generalized Fermat equations. [Local cubic and quintic proofs](EULER_SQUARE_CLASS.md) · [Hirakawa, Lemma 2.5 and Theorem 2.2](https://arxiv.org/pdf/2309.17084v3)

Run `lake build OddPerfect.Hirakawa` to replay the geometric-sum theorem, twice-square exclusion, gcd identity, nonsquare-index results and prime-times-square branches. [Checked consequences](../OddPerfect/Hirakawa.lean)
