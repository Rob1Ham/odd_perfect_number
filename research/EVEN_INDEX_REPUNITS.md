# Simultaneous repunit equations for an even prime-power index

Let an exact component of an odd perfect number have index $p^{2u}$, with $u>0$. In the cofactor split $N=q(p^u s)^2$, each $r\mid s$ supplies a positive odd exponent $\beta_r$ and a prime length $n_r=2v_r(s)+1>2$, with
$$
 G(r,n_r)=1+r+\cdots+r^{n_r-1}=p^{\beta_r},\qquad
 \sum_{r\mid s}\beta_r=2u.
$$
Different cofactor primes give different left-hand bases. [Cofactor equations](EVEN_PRIME_POWER_SOURCES.md) · [Single-witness reduction](NAGELL_LJUNGGREN_INDEX.md)

Either the prime $p$ is a repunit of prime length greater than two in **two distinct odd prime bases**, or at least **three** such bases give Nagell–Ljunggren solutions sharing the same right-hand prime $p$. Indeed, two single-copy sources give the first alternative. With at most one single-copy source, every other source has $\beta_r>1$. Choose an odd prime $l\mid\beta_r$ to write $G(r,n_r)=(p^{\beta_r/l})^l$. There are at least four cofactor primes because $\omega(N)\ge5$, $\omega(s)=\omega(N)-2$, and $\omega(s)$ is even. [Formal alternatives](../OddPerfect/EvenIndexRepunits.lean)

The two odd prime bases in the first alternative give a Goormaghtigh equation. The two classical numerical values are $31=G(2,5)=G(5,3)$ and $8191=G(2,13)=G(90,3)$. Checking their possible odd prime bases and prime lengths rules out either as the value of the first alternative. Grantham's corrected October 2026 computation reports that there are no other Goormaghtigh primes below $10^{700}$. This is an external quantitative restriction. The Lean alternatives here are independent of that computation. [Grantham, corrected version and specific computational corrections](https://arxiv.org/html/2410.03677v3) · [Bugeaud and Shorey](https://msp.org/pjm/2002/207-1/pjm-v207-n1-p04-p.pdf)

A repetition of any $\beta_r$ gives the same two-base equation at $p^{\beta_r}$. If the exponents are all distinct, the sum of $k=\omega(s)$ distinct positive odd numbers is at least $k^2$. Hence $\omega(s)^2\le2u$ unless a power of $p$ has two such representations. The common value here can be composite, so Grantham's prime-only bound applies specifically when $\beta_r=1$. [Repeated-value and cardinality theorem](../OddPerfect/EvenIndexRepunits.lean)
