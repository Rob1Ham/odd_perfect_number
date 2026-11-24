# The radical of the cofactor modulo the index prime

Consider the equations $q=\sigma(p^{2u})$, $q+1=2s^2$ and $\sigma(s^2)=p^{2u}$ with $p$ an odd prime, $s$ odd and $u>0$. They are necessary at any component of an odd perfect number having index $p^{2u}$. Write $P=\operatorname{rad}(s)$, $j=2u$ and $\sigma(r^{2v_r(s)})=p^{\beta_r}$ for each prime $r\mid s$. The multiplicities are positive odd integers and sum to $j$. Define
$$D(X)=\prod_{r\mid s}(1+(r-1)X^{\beta_r}).$$
The geometric identities at all the sources multiply to $s^2P=D(p)$. Since $q\equiv1\pmod p$, we have $s^2\equiv1\pmod p$. Thus $P\equiv1\pmod p$. The positive odd integer $P$ exceeds one because $s>1$. Its difference from one is divisible by $2p$, giving $2p+1\le P$. [Radical identity and congruence](../OddPerfect/EvenIndexRadical.lean)

Let $h=(P-1)/p$ and $T=\sum_{\beta_r=1}(r-1)$. The single-copy primes divide $u+1$. Their product is at most $u+1$ and at least $1+T$, so $T\le u$. In the ring modulo $p^2$, $D(p)=1+pT$, $q=1+p$ and $2s^2=2+p$. Hence $(2+p)(1+ph)=2+2pT$, or
$$2h+1\equiv2T\pmod p.$$
When $p>2u$, the residue $2T$ is less than $p$. Parity prevents $2h+1$ from equalling $2T$, so $p\le2h+1$. In particular
$$p\le 2u\quad\text{or}\quad p^2\le2(P-1)+p.$$
[First lift and quadratic inequality](../OddPerfect/EvenIndexRadicalLift.lean)

At an exact component at least four distinct primes divide $s$. Combining the first lift with the determinant bound gives the explicit alternative $p\le2u$ or $p^2\le2((u+1)4^{2u-4}-1)+p$. [Component wrapper](../OddPerfect/EvenIndexRadicalCutoff.lean) · [Determinant bound](EVEN_INDEX_EFFECTIVE.md)
