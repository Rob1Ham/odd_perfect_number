# Forced prime squares at an exceptional Euler exponent

Assume $N=q^a m^2$ is odd and perfect, $q$ is its Euler prime, $a>1$, and the Euler index $I=\sigma(m^2)/q^a$ equals $\ell t^2$ with $\ell=1$ or prime. Put $s=(a+1)/2$. An earlier reduction gives $s$ prime, $s\equiv1\pmod8$, and $q+1=2sw^2$, $q^s+1=2y^2$. [Euler half-length reduction](ALTERNATING_PELL.md)

An odd prime $r$ must divide $w$ whenever $r-1\mid s-1$ and $s$ is a quadratic nonresidue modulo $r$. Indeed $q^s\equiv q\pmod r$ by Fermat's little theorem, including the case $r\mid q$. The two displayed equalities then give $y^2\equiv sw^2\pmod r$. If $w$ were invertible modulo $r$, the quotient $y/w$ would be a square root of $s$. For any finite set $R$ of such primes, $\prod_{r\in R}r\mid w$. Also $2w^2\mid q+1\mid\sigma(q^a)$ and $\sigma(q^a)I=2m^2$. Therefore $(\prod_{r\in R}r)^2\mid N$. An abundant square of this form contradicts perfection for every $q$. [Individual forcing and abundant-product theorem](../OddPerfect/ExceptionalNonresidues.lean)

For example, the entire congruence class
$$s\equiv23057\pmod{91{,}869{,}360}$$
forces $R=\{3,5,17,23,89\}$. Lean checks primality, the order divisibilities and the five quadratic nonresidues in their finite fields. The square $(3\cdot5\cdot17\cdot23\cdot89)^2$ is abundant. Its exact divisor sum is the product of $r^2+r+1$ over these primes and exceeds twice the square. This excludes a square or prime-times-square index throughout the class, without a bound on $q$ or $N$. For instance $s=23057$ gives $a=46113$. The general paper exclusion covers the remaining exponent classes by a different Diophantine theorem. [Formal residue-class exclusion](../OddPerfect/ExceptionalNonresidues.lean) · [Hirakawa](https://arxiv.org/pdf/2309.17084v3)

## Order of the index prime

The sole odd-valuation prime $\ell$ in the exceptional index must satisfy
$$\operatorname{ord}_{\ell}(q)=s, \qquad \ell\equiv1\pmod{8s}.$$
In particular $\ell\ge8s+1$. The positive block $A=G(q,s)$ is nonsquare. Choose an odd-valuation prime divisor $r$ of $A$. The other Euler half-block is coprime to $A$, so this odd valuation transfers to $I=\ell t^2$ and $r=\ell$. Reduction of $G(q,s)$ modulo $\ell$ gives $q^s\equiv1$. If $\ell=s$, Fermat's theorem forces $q\equiv1\pmod s$, incompatible with $s\mid q+1$ and odd $s$. If $q\equiv1\pmod\ell$, the same geometric sum reduces to $s$, again forcing $\ell=s$. The order is therefore $s$. The independently checked $I\equiv1\pmod8$ gives $\ell\equiv1\pmod8$, and the two moduli combine because $s$ is odd. [Exact order proof](../OddPerfect/ExceptionalOrder.lean) · [Euler index modulo eight](../OddPerfect/ExceptionalIndexResidue.lean)

Run `lake build OddPerfect.ExceptionalNonresidues OddPerfect.ExceptionalOrder` to replay the two restrictions.
