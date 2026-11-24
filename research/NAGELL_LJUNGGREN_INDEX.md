# Prime-power component indices and the Nagell–Ljunggren equation

A hypothetical odd perfect number with a prime-power index at **any** exact component would produce integers satisfying
$$
 \frac{x^n-1}{x-1}=(v^c)^\ell,
$$
where $x$ is an odd prime, $n>2$ is prime, $v$ is prime, $c>0$, and $\ell$ is an odd prime. Lean proves this implication without any Diophantine classification hypothesis. The formal equation uses the finite geometric sum, which equals the displayed quotient for $x>1$. [Formal reduction](../OddPerfect/PrimePowerNagellLjunggren.lean) · [Geometric-sum identity](../OddPerfect/IndexSieveBudget.lean)

This would give a further positive solution of the Nagell–Ljunggren equation. Its three standard positive solutions $(x,n,y,\ell)$ are $(3,5,11,2)$, $(7,4,20,2)$ and $(18,3,7,3)$. The first two have even exponent on the right, and the third has even base on the left. The complete positive classification remains open. The Lean corollary `no_prime_power_component_index_of_nagell_ljunggren_classification` accepts the full classification as a hypothesis and deduces that every exact component index differs from every positive power of a prime. [Bugeaud–Mihăilescu, Theorem NL and Theorem 1](https://irma.math.unistra.fr/~bugeaud/travaux/PredaYann1.pdf) · [Bennett–Levin, introduction and main theorem](https://arxiv.org/abs/1312.4037) · [2026 account of the classical solutions](https://math.colgate.edu/~integers/aa44/aa44.pdf)

## Odd exponent of the index prime

Let $i=p^j$ with $j$ odd. The index identifies the Euler component $q^a$ in $N=q^a m^2$. The exact return theorem supplies $d=(a+1)/2$, an odd prime, with $\sigma(p^{j+1})=q^d$. Its length $j+2$ is prime. This realizes the displayed equation with $x=p$, $n=j+2$, $v=q$, $c=1$ and $\ell=d$. [Odd-exponent proof and exact return](ODD_PRIME_POWER_INDEX.md)

## Even exponent of the index prime

Let $i=p^{2u}$ with $u>0$. Here $a=1$, $m=p^u s$, $q=\sigma(p^{2u})$, $q+1=2s^2$, and $\sigma(s^2)=p^{2u}$. For each $r\mid s$, the component sum $\sigma(r^{2v_r(s)})=p^{\beta_r}$ supplies a positive **odd** exponent. The exponents add to $2u$. [Cofactor equations and odd exponents](EVEN_PRIME_POWER_SOURCES.md)

Suppose each $\beta_r=1$. Then $p\equiv1\pmod r$, so $q=\sigma(p^{2u})\equiv2u+1\pmod r$. Also $q\equiv-1\pmod r$, implying $r\mid u+1$ since $r$ is odd. All these distinct primes therefore belong to the integer interval $[2,u+1]$, of cardinality $u$. Their number would be $2u$ because each contributes one copy of $p$. This contradiction forces some odd $\beta_r>1$. Choose an odd prime $\ell\mid\beta_r$ and write $\beta_r=c\ell$. The pure divisor-sum theorem gives primality of the length $2v_r(s)+1$, producing the required solution with $x=r$ and $v=p$. [Formal single-copy argument](../OddPerfect/PrimePowerNagellLjunggren.lean) · [Pure geometric lengths](../OddPerfect/IndexPowerLength.lean)

Bugeaud and Mihăilescu's Theorem 1 yields the further published restriction $n\ge29$ for such a witness. This additional bound uses results on linear forms in logarithms and is recorded here as a consequence of their paper. The Lean reduction itself proves $n>2$ and primality directly. [Bugeaud–Mihăilescu, Theorem 1](https://irma.math.unistra.fr/~bugeaud/travaux/PredaYann1.pdf)
