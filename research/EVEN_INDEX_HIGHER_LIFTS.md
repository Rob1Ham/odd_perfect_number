# Higher radical congruences and an exponent-only bound

This is a mathematical derivation awaiting its Lean proof. It uses the odd prime $p$, odd $s$, positive $u$, multiplicities $\beta_r$ and polynomial $D(X)$ in the radical note. Put $j=2u$ and $P=\operatorname{rad}(s)$. [Radical and first lift](EVEN_INDEX_RADICAL_LIFTS.md)

From $P s^2=D(p)$ and the geometric formula for $q$, one has the integer identity
$$P(2-p-p^{j+1})=2(1-p)D(p).$$
For $1\le k\le j$, form $H_k(X)=\sum_{a=0}^k2^{k-a}X^a$ and let $E_k$ retain the terms of degrees $0$ through $k$ in $(1-X)D(X)H_k(X)$. The identity $(2-X)H_k(X)=2^{k+1}-X^{k+1}$ gives
$$2^kP\equiv E_k(p)\pmod{p^{k+1}}.$$
Cancelling the factor two is valid since $p$ is odd. All nonconstant coefficients of $D$ are even. Modulo two, $H_k=X^k$ and the truncation of $(1-X)D H_k$ is $X^k$. Thus $E_k(p)$ is odd, while $2^kP$ is even. Their nonzero difference has absolute value at least $p^{k+1}$.

## A uniform coefficient bound

Write $D=\sum_h d_h X^h$. All the coefficients are nonnegative. If $r\nmid u+1$, the checked determinant bound gives $r\le4^{\beta_r-1}$ and hence $64^{\beta_r}\ge64r^3$. Therefore
$$1+(r-1)64^{-\beta_r}\le\frac{r^2}{r^2-1}.$$
The product of this last fraction over $r=2,\ldots,M$ equals $2M/(M+1)<2$. All fractions exceed one, so this bounds any finite subset of primes. For $r\mid u+1$ the individual factor $1+(r-1)64^{-\beta_r}$ is at most $r$ and the product of those distinct primes divides $u+1$. Consequently $D(1/64)\le2(u+1)$, and $d_h\le2(u+1)64^h$. [Checked determinant estimate](../OddPerfect/EvenIndexEffective.lean)

At $x=1/64$, the polynomial with absolute coefficients of $E_k$ has value at most $(1+x)D(x)H_k(x)$. Since $H_k(x)\le2^k/(1-x/2)$, this value is at most $3(u+1)2^k$. For $p\ge1$ and $0\le h\le k$, $p^h\le(64p)^k64^{-h}$. Hence $|E_k(p)|\le3(u+1)128^k p^k$. If $p>6(u+1)128^k$, the absolute value is less than $p^{k+1}/2$. Combining with the nonzero difference then gives
$$p\le6(u+1)128^k\quad\text{or}\quad p^{k+1}\le2^{k+1}P.$$

The checked radical bound gives $P\le(u+1)4^j$. With $k=\lfloor\sqrt j\rfloor\ge1$, the second alternative implies $p\le2(u+1)4^{k+1}$ because $j<(k+1)^2$. The first is larger, so $p\le6(u+1)128^{\lfloor\sqrt j\rfloor}$ suffices. This exponent-only bound grows subexponentially in $j$. Substitution in $N<2p^{3j}$ gives a corresponding conditional size bound for an odd perfect number with such an index. The infinite family of possible index exponents remains open.
