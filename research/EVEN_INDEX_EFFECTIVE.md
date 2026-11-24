# Explicit size bounds from an even prime-power index

Suppose an exact component of an odd perfect number $N$ has index $p^{2u}$ with $p$ prime and $u>0$. Define $B=14(u+1)4^{2u-4}$. The bounds are
$$
 p\le B,\qquad N<2B^{6u}.
$$
The component has Euler exponent one and $N=q(p^u s)^2$. The cofactor satisfies $q=\sigma(p^{2u})$, $q+1=2s^2$, and $\sigma(s^2)=p^{2u}$. If $w=\omega(s)$, the intermediate bounds are
$$
 p\le2(w+3)\operatorname{rad}(s),\qquad
 \operatorname{rad}(s)\le(u+1)4^{2u-w}.
$$
[Effective inequalities](../OddPerfect/EvenIndexEffective.lean) · [Cofactor split](EVEN_PRIME_POWER_SOURCES.md)

## Bounding the index prime by the cofactor radical

Write $P=\prod_{r\mid s}r$, $R=\prod_{r\mid s}(r-1)$ and $c_r=r^{2v_r(s)+1}$, where $r$ runs over distinct primes. Each $c_r-1=(r-1)\sigma(r^{2v_r(s)})$ and the rightmost divisor sum is a positive power of $p$. Thus $c_r\ge p$, even for a single-copy return. With $j=2u$, one has $\prod(c_r-1)=Rp^j$ and $\prod c_r=Ps^2$. Use these relations together with $p^{j+1}-1=q(p-1)$ and $q+1=2s^2$ to obtain the balance
$$
 P\prod_r(c_r-1)\;p\;(p^{j+1}-1)\;(q+1)
 =
 2R\prod_r c_r\;(p-1)\;p^{j+1}\;q.
$$
Here $P$ is odd, and $2R$ is even. The remaining $w+3$ indexed pairs are adjacent integers; the larger number in each pair is at least $p$. The product-gap theorem gives $p\le(w+3)\max(P,2R)\le2(w+3)P$. Coincident label values still count separately. [Label-balance proof](../OddPerfect/EvenIndexBaseBound.lean) · [Product-gap theorem](../OddPerfect/ProductGap.lean)

## A determinant for each local return

Let $\sigma(r^{2v_r(s)})=p^\beta$ and put $x=p\bmod r$. Then $x^\beta=1$ and $x^{2u+1}+x=2$ in $\mathbb F_r$. If $x=1$, then $r\mid u+1$. Otherwise set $n=2u+1$ and use the matrix indexed by $\mathbb Z/\beta\mathbb Z$ that acts on a vector $f$ by
$$
 (Mf)(0)=f(0),\qquad (Mf)(t)=2f(t)-f(t+1)-f(t+n)\quad(t\ne0).
$$
An integer kernel vector has no positive maximum. Such a maximum cannot occur at the anchored row. At any other row equality forces the next value at $t+1$ to be the same maximum, which propagates to zero. Applying the same proof to the negative vector proves that the determinant is nonzero. Modulo $r$ the vector $t\mapsto x^t-1$ is nonzero and belongs to the kernel. Hence $r$ divides the nonzero integer determinant. This also gives a finite exceptional set for each $\beta$, independently of $u$, by taking all possible residues of $n$ modulo $\beta$. [Determinant construction](../OddPerfect/EvenIndexDeterminant.lean) · [Modular root identities](../OddPerfect/EvenIndexRoots.lean)

The Leibniz formula bounds the determinant in absolute value by the product of the row sums of absolute values. Summing absolute products over all functions from the rows to the columns includes every permutation. The anchor has row sum one, and every other row has sum at most four, including coincident neighbors. Consequently $r\nmid u+1$ forces $r\le4^{\beta-1}$. The primes of $s$ that divide $u+1$ have product at most $u+1$. The total of all $\beta-1$ is $2u-w$, proving the radical bound. [Determinant estimate and product over cofactor primes](../OddPerfect/EvenIndexEffective.lean)

For an odd perfect number $w\ge4$. Combining the intermediate bounds uses $w+3\le7\cdot4^{w-4}$. The checked exponent-one size inequality $N<2i^3$ then gives the displayed bound on $N$. The index exponent may vary, so this result gives a finite range for each specified $u$. [Exponent-one size inequality](../OddPerfect/ExponentOneSize.lean)
