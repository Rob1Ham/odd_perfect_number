# The odd valuations in an ordinary component

For a natural base $b>1$ and odd length $d$, put $G(b,d)=1+b+\cdots+b^{d-1}$. Let $O(n)$ be the set of primes that divide $n$ to an odd exponent. Write
$$
W(b,d)=\sum_{s\mid d,\ s\text{ prime}}
\begin{cases}
\lceil v_s(d)/2\rceil,&s\mid b-1,\\
v_s(d),&s\nmid b-1.
\end{cases}
$$
The checked inequality is
$$W(b,d)\le |O(G(b,d))| + [b=3\ \text{and}\ 5\mid d].$$
The bracket is one if both conditions hold and zero otherwise. The correction is attained by $G(3,5)=121$. The proof covers composite bases. [Lean theorem](../OddPerfect/OddSourceWeight.lean) · [Odd-length square classification](ODD_GEOMETRIC_SQUARES.md)

Sort the distinct prime divisors of the length in decreasing order. When the existing length $D$ gains the full prime power $s^k$, the old block $G(b,D)$ and new block $G(b^D,s^k)$ are coprime. A common divisor would divide both $s$ and $G(b,D)$. Reduction modulo $s$ would force either $s\mid D$ or a nontrivial order dividing both $D$ and $s-1$. Neither is possible because every prime of $D$ exceeds $s$. In particular, $s\nmid b-1$ gives $s\nmid b^D-1$ by the same order argument. [Coprime decomposition](../OddPerfect/GeometricSquareClass.lean)

For $s\nmid b^D-1$, adjoining successive factors of $s$ again gives coprime blocks. Each is nonsquare by the odd-length classification, except for the possible initial $G(3,5)$. For $s\mid b^D-1$, two successive steps form a block of length $s^2$. That block is nonsquare and its $s$-valuation is even by lifting the exponent. The old and new odd-valuation primes are disjoint because their only possible common prime is $s$. If the number of steps is odd, its first block also contributes an odd valuation. These counts add across the full prime-power blocks. [Local valuation argument](../OddPerfect/HalfLengthSupport.lean) · [Weighted count](../OddPerfect/OddSourceWeight.lean)
