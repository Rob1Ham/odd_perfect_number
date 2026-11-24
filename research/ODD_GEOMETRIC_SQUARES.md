# Odd-length geometric squares

For every natural base $b>1$ and odd length $n>1$, the sum $G(b,n)=1+b+\cdots+b^{n-1}$ is a square exactly when $(b,n)=(3,5)$. The witness is $G(3,5)=121=11^2$. For a prime $p$ and positive even exponent $e$, it follows that $\sigma(p^e)$ is a square exactly when $p=3$ and $e=4$. The base in the first statement may be composite. [Lean statements](../OddPerfect/OddGeometricSquares.lean)

Ljunggren's Theorem 1 gives the full positive-base classification for $n>2$. Its other positive-base solution $(7,4)$ has even length. At $n=1$, every geometric sum is one. At $b=1$, the sum equals its length and can be a square. The companion negative-base odd-length statement is checked separately. [Ljunggren, *Norsk Matematisk Tidsskrift* 25 (1943)](https://msleziak.com/temp/Ljunggren.pdf) · [Alternating geometric sums](ALTERNATING_PELL.md)

## Positive-coordinate proof

Write $n=2h+1$ and $x=b-1$. A square sum $G(b,n)=y^2$ gives $(x+1)(b^h)^2-xy^2=1$. Descent places $(b^h,y)$ among the iterates $(Y_j,Z_j)$ of $(1,1)$ by the integral matrix with rows $(2x+1,2x)$ and $(2x+2,2x+1)$. If $j>0$, the coordinate $Y_j$ exceeds $2j+1$. For each prime $p\ge5$ dividing $b$, a binomial congruence in the quadratic ring shows $v_p(Y_j)\le v_p(2j+1)$. All $Y_j$ are odd. Consequently, if every prime divisor of $Y_j$ divides $b$ and three does not divide $Y_j$, then $Y_j\mid 2j+1$ and $j=0$. [Pell coordinates](../OddPerfect/PellCoordinates.lean) · [Binomial congruence](../OddPerfect/AlternatingPell.lean)

At a positive index with $Y_j=b^h$, this leaves $3\mid b$ and $3\mid Y_j$. The recurrence modulo three gives $Y_j\equiv(-1)^j(2j+1)\pmod3$, so $j=3k+1$. The exact triple-index formula is
$$Y_{3k+1}=Y_k(4bY_k^2-3).$$
The second factor exceeds three, divides $b^h$, and has no prime divisor other than three. It is therefore divisible by nine. If $3\mid Y_k$, the same formula for the second factor would give $9\mid3$. Thus $3\nmid Y_k$. All prime divisors of $Y_k$ divide $b$, so $k=0$ and $j=1$. We now have $b^h=4b-3$. Divisibility by $b$ gives $b=3$, hence $h=2$ and $n=5$. [Checked proof](../OddPerfect/OddGeometricSquares.lean)

Run `lake build OddPerfect.OddGeometricSquares` to replay the classification and its divisor-sum corollary.
