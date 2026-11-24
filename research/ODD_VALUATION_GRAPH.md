# Odd valuations on the divisor-sum graph

Let $S$ be the distinct prime divisors of an odd perfect number $N$. Draw an edge $p\to r$ when $p,r\in S$ and $v_r(\sigma(p^{v_p(N)}))$ is odd. Every such edge is a divisor-sum edge, and no source is its own target. At each $r$, the number of incoming edges has the same parity as $v_r(N)$. This follows by adding the exact incoming valuations and reducing modulo two. Thus the Euler prime has odd indegree and every other prime has even indegree. [Valuation identity](../OddPerfect/Valuations.lean) · [Graph theorems](../OddPerfect/OddValuationGraph.lean)

Some nonspecial prime always receives edges from at least two distinct sources. If the Euler exponent $a>1$, its half-sum $\sigma(q^a)/2$ is nonsquare, so $q$ emits an odd-valuation edge. Its target differs from $q$ and has positive even indegree. If $a=1$, at least three ordinary primes remain after removing $q$ and the possible source $3$. Each emits an edge because the only square sum at a positive even exponent is $\sigma(3^4)=11^2$. They cannot all point to $q$, whose total incoming valuation is one. [Euler half-sum](HIRAKAWA.md) · [Even-exponent square classification](ODD_GEOMETRIC_SQUARES.md) · [Distinct-prime lower bound](../OddPerfect/FewPrimes.lean)

At least one of these alternatives holds.

- The odd-valuation edges contain a directed cycle.
- The exact power of three is $3^4$, and $11^2\mid N$.
- The Euler exponent is one and $(q+1)/2$ is square. This forces $q\equiv1\pmod{16}$.

The two exceptional cases identify possible terminal vertices. When neither occurs, every vertex has an outgoing edge. Following edges in the finite set $S$ then repeats a vertex. A directed cycle can coexist with an exceptional component. [Cycle theorem](../OddPerfect/OddValuationGraph.lean)

Local divisibility admits a three-cycle even when all three primes are three modulo four. The components $7^2,19^4,151^2$ give edges $7\to19\to151\to7$, each with odd valuation. These exact component identities supply a graph example. The product of the three components is deficient, since its abundancy is bounded by $(7/6)(19/18)(151/150)<2$. [Checked odd valuations](../OddPerfect/OddValuationGraph.lean) · [Quadratic reciprocity for edges](RECIPROCITY.md)

## Outdegree and the residue class three modulo four

At an ordinary component $p^e$ of an odd perfect number, all odd-valuation prime divisors of $\sigma(p^e)$ are graph targets. The length weight $W(p,e+1)$ is bounded by this outdegree, with the correction at $p=3$ and $5\mid e+1$. At the Euler prime, the targets form precisely $O(I)$ for the component index $I$. Thus the weighted half-length bound counts genuine outgoing edges of the Euler prime. [Graph weights](../OddPerfect/OddGraphWeight.lean) · [Ordinary length weight](ODD_SOURCE_WEIGHT.md) · [Euler half-length weight](PAIRED_LENGTH.md)

For each source $p\equiv3\pmod4$, the number of odd-valuation targets $r\equiv3\pmod4$ is even. Its exponent is even, so $\sigma(p^e)\equiv1\pmod4$. Every odd integer has residue $3^k\pmod4$ where $k$ counts its distinct primes three modulo four with odd valuation. Thus any edge $p\to r$ within this class forces another edge $p\to t$ there. Quadratic reciprocity excludes the reverse edges from both targets. In particular any two-step path $p\to r\to s$ within the class forces a fourth distinct prime in the class. For the Euler prime, the number of class-three targets is odd exactly when $q$ and its exponent differ modulo eight. [Parity and forcing theorems](../OddPerfect/ThreeModFourGraph.lean) · [Euler residues](CHEN_LUO.md)
