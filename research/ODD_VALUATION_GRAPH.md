# Odd valuations on the divisor-sum graph

Let $S$ be the distinct prime divisors of an odd perfect number $N$. Draw an edge $p\to r$ when $p,r\in S$ and $v_r(\sigma(p^{v_p(N)}))$ is odd. Every such edge is a divisor-sum edge, and no source is its own target. At each $r$, the number of incoming edges has the same parity as $v_r(N)$. This follows by adding the exact incoming valuations and reducing modulo two. Thus the Euler prime has odd indegree and every other prime has even indegree. [Valuation identity](../OddPerfect/Valuations.lean) · [Graph theorems](../OddPerfect/OddValuationGraph.lean)

Some nonspecial prime always receives edges from at least two distinct sources. If the Euler exponent $a>1$, its half-sum $\sigma(q^a)/2$ is nonsquare, so $q$ emits an odd-valuation edge. Its target differs from $q$ and has positive even indegree. If $a=1$, at least three ordinary primes remain after removing $q$ and the possible source $3$. Each emits an edge because the only square sum at a positive even exponent is $\sigma(3^4)=11^2$. They cannot all point to $q$, whose total incoming valuation is one. [Euler half-sum](HIRAKAWA.md) · [Even-exponent square classification](ODD_GEOMETRIC_SQUARES.md) · [Distinct-prime lower bound](../OddPerfect/FewPrimes.lean)

At least one of these alternatives holds.

- The odd-valuation edges contain a directed cycle.
- The exact power of three is $3^4$, and $11^2\mid N$.
- The Euler exponent is one and $(q+1)/2$ is square. This forces $q\equiv1\pmod{16}$.

The two exceptional cases identify possible terminal vertices. When neither occurs, every vertex has an outgoing edge. Following edges in the finite set $S$ then repeats a vertex. A directed cycle can coexist with an exceptional component. [Cycle theorem](../OddPerfect/OddValuationGraph.lean)

Local divisibility admits a three-cycle even when all three primes are three modulo four. The components $7^2,19^4,151^2$ give edges $7\to19\to151\to7$, each with odd valuation. These exact component identities supply a graph example. The product of the three components is deficient, since its abundancy is bounded by $(7/6)(19/18)(151/150)<2$. [Checked odd valuations](../OddPerfect/OddValuationGraph.lean) · [Quadratic reciprocity for edges](RECIPROCITY.md)
