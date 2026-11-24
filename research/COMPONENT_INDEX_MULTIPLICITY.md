# Finiteness from bounded factor count of a component index

For every exact component $q^a$ of a hypothetical odd perfect number $N$, write $i=\sigma(N/q^a)/q^a$, and let $\omega$ and $\Omega$ count distinct prime divisors and prime factors with multiplicity. We prove
$$
 \omega(N)\le 2\bigl(\omega(i)+\Omega(i)\bigr)+4.
$$
The selected component may be the Euler component or an even-exponent component. [Factor-count theorem and effective bounds](../OddPerfect/BoundedIndexWeight.lean)

In the component-cover argument, all but at most two primes of $N$ belong to one of three sets. These are the odd prime divisors of $a+1$, the prime divisors of $i$, and a set with cardinality at most $\Omega(i)$. Put $L=\omega(a+1)$. Primitive-order witnesses give $2^L\le\omega(N)$, while $2L\le2^L$. Substituting the resulting $2L\le\omega(N)$ in the cover bound proves the inequality. [Index cover](../OddPerfect/IndexSupport.lean) · [Length and support](../OddPerfect/IndexWeight.lean)

It follows that for every fixed natural $K$, only finitely many odd perfect numbers can have even one exact component with $\Omega(i)\le K$. In fact $\omega(N)\le4K+4$, and the formal Dickson bound gives an explicit computable upper bound for $N$. This permits the primes in the index to vary freely. [Effective Dickson bound](../OddPerfect/Dickson.lean)
