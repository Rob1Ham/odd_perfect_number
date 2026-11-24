# Square classes in the Euler component index

For $n>0$, write $T(n)$ for the set of primes $r\equiv3\pmod4$ such that $v_r(n)$ is odd. Let $N=q^a m^2$ be odd and perfect in Euler form and write $I=\sigma(m^2)/q^a$ and $d=(a+1)/2$. The checked bound is

$$|T(d)| + [q\equiv5\pmod8] \le |T(I)|.$$

The bracket is one when the condition holds and zero otherwise. For instance, $a=41$ gives $d=21$ and demands two distinct primes 3 modulo 4 of odd valuation in the index, for every possible Euler prime. This bound carries information about a whole family of exponents without imposing a bound on the size of $N$. [Euler index proof](../OddPerfect/EulerSquareClass.lean)

## Separating the factors

Put $G(b,t)=1+b+\cdots+b^{t-1}$, $A=G(q,d)$, and $B=(q^d+1)/2$. Pairing the two blocks of length $d$ in $\sigma(q^a)$ gives $m^2=ABI$. Every odd prime of $A$ divides $q^d-1$, whereas every prime of $B$ divides $q^d+1$. Also $B$ is odd, so $A$ and $B$ are coprime. Valuations in $AB$ and $I$ have the same parity at every prime. If $q\equiv5\pmod8$, then $B\equiv3\pmod4$ supplies a prime 3 modulo 4 to odd valuation.

`threeOddFactors_card_geometricBlock` proves $|T(d)|\le |T(G(b,d))|$ for **every** positive $d$ and every $b\equiv1\pmod4$. Sort the distinct prime powers $\ell^k\parallel d$ by decreasing prime. When the previous product is $D$, split off $G(b^D,\ell^k)$ using $G(b,D\ell^k)=G(b,D)G(b^D,\ell^k)$. If a prime $r$ divides both factors, then $b^D\equiv1\pmod r$ and $r\mid\ell^k$, so $r=\ell$. The order of $b$ modulo $\ell$ divides $D$ and $\ell-1$. Every prime of $D$ exceeds $\ell$, forcing order one. Now $\ell\mid G(b,D)$ forces $\ell\mid D$, a contradiction. The factors from successive blocks are therefore coprime. Each $\ell\in T(d)$ contributes a block congruent to 3 modulo 4 and a separate prime in $T(G(b,d))$. [Geometric sum proof](../OddPerfect/GeometricSquareClass.lean)

When $q\equiv a\equiv5\pmod8$, both $A$ and $B$ are 3 modulo 4. The two resulting primes $r,s\in T(I)$ have opposite quadratic characters modulo $q$. The prime from $A$ sees $q^d=1$, which makes $q$ a square modulo $r$ because $d$ is odd. The prime from $B$ sees $q^d=-1$ and is 3 modulo 4, which makes $q$ a nonsquare modulo $s$. Reciprocity transfers the characters to modulus $q$. This excludes $I=t^2$ and $I=\ell t^2$ for every prime $\ell$ in this residue class. Hirakawa proves both exclusions for every Euler exponent greater than one using broader number-theoretic tools. The present argument also specifies primes, multiplicities, and residue classes in the indicated branch. [Hirakawa, Theorem 1.1](https://arxiv.org/pdf/2309.17084v3)

Run `lake build OddPerfect.EulerSquareClass` to replay both modules. The hypotheses do not determine the exponent $a$ or force the index to have a bounded number of prime factors, so compatible square classes remain.

## The cubic half-length

When $3\mid d$ and $T(d)$ is nonempty, the same exclusion holds for every Euler prime $q$. In particular, `euler_five_index_ne_prime_mul_square` proves the entire $a=5$ case, with no congruence condition on $q$ beyond Euler's $q\equiv1\pmod4$. More generally, `euler_index_ne_prime_mul_square_of_count` gives the exclusion whenever the lower bound in the first display is at least two.

To see the cubic argument, write $x=q^{d/3}$ and $C=x^2-x+1$. The integer $C$ lies strictly between $(x-1)^2$ and $x^2$ and satisfies $C\equiv1\pmod4$. A nonsquare with this residue must have an odd-valuation prime other than 3. Any common prime of $C$ and $x+1$ divides 3, so that prime still has odd valuation in $B=((x+1)/2)C$. The nonempty set $T(d)$ forces a separate odd-valuation prime in $A$. The equation $m^2=ABI$ transfers both odd valuations to $I$. The quintic case below gives a second test for the other block.

Hirakawa's published theorem treats all $a>1$. A public Prove2Me entry by WillR lists the full $a=5$ statement for Lean 4.33.1 and displays a statement with a proof placeholder. The present development checks its own proof on the project pin. [Hirakawa, Indagationes Mathematicae 35 (2024), 282–287](https://doi.org/10.1016/j.indag.2023.12.004) · [WillR's theorem entry](https://prove2.me/theorems/2ec27119-2f77-425b-ab15-a95e11c2f9bc)

## The quintic half-length

The entire $a=9$ branch also satisfies $I\ne\ell t^2$ for $\ell=1$ or prime, including $q=17$. More generally, it suffices that $3\mid d$ or $5\mid d$, and that either $d\not\equiv1\pmod8$ or $T(d)$ is nonempty. The new first-block test follows from $G(q,d)\equiv d\pmod4$ and $G(q,4j+1)\equiv4j+1\pmod8$ for $q\equiv1\pmod4$. An odd square is one modulo eight. The declarations are `geometricBlock_not_square_of_length_mod_eight`, `euler_index_ne_prime_mul_square_of_three_or_five_length`, and `euler_nine_index_ne_prime_mul_square`. [Checked quintic results](../OddPerfect/EulerSquareClass.lean)

For the second block with $5\mid d$, take $x=q^{d/5}=4u+1$, where $u>0$. Set $C=x^4-x^3+x^2-x+1$ and $z=16u^2+6u$. Direct expansion gives
$$C-z^2=28u^2+8u+1,\qquad (z+1)^2-C=4u^2+4u.$$
Thus $C$ lies between consecutive squares. Also $C\equiv1\pmod8$, which excludes five times a square. It has an odd-valuation prime other than five. A common prime of $C$ and $x+1$ must divide five, and hence $B=((x+1)/2)C$ retains this odd valuation. The interval argument proves `half_fifth_succ_not_square` for every integer $x>1$ congruent to one modulo four.

For a general odd prime $s$, a prime common to $x+1$ and $\Phi_{2s}(x)$ must divide $s$, by substituting $x=-1$. The quintic proof also used a consecutive-square interval for its particular quartic and that 5 times an odd square is 5 modulo eight. Neither step gives the uniform result by itself. For example, $s=17$, $q=577$ gives $q\equiv1\pmod{16}$ and $q\equiv-1\pmod{17}$. Both a square and 17 times an odd square are one modulo eight. Hirakawa uses the generalized Fermat equation $X^s+Y^s=2Z^2$ for the general nonsquare half-sum. [Hirakawa, Lemma 2.5 and Theorem 2.2](https://arxiv.org/pdf/2309.17084v3)
