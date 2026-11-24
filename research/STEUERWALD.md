# Steuerwald’s exponent theorem

Rudolf Steuerwald proved in 1937 that among the non-special primes in Euler's factorization of an odd perfect number, at least one has exponent at least four. Equivalently, if (N=p^a m^2) is in Euler form with (p∤m), then (m) has a squared prime divisor. His proof of the main theorem occupies pp. 70–71. The paper also considers a further exponent pattern on p. 72. [Original paper and bibliographic record](https://archiv.badw.de/en/003396146)

## Shared contradiction hypothesis

Assume (N) is odd and perfect. Write (p) for its Euler prime and (v_r(N)) for `N.factorization r`. Thus (p) and (v_p(N)) are both 1 modulo 4. Suppose that **every prime (r≠p) dividing (N) has (v_r(N)=2)**. The following branches correspond to the two truth values of (3∣N).

### When 3 divides N

The prime 3 differs from (p) by the congruence modulo four. Its exact square forces 13. If 13 is special, its odd exponent forces 7 from (13+1). Otherwise its exact square forces 61. When 61 is also ordinary, its exact square forces 97. These splits produce the following four possibilities. The remaining forced primes in each row come from full square components or from the half-successor of the special prime.

| Special prime | Three distinct ordinary primes forced, each 1 modulo 3 |
| --- | --- |
| 13 | 7, 19, 127 |
| 61 | 13, 31, 331 |
| 97 | 13, 61, 7 |
| Any other prime | 13, 61, 97 |

For example, when (p=61), half its successor is 31 and the divisor sum at 31² is (3·331). The factors of 3 from the three different prime powers multiply in σ(N). Consequently 27 divides (2N) and then (N), contradicting the exact exponent two at 3. Counting the three contributions requires divisibility of their product. Three separate proofs of (3∣N) would yield only one copy of 3.

### When 3 does not divide N

Choose a prime (q) dividing ((p+1)/2). This half-successor is an odd integer greater than one. The even length of the geometric sum for the Euler component guarantees that (p+1) divides σ((p^{v_p(N)})), so (q∣N). The inequality (q≤(p+1)/2<p) makes (q) ordinary. Its exact square contributes its odd divisor sum (q²+q+1) to (N).

Choose any prime (r∣q²+q+1). In the field of order (r), the residue of (q) has multiplicative order three unless (q≡1); the latter case forces (r=3). The 3-free branch therefore gives (r≡1) modulo 3. If (r≠p), its exact square contributes (r²+r+1), a multiple of 3, to (N). Hence (r=p).

Finally, write (q²+q+1=py). Both sides are odd, and (q∣p+1) implies (q∣y+1) by reduction modulo (q). As (y+1) is even and (q) is odd, (2q∣y+1). We also have (2q≤p+1) from the half-successor. Thus (p,y≥q+1) and (py≥(q+1)^2>q²+q+1), a contradiction.

## The supplementary branch

Page 72 treats exact exponent four at 3 with every other nonspecial exponent two. `OddPerfect.steuerwald_four_at_three` in `OddPerfect/SteuerwaldSupplement.lean` specifies the finite set where a second exponent of at least four must occur. Its six primes are 7, 11, 19, 31, 127 and 5419, all congruent to 3 modulo 4. If each of these that divides N occurs exactly twice, then the square components forced successively from 3⁴ include 7², 19², 31², 127² and 5419². Those five distinct sources contribute at least five factors of 3, exceeding the assumed exponent four. This case imposes no conditions on primes outside the six-element set.
