# Residue tests for odd prime-power component indices

Let an odd perfect number have Euler form $N=q^a m^2$, and write $I=\sigma(m^2)/q^a$. Suppose $I=p^j$ with $p$ prime and $j$ odd. Put $d=(a+1)/2$, $n=j+2$, and $G(b,n)=1+b+\cdots+b^{n-1}$. The exact return equation and the Euler square restrictions give integers $w,y$ satisfying

$$
 q+1=2dw^2,\qquad q^d+1=2y^2,\qquad G(p,n)=q^d .
$$

The index constraints also give $16\mid j+1$, $n$ prime, $d$ prime, $d\equiv1\bmod8$, and $d\mid n+1$. These deductions apply without an upper bound on $p$, $q$, $a$, or $N$. [Exact divisor-sum return](../OddPerfect/OddPrimePowerReturn.lean) · [Euler half-length](../OddPerfect/ExceptionalLength.lean) · [Three equations](../OddPerfect/OddIndexLocal.lean)

## Why exponent 191 fails

The preliminary restrictions at $j=191$ give $n=193$ and $d=97$. Over $\mathbb F_5$, both exponents are one modulo four, so $q^{97}=q$. The first two equations give $y^2=97w^2=2w^2$ in this field. Since 2 is a quadratic nonresidue, $w=0$, hence $q=-1$. For $p\ne1$ in the field, $G(p,193)=(p^{193}-1)/(p-1)=1$, including $p=0$. At $p=1$ the sum is $193=3$ in the field. Neither value equals $-1$. This excludes every prime base of the putative index at this exponent.

## Finite coverage

For each candidate $(d,n)$ in the stated exponent interval, a prime modulus $r$ and two bit masks appear in the Lean certificate. The first mask must contain all $G(b,n)\bmod r$, and the second must contain all $2b^2-1\bmod r$, for $0\le b<r$. For every residue $w$, the checker verifies that

$$
 (2dw^2-1)^d\bmod r
$$

misses their intersection. Consequently the three equations cannot hold together at that pair. Masks may include extra residues. The soundness theorem uses the verified containments and disjointness. The geometric evaluator handles the residue $b=1$ separately and uses Fermat’s little theorem to invert $b-1$ at every other residue. Modular exponentiation avoids constructing full geometric sums. [Field arithmetic and checker](../OddPerfect/OddIndexLocal.lean)

For $j<36207$, write $j=16k+15$. Lean tests each $0\le k<2262$. Whenever $16k+17$ is prime, its successor’s prime-factor list contains every possible $d$. Each entry congruent to one modulo eight must occur in the certificate table. The 165 exact $(d,n)$ pairs use 3,917 field residues altogether, counting the residues separately in each pair’s chosen field. [Length coverage and obstructions](../OddPerfect/OddIndexExponentScreen.lean)

Thus $j\ge36207$ for every odd prime-power index exponent. The exclusion holds at every exact component. The two index equations identify an odd index with the Euler component, and the even prime base is handled separately. The first unrejected pair in the three-equation discovery search is $(j,d)=(36207,17)$. Surviving modular checks supply necessary conditions only. The Python verifier independently enumerates the candidate half-lengths and checks the two masks using modular inverses. [Lean exponent exclusion](../OddPerfect/OddIndexExponentScreen.lean) · [Independent certificate verifier](index_residue_check.py)

Hirakawa’s published Theorem 1.1(2) excludes every prime-times-square Euler index at $a>1$. The argument above proves finite-exponent conclusions directly from arithmetic of the Euler component. The full generalized Fermat result used in the published argument is external to this replay. [Hirakawa, Theorem 1.1 and Lemma 2.5](https://arxiv.org/pdf/2309.17084v3) · [Ivorra, Theorem 2](https://www.impan.pl/shop/en/publication/transaction/download/product/82637)

## Congruences modulo squares

The return relation also gives $d^2\mid p+n$. To see the extra power of $d$, write $p=1+u$ modulo $d^2$. The identity $u^2=0$ gives $2G(p,n)=2n+n(n-1)u$ in that ring. Since $d\mid n+1$ and $d\mid q+1$, the odd power $q^d$ equals $-1$ modulo $d^2$. Substituting $G(p,n)=q^d$ and cancelling two, which is invertible modulo $d^2$, gives the congruence. [Square modulus argument](../OddPerfect/OddIndexSquareLift.lean)

Let $r$ be an odd prime with $r-1\mid d-1$, $r-1\mid n-1$, and $d$ a quadratic nonresidue modulo $r$. The two square equations force $r\mid w$, giving $r^2\mid q+1$. The geometric return then forces $p=1$ and $n=-1$ modulo $r$. The same argument modulo $r^2$ gives $r^2\mid p+n$. The squares for all such $r$ and for $d$ can be multiplied after counting each distinct prime once. At $d=17$ the primes 3 and 5 qualify because $16\mid n-1$, yielding $65025\mid p+n$. [Simultaneous divisibility theorem](../OddPerfect/OddIndexFeedback.lean)

## Squarefree part of the first block

For every prime-times-square Euler index $I=pt^2$ with $a>1$, the positive half-length block satisfies $G(q,d)=pv^2$. The two coprime halves of $\sigma(q^a)/2$ are $G(q,d)$ and $(q^d+1)/2$. The latter is a square. The perfect-number identity and the odd valuation of $p$ in the index therefore leave exactly $p$ in the squarefree part of $G(q,d)$. Reduction at $q=-1$ and $q=1$ gives $pv^2\equiv1\pmod{q+1}$ and $pv^2\equiv d\pmod{q-1}$ for that same $v$. For $I=p^j$ this fourth equation holds simultaneously with the first three above. [Integral equations and neighboring congruences](../OddPerfect/PositiveHalfReturn.lean)

Bennett and Skinner's Proposition 8.1 directly classifies $2y^2-1=q^d$ for positive integers with $d\ge3$. Its only solution with $q>1$ is $(y,q,d)=(78,23,3)$. The half-length in our unresolved prime-times-square branch is a prime congruent to one modulo eight. Substitution into that published proposition therefore closes the branch on paper. The independent finite-field certificates use the displayed integral equations and do not assume Proposition 8.1 in Lean. [Bennett and Skinner, *Ternary Diophantine equations via Galois representations and modular forms*, Proposition 8.1, pp. 46–47](https://doi.org/10.4153/CJM-2004-002-2)
