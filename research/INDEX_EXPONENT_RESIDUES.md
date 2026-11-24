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
