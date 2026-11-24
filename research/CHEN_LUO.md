# Congruences for the square part

Let $N=q^a m^2$ be odd and perfect, with $q$ prime, $q\nmid m$ and $q\equiv a\equiv1\pmod4$. The Euler theorem supplies these hypotheses for every odd perfect number. `OddPerfect.chen_luo_congruences` proves both parts of Chen and Luo's Theorem 3.3. The divisor sum $\sigma(m^2)$ is 1 modulo 4 exactly when $q\equiv a\pmod 8$, and is 3 modulo 4 exactly when $q\equiv a+4\pmod8$. [Chen and Luo, *Odd multiperfect numbers*, Theorem 3.3 and its remark](https://doi.org/10.1017/S0004972712000858) [Lean module](../OddPerfect/ChenLuo.lean)

`OddPerfect.sigma_square_mod_eight_of_euler` gives all four possible residues in one formula,

$$\sigma(m^2)\equiv q\,\frac{q+1}{2}\,\frac{a+1}{2}\pmod 8.$$

Pairing adjacent terms in the Euler component sum gives $\sigma(q^a)/2\equiv ((q+1)/2)((a+1)/2)\pmod8$. The result follows by using $\sigma(q^a)\sigma(m^2)=2q^a m^2$ and the fact that each odd residue is its own inverse modulo 8. The halved component lemma also applies to every odd prime base and every odd exponent. `OddPerfect.chen_luo_odd_factor_count` proves the remark following Theorem 3.3. The difference $q-a$ is 4 modulo 8 exactly when an odd number of primes $p\mid m$ satisfy $p\equiv1\pmod4$ and $v_p(m)$ is odd. In particular, if all primes dividing $m$ are 3 modulo 4, then $q\equiv a\pmod8$.

`OddPerfect.sigma_square_three_or_seven_mod_eight` distinguishes a sign that was reversed in an intermediate publication. The divisor sum is 3 modulo 8 exactly when $a\equiv q+4\pmod{16}$, and 7 modulo 8 exactly when $a\equiv q+12\pmod{16}$. This agrees with Chen and Luo and with the corrected Theorem 2.1 published by Dris and San Diego in 2023. The local proof computes the two equivalences from the formula above. [Dris and San Diego, 2023 corrigendum](https://nntdm.net/papers/nntdm-29/NNTDM-29-1-181-184-corrigendum.pdf)

## A separate index theorem in the literature

Hirakawa's Theorem 1.1(ii) concerns the index $I=\sigma(m^2)/q^a$ under the same Euler hypotheses. If $a>1$, writing $I=t^2$ or $I=\ell t^2$ with $\ell$ prime is impossible. Equivalently, at least two distinct primes have odd valuation in the index. For $a=1$, part (i) asserts $I>1$. The full paper derives part (ii) from Theorems 2.1 and 2.2 on $2\ell t^2=\sigma(q^a)$; the prime-$\ell$ result assumes $a>3$, which follows from $a>1$ and the Euler congruence. The author uses prime ideals in a quadratic order and results about a generalized Fermat equation. The manuscript checked here was arXiv v3 dated 30 November 2023. The journal version appeared in March 2024. The general nonsquare result remains a cited theorem here. The project proves the independent all-component index bound of Dris and Luca. [Hirakawa, v3, Theorem 1.1](https://arxiv.org/pdf/2309.17084v3) [Journal article](https://doi.org/10.1016/j.indag.2023.12.004) [Local index results](RECIPROCAL.md)

Run `lake build OddPerfect.ChenLuo` to replay the modular proofs. The congruences constrain the components of an odd perfect number and leave compatible residue classes.
