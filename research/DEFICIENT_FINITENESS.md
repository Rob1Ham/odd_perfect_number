# Finiteness for a fixed number of prime divisors

Dutta and Saikia ask whether, for each $k\ge3$, there are finitely many odd deficient-perfect numbers with exactly $k$ distinct prime factors. The reduction below gives an explicit bound for every $k\ge0$ and also bounds the deficient divisor. It uses the positive spoof finiteness theorem published by the BYU Computational Number Theory Group. [Dutta and Saikia, Conjecture 3.2, p. 10](https://arxiv.org/pdf/1906.09947#page=10) · [BYU, Proposition 4.2 and Corollary 4.3](https://arxiv.org/pdf/2006.10697#page=5)

Carlo Francisco Adajar’s July 2016 University of the Philippines Diliman master’s thesis studied odd near-perfect and deficient-perfect numbers with a fixed number of distinct prime divisors. His CV records the thesis and a July 2016 poster with Richell O. Celeste. Gumaru, Casuco and Bernal explicitly attribute both odd finiteness statements to Adajar in their 2018 Theorem 3.4.1. In his March 2019 ZetaValue abstract, Adajar himself states both finiteness theorems for every positive number of distinct prime divisors. The CV and university record document the thesis, the abstract gives the author’s own theorem statement, and the 2018 paper provides the earlier published attribution. [Adajar’s March 2019 abstract](https://drive.google.com/file/d/1R0mKgqzWMYBJi5-EY_Oo52cETyLIO_DQ/view) · [ZetaValue 2019 programme](https://sites.google.com/view/zetawako2019/speakersprogram) · [Adajar’s CV](https://www.pacoadajar.com/Paco_Adajar_CV_2024.pdf) · [University of the Philippines Diliman](https://math.upd.edu.ph/faculty/adajar-carlo-francisco) · [Gumaru, Casuco and Bernal, Theorem 3.4.1](https://www.sciencepg.com/article/10.11648/j.pamj.20180705.11)

Let $d$ be a proper divisor of the odd integer $n$ with $\sigma(n)=2n-d$. Write $n=dt$ and $x=2t-1$. Then $t>1$ is odd, so $x>1$ is odd, and
$$
\sigma(n)(x+1)=2nx.
$$
Adjoin the formal component $(x,1)$ to the $\omega(n)$ true prime-power components of $n$. The product of the geometric sums is $2nx$, and the represented integer is $nx$. The construction uses $\omega(n)+1$ indexed components even when $x$ is composite, shares a prime factor with $n$, or equals a true base. The positive spoof finiteness theorem gives finitely many such tuples at each fixed length. Removing the distinguished linear component recovers $n$, and $2n-\sigma(n)$ recovers $d$. [Conversion to a formal multiplier](../OddPerfect/DeficientPerfect.lean) · [Positive spoof finiteness](../OddPerfect/SpoofFiniteness.lean)

For $\omega(n)\le k$, put $K=k+1$ and $R=\prod_{p\mid n}p$. The product of the indexed bases is $xR$. The product bound for positive odd spoof factorizations therefore gives
$$
4K x^3 R^2 n \;\le\; (4K)^{\,4^{\omega(n)+1}},
\qquad
n\le (4K)^{\,4^K}.
$$
Dittmer’s Lemma 1.6 gives the separate literature bound $nx<2^{4^K}$ under the same representation. His definition permits repeated bases and common factors. The lemma predates the 2019 conjecture. [Dittmer, Definitions 1.3–1.4 and Lemma 1.6, p. 2576](https://www.ams.org/journals/mcom/2014-83-289/S0025-5718-2013-02793-7/S0025-5718-2013-02793-7.pdf#page=2)

Both entries of every pair $(n,d)$ lie below the same computable ceiling. The Lean theorem also covers the positive-divisor convention in Dutta and Saikia’s definition. Allowing $d=n$ adds only $(1,1)$, since then $\sigma(n)=n$. [Effective bound and finite sets](../OddPerfect/DeficientFiniteness.lean)

Yang and Togbé’s 2023 paper proves the exact odd four-prime classification and gives a fixed-rank finiteness conjecture for $k\ge5$ without an oddness qualifier in its final section. The result here covers its odd terms. The explicit transfer above makes Dutta and Saikia’s odd finiteness statement a consequence of the published positive spoof theorem. [Yang and Togbé, Theorem 1 and §6](https://math.colgate.edu/~integers/x5/x5.pdf#page=19)
