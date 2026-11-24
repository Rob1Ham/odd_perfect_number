# Prime-index size certificates

Richard Brent and Graeme Cohen proved in 1989 that no odd perfect number lies below 10¹⁶⁰. They eliminated the prime divisors 127, 19, 7, 11, 31, 13, 3 and 5 in that order. Brent's archive identifies 3,132 leaves in their proof tree and supplies the published microfiche supplement. Brent, Cohen and te Riele extended the bound to 10³⁰⁰ in 1991. Brent also makes a later 12,644-leaf version of that appendix available as TeX. [Brent and Cohen, paper and 1989 supplement](https://maths-people.anu.edu.au/~brent/pub/pub100.html) · [Brent, Cohen and te Riele, paper and 1991 appendix](https://maths-people.anu.edu.au/~brent/pub/pub116.html)

## Branch coverage

If p divides N, its actual exponent v is positive. Choose any prime ℓ dividing v+1 and put e = ℓ−1. Then pᵉ divides N and the geometric sum σ(pᵉ) divides σ(pᵛ). This permits e to be smaller than v. If e is even, σ(pᵉ) is odd and divides 2N, hence divides N. It is coprime to pᵉ and exceeds pᵉ. Consequently p²ᵉ < N. These facts justify checking only the prime lengths satisfying the absolute-size cap. The verifier also checks the length two; this covers odd v and records the Euler prime. [Brent and Cohen, §2](https://maths-people.anu.edu.au/brent/pd/rpb100.pdf)

`IndexComponent.lean` proves that if the selected powers form D, and each selected exponent has compatible length, then D divides N and σ(D) divides σ(N). This product divisibility accounts for common prime factors of several selected divisor sums. Write A = σ(D) and U = lcm(D, A/gcd(A,2)). Then U divides N. At each split the next base must be a certified prime outside D that divides U or equals the starting seed. `IndexState.lean` proves preservation when a new compatible component is added.

An accumulated divisor U exceeding the size limit closes a branch. A prime already forbidden by an earlier seed cannot divide U. A selected divisor sum divisible by four cannot divide 2N. An abundant D cannot divide a perfect N.

For the remaining leaves, suppose pᵏ exactly divides U with k odd. If p is nonspecial, its even valuation in N forces p to divide N/U. The checker verifies both pᵏ ∣ U and pᵏ⁺¹ ∤ U for every supplied pair. If a special prime has been fixed, all supplied bases differ from it. Otherwise the largest supplied prime congruent to one modulo four bounds the one possible missing factor. `IndexRounding.lean` verifies the resulting product inequality using the distinct prime bases in the witness.

## Numerical evidence

The generator independently chooses its branches. It uses GNU `factor` and numeric candidates recovered from a local copy of the authors' 1991 TeX appendix. The candidate list includes probable primes during discovery. The Lean prime bank requires Lucas witnesses checked by mathlib and every arithmetic leaf is recomputed. The generator treats an absent branch as a direct arithmetic leaf, which must itself pass the checker. No numerical claim from either published proof tree serves as an axiom. [1991 proof tree and factorizations](https://maths-people.anu.edu.au/~brent/pub/pub116.html)

The following inventory counts the independently generated tree after replacement of three rounded leaves by subtrees. A split chooses a new prime base. A rounded leaf uses the odd valuations of the forced divisor. A direct leaf checks the accumulated sizes, divisibility by four or a forbidden prime. The maximum depth counts the root. The 1989 authors' 3,132-leaf figure describes their own tree. [Brent's archive](https://maths-people.anu.edu.au/~brent/pub/pub100.html)

| Seed | Earlier primes forbidden, as a product | Splits | Rounded leaves | Direct leaves | Maximum explicit depth |
|---:|---:|---:|---:|---:|---:|
| 127 | 1 | 337 | 297 | 1,118 | 15 |
| 19 | 127 | 210 | 186 | 569 | 11 |
| 7 | 2,413 | 333 | 264 | 1,031 | 13 |
| 11 | 16,891 | 74 | 45 | 163 | 8 |
| 31 | 185,801 | 54 | 34 | 135 | 9 |
| 13 | 5,759,831 | 163 | 82 | 507 | 9 |
| 3 | 74,877,803 | 124 | 69 | 367 | 8 |
| 5 | 224,633,409 | 34 | 18 | 93 | 5 |
| **Total** | | **1,329** | **995** | **3,983** | **15** |

The factor witnesses use 2,728 distinct certified primes. Unfactored cofactors still enter U as part of the full divisor sum. No complete factorization of a component sum is needed. Composite divisors of two sums are counted with their full common multiplicities through A. The checker requires an exact valuation of U only when using it to round a nonspecial exponent upward. Every selected prime length with e = 1 is checked even when it must give a divisor sum divisible by four. For e > 1, the strict inequality p²ᵉ < N supplies a valid cutoff even when p²ᵉ equals the alleged upper bound.

The paper's last branch has distinct-prime count at least 101 and size above 10⁴⁷³. For the 10¹⁶⁰ proof the existing strict bound of 10¹⁸⁰ when 3, 5, 7 and 11 are all absent already suffices. [Brent and Cohen, page 432](https://maths-people.anu.edu.au/brent/pd/rpb100.pdf) · [Four-prime complement](../OddPerfect/SizeSeeds.lean)

Run `lake build OddPerfect.SizeBound160` to replay the supplied prime witnesses and all branches. The source tree is self-contained. For a fresh numerical search with a local copy of the authors' compressed TeX appendix, run `python3 research/index_size.py 160 --table /path/to/rpb116p.tex.gz --reuse-primes OddPerfect/SizeIndex160`. Add `--output OddPerfect/SizeIndex160.lean` to regenerate the Lean modules. GNU coreutils supplies the `factor` program. Timed factor discovery may choose different valid subtrees on different machines. [Host archive for the compressed TeX](https://maths-people.anu.edu.au/~brent/pub/pub116.html)

The targeted production build of `OddPerfect.SizeBound160` completed successfully in 2,703.6 seconds on the project pin. Its 28 generated source files occupy 1,006,538 bytes. The sampled peak allocation for the size-certificate build products was 71,176,192 bytes, and the child-process maximum resident set reported by the operating system was 1,077,952,512 bytes. These measurements include concurrent host load. Two independent runs of `#print axioms OddPerfect.ten_pow_one_sixty_lt_of_odd_perfect` returned exactly `propext`, `Classical.choice` and `Quot.sound`. [Final theorem](../OddPerfect/SizeBound160.lean) · [Generated source](../OddPerfect/SizeIndex160)

## Reciprocal divisibility in the 1991 paper

Lemma 1 of Brent, Cohen and te Riele bounds how much of the source prime can return through a target's successor. The Lean theorem `three_mul_le_of_sigma_dvd_return` allows any odd positive divisor p of σ(qᵏ), with q an odd prime. If qᵐ divides p+1, then 3m ≤ k. For m>0 put x=qᵐ and p+1=xc. The complementary divisor r of qᵏ⁺¹−1 is even and satisfies r=1+xb. Divisibility by x² forces c and b to coincide modulo x. Their opposite parities force at least one to reach x. The identity qᵏ⁺¹=pr+1 then gives qᵏ⁺¹>x³. The published sharp example uses p=5, q=3, k=3 and m=1. [Formal return theorem](../OddPerfect/BrentReturn.lean) · [1991 paper, §2, Lemma 1](https://maths-people.anu.edu.au/~brent/pd/rpb116.pdf)
