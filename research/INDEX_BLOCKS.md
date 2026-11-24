# A finite sieve for Euler indices

`OddPerfect.euler_component_index_ge_343` proves that every odd perfect number in Euler form `N=q^a m²` satisfies `σ(m²)/q^a ≥ 343` and `343q^a < 2m²`. The numerical calculation checks eighteen pairs of prime bases and uses the repository's earlier bound of 165. It does not enumerate `N`, `q`, or the exponent `a`.

Broughan, Delbourgo and Zhou published the bound `σ(m²)/q^a ≥ 315` and the strict ratio bound `m²/q^a > 315/2`. Their Theorem 10 excludes eleven symbolic factorizations. The Lean result here proves a numerical bound using different hypotheses within the proof, including Hirakawa’s square-class restrictions and the local five-prime lower bound. Chen and Chen subsequently excluded thirty symbolic factorizations, which also cover the small values examined here. [Broughan, Delbourgo and Zhou, Theorem 10 and Corollary 11](https://kevinbroughan.nz/papers/chenchenformatted.pdf) · [Chen and Chen, 2014](https://doi.org/10.4064/cm136-1-4) · [Hirakawa, 2024](https://arxiv.org/abs/2309.17084)

## How the index determines candidate sums

Set `i=σ(m²)/q^a`. Write `τ` for the divisor count, `ω` for the number of distinct prime factors, and `Ω` for the count with repetition. Set `B=ω(i)+Ω(i)`. For the checked rows, `4+B<16`, so the weight and primitive-order inequalities give `τ(a+1)≤3+B`. Put `H=⌊(3+B)/2⌋`.

For each chosen `p∣i`, the exponent `e=2v_p(m)` is positive and even. Its sum `σ(p^e)` divides `q^a i`. If that sum is a pure power of `q`, the reciprocal bound gives `p^(e−v_p(i)−1)∣a+1`; since `2∣a+1`, divisor counting gives `2(e−v_p(i))≤τ(a+1)`. Thus the list of candidate lengths can include every `e+1` with `e` even and `max(2,v_p(i))≤e≤v_p(i)+H`.

Otherwise some index prime `r` divides `σ(p^e)`. If `p≡1 (mod r)`, then `r∣e+1` and we use the candidate length `d=r`. For the other residues, the multiplicative order `d` of `p` modulo `r` is an odd divisor of `e+1` exceeding one. Its minimality is a finite residue computation through `r`. In either case `S=1+p+⋯+p^(d−1)` divides `σ(p^e)`, hence divides `q^a i`. `OddPerfect.IndexSieve.exists_block` proves that some listed `S` always satisfies this divisibility.

## How two bases can exclude an index

For each candidate sum `S`, form `R=S/gcd(S,i)`. Cancelling the gcd in `S∣q^a i` shows that `R` is a power of `q`, with exponent zero allowed. Thus `R` is coprime to `i` and congruent to one modulo four. For a prime-times-square index at exponent `a>1`, Hirakawa’s checked result at `q≢1 (mod 16)` instead requires `R≡1 (mod 16)`. Any prime up to thirteen dividing `R` must equal `q`, so it must satisfy the same congruence. Exponent one already gives `i≥22,971`.

If both selected bases leave only residuals exceeding one, their allowed residuals must share a divisor exceeding one since both are powers of `q`. For `i=189`, base three leaves `1093` and base seven leaves `2801`; their gcd is one. If a chosen base has no allowed residual, that single base already excludes the index. For instance `i=165` fails at base five. These checks are the predicate `OddPerfect.IndexSieve.Row.valid`. Its soundness theorem `OddPerfect.IndexSieve.excludes_of_valid_row` takes an odd perfect number, its Euler decomposition and its two index identities as hypotheses.

`OddPerfect/IndexBound343.lean` contains the eighteen rows and the kernel-checked coverage of `[165,343)`. Multiples of 105 are excluded since the odd index divides `m²`, and `105∤N`. The remaining square, 225, is excluded by the nonsquare theorem for `a>1`. None of these arguments places an upper bound on the Euler index.
