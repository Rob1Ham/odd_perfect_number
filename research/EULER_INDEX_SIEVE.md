# Fixed Euler indices and the exponent-one case

Write `N=q^a m²` in Euler form and `i=σ(m²)/q^a`. The integral identities are `σ(m²)=q^a i` and `σ(q^a)i=2m²`. The bounds below apply to this Euler component. Broughan, Delbourgo and Zhou proved the general inequality `i≥315` and the strict size inequality `m²/q^a>315/2`. [Broughan, Delbourgo and Zhou, *Improving the Chen and Chen result for odd perfect numbers*](https://kevinbroughan.nz/papers/chenchenformatted.pdf)

## Euler exponent one

`OddPerfect.euler_exponent_one_index_ge_22971` in `OddPerfect/ExponentOneIndex.lean` proves `i≥22,971` when `a=1`. Choose a prime-power component of `m²` whose divisor sum contains the Euler prime. Since that single `q` cancels from `σ(m²)=qi`, the product of all other component sums divides `i`. There are at least three other distinct odd primes by the repository's five-prime lower bound on `N`. Their component sums are at least `σ(3²)=13`, `σ(5²)=31`, and `σ(7²)=57` after ordering the selected bases. Their product is `22,971`. Hirakawa uses the same single-source argument with a stronger literature bound on the number of distinct prime factors. [Hirakawa, §2.1](https://arxiv.org/abs/2309.17084)

`OddPerfect.even_prime_power_index_at_euler_exponent_one` in `OddPerfect/IndexPrimeReturn.lean` proves that a prime-power index `i=p^j` with `a=1` has even `j`. The positive component at `p` cannot send any factor to its own base, so its entire divisor sum equals `q`. Thus `q≡1 (mod p)` and `p∤q+1`. Taking valuations in `(q+1)p^j=2m²` gives `j=2v_p(m)`.

More generally, if `σ(p^e)=q^β` for the actual cofactor exponent `e=2v_p(m)`, `OddPerfect.pure_component_index_return_length` gives `p^(e−v_p(i)−1) ∣ a+1`, with subtraction on natural numbers. The return identity supplies `v_p(σ(q^a))=e−v_p(i)`. The reciprocal valuation lemma then yields the length divisibility.

## Residues at individual index primes

`OddPerfect.fermat_supported_index_ne_small_prime_mul_square` excludes the square classes `t²`, `3t²` and `5t²` for Euler indices supported wholly on primes `p` whose predecessor is a power of two. A primitive odd order at each even-exponent cofactor component must occur at the Euler prime `q`. Thus `ω(N)≤a+1` and `a>1`. For an index `lt²`, `l=3` or `5`, the index valuation at `l` is odd. The exact return valuation gives `l∣a+1`. The corresponding checked case of Hirakawa’s theorem then gives the contradiction. [Hirakawa, Theorem 1.1](https://arxiv.org/abs/2309.17084)

For `i=p²r`, where `r` is an arbitrary odd prime distinct from the Fermat prime `p`, `OddPerfect.square_times_prime_index_source_exponent` restricts the exponent at `r` to `2`, `4`, or `p−1`. Its outgoing sum cannot contain `r`, so it divides `p²q^a`. If it contains `p`, the primitive-order result forces component length `p`. Otherwise it is a pure power of `q`. For its exponent `e`, reciprocity gives `r^(e−2)∣a+1`, while the weight bound gives `τ(a+1)≤8`. At `e≥6`, the divisor `2r⁴` already has ten divisors.

`OddPerfect.euler_index_avoids_two_component_witnesses` checks explicit prime divisors of the component sums at exponents two and four for nine values. For example, at `i=99=3²·11`, the possible sums are `σ(11²)=133` and `σ(11⁴)=16,105`. They force the Euler prime to equal `7` or `5`, respectively. Each conflicts with the Hirakawa condition `q≡1 (mod 16)` for this prime-times-square index at `a>1`. Exponent one was already excluded by the `22,971` bound.

`OddPerfect.euler_index_avoids_pure_sources_mod_seven` excludes `63,147,175,245`. Both three and five have order six modulo seven, precluding seven in any even-exponent component sum at those bases. The component at the relevant base `p=3` or `5` is pure and its index multiplicity is one or two. If `p∣a+1`, Hirakawa applies directly at `a>1`. Otherwise the reciprocal bound forces that component to have exponent two. Its outgoing sum forces `q=13` or `31`, contradicting the same index restrictions.

`OddPerfect.sixteen_le_euler_length_divisors_of_fermat_valuations` treats the remaining factorization `135=3³·5`. The index valuation at five is one modulo four, while its cofactor exponent is divisible by four. This gives `5³∣a+1`. At three an odd index valuation forces `3∣a+1`. The divisor `2·5³·3` of the length has sixteen divisors, while the weight bound allows nine. Applying these restrictions together with the square, cube, semiprime, and `105` exclusions yields `i≥165` and `165q^a<2m²` in `OddPerfect.euler_component_index_ge_165`.
