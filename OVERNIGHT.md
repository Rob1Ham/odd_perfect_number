# Overnight proof report

The existence of an odd perfect number remains open. The research cutoff was 7:00 a.m. Chicago time on November 24, 2026. Final verification and publication resumed after the cutoff.

**How large would an odd perfect number have to be?** Ochem and Rao’s 2012 Theorem 1 proves that every odd perfect number exceeds 10¹⁵⁰⁰. Pascal Ochem’s project page reports that a subsequent computation raised this to **10²²⁰⁰**, so even the smallest possible example would have at least **2,201 decimal digits**. The strongest unconditional size bound independently checked by Lean in this checkout is **10¹⁶⁰**. [Ochem–Rao, §3, Theorem 1](https://www.lirmm.fr/~ochem/opn/opn.pdf) · [Ochem’s computational update](https://www.lirmm.fr/~ochem/opn/) · [Local Lean size theorem](OddPerfect/SizeBound160.lean)

## Strongest unconditional count theorem at this checkpoint

For **every** odd perfect N, `18 * N.primeFactors.card ≤ 7 * N.primeFactorsList.length + 31`. This is Ochem and Rao's published Theorem 1. Its local proof covers both the presence and absence of 3 and has received independent review against the paper. The exact declaration is `OddPerfect.ochem_rao_prime_factor_count`. [Lean proof](OddPerfect/OchemRao.lean) · [Ochem–Rao, §3](https://www.lirmm.fr/~ochem/opn/opnf.pdf)

Every odd perfect natural number N satisfies **Ω(N) ≥ 37** and **N > 10¹⁶⁰**. The size declaration is `OddPerfect.ten_pow_one_sixty_lt_of_odd_perfect {N : ℕ} (ho : Odd N) (hN : N.Perfect) : 10^160 < N`. Brent and Cohen published the size bound in 1989. The local replay uses 2,728 certified primes and eight prime-index factor chains, followed by the complementary case. Independent review checked both the coverage argument and the compiled declaration. [Public size theorem](OddPerfect/SizeBound160.lean) · [Eight cases and replay](research/BRENT_SIZE.md)

The nine exceptional branches in §4 of Brent, Cohen and te Riele’s 1991 paper now have checked proofs of their conditional size estimates. These use all 20 prime factors of nine specified divisor sums. The eighth case needs the paper’s preceding exclusion of 11. The proof of the full 10³⁰⁰ bound still needs the remaining branches. [Branch statements, certificates and primary sources](research/BRENT_300.md)

The earlier pair of results established Ω(N) ≥ 37 and N > 10⁵⁰. The first theorem counts prime factors with multiplicity and reproduces Iannucci and Sorli’s bound. The second reproduces Hagis’s 1973 bound using a fresh exact-exponent proof. Both declarations quantify over every odd perfect natural number. The count certificate uses 101 reusable subtree proofs covering two roots and an analytic bound for the complement. The size proof handles least primes 3, 5 and 7, followed by a separate bound for the complement. [Count declaration and certificate](research/COUNT_CHAIN.md) · [Size declaration](OddPerfect/SizeBound50.lean) · [Size certificate](research/ABSOLUTE_SIZE.md)

When none of 127, 19, 7, 11, 31, 13, 3, or 5 divides N, the stronger conditional bounds are ω(N) ≥ 101, Ω(N) ≥ 259, and N > 10⁵³⁶. The eight cases in which a listed prime divides N are still required for any improvement to the unconditional size bound. [Complement theorem](OddPerfect/BrentSeeds.lean)

A separate certificate proves **Ω(N) ≥ 2ω(N)+7 for every odd perfect N**. Here Ω includes multiplicity and ω counts distinct primes. The declaration is `OddPerfect.seven_le_prime_factor_count_excess`. [Additive count proof](OddPerfect/CountExcessSeven.lean) · [Derivation and published comparison](research/COUNT_CHAIN.md)

## Structural theorem

The project also proves Dickson's finiteness theorem. For each k, the set of odd perfect natural numbers with at most k distinct prime divisors is finite. The declaration `OddPerfect.dickson_finite` has received independent review. Its proof gives an explicit recursive upper bound depending on k. The bounds vary with k. [Lean proof](OddPerfect/Dickson.lean) · [Mathematical argument](research/DICKSON.md)

A kernel-checked finite sieve forces a prime divisor greater than 257. It yields Sylvester's distinct-prime bounds of five in general and eight when 3 is absent. Excluding all seven odd primes through 19 raises the checked lower bound to 115. [Support certificate](research/SUPPORT.md) · [Cardinality proofs](research/SIEVE.md)

For **every** exact prime-power component qᵃ of an odd perfect N, the integral quotient σ(N/qᵃ)/qᵃ is greater than five. The declaration `OddPerfect.five_lt_divisor_sum_component_index` proves Dris and Luca's Theorem 1.1. An independent worker checked the universal hypotheses, the Euler and nonspecial cases, and each finite endpoint. [Lean proof](OddPerfect/DrisLuca.lean) · [Argument and source](research/RECIPROCAL.md)

If the index of any exact component is p^(2u), put B = 14(u+1)4^(2u−4). Then p ≤ B and N < 2B^(6u). The simultaneous repunit equations in this case require either another Goormaghtigh prime or at least three different odd-base solutions of the Nagell–Ljunggren equation at a common prime. [Effective bound](research/EVEN_INDEX_EFFECTIVE.md) · [Equations and known cases](research/EVEN_INDEX_REPUNITS.md)

A lift modulo p² sharpens the dependence on the exponent: p≤2u or p²≤2((u+1)4^(2u−4)−1)+p. [Radical identity and quadratic bound](research/EVEN_INDEX_RADICAL_LIFTS.md)

The same paper's Theorem 1.2 is checked as `OddPerfect.finite_of_bounded_component_index`. For every real K, only finitely many odd perfect numbers have an exact component of index below K. The project gives an explicit bound, using Dickson finiteness and a count of exceptional components with multiplicity. [Lean proof](OddPerfect/BoundedIndex.lean)

A bound on the number of prime factors of the index suffices for the same finiteness conclusion. For every exact component with index i, ω(N) ≤ 2(ω(i)+Ω(i))+4. A prime-power index pʲ forces j ≥ 66. [Finiteness proof](research/COMPONENT_INDEX_MULTIPLICITY.md) · [Exponent bound](research/PRIME_POWER_EXPONENT.md)

Every component index is composite. Every exact component index also differs from every prime square. The Euler component index has at least three prime factors counted with multiplicity and is at least 343. No exact component has prime-cube index. For any exact component with index pʲ and odd j, the checked lower bound is j ≥ 36207. The residue certificate covers 165 candidate exponent and length pairs. Earlier bounds also give p ≥ 137 and i > 10⁴⁰⁸ for the Euler component. [Residue certificate](research/INDEX_EXPONENT_RESIDUES.md) [Scope and proof](OddPerfect/OddPrimePowerBound.lean) There are additional restrictions on index primes that are 3 modulo 4 and occur to odd valuation. [Index lower bound](OddPerfect/IndexBound343.lean) · [Square-class bounds](research/EULER_SQUARE_CLASS.md)

For an Euler prime q and any positive exponent e, σ(qᵉ) is never square. For an odd perfect number in Euler form with a > 1, the index σ(m²)/qᵃ is also never square. Hirakawa’s stronger prime-times-square claim is checked for the branches q ≢ 1 modulo 16, or any of 3, 5, 7, 11 and 13 dividing (a+1)/2. [Exact results and sources](research/HIRAKAWA.md)

When the Euler exponent is one, N < 2i³ for its index i. In conjunction with N > 10¹⁶⁰ this gives i > 10⁵³. [Size-to-index implication](OddPerfect/ExponentOneSize.lean) For a > 1, a prime-times-square index forces (a+1)/2 to be a prime s with s ≡ 1 modulo 8, q ≡ 1 modulo 16 and (q+1)/2=s·w². The argument uses a checked Pell descent proving that (xⁿ+1)/(x+1) is nonsquare for every x>1 and odd n>1. [Exponent-one proof](OddPerfect/ExponentOneIndex.lean) · [Pell descent and remaining equation](research/ALTERNATING_PELL.md)

For each prime divisor q, `OddPerfect.prime_cube_lt_three_mul` proves q³ < 3N. The separate rank theorem `OddPerfect.prime_rank_bound` gives 2t^(2j) < 3N when j of the prime divisors are at least t > 0. [Sources and proofs](research/PRIME_SIZES.md)

For every odd perfect natural number N, there are distinct prime divisors p and q such that p and its exponent are both 1 modulo 4, while the exponent of q is even and at least four. This proves Steuerwald's 1937 theorem. Its Lean declaration is `OddPerfect.steuerwald`. The proof covers both possibilities for 3 dividing N. [Declaration](OddPerfect/Steuerwald.lean) · [Source and independent case review](research/STEUERWALD.md)

If an odd perfect N has any divisor q with 2 ≤ q < 53, some prime sixth power divides N. This includes Fletcher, Nielsen and Ochem’s theorem excluding multiples of 5 under the sixth-power-free hypothesis. [Least-prime certificates and review](research/SIXTH_POWERS.md)

It follows that Ω(N) ≥ 2ω(N)+1. Here Ω counts prime factors with multiplicity and ω counts distinct primes. The declaration is `OddPerfect.steuerwald_prime_factor_count`. [Prime counts](OddPerfect/Counts.lean)

For an odd deficient-perfect n, the proper divisor d with σ(n)+d=2n yields an odd multiplier x=2n/d−1. The true prime powers of n together with (x,1) give a positive odd spoof list. Its five-entry minimum proves Tang and Feng’s three-prime exclusion. Through 10¹², the only such cofactor is 9,018,009 and d=819. For all sizes, a four-prime cofactor must contain 3 and another prime at most 13. The cofactor of an odd perfect number at Euler exponent one belongs to this deficient-perfect class, with its Euler index as d. [Trillion-bound proof](research/TOTH.md) [Exact equivalence, count and source references](research/DEFICIENT_PERFECT.md)

For any exact component, a prime-power index would yield an odd-prime-base, odd-prime-exponent solution of the Nagell–Ljunggren equation at a prime length greater than two. The unconditional result is an implication from the hypothetical component. The three classical solutions do not have that parity data, and completeness of their classification remains open. [Statements and source](research/NAGELL_LJUNGGREN_INDEX.md)

When 5 and 7 are absent, the complementary divisor n/d of a four-prime odd deficient-perfect number is exactly 3. At most two prime factors one modulo three then forces the exact component 3² and the divisor 13. The residue argument also excludes the entire case containing the omitted prime 3061 in the published §5.3 enumeration. [Derived restrictions and source](research/DEFICIENT_FERMAT.md) · [Quotient proof](OddPerfect/DeficientQuotient.lean)

Every Euler component index has a prime divisor p for which p−1 is not a power of two. Above Euler exponent one such a p occurs with odd valuation in the Euler index, and every other component index also has a prime of this kind. [All-component result](research/FERMAT_INDEX_TARGETS.md) Thus a positive power of a Fermat prime cannot be the index of any exact component. [Fermat-support obstruction](research/FERMAT_INDEX_OBSTRUCTION.md)

The product-gap proof also gives 4kR²N ≤ (4k)^(4^k), where k counts the distinct primes of N and R is their product. Its finite-list version applies to positive odd spoof factorizations even if the bases repeat. [Proof and cutoff-dependent version](research/DICKSON.md)

## Published works and checked examples

The project contains checked proofs of Euler form, Sylvester's exclusion of multiples of 105, Touchard's congruence, Roberts's refinement, the exact-square chain steps at 3 and 13 from Iannucci–Sorli, and Steuerwald's fourth-power result. It also checks five even perfect numbers using mathlib's Euclid–Euler theorem. The corpus records the sources and the outstanding work for stronger published bounds. [Literature corpus](research/CORPUS.md) · [Euler replay](research/EULER.md)

For every perfect N divisible by 13, the 13-component forces 7, 61, or a different prime of at least 23, with a witness in the remaining even exponent classes. The endpoint identity for a single coprime spoof base holds for a genuine perfect number exactly when that base is prime. Lean computes Descartes's actual divisor sum as 426,027,470,778. Its value passes the Euler, Touchard and 105 tests and fails the fourth-power test. [Exponents at 13](OddPerfect/ThirteenRemainder.lean) · [Spoof calculation](OddPerfect/Spoof.lean) · [Candidate sets](OddPerfect/CandidateSets.lean)

Dittmer's Lemma 7.1 and Corollaries 7.2–7.3 and the BYU group's positive finiteness Corollary 4.3 are checked. Every hypothetical odd perfect number has a normalized formally balanced factorization with prime lengths and a single linear entry whose base is a prime. The canonical refinement preserves the actual divisor sum. For any fixed number of entries there are only finitely many positive odd spoof-perfect factorizations, even allowing repeated bases and the base one. [Normalization and inclusion](OddPerfect/QuasiFactors.lean) · [Finiteness](research/DICKSON.md)

The normalized candidate set also requires a genuine prime fourth power. This rules out Descartes’s integer in every allowed normalized representation, including alternatives to its historical factorization. The proof uses the uniquely prescribed linear entry and splits on whether its base also occurs as a square entry. [Checked theorem](OddPerfect/FourthPowerSpoof.lean) · [Case analysis](research/SPOOFS.md)

The related quasiperfect equation σ(N)=2N+1 is equivalent to omitting the proper divisor one. The project proves Cattaneo’s odd-square restriction, deficiency of every proper divisor, and the restriction to residues 1 or 3 modulo 8 for every divisor of σ(N). These conditions apply to a different equation and its own candidate set. [Quasiperfect proofs](OddPerfect/Quasiperfect.lean) · [Hagis–Cohen, properties A–C](https://doi.org/10.1017/S1446788700018401)

Every perfect integer is harmonic in Ore’s sense. For an odd harmonic integer greater than one, every exact component is 1 modulo 4 and an odd prime divides its divisor count. This reproduces Garcia’s two restrictions under the broader harmonic hypothesis. Descartes’s integer fails the harmonic test with 486 actual divisors. [Harmonic inclusion and example](OddPerfect/Harmonic.lean) · [Component and divisor-count proofs](OddPerfect/HarmonicComponents.lean)

For positive odd formally balanced lists with bases exceeding one, the least possible number of entries is exactly five. Descartes attains it. The true prime-power factorization of any odd perfect N has the additional property that every odd prime divisor of a local sum occurs as a base. [Sharp minimum](OddPerfect/SpoofBelowFive.lean) · [Prime closure](OddPerfect/PrimeSlots.lean)

The positive-base square classification at odd lengths has the sole solution (3,5), giving σ(3⁴) = 11². Cohen and Sorli’s three divisor-count estimates for odd integers are checked, including both sharp upper endpoints for exceptions. Their Lemmas 1–2 and Theorems 4–5 are checked across the full odd harmonic class. The strongest estimates give τ(N)⁴ ≤ N and P⁸ < N⁵ for every positive prime power P dividing N. Consequently P ≥ 10¹⁵ implies N > 10²⁴. [Geometric-square proof](research/ODD_GEOMETRIC_SQUARES.md) · [Divisor-count proofs](research/DIVISOR_COUNTS.md)

The odd deficient-perfect cofactors with at most k distinct prime factors form a finite set, including their associated proper divisors. For a cofactor n with multiplier x, radical R and K=k+1, Lean proves 4K x³ R² n ≤ (4K)^(4^(ω(n)+1)). Adajar previously stated the finiteness result. The proof here transfers an explicit bound from positive spoof factorizations. [Exact finite sets, hypotheses, and sources](research/DEFICIENT_FINITENESS.md)

## Open cases at handoff

The eight seeds for the 10³⁰⁰ size bound are 127, 19, 7, 11, 31, 13, 3 and 5. Each seed assumes the earlier primes are absent. All 6,977 prime witnesses have passed Lean checks, including the eleven elliptic-certificate steps. The aggregate 10³⁰⁰ declaration awaits the remaining tree evaluations. Its claim is a published theorem of Brent, Cohen and te Riele. [Case split and prime certificates](research/BRENT_300.md)

The unrestricted four-prime deficient-perfect classification also remains outside the verified corpus. The finite search identified the Descartes cofactor across the candidate branches, with unbounded exponents, but the full Lean tree replay is unfinished. The bounded classification through 10¹² and the unrestricted second-prime bound of 13 are independently checked. The near-perfect fixed-rank proof, larger prime-factor counts, and complete odd-harmonic 10²⁴ exclusion also have outstanding local work. The corpus records gaps by theorem. [Deficient-perfect proof status](research/DEFICIENT_PERFECT.md) · [Literature and outstanding results](research/CORPUS.md)

## Reproduce

On the research branch with Elan installed, run these commands from the repository root.

```sh
lake build
lake lean research/Audit.lean
```

Lean is pinned to v4.36.0 and mathlib to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The final combined build completed 6,924 jobs. The audit checked the axiom dependencies of 31,966 project declarations and printed the types and dependencies of 3,499 named theorems. The only permitted foundational axioms were `propext`, `Classical.choice` and `Quot.sound`. Each proof uses only standard foundations. [Audit](research/Audit.lean)

## Remaining question and next assignment

The general existence question remains open. A nonspecial fourth power, Ω ≥ 37, and N > 10¹⁶⁰ are now necessary. The single best next assignment is to replay `lake build OddPerfect.SizeBound300` and independently audit `OddPerfect.ten_pow_three_hundred_lt_of_odd_perfect`. The prime bank passed. Arithmetic closure of the eight seed cases is pending. The complete 10³⁰⁰ wrapper and certificates are in the repository for that replay. [Branch ledger](research/LEDGER.md) · [Size results and reproduction](research/ABSOLUTE_SIZE.md)
