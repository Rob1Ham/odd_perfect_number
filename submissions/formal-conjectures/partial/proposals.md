# Proposed issues for restricted results

The strongest first discussions are **Ore’s conjecture with at most two distinct prime factors** and **bounds for odd almost-perfect numbers**. The Ore result proves the exact conclusion of the catalog entry on a specified class. The almost-perfect result gives two independently checkable restrictions on a hypothetical witness. Each issue below asks whether maintainers want a separate declaration with an external proof reference. The unrestricted entries retain their existing status.

The signatures use the local names. Except for the Descartes result, their namespace is `OddPerfect.CatalogCases`, with `ArithmeticFunction` open. In these statements `sigma 1 n` sums the divisors of $n$, and `sigma 0 n` counts them.

## Ore’s conjecture for odd numbers with at most two distinct prime factors

Would the A001599 entry accept the following case of its odd harmonic number conjecture? Under the same positivity and divisibility hypotheses, the conclusion $n=1$ follows when $n$ has at most two distinct prime factors. There is also a companion lemma excluding every positive power of a prime, including powers of 2. [Catalog statement](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/OEIS/1599.lean#L89-L90)

```lean
theorem ore_odd_of_at_most_two_primes {n : ℕ} (hn : 0 < n) (ho : Odd n)
    (hh : sigma 1 n ∣ n * sigma 0 n) (hfew : n.primeFactors.card ≤ 2) : n = 1

theorem ore_no_prime_power {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ¬ sigma 1 (p ^ e) ∣ (p ^ e) * sigma 0 (p ^ e)
```

[Proof of the odd case](Consequences.lean#L83) · [Two-prime exclusion](../../../OddPerfect/HarmonicFinite.lean#L1362) · [Prime-power proof](Consequences.lean#L76)

## Size and number of prime divisors of an odd almost-perfect number

Would a necessary-condition theorem fit beside the existence question? Any odd almost-perfect integer $n>1$ must exceed $10^{12}$ and have at least five distinct prime divisors. The proof applies classifications of odd deficient-perfect numbers in two cases, one bounded by size and one by prime count. The parent question also allows even non-powers of two. [Catalog statement](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/AlmostPerfectNumbers.lean#L48-L50)

```lean
theorem odd_almostPerfect_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : 1 + sigma 1 n = 2 * n) : 10 ^ 12 < n ∧ 5 ≤ n.primeFactors.card
```

[Proof](Consequences.lean#L23) · [Size classification](../../../OddPerfect/TothTrillion.lean#L46) · [Four-prime classification](../../../OddPerfect/DeficientFourClassification.lean#L17)

## A new OEIS entry for the abundancy ratio 5/3

Would maintainers accept a new A388012 entry for its open equality question, together with a separate proved condition on equality? The sequence comprises positive integers with $σ(n)/n\ge 5/3$. Its comments conjecture that equality never occurs. The proposed theorem shows that any equality witness has two distinct prime factors congruent to 1 modulo 5. A new entry is needed at the pinned revision. [OEIS sequence and comments](https://oeis.org/A388012) · [Upstream OEIS directory](https://github.com/google-deepmind/formal-conjectures/tree/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/OEIS)

```lean
theorem five_thirds_residue_primes {n : ℕ} (hn : 0 < n) (h : 3 * sigma 1 n = 5 * n) :
    ∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, r ≠ s ∧ r % 5 = 1 ∧ s % 5 = 1
```

[Proof](Consequences.lean#L38) · [General residue theorem](../../../OddPerfect/DeficientThirdSource.lean#L69)

## The Ochem–Rao bounds when an odd perfect number is sixth-power-free

Would a formal proof of the sixth-power-free case fit beside the published Ochem–Rao theorem? If no sixth power of a prime divides an odd perfect number, the project derives both catalog bounds, including the count of prime factors **with multiplicity**. A formal proof of the unrestricted bounds must also cover numbers divisible by a prime sixth power. [Catalog statement](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/PerfectNumbers.lean#L83-L96)

```lean
theorem ochem_rao_of_sixth_power_free {n : ℕ} (ho : Odd n) (hp : n.Perfect)
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ n) :
    n > 10 ^ 1500 ∧ n.primeFactorsList.length ≥ 101
```

[Proof](Consequences.lean#L59) · [Underlying bounds](../../../OddPerfect/SixthPowerBounds.lean#L123)

## Prime divisors of a hypothetical quasiperfect number

Would the quasiperfect numbers entry benefit from a separate theorem recording what follows from its defining equation? Every witness is an odd square with at least four distinct prime factors. A witness coprime to 3 has at least seven. The existence question remains open. [Catalog statement](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/QuasiperfectNumbers.lean#L46-L48)

```lean
theorem quasiperfect_witness {n : ℕ} (h : sigma 1 n = 2 * n + 1) :
    Odd n ∧ IsSquare n ∧ 4 ≤ n.primeFactors.card ∧ (¬ 3 ∣ n → 7 ≤ n.primeFactors.card)
```

[Proof](Consequences.lean#L68) · [Four-prime bound](../../../OddPerfect/QuasiperfectSupport.lean#L157) · [Seven-prime bound](../../../OddPerfect/QuasiperfectSupport.lean#L251)

## Necessary conditions for a second Descartes number

Would maintainers want a single statement collecting restrictions on any second Descartes number? For a factorization $mw$ distinct from the known number, $m$ exceeds $10^{12}$ and has at least five distinct prime factors. Furthermore, a prime cube divides the **product** $mw$ or the product has at least seven distinct prime factors. This proposal combines consequences of results in the two [separate proof-reference packets](../README.md). [Catalog uniqueness question](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/DescartesNumber.lean#L166-L170)

The declaration is in `DescartesSubmission`, with `OddPerfect` open.

```lean
theorem second_descartes_restrictions {m w : ℕ} (h : SingleCompositeSpoof m w)
    (hne : m * w ≠ 198585576189) :
    10 ^ 12 < m ∧ 5 ≤ m.primeFactors.card ∧
      ((∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ m * w) ∨ 7 ≤ (m * w).primeFactors.card)
```

[Proof](DescartesConsequences.lean#L16) · [Four-prime factorization](../../../OddPerfect/DeficientFourClassification.lean#L55) · [Cube-free uniqueness](../cube-free/CubeFree.lean#L20)
