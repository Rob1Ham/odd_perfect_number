# Euler form and the upstream replay

`OddPerfect.euler_form` in `OddPerfect/Euler.lean` takes `Odd n` and mathlib's `Nat.Perfect n`. It supplies a prime `q`, an exponent `a`, and a cofactor `m` such that `q % 4 = 1`, `a % 4 = 1`, `¬ q ∣ m`, and `n = q ^ a * m ^ 2`. `OddPerfect.euler_exponents` additionally identifies `a` as `n.factorization q` and proves each other exponent even, including the zero exponents of absent primes. These are local proofs of Euler's classical necessary condition.

The published Lean formalization by `umpolungfish` uses `¬ 2 ∣ n` and a local predicate defined by `sigma 1 n = 2 * n`. This equation alone includes zero. In the local proof the equation follows from `Nat.perfect_iff_sum_divisors_eq_two_mul` and positivity. The upstream README declares the source public domain under the Unlicense and lists Lean `v4.30.0-rc2`, with a relative mathlib dependency. [Upstream source at the tested revision](https://github.com/umpolungfish/odd-perfect-numbers/blob/8819676aa1ce20652f5898a369250a048ff35c76/OddPerfectNumbers.lean#L355) · [README and license](https://github.com/umpolungfish/odd-perfect-numbers/blob/8819676aa1ce20652f5898a369250a048ff35c76/README.md#author-and-license)

On this project's Lean `v4.36.0` and mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, the unchanged 593-line source fails at lines 486 and 502. Two declaration renames suffice to replay the entire upstream file. Both upstream declarations `Nat.ArithmeticFunction.OddPerfect.euler_opn_form` and `Nat.ArithmeticFunction.OddPerfect.touchard_congruence` then print exactly `[propext, Classical.choice, Quot.sound]`. The imported source has SHA-256 `c81ef966c6c0132e6d1d6ccbfd8d31119957a841685b5391a5407ffe5cd99824`.

To reproduce the historical replay inside this checkout after resolving the project dependencies, run the following commands.

```sh
mkdir -p .lake/euler-replay
curl -fsSL 'https://raw.githubusercontent.com/umpolungfish/odd-perfect-numbers/8819676aa1ce20652f5898a369250a048ff35c76/OddPerfectNumbers.lean' -o .lake/euler-replay/OddPerfectNumbers.lean
lake exe cache get Mathlib.Data.Nat.Multiplicity Mathlib.NumberTheory.ArithmeticFunction.Misc Mathlib.Tactic.Common Mathlib.Data.Nat.Factorization.Basic Mathlib.Data.Nat.PrimeFin Mathlib.Algebra.BigOperators.Associated Mathlib.Algebra.Ring.GeomSum
sed -e 's/Nat.factorization_prod_pow_eq_self hn_pos/Nat.prod_factorization_pow_eq_self hn_pos/g' -e 's/dvd_finset_prod_iff/dvd_finsetProd_iff/g' .lake/euler-replay/OddPerfectNumbers.lean > .lake/euler-replay/Replay.lean
cat >> .lake/euler-replay/Replay.lean <<'LEAN'
#print axioms Nat.ArithmeticFunction.OddPerfect.euler_opn_form
#print axioms Nat.ArithmeticFunction.OddPerfect.touchard_congruence
LEAN
lake env lean .lake/euler-replay/Replay.lean
```

The integrated proof uses the factorization of `sigma 1 n`. Since `n` is odd, its value `2 * n` is divisible by two exactly once. An even component exists, and every other component must be odd. The divisor sum of an odd prime power has the parity of the number of terms. For the even component, pairing consecutive powers makes `q + 1` divide its divisor sum. This excludes `q ≡ 3 (mod 4)`. With `q ≡ 1 (mod 4)`, the divisor sum is congruent to `a + 1` modulo four, yielding `a ≡ 1 (mod 4)`. Mathlib's square criterion applied to `ordCompl[q] n` gives the cofactor. The build and independent `#print axioms` commands for both local declarations returned `[propext, Classical.choice, Quot.sound]`.

## Touchard and exact prime-power refinements

`OddPerfect/Touchard.lean` proves Touchard's two congruences and Roberts's 2008 refinement `OddPerfect.roberts_congruence`. Every odd perfect `N` is `1` modulo `12`, `117` modulo `468`, or `81` modulo `324`. The proof splits on the exponent of three. If it is zero, the Euler prime cannot be `2` modulo three, since its successor divides its divisor sum and would force three into `N`. Every positive exponent of three is even by Euler's theorem, as three cannot be the prime congruent to one modulo four. Exponent two forces thirteen. Every larger positive even exponent gives `81 ∣ N`. The first and third residues are disjoint from each other, but the second and third congruences can overlap as arithmetic conditions. The underlying exponent split is disjoint and exhaustive. [T. S. Roberts, *On the form of an odd perfect number*](https://austms.org.au/wp-content/uploads/Gazette/2008/Sep08/Gazette35%284%29Web.pdf)

The local theorem `OddPerfect.exact_even_component_congruence` gives an entire family. For any prime `p` congruent to three modulo four with `N.factorization p = 2*k`, write `M = p^(2*k) * sigma 1 (p^(2*k))`. Then `N = M * (4*t + 1)` for some natural `t`. Thus at exact exponent four of three the necessary residue is `9801` modulo `39204`, since `81 * 121 = 9801`. The divisibility statement uses the entire divisor sum, including all its prime multiplicities. `OddPerfect.half_sigma_euler_dvd_square` gives the parallel restriction at the special prime: in Euler form `N = q^a * m^2`, the integer `sigma 1 (q^a) / 2` divides `m^2`. These are locally checked consequences. No claim of research priority is made for the parameterized consequence.

`lake build OddPerfect.Touchard` succeeded, and separate `#check` and `#print axioms` commands confirmed all seven public declarations in that module as well as the four in `OddPerfect.Euler`. Their axiom lists were each `[propext, Classical.choice, Quot.sound]`.

The Google DeepMind *Formal Conjectures* catalog also links a different Lean implementation of `odd_perfect_number.euler_form`. Its fork uses mathlib's `Nat.Perfect` directly and includes both congruences and the condition `¬ p ∣ m`. The two-renaming replay above concerns the `umpolungfish` source. [Catalog entry](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/PerfectNumbers.lean) · [Proof at the catalog's cited commit](https://github.com/mzhorvath1/formal-conjectures/blob/7deed78f7babe2ae9ea13969a8dfa26854982407/FormalConjectures/Wikipedia/PerfectNumbers.lean#L110)
