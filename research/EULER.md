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
