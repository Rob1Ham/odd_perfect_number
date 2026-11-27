# Cube-free uniqueness with fewer than seven distinct prime factors

Private contributor notes. Write the public issue in your own words, and explain the role of AI in the PR description. [DeepMind contribution guidelines](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md) · [Mathlib AI conventions](https://leanprover-community.github.io/contribute/index.html#use-of-ai)

**Proposed issue title** Link a Lean formalization of the Banks–Güloğlu–Nevans–Saidak cube-free uniqueness theorem

The upstream declaration states that a cube-free Descartes integer with fewer than seven distinct prime divisors is 198585576189. Banks, Güloğlu, Nevans, and Saidak proved the mathematical result in 2008. The external proof uses an odd deficient-perfect cofactor classification and short factor chains.

| Source | Role |
| --- | --- |
| Structure.lean | The four-prime cofactor classification forces the exceptional component to be a prime square, and every ordinary exponent to be two. Divisibility of local divisor sums propagates primes into the support. |
| ThreeDivides.lean | The limiting abundancy product of six primes starting at 5 is below 2, forcing 3 into the support. |
| Valuations.lean | Three distinct ordinary primes congruent to 1 modulo 3 force 27 to divide $2n$. |
| FactorChains.lean | The exceptional primes 3, 13, 61, 97 and the complementary case each force such a triple. |
| CubeFree.lean | Composes the lemmas and exposes the statement with DeepMind’s definitions unfolded. |

**Proposed PR title** Add a formal proof reference for cube-free Descartes uniqueness below seven primes

The upstream edit should add the published Palomar entry to the existing research-solved declaration. Publish an immutable external revision containing the five files and the complete import closure of `OddPerfect.DeficientFourClassification`, including its staged certificate files. Verify from a clean checkout of that revision. A link to the older Tóth commit cannot identify this new proof. See the registry material in the parent folder. Once an entry is issued, `proof-reference.py` generates the upstream edit.

[Upstream statement and original reference](https://github.com/google-deepmind/formal-conjectures/blob/ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8/FormalConjectures/Wikipedia/DescartesNumber.lean#L157-L164)
