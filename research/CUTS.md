# Divisor-sum edges across a partition

Take the actual prime divisors of a perfect number N as vertices. There is a directed edge from u to v if v divides σ(u^e), where e is the exact exponent of u. The local theorem `OddPerfect.sigmaEdge_reachable` proves that every vertex reaches every other one along these edges. Its hypothesis is mathlib's `Nat.Perfect`, so the theorem also applies to even perfect numbers. Strong connectivity for odd perfect candidates has also been described in a recent preprint. [Zhu and Li, 2026, preprint](https://zenodo.org/records/22005604)

## Proof

Partition the prime support into two nonempty sets and multiply the full prime powers on the two sides to obtain coprime a and b with ab=N. Since a,b>1, both σ(a)>a and σ(b)>b. The identity σ(a)σ(b)=2ab gives σ(a)<2a. If σ(a) were coprime to b, its divisibility into 2ab would give σ(a)∣2a. Every proper divisor of 2a is at most a, contrary to the two strict inequalities. Thus a prime r divides both σ(a) and b. Multiplicativity on the a-side identifies a source prime u with r∣σ(u^e). The prime r is on the b-side by unique factorization.

This argument applies to every nonempty proper subset of the support. The vertices reachable from a specified u form a nonempty subset. If some vertex v were outside it, the theorem would give an outgoing edge to a reachable vertex outside the subset, a contradiction. [Lean proof](../OddPerfect/Cuts.lean)

## What this says about a contradiction

A nonempty proper set that is closed under every forced edge is impossible inside the support. The full finite support may itself be closed. Even the cycle on the actual prime components of the perfect number 6 exhibits closure and strong connectivity. At 2 the exact exponent is one and σ(2)=3. At 3 the exact exponent is one and σ(3)=4, which is divisible by 2.

To turn this into a nonexistence argument, one would need a theorem that every odd candidate has a *proper*, nonempty closed subset, or that a prime forced out of the full support always exists. The per-source distinct-order theorem does not do this by itself. Different sources can force the same destination. The finite-support sieve tests this question for bounded sets of primes.
