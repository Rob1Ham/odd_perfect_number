# Tóth's cofactor bound and the bounded deficient-perfect set

For an odd positive cofactor n and an odd multiplier x > 1, consider the equation σ(n)(x+1) = 2nx using the actual divisor sum of n. Among all pairs with n ≤ 10¹², the entire solution set is the singleton {(9,018,009, 22,021)}. Consequently every single coprime composite pseudoprime spoof distinct from Descartes's example has cofactor exceeding 10¹². This recovers Tóth's Theorem 1. The theorem concerns the size of the cofactor. The multiplier can be arbitrarily large at the start of the proof. [Tóth, 2021, Theorem 1](https://cmst.eu/wp-content/uploads/files/10.12921_cmst.2021.0000005_TOTH.pdf) · [Exact statements and set equality](../OddPerfect/TothTrillion.lean)

Projecting through the odd-multiplier equivalence gives a second classification. For an odd n ≤ 10¹² and a proper divisor d with σ(n)+d=2n, necessarily n=9,018,009 and d=819. These values satisfy the equation. Tóth's original set also permits even multipliers, and x=1 gives the trivial cofactor n=1. The singleton theorem explicitly assumes x is odd and exceeds one. [Deficiency and endpoint](../OddPerfect/DeficientPerfect.lean)

## Coverage

The balance equation forces n=m² and x≡1 modulo 4. Thus the search starts with odd roots m≤10⁶. At a prefix D of the root, the proof records the exact value S=σ(D²) and a lower bound on the remaining prime factors. Splitting at a prime covers its absence and every exponent that keeps m within the bound. For a final unknown prime r, the divisor sum of r² is r²+r+1. The interval tests evaluate all remaining integer values of r, which includes every possible prime. Other branches close by size or by bounding the abundancy of the remaining factors. The generator produces 754 splits. Its 535 final-prime intervals test 148,722 integer values in total, counted separately across intervals. Lean also verifies Descartes's pair directly. [Square and balance lemmas](../OddPerfect/TothCandidates.lean) · [Prime splitting](../OddPerfect/TothSplit.lean) · [Abundancy estimates](../OddPerfect/TothAbundancy.lean) · [Interval coverage](../OddPerfect/TothIntervals.lean)

## Reproduction

The Python program proposes the proof tree. All interval endpoints, primality facts, exact divisor-sum updates, and inequalities are verified by Lean. [Generator](toth.py)

```sh
python3 research/toth.py --root-limit 1000000 --chunk 20 --output OddPerfect/TothTrillion
lake build OddPerfect.TothTrillion
lake build
lake lean research/Audit.lean
```
