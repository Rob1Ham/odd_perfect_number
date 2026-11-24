# Overnight research ledger

The target is `∃ n : ℕ, Odd n ∧ Nat.Perfect n`. The scheduled cutoff is November 24, 2026 at 7:00 a.m. America/Chicago (13:00 UTC). Until then, the coordinator assigns regular rounds of independent subagent proof work and review, with up to three workers at a time. Integrated milestones receive a statement and axiom check, a commit, and a push to the research branch.

## Round one

| Owner | Deliverable | Coverage |
| --- | --- | --- |
| Euler worker | Replay and audit a published Euler-form proof | Every hypothetical odd perfect number |
| Forcing worker | Factor forcing and the implication from exact exponent two at 3 | Every perfect number satisfying the indicated hypotheses |
| Review worker | Challenge the hypotheses and formalize the link from 13 to 61 | Exact exponent two at 13 initially |
| Coordinator | Pin dependencies, integrate proofs, inspect axioms and choose the next round | The full existence question remains open |

## Exact-power forcing

An exact exponent `e` means `p^e ∣ N` and `¬p^(e+1) ∣ N`. Every positive integer has one exact exponent at each prime. An odd divisor of the divisor sum of a coprime component of a perfect number divides the number itself. The exact exponent makes the prime-power component coprime to its cofactor.

| Parent case | Condition | Conclusion |
| --- | --- | --- |
| Perfect, exact exponent at 3 | `e = 2` | 13 divides the number |
| Perfect, exact exponent at 13 | `e % 6 = 2` | 61 divides the number |
| Same | `e % 6 = 1` or `3` | 7 divides the number |
| Same | `e % 6 = 5` | Both 7 and 61 divide the number |
| Same | `e % 6 = 0` or `4` | For `e > 0`, the component supplies a prime at least 23 different from 61. The bound is attained locally at `e = 10`. Other components could supply 7 or 61. |

The six possible remainders exhaust the exact exponents, including zero. The conclusion at 3 gives divisibility by 13 but leaves its exponent unknown. The congruence tests in `OddPerfect/Thirteen.lean` are equivalences for the local divisor sum and implications for the full number.

The literature track will cover published necessary conditions, factor-chain methods, computational bounds, formal proofs and spoof constructions. The coordinator records the status of each result and assigns further formalizations from the cited papers.

## Verified exclusions and open cases

- Euler form holds for every candidate. The port and the historical replay pass the standard-axiom audit. [Source and replay](EULER.md)
- Sylvester's exclusion eliminates all multiples of 105. If 3, 5 and 7 divide an odd perfect number, 3² and 7² also divide it, so its divisor 2205 is abundant. Every candidate either is a multiple of 105 or survives this exclusion.
- For perfect numbers containing 13, the final line of the residue table supplies a witness even with an unknown exponent. [Proof and counterexamples to weaker hypotheses](REVIEW.md)
- The remaining candidates include the cases with and without 3. The next joint proof targets Steuerwald's exclusion of candidates whose every nonspecial prime has exact exponent two. The spoof worker is studying Descartes's composite-base class in parallel.
