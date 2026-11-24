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
| Same | `e % 6 = 0` or `4` | Neither 7 nor 61 divides the divisor sum of this component. Other components could supply either prime. |

The six possible remainders exhaust the exact exponents, including zero. The conclusion at 3 gives divisibility by 13 but leaves its exponent unknown. The congruence tests in `OddPerfect/Thirteen.lean` are equivalences for the local divisor sum and implications for the full number.

The literature track will cover published necessary conditions, factor-chain methods, computational bounds, formal proofs and spoof constructions. The coordinator records the status of each result and assigns further formalizations from the cited papers.
