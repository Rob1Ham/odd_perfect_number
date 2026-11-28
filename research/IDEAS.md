# Current proof ideas

| # | Idea | Branch | Status | Deliverable |
| --- | --- | --- | --- | --- |
| 1 | Locate existing target-reuse work and check its count families | A1_SPF | DONE | Abstract families checked. The [review](STRATEGY_REVIEW.md) records the standalone replay limit. |
| 2 | Iterate suppliers monotonically from the largest prime | A1_SPF | KILLED | A divisor of a quartic block need not be at most the fourth power of its base. Later suppliers need not decrease. |
| 3 | Use a fixed-rank Dickson gap for the even-index system | IQ_PRIME_POWER_EVEN | PAUSED | Requires control of support rank and an incompatible growth rate. |
| 4 | Descend on the coprime quotient equations | A1_G1 | PAUSED | Requires a map preserving the admissible system; a strict inequality between entries of one triple does not furnish it. |
| 5 | Spoof testing | All | DONE | Use branch-matched controls as part of each review. |
| 6 | Count square-source outputs by residue and target valuations | A1_SPF | DONE | Public theorem and high-square-count exclusion. |
| 7 | Charge high-exponent capacity against its outgoing factors | ROOT | PROPOSED | Find a compulsory payment or identify the obstruction in an uncovered case. |
| 8 | Separate incoming partitions by residue | A1_SPF | PROPOSED | Exclude the lower-square-count family or produce a compatible refined model. |

## 6. Modulo-five capacity

**Theorem.** With $S$ square sources, $U$ square sources outside $1\bmod5$, and $Q$ quartic sources congruent to $1\bmod3$, the candidate satisfies $10S\le19Q+5U+10$. The [complete argument](STRATEGY_REVIEW.md#a-direction-that-arithmetic-distinguishes) includes the exceptional Euler target. The [formal proof](../OddPerfect/SquareOutputCapacity.lean) instantiates the inequality using only perfection, sixth-power-freeness and the Euler-prime facts available for every candidate.

**Closure argument.** The modulo-five target budget excludes the square-ramified count family at every positive scale and leaves a smaller named residual.

| Check | Evidence |
| --- | --- |
| Spoofs and local controls | Primality supplies the order-three target restriction, and actual perfection supplies exact incoming valuations. The Descartes composite-base factorization has no such budget. The 4153 and 22639 chains sharing 73 are allowed. |
| Count model | Including the row with the target-reuse inequalities excludes a whole unbounded direction. The lower-square-count family remains. Both substitutions hold algebraically in the parameter. |
| Local solvability | A single congruence cannot force the contradiction. The residue of the entire output controls its multiplicity only when all its targets have the specified residue. Exceptional targets are charged explicitly. |
| Floor and ceiling | The two sides concern the same source counts. On the excluded family the coefficient gap is $2m$. The rank objective remains unbounded. |
| Independent mathematical review | The arithmetic, capacity and elimination steps survived review. Literature priority is unassessed. |

**Branch impact.** When U = 0 and S ≥ 2Q the theorem forces Q ≤ 10. The public bound Q ≥ 80 excludes that entire slice. The lower-square-count family remains a regression case.

## 7. Arbitrary exponents

First derive the weighted analogue on paper, keeping every $v_t(N)$ variable. Test whether a single high-exponent target can absorb the entire deficit. The [unrestricted experiment](STRATEGY_REVIEW.md#where-to-spend-the-next-round) states the inequality, the precise missing estimate and the vacuous case. Advance to formalization only after an argument restricts an uncovered case.

## 8. Residues on the surviving family

Start with the explicit tuple of rank 6m+2 in the [comparison](STRATEGY_REVIEW.md#what-survives-the-calculation). Record which residues can occur together in a single output and which supplier supplies the repeated target in a 2+1+1 incoming partition. Test those constraints jointly. A contradiction must persist for arbitrarily large m; otherwise preserve the surviving assignment and identify which prime or valuation information is missing.
