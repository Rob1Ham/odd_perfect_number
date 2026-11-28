# Roadmap

The target is `¬ OddPerfect.existsOddPerfect`. The public proof library leaves both Euler-exponent branches open. The [strategy review](STRATEGY_REVIEW.md) traces the available arguments to their hypotheses and gives the calculations behind this allocation. Branch status is recorded in the [case tree](BRANCH_MAP.md).

## 1. Sixth-power-free candidates

Use the existing target-reuse proof and its surviving count families as the starting point. The next arithmetic test couples the residue of an entire square-source output modulo five to the incoming valuations available on the target primes. The audited inequality eliminates the square-ramified family and every candidate with U = 0 and S ≥ 2Q. The combined model still admits a family of rank $6m+2$ for every $m\ge100$.

1. Start from the [actual-candidate theorem](../OddPerfect/SquareOutputCapacity.lean). The comparison command and exact families are in the [review](STRATEGY_REVIEW.md#what-survives-the-calculation).
2. On the surviving family, refine the incoming partitions by residue and by which primes are themselves prime outputs. Seek a contradiction at arbitrary scale, or exhibit a consistent enlarged count assignment.
3. Continue only if the new information removes a specified family, forces a smaller arithmetic subcase or exposes a reusable obstruction. A different simplex pivot or a different choice of witness with the same feasible set has no mathematical significance.

Full success on this branch forces some prime sixth power to divide every odd perfect number. The unrestricted cases below would remain.

## 2. Candidates with unbounded exponents

Use a second investigation for the root itself. The weighted form of the preceding argument, derived in the [review](STRATEGY_REVIEW.md#where-to-spend-the-next-round), isolates two quantities that may grow together: the incoming valuations and the excess capacity of large-exponent targets. Test whether the outgoing divisor-sum factors of those same targets can compensate for that growth. Include an ordinary component whose exponent plus one is prime, and the case of no selected square sources. Record exactly where the argument still allows arbitrary capacities. A successful result would apply on `A1_P6` or `IQ_MULTI` with explicit hypotheses.

## 3. Separate deliverables and paused routes

| Work | Reopening or completion condition |
| --- | --- |
| Coprime half-successor descent | Exhibit a map to another admissible triple and prove a strict decrease in a well-founded measure. Check primality of the reconstructed Euler multiplier. |
| Even prime-power index | Derive bounds with incompatible growth rates, or a genuine descent. A bound depending on an uncontrolled support size or an unspecified inverse does not suffice. |
| Exceptional Fermat input | Port a proof of the precise positive-integer classification used by the local interface. This would finish published mathematics on one index class. [Hirakawa](https://arxiv.org/pdf/2309.17084) · [Local reduction](../OddPerfect/ExceptionalFermatReduction.lean) |
| Least-prime, size and count replays | Treat each as a certification project with its own end theorem. Schedule a replay as resolution work when an active argument needs its numerical threshold. |
| Breakouts, submissions and Mathlib contributions | Judge on proof portability, exact external statements and literature provenance. [Portfolio](PUBLICATION_PORTFOLIO.md) |

The archived [wave plan](archive/ROADMAP_2026-11-27.md) and [ledger](LEDGER.md) document earlier work.
