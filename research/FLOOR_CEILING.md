# Floor/ceiling register (gate G4)

A lower bound (a floor) closes a branch only when it meets an upper bound (a ceiling) on the **same** parameter. Before raising any floor, find its row here.
- If the ceiling column says **none**, the task is frozen (see [NO_GO.md](NO_GO.md) §3).
- If raising a floor or adding a ceiling would close the gap, say so in the task's closure argument.

| Parameter | Branch | Best audited floor | Best audited ceiling | Can they cross? | What would change this |
| --- | --- | --- | --- | --- | --- |
| u (i_q = p^{2u}) | `IQ_PRIME_POWER_EVEN` | 2u ≥ 1.3·10¹⁶ (`even_prime_power_component_size_gt_ten_pow_353234555955090756`) | **none** | No | A bound incompatible with the existing growth rates |
| p (same branch) | `IQ_PRIME_POWER_EVEN` | p ≥ 10²⁷ | p < 6^u (`even_prime_power_component_base_lt_six_pow`; local constants up to (10¹⁰⁰⁰)⁶), p ≤ 8(u+1)·128^{√(2u)} (`even_index_base_subexponential`) | Only together with u ≤ g(p) | A ceiling on u growing slower than the inverse of the p-ceilings |
| d = (a+1)/2 | `IQ_PRIME_SQUARE` | d ≥ 17 (≥ 241 if 3, 5 ∤ N) | **none** | No | Port of the generalized-Fermat input (NO_GO §2) |
| ω (number of distinct primes) | `A1_SPF` | ω ≥ 443 | **none** (count LP unbounded) | No | Arithmetic cut of the LP ray (`count_lp.py --branch A1_SPF`) |
| Ω (total prime factors) | `A1_SPF` | Ω ≥ 1179 | **none** | No | Same |
| least prime factor | `A1_SPF` | ≥ 53 locally; > 10⁸ published (Fletcher–Nielsen–Ochem) | < 10¹⁰⁰⁰ published (FNO), not formalized | Not by itself: a least-prime window does not bound N | A proof eliminating every allowed least prime or a different uniform obstruction |
| ω | `ROOT` | ω ≥ 6 locally (published: ω ≥ 10) | **none**. Dickson gives N in terms of ω, not the reverse | No | A uniform cap ⇒ finitely many OPNs (open problem) |
| N | `ROOT` | 10³⁰⁰ locally (10¹⁵⁰⁰ published) | 2^{4^ω}-type (Dickson/Nielsen) | No: the ceiling grows with ω | — |
| W (coprime half-successor) | `A1_G1` | W ≥ 5113 on sixth-power-free | **none** | No | A descent on (h, u, W) (IDEAS #4) |

## Count models

The [strategy review](STRATEGY_REVIEW.md#what-survives-the-calculation) gives the baseline, target-reuse comparison, audited modulo-five cut and an exact unbounded family remaining after all three. An improvement can remove one direction while others remain. A single printed ray is only one witness for the relaxation.
