# Odd Perfect Number — Continuous Progress & Reevaluation Dashboard

**Snapshot UTC**: `2026-11-27T14:09:23Z` · **Hygiene (`sorry`/`axiom`)**: `0 violations`

## 1. Macro Health & Integration Metrics

Module totals come from the import graph. See the [research ledger](LEDGER.md) for the last completed Lean build and axiom audit.

| Metric | Current (Δ vs prior) | Interpretation |
| --- | --- | --- |
| Modules reachable from `OddPerfect.lean` | `845` (+12) | Covered by the public audit when it passes |
| Unintegrated modules in `OddPerfect/` | `516` (-4) | Staged / WIP debt awaiting harvest or pruning |
| Structural modules vs Certificate chunks | `395` / `966` (`29.0%` structural) | Guards against brute-force tree bloat |
| Structural declarations (`OddPerfect/`) | `4,206` (+85) | Reusable lemmas & public theorems |
| Distinct Mathlib modules imported (structural) | `115` (+23) | Breadth of Mathlib theorem reuse |

## 2. Candidate-Set Contraction Frontier (`∃ N, Odd N ∧ Nat.Perfect N`)

| Axis | Imported by `OddPerfect.lean` | Staged in Workspace | Published Frontier |
| --- | --- | --- | --- |
| **Absolute Size Bound (N > 10^k)** | N > 10^300 (> 10^740 on all I=ℓt² a>1; > 10^17240 if i=p^j; > 10^3136 if 6th-power-free) (`IMPORTED`) | N > 10^1500 branch-tree replay (`OPEN`) | N > 10^1500 (Ochem–Rao 2012); 10^2200 reported |
| **Distinct Prime Divisors ω(N)** | ω(N) ≥ 6 (≥ 8 if 3 ∤ N or i=p^(2u); ≥ 443 if 6th-power-free) (`IMPORTED`) | ω(N) ≥ 7 / Nielsen ω(N) ≥ 10 (`OPEN`) | ω(N) ≥ 10 (Nielsen 2015) |
| **Total Prime Divisors Ω(N)** | Ω(N) ≥ 37. Every candidate has an index with Ω(i_p)+5 ≤ Ω(N). Sixth-power-free gives Ω(N) ≥ 1179. (`IMPORTED`) | Ω(N) ≥ 47 (`STAGED (unbuilt)`) | Ω(N) ≥ 101 (Ochem–Rao 2012) |
| **Linear / Additive Factor Excess** | 21ω ≤ 8Ω+39. At 3∤N, 8ω+4L₂ ≤ 3Ω+7. In the sixth-power-free case more than one sixth of the support is an exact-square prime ≡1 mod 5. (`IMPORTED`) | Extend Clayton–Hansen and Zelinsky slopes across uncovered residue classes (`OPEN`) | Ω ≥ 2ω + 51 (Ochem–Rao). Clayton–Hansen (2023) give 99ω ≤ 37Ω+187 and, for 3∤N, 51ω ≤ 19Ω+46. |
| **Euler Component Index i_q = σ(m²)/qᵃ** | i_q ≥ 2379. At a>1, I=ℓt² forces N > 10^740 and excludes q ≡ 2,4 mod 7. (`IMPORTED`) | Full closure of I = ℓ t² (Hirakawa 2024) (`OPEN`) | Dris / Broughan–Delbourgo–Zhou / Hirakawa (2024) |
| **Prime-Power Component Index i = p^j** | j ≥ 30028 (≥ 36207 odd); 5 repunits \|S₁\|≥5; i,N > 10^17240 (> 10^300280 even) (`IMPORTED`) | Unconditional elimination of i = p^(2u) via higher p-adic congruences (`OPEN`) | Conditional exclusion via Nagell–Ljunggren / Goormaghtigh |
| **Odd Harmonic Superclass (σ(N) ∣ Nτ(N))** | ω ≥ 3 (≥ 4 if 5th-power-free); HarmonicRange/Smooth; fixed-support/mean finite (`IMPORTED`) | HarmonicTauSmooth toward N > 10^24 (`STAGED (unbuilt)`) | N > 10^24 (Cohen–Sorli 2010); Pollack (2014) Subspace finiteness |
| **Deficient-Perfect / Near-Perfect / Spoof Classes** | The unique four-prime odd deficient-perfect case is (9018009, 819). A coprime divisor-sum split gives the proper factor 19 of its Tóth multiplier. (`IMPORTED`) | 4-prime odd near-perfect uniqueness (Tang–Ma–Feng) (`OPEN`) | Yang–Togbé (2023), Tang–Ma–Feng (2016), BYU signed spoofs |

## 3. Unintegrated Work Tracks (Harvest Queue)

| Track | Total Files | Fresh `.olean` | Stale `.olean` | Unbuilt | Compiled % | Entry Modules |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| HarmonicRange (background — Cohen–Sorli odd harmonic exclusion) | 322 | 67 | 16 | 239 | 20.8% | `HarmonicTauSmooth` |
| CountBound47 (background — Ω(N) ≥ 47) | 167 | 7 | 2 | 158 | 4.2% | `ChainArithmetic`, `ChainWitness`, `CountBound47`, `CountChain45` |
| DeficientFour & ω(N) ≥ 6 (background — Yang–Togbé / Gradshtein) | 27 | 0 | 0 | 27 | 0.0% |  |

## 4. Carbon Strategic Signals & Recommended Next Actions

- See [the resolution handoff](RESOLUTION_HANDOFF.md) for the six-factor criterion, Tóth split, exceptional Fermat reduction and the global B3 cap.
