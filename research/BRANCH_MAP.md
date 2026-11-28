# Branch map: the case tree for `¬ existsOddPerfect`

**This is the unit of progress.** Every hypothetical odd perfect number N = q^a m² (Euler form) falls into the partition nodes below.
- A node is `CLOSED` only when an audited Lean theorem derives `False` on it.
- A node is `CONDITIONAL` when such a theorem exists but takes a named, unproved hypothesis.
- Everything else is `OPEN`.

Restrictions such as floors, counts and residue classes are recorded on the node. When one excludes a slice, record its defining arithmetic hypotheses and the previously surviving family that motivated it. Its parent retains its own status.

Two kinds of node:
- `partition`: the children cover the parent exactly.
- `slice`: a cross-cutting subfamily that is tracked separately because a specific method applies to it.

Rules:
- At most **3** nodes are `active: true`. Each active node names its missing ingredient and owner.
- **Anti-slice-inflation rule:** Partition closures (`kind: "partition"`) and slice closures (`kind: "slice"`) are counted separately. A narrow post-hoc `slice` closure never counts as closing its parent partition node and never resets a parent node's 2-round pivot clock. Any new `slice` node must state the named unbounded family or pre-existing branch subcase it excludes.
- Lean theorems that close or restrict a node cite its `id` in their docstring (`BRANCH_MAP: <id>`).
- The JSON block below is read by `research/tools/evaluate_progress.py` and `research/tools/claims.py`. Keep it valid JSON.

## Overview

```mermaid
flowchart TD
  ROOT["ROOT: odd perfect N = q^a m^2 (OPEN, FROZEN)"] --> A1["A1: a = 1 (OPEN, ACTIVE)"]
  ROOT --> AG["A_GT1: a > 1 (OPEN, ACTIVE)"]
  A1 --> SPF["A1_SPF: sixth-power-free (OPEN, FROZEN)"]
  SPF -.-> HS["A1_SPF_HIGH_SQUARE: all square sources 1 mod 5 and S ≥ 2Q (CLOSED)"]
  A1 --> P6["A1_P6: some p^6 divides N (OPEN)"]
  AG --> SQ["IQ_SQUARE: Euler index a square (CLOSED)"]
  AG --> PS["IQ_PRIME_SQUARE: index = l t^2 (CONDITIONAL)"]
  AG --> MU["IQ_MULTI: >= 2 odd-valuation primes (OPEN)"]
  A1 -.-> G1["slice A1_G1: coprime half-successor (OPEN)"]
  ROOT -.-> PPE["slice IQ_PRIME_POWER_EVEN: i_q = p^(2u) (OPEN)"]
  ROOT -.-> PPN["slice IQ_PRIME_POWER_NONEULER (CLOSED)"]
  ROOT -.-> PPO["slice IQ_PRIME_POWER_ODD (CONDITIONAL)"]
  ROOT -.-> R3["slice RESTRAINED_3FREE (CLOSED)"]
```

## Machine-readable tree

```json
{
  "nodes": [
    {"id": "ROOT", "kind": "partition", "parent": null, "status": "OPEN", "active": false,
     "missing": "FROZEN at Round 2 pivot checkpoint: IDEAS #7 and multi-degree cyclotomic count-LPs killed (NO_GO §8); S = 0 powerful-m non-cardinality mechanisms killed (NO_GO §12).", "owner": "Carbon Strategist",
     "description": "Odd perfect N in Euler form q^a m^2, q ≡ a ≡ 1 (mod 4).",
     "lean": ["euler_form"], "floors": "N > 10^300, ω ≥ 6, Ω ≥ 37 (frontier: 10^1500, ω ≥ 10, Ω ≥ 101)"},
    {"id": "A1", "kind": "partition", "parent": "ROOT", "status": "OPEN", "active": true,
     "description": "Euler exponent a = 1. Then m^2 is odd deficient-perfect with omitted divisor i_q (Tóth pair with prime multiplier q).",
     "missing": "r₀ ∣ m_L eliminated unconditionally (IDEAS #9), and Branch R1 (r₀ ∣ g_R) restricted to r₀ ≡ 1 mod 4, non-Fermat 4ℓ ∣ q − 1, A < r₀^(v_{r₀}(I)), k_R ≤ 2b, and b = 1 ⇒ k_R = 1 (IDEAS #11). All 7 remaining local (R1/R2)×(g_L, g_R) regimes retain abundancy < 2 witnesses (Round 2 pivot budget exhausted for local/valuation attacks).",
     "owner": "Carbon Strategist",
     "lean": ["linear_euler_unique_q_source_and_bound", "universal_half_succ_index_gcd_square_parametrization", "linear_euler_unique_source_right_forcing", "linear_euler_right_branch_structure"]},
    {"id": "A1_SPF", "kind": "partition", "parent": "A1", "status": "OPEN", "active": false,
     "description": "Sixth-power-free (forces a = 1; every other exponent is 2 or 4; least prime ≥ 53).",
     "lean": ["sixth_power_free_euler_exponent_one", "sixth_power_or_large_support", "sixth_power_free_oneModThreeLarge_ge_80", "OddPerfect.SquareOutputCapacity.sixth_power_free_square_output_capacity", "quartic_chain_mod_five_target_reuse"],
     "floors": "ω ≥ 443, Ω ≥ 1179, N > 10^3136, |Q13| ≥ 80, E ≥ 221",
     "missing": "FROZEN at Round 2 pivot checkpoint: 5 D_all ≥ 4k − 2 proved, but Ray_18 (364-var integer + bipartite log-height witness at ω = 1800) and lower-square-count (k ≥ m - 2) survive every linear count, residue, complete-factorization, and log-height LP (NO_GO §§11, 13).",
     "owner": "Carbon Strategist"},
    {"id": "A1_SPF_HIGH_SQUARE", "kind": "slice", "parent": "A1_SPF", "status": "CLOSED", "active": false,
     "description": "All exponent-two prime sources are 1 mod 5 (U = 0) and their number S is at least twice the number Q of exponent-four primes that are 1 mod 3.",
     "lean": ["OddPerfect.SquareOutputCapacity.no_high_square_count_of_all_one_mod_five"]},
    {"id": "A1_P6", "kind": "partition", "parent": "A1", "status": "OPEN", "active": false,
     "description": "a = 1 and some prime p has p^6 | N."},
    {"id": "A1_G1", "kind": "slice", "parent": "A1", "status": "OPEN", "active": false,
     "description": "a = 1 and gcd((q+1)/2, i_q) = 1 (coprime half-successor): u² = W σ(h²), σ(u²) = W(2h² − 1).",
     "lean": ["linear_euler_coprime_half_succ_quotient_system"],
     "missing": "A descent (strictly smaller solution of the same system) or a size contradiction on (h, u, W).",
     "owner": "Carbon Strategist"},
    {"id": "A_GT1", "kind": "partition", "parent": "ROOT", "status": "OPEN", "active": true,
     "description": "Euler exponent a > 1. Split by the odd-valuation primes of the Euler index I = σ(m²)/q^a.",
     "lean": ["high_euler_half_sum_not_square_of_prime_power_fermat"],
     "missing": "Subcase A ((q^d+1)/2 = □, prime and composite d) isolated to the explicit external modular-forms prerequisite PrimePowerFermatObstruction (Ivorra 2003, Acta Arith. 108(4); Bennett–Skinner 2004, Canad. J. Math. 56(1), Prop. 8.1 — absent from pinned Mathlib). Subcase B ((q^d+1)/2 ≠ □) forces d.Prime unconditionally at |oddVal(I)| = 2, but prime-d Subcase B retains local witnesses (17, 13, 7) and (293, 5, 3) (NO_GO §10).",
     "owner": "Carbon Strategist"},
    {"id": "IQ_SQUARE", "kind": "partition", "parent": "A_GT1", "status": "CLOSED", "active": false,
     "description": "I is a square.", "lean": ["euler_index_not_square_of_exponent_gt_one"]},
    {"id": "IQ_PRIME_SQUARE", "kind": "partition", "parent": "A_GT1", "status": "CONDITIONAL", "active": false,
     "description": "I = ℓ t² with ℓ prime; reduces to q^d + 1 = 2y², d = (a+1)/2 prime ≥ 17.",
     "lean": ["euler_index_ne_prime_mul_square_of_fermat_obstruction"],
     "hypothesis": "ExceptionalFermatObstruction (OddPerfect/ExceptionalFermatReduction.lean)",
     "note": "Residue sieves cannot finish ((q,y) = (1,1) survives every modulus; NO_GO §2). Hirakawa Lemma 2.5 supplies the published result. The local Lean reduction retains an explicit premise."},
    {"id": "IQ_MULTI", "kind": "partition", "parent": "A_GT1", "status": "OPEN", "active": false,
     "description": "I has at least two primes of odd valuation.",
     "lean": ["two_odd_valuations_nonsquare_half_sum_forces_prime_half_length"],
     "missing": "Subcase A ((q^d+1)/2 = □) conditionally closed on PrimePowerFermatObstruction; Subcase B unconditionally forces d.Prime when |oddVal(I)| = 2, but prime-d Subcase B is locally unobstructed (witnesses (17, 13, 7) and (293, 5, 3), NO_GO §10)."},
    {"id": "IQ_PRIME_POWER_NONEULER", "kind": "slice", "parent": "ROOT", "status": "CLOSED", "active": false,
     "description": "Some non-Euler component index i_r (r ≠ q) is a prime power.",
     "lean": ["component_prime_power_index_euler_only_and_septuple_lift"]},
    {"id": "IQ_PRIME_POWER_ODD", "kind": "slice", "parent": "ROOT", "status": "CONDITIONAL", "active": false,
     "description": "Euler index i_q = p^j with j odd.",
     "hypothesis": "ExceptionalFermatObstruction (componentIndex_ne_odd_prime_power_of_fermat_obstruction)"},
    {"id": "IQ_PRIME_POWER_EVEN", "kind": "slice", "parent": "ROOT", "status": "OPEN", "active": false,
     "description": "Euler index i_q = p^(2u) (forces a = 1, q = σ(p^(2u)), q + 1 = 2s², σ(s²) = p^(2u)).",
     "lean": ["even_prime_power_component_size_gt_ten_pow_353234555955090756", "even_prime_power_component_base_lt_six_pow", "even_index_base_subexponential"],
     "floors": "2u ≥ 1.3·10^16, p ≥ 10^27, ≥ 13 repunit bases",
     "missing": "A descent or an upper bound on u quantitatively incompatible with the known p-bounds.",
     "owner": "Carbon Strategist"},
    {"id": "RESTRAINED_3FREE", "kind": "slice", "parent": "ROOT", "status": "CLOSED", "active": false,
     "description": "3 ∤ N and at most one non-Euler prime r ≠ 3 with exponent ≥ 4.",
     "lean": ["two_le_largeSources_of_three_free"],
     "note": "Ochem–Zelinsky §2 covers one exceptional even exponent, Steuerwald covers zero. The local proof is an alternative derivation."},
    {"id": "RELATED", "kind": "slice", "parent": null, "status": "OPEN", "active": false,
     "description": "Results on neighbouring classes (near-perfect, deficient-perfect, harmonic, spoofs). Not part of the case tree."}
  ]
}
```

## How a node changes status

1. A Lean theorem with conclusion `False` (or `x ∉ node`) under exactly the node's hypotheses passes `lake build && lake lean research/Audit.lean`.
2. `neon-auditor` confirms that the theorem's hypotheses match the node description word for word.
3. The Strategist updates the JSON above, adds the theorem to [claims_registry.json](claims_registry.json), and records the change in [LEDGER.md](LEDGER.md) under **Branch impact**.
