# Roadmap

**Target.** `¬ OddPerfect.existsOddPerfect`, equivalently `∀ n, Nat.Perfect n → Even n` (`not_existsOddPerfect_iff_forall_perfect_even`, matching formal-conjectures `PerfectNumbers.odd_perfect_number_conjecture`). The proof must be axiom-pure on the pinned Lean/Mathlib.

**Honest status.** The conjecture is open. No route to it is known in the literature or in this repository. The repository is a large audited library of restrictions on odd perfect numbers: about 10,000 named theorems, all using only the standard axioms (see [CLAIMS.md](CLAIMS.md) for the headline results). Progress is measured only by [BRANCH_MAP.md](BRANCH_MAP.md). The operating rules are in [AGENTS.md](../AGENTS.md).

The earlier roadmap (Tier 0 harvests, Stepping Stones S1–S19, Tier 2 Waves A–Q) is archived at [archive/ROADMAP_2026-11-27.md](archive/ROADMAP_2026-11-27.md).

---

## 1. Status

The live table is section 0 of [PROGRESS_DASHBOARD.md](PROGRESS_DASHBOARD.md), generated from BRANCH_MAP. Summary on 27 Nov 2026:

| Node | Status | Active | Missing ingredient |
| --- | --- | --- | --- |
| `A1_SPF`: sixth-power-free | OPEN | **yes** | Arithmetic target-reuse bound cutting the count-LP ray |
| `A1_G1`: a = 1, gcd((q+1)/2, i_q) = 1 | OPEN | **yes** | Descent or size contradiction on u² = Wσ(h²), σ(u²) = W(2h²−1) |
| `IQ_PRIME_POWER_EVEN`: i_q = p^{2u} | OPEN | **yes** | Ceiling u ≤ g(p) |
| `IQ_SQUARE`: a > 1, i_q a square | CLOSED | | |
| `IQ_PRIME_SQUARE`: a > 1, i_q = ℓt² | CONDITIONAL on `ExceptionalFermatObstruction` | | Modular methods (NO_GO §2) |
| `IQ_PRIME_POWER_NONEULER` | CLOSED | | |
| `IQ_PRIME_POWER_ODD` | CONDITIONAL on `ExceptionalFermatObstruction` | | |
| `RESTRAINED_3FREE` | CLOSED (priority vs Ochem–Zelinsky unchecked) | | |
| `A1_P6`, `IQ_MULTI`, and `A1` / `A_GT1` / `ROOT` overall | OPEN | | No program yet |

## 2. Active program (at most 3 nodes)

Each active node runs the loop in `.agents/skills/carbon-reevaluation-loop/SKILL.md`. Ideas start in [IDEAS.md](IDEAS.md) and pass [GATES.md](GATES.md) before any Lean work.

### 2.1 `A1_SPF` (sixth-power-free)

- **Why this node.** It is the most closed algebraic system available. The Euler exponent is 1, every other exponent is 2 or 4, every block is q+1, Φ₃(p) or Φ₅(p), and every prime has in-capacity 2 or 4. A full exclusion would be a genuinely new theorem: Fletcher–Nielsen–Ochem only confine the least prime to (10⁸, 10¹⁰⁰⁰).
- **Missing ingredient.** `python3 research/tools/count_lp.py --branch A1_SPF` is UNBOUNDED. Count inequalities alone cannot close it (NO_GO §4). We need arithmetic constraints on *which* primes are targets: root classes mod t, sizes of sources versus targets, and the quartic-chain lemma.
- **Next ideas.** IDEAS #1 (target reuse) and #2 (largest-prime chain).
- **Kill criterion.** Two rounds without cutting the LP ray or producing a new non-count constraint → freeze.

### 2.2 `IQ_PRIME_POWER_EVEN` (i_q = p^{2u})

- **Missing ingredient.** A ceiling u ≤ g(p) to meet the existing p < 6^u and p ≤ 8(u+1)·128^{√(2u)}. Floor-raising on u, j and the Padé constants is frozen (NO_GO §3).
- **Next idea.** IDEAS #3: a Dickson-type gap on the deficient square s² with σ(s²) = p^{2u}.
- **Kill criterion.** If only Baker-type (linear forms in logarithms) methods give a ceiling, freeze the node and record it in NO_GO.

### 2.3 `A1_G1` (coprime half-successor, a = 1)

- **Missing ingredient.** A descent or size contradiction on (h, u, W). The existing parametrization is `linear_euler_coprime_half_succ_quotient_system`.
- **Next idea.** IDEAS #4.
- **Kill criterion.** The system admits spoof solutions (G1), or two rounds pass without a strictly smaller family.

## 3. Terminating deliverables (parallel, low risk, publishable)

These finish for certain and raise the floors any future closure must beat. Run at most one background slot.

| Deliverable | Value | Notes |
| --- | --- | --- |
| Replay Fletcher–Nielsen–Ochem: least prime > 10⁸ for sixth-power-free N | Feeds `A1_SPF` directly (abundancy pinch: ω ≳ π(P²) − π(P)) | Local floor is 53 |
| Replay Goto–Ohno: largest prime > 10⁸ | Frontier certification | |
| Replay Ochem–Rao: N > 10¹⁵⁰⁰, Ω ≥ 101; Nielsen ω ≥ 10 | Frontier certification; first formal verification | Large certificate effort; reuse the `SizeBound300` infrastructure |
| General Bang–Zsigmondy theorem upstreamed to Mathlib | Lasting community value; used throughout OPN theory | Partial cases exist in `Primitive.lean` and `CyclotomicOrders.lean` |
| Breakout papers (Tóth, parity/finiteness, prime-power index, restrained, Euler index) | Publication | Literature check first (`.agents/agents/literature-checker.md`) |
| Port of Hirakawa's input | Would close `IQ_PRIME_SQUARE` and `IQ_PRIME_POWER_ODD` | Needs generalized-Fermat results from modular methods; depends on the long-term Lean FLT effort. Not a near-term task |

## 4. Frozen or retired

Details are in [NO_GO.md](NO_GO.md).

- Finite-residual bridges B1–B3 (each implies finitely many OPNs; the residual cannot be computed).
- Residue-class sieves on `q^d + 1 = 2y²` (defeated by (q, y) = (1, 1)).
- Floor-raising on u, j, the Padé constants, d, l, r, W, |S₅₁| with no ceiling.
- Count-inequality tightening that leaves the LP ray uncut.
- Universal identities presented as obstructions; Mathlib-coverage integrations.
- Certificate-tree growth not tied to a §3 replay.

## 5. History

Completed rounds are in [LEDGER.md](LEDGER.md). Archived plans are in [archive/](archive/).
