# Whiteboard: current mathematics only

Keep this file under about 120 lines. It holds the settled framework and the **current** sketches. Clear finished material every round: proven results go to [CLAIMS.md](CLAIMS.md) and [LEDGER.md](LEDGER.md), dead ideas go to [NO_GO.md](NO_GO.md), candidate ideas live in [IDEAS.md](IDEAS.md). The previous whiteboard, with the Waves 1–Q lock-in list, is archived at [archive/WHITEBOARD_2026-11-27.md](archive/WHITEBOARD_2026-11-27.md).

---

## 1. The closed equation

Write N = q^a ∏_{p∈S∖{q}} p^{e_p} (Euler form, q ≡ a ≡ 1 mod 4, e_p even). Perfection is

$$2\,q^a\!\!\prod_{p\in S\setminus\{q\}}\! p^{e_p} \;=\; \prod_{p\in S}\;\prod_{\substack{d\mid e_p+1\\ d>1}} \Phi_d(p).$$

If r divides Φ_d(p) with d > 2, then either r ≡ 1 (mod d), or r is the largest prime factor of d and r ∥ Φ_d(p).

Component index: i_p = σ(N/p^{e_p})/p^{e_p} = 2N/(p^{e_p}σ(p^{e_p})). Conservation law: Ω(i_p) + e_p + Ω(σ(p^{e_p})) = 1 + Ω(N).

## 2. The non-spoofable properties

A proof must use at least one property that spoofs violate (see gate G1):

- **I1. Primality of the bases.** Spoofs use composite bases (Descartes: 22021 = 19²·61) or negative bases (Voight: −127).
- **I2. Closure with exact valuations.** Every prime factor of every σ(p^{e_p}) lies in S, and the incoming valuations at r sum exactly to e_r. Spoofs leak prime factors outside the base set.
- **I3. Abundancy balance.** ∏ σ(p^e)/p^e = 2, hence ∑ 1/p < log 2 < ∑ 1/(p−1). On its own this is satisfied by spoofs; it is useful only combined with I1/I2.
- **I4. Prefix-gap rigidity.** No proper sub-product of local abundancies hits a forbidden rational target (`Dickson.lean`, `NearPerfectFinite.lean`).

Counting arguments use I2 only through *numbers* of targets. The surviving count-LP ray (FLOOR_CEILING) shows that this throws away the information that matters. The next step must use I2 *arithmetically*: which primes, in which residue classes, of which size.

## Counterexample filter bank

Every candidate global lemma is tested against these (gate G1):

1. **Descartes spoof** `198585576189 = 3²·7²·11²·13²·19²·61`, formal base `22021`. It passes Euler form, Touchard, 105 ∤ N and formal balance. It fails primality of 22021, the fourth-power requirement and Ore harmonicity.
2. **Voight negative-base spoof** `3⁴·7²·11²·19²·(−127)`.
3. **BYU primitive odd spoofs.** All 21 with fewer than seven bases, plus the infinite families (Andersen et al., *Odd, spoof perfect factorizations*, J. Number Theory).
4. **Tóth / deficient-perfect cofactor** `(9018009, 819)`, multiplier 22021. At a = 1, m² is odd deficient-perfect with omitted divisor i_q.
5. **Johnson near-perfect** `173369889 = 3⁴·7²·11²·19²`, σ(n) = 2n + 2751903.
6. **Local cycles** `3 → 11 → 7 → 3` and `7² → 19, 19⁴ → 151, 151² → 7`. They cycle locally only because they leak primes (13, 19, …).
7. **Quartic-chain controls** w = 4153 and w = 22639. Both give a prime s = Φ₅(w), and 73 divides s²+s+1 to the first power in both chains. This is local reuse of a target (27 Nov assessment).
8. **Shared Φ₃/Φ₅ target** 31 | Φ₃(191) and 31 | Φ₅(97).

## 3. Known reformulations (not routes)

The bridges B1 (cap on ω), B2 (cap on i_p) and B3 (cap on Ω(i_p)) are correct implications (`not_existsOddPerfect_of_*` in `GlobalObstruction.lean`). Each, however, implies finitely many OPNs, and each leaves a remainder that cannot be checked by computation. See NO_GO §1. They are useful only when a cap falls below a floor proven on the same node.

## 4. Current sketches

Sketches are developed in [IDEAS.md](IDEAS.md). One-line summaries:

- **#1 `A1_SPF` target reuse.** A target t of Φ₃ receives only from base primes in 2 root classes mod t (roots summing to −1); a target of Φ₅, from 4 classes. In-capacity is 2 or 4, and t ≤ p²+p+1. Look for a superlinear bound on the number of distinct targets.
- **#2 `A1_SPF` largest-prime chain.** The largest prime P has a supplier p ≥ P^{1/4}. Iterate down to the least prime, whose floor rises to 10⁸ after an FNO replay.
- **#3 `IQ_PRIME_POWER_EVEN` ceiling.** 2(p−1)s² = p^{2u+1} + p − 2 and σ(s²) = p^{2u}, so s² is deficient with abundancy just below 2 − 2/p. Look for a Dickson gap giving u ≤ g(p, ω(s)).
- **#4 `A1_G1` descent.** u² = W·σ(h²) and σ(u²) = W(2h² − 1), with h₀ + 2 ≤ u₀ and W ≥ 5113 on sixth-power-free N.
