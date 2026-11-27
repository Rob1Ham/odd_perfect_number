# Odd Perfect Number — Mathematical Architecture & Active Whiteboard

**Premise**: `OddPerfect.existsOddPerfect` admits a complete, unconditional Lean 4 proof on our pinned Mathlib commit (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) using only standard foundations. This whiteboard tracks *how* a genuine proof must work, *which* invariants separate true odd perfect numbers from spoofs, and active proof sketches for Carbon and Neon agents.

---

## 1. The Four Bridges to Global Resolution

For B3, every candidate has a five-factor relative drop. The uniform cap still needed and the next concrete residue and cofactor tests are in the [resolution handoff](RESOLUTION_HANDOFF.md).

Any unconditional proof of `¬ OddPerfect.existsOddPerfect` must close the candidate set $\mathcal{O} = \{N \in \mathbb{N} \mid \text{Odd } N \wedge \text{Nat.Perfect } N\}$ through one of four checked or direct bridges:

| Bridge | Mathematical Mechanism | Audited Lean Foundation Already in Repo | What Remains to Close Globally |
| :--- | :--- | :--- | :--- |
| **B0: Direct Global Contradiction** | Prove an identity/inequality over $\prod_{p \in S} \sigma(p^{e_p}) = 2 \prod_{p \in S} p^{e_p}$ whose LHS and RHS disagree for all odd $N$. | `euler_form`, `steuerwald`, `sigmaEdge_reachable`, `CyclotomicOrders` | Find a global invariant using all four non-spoofable properties (`I1`–`I4` below) simultaneously. |
| **B1: Uniform Rank Cap ($\omega(N) \le K_0$)** | Bound distinct prime divisors $\omega(N)$ above by an explicit constant $K_0$, then eliminate $\omega \le K_0$. | `OddPerfect.dickson_finite` ($4k R^2 N \le (4k)^{4^k}$) | Prove an incompatible slope/density pair forcing $\omega(N) \le K_0$, plus finite elimination below $K_0$. |
| **B2: Component Index Value Cap ($\exists p^e \parallel N,\; i_p \le K_0$)** | Show at least one exact component has index $i_p = \sigma(N/p^e)/p^e \le K_0$. | `OddPerfect.finite_of_bounded_component_index` | Prove minimum component index cannot diverge across all components simultaneously, then close finite set. |
| **B3: Component Index Multiplicity Cap ($\exists p^e \parallel N,\; \Omega(i_p) \le K_0$)** | Bound $\Omega(i_p)$ for at least one component; since $\omega(N) \le 2(\omega(i_p)+\Omega(i_p))+4$, this implies **B1**! | `OddPerfect.EulerIndexMultiplicity` (`ω(N) ≤ 2(ω(i)+Ω(i))+4`) | **Dual view**: Either $\exists p^e$ with bounded $\Omega(i_p)$ ($\implies$ finite!), OR **every** component $p^e \parallel N$ has $\Omega(\sigma(N/p^e)/p^e) \ge \frac{\omega(N)-4}{4}$, forcing massive simultaneous GCD cancellation! |

---

## 2. Counterexample Filter Bank (Mandatory Fast-Fail Gate)

Before spending Neon prover cycles on a proposed global contradiction, check which of these concrete test objects breaks the naive hypothesis. **Any proof of `¬ existsOddPerfect` MUST fail on every spoof/relaxation below — the exact step where the spoof fails reveals the live mathematical leverage!**

1. **Descartes's Positive Spoof (`N_D = 198,585,576,189 = 3² · 7² · 11² · 13² · 19² · 61`, formal base `22021 = 19² · 61`)**:
   - *Passes*: Euler form, Touchard's congruence, $105 \nmid N$, formal balance at length 5 (`OddPerfect/Spoof.lean`).
   - *Fails*: True primality of the linear slot (`22021` composite), true fourth-power requirement (`OddPerfect/FourthPowerSpoof.lean`), and Ore harmonicity (`descartes_not_oreHarmonic`: $426027470778 \nmid 198585576189 \cdot 486$).
2. **Tóth / Descartes Deficient-Perfect Cofactor (`n = 9,018,009 = 3² · 7² · 11² · 13²`, `d = 819`, `x = 22,021`)**:
   - Satisfies $\sigma(n) + d = 2n$ and $3\sigma(n)$ / multiplier balance (`OddPerfect/TothTrillion.lean`). Tests any cofactor argument at Euler exponent $a = 1$ ($N = q m^2 \implies \sigma(m^2) = 2m^2 - \dots$? Specifically $\sigma(m^2)(q+1) = 2 q m^2 \implies (2m^2 - \sigma(m^2))\dots$ wait: $\sigma(m^2) = \frac{2q}{q+1} m^2 = 2m^2 - \frac{2m^2}{q+1} = 2m^2 - i_q$ with $i_q \mid m^2$!).
   - **Key Identity**: In Euler form at $a=1$, $m^2$ is **literally an odd deficient-perfect number** with omitted divisor $d = i_q = \sigma(m^2)/q$ and multiplier $x = q$ prime!
3. **Johnson's Odd Near-Perfect Square (`n = 173,369,889 = 3⁴ · 7² · 11² · 19²`, `d = 2,751,903`)**:
   - Satisfies $\sigma(n) = 2n + d$ (`OddPerfect/NearPerfect.lean`). Tests abundancy-excess and square-cofactor arguments.
4. **Local Reciprocity & Valuation Cycles (`3 → 11 → 7 → 3` and `7² → 19, 19⁴ → 151, 151² → 7`)**:
   - Proves that local directed edge rules (`OddPerfect/Reciprocity.lean`, `OddPerfect/OddValuationGraph.lean`) allow cycles *only because* those small subgraphs leak unabsorbed prime factors (`13`, `19`, etc.) outside the subgraph!

---

## 3. The Four Non-Spoofable Global Invariants (`I1`–`I4`)

A global obstruction can succeed **if and only if** it couples at least two of the four properties true for genuine odd perfect numbers and false for spoofs/leaking subgraphs:

- **`I1` — Exact Cyclotomic Factorization Over Distinct Prime Bases**:
  $$2 \, q^a \prod_{p \in S \setminus \{q\}} p^{e_p} = (q + 1) \left(\prod_{\substack{d \mid a+1 \\ d > 2}} \Phi_d(q)\right) \prod_{p \in S \setminus \{q\}} \prod_{\substack{d \mid e_p + 1 \\ d > 1}} \Phi_d(p).$$
  Every prime $r \mid \Phi_d(p)$ ($d > 2$) satisfies either $r \equiv 1 \pmod d$ (unramified) or $r = P(d)$ with $d = d_0 r^k$ and **exact valuation $v_r(\Phi_d(p)) = 1$** (ramified intrinsic divisor).
- **`I2` — Closed-Graph Valuation Conservation & Global Reciprocity**:
  Sum of incoming $r$-adic valuations across all blocks $\Phi_d(p)$ equals the outgoing exponent $e_r$ for *every* $r \in S$, with **zero leaked primes** ($r \notin S$). Multiplying Legendre/Jacobi symbols $\left(\frac{\cdot}{r}\right)$ or evaluating $\Phi_d(p) \pmod{8}$ / $\pmod{p_{\min}}$ across the entire closed product constrains residue classes globally.
- **`I3` — Slope vs. Logarithmic Abundancy Pinch**:
  - Small exponents ($e_p = 2$) force primes $r \mid p^2+p+1$ ($r = 3$ or $r \equiv 1 \pmod 3$) and injectivity collisions, driving $\Omega(N)/\omega(N)$ **up** (`OchemRao`: $\Omega \ge \frac{18}{7}\omega - \frac{31}{7}$; Zelinsky: $\Omega \ge \frac{302}{113}\omega - \frac{286}{113}$).
  - Meanwhile, $\prod_{p \in S} \frac{\sigma(p^{e_p})}{p^{e_p}} = 2$ pins $\sum_{p \in S} \log \frac{\sigma(p^{e_p})}{p^{e_p}} = \log 2$, bounding prime reciprocals (`PrimeReciprocalLog`, `ZelinskyReciprocal`) and component sizes (`Dickson`, `SecondLargestPrime`).
- **`I4` — Prefix Product-Gap Rigidity (`labels_bounded_of_no_balanced_prefix`)**:
  No nonempty proper subset of opening/closing labels $(p, p^{e_p+1})$ can balance a rational target when 2-adic / parity obstructions forbid intermediate equality (`OddPerfect/Dickson.lean`, `OddPerfect/SpoofFiniteness.lean`, `OddPerfect/NearPerfectFinite.lean`).

---

## 4. Active Mathematical Sketches (Next Wave)

### Sketch A (Tier 1 / Stepping Stone S1 — Even vs. Odd Deficient/Near-Perfect Parity Theorem)
- Why did `DeficientFiniteness` and `NearPerfectFinite` require `Odd n`? Because for $p = 2$, the limiting abundancy $\frac{2}{2-1} = 2$ reaches the target $2$ on a **1-element prefix** $\{2\}$!
- Specifically:
  - $n = 2^a$ ($a \ge 1$) satisfies $\sigma(2^a) = 2^{a+1} - 1 = 2n - 1$ ($d = 1$, $k = 1$ infinite family).
  - Whenever $q = 3 \cdot 2^a - 1$ is a **Thabit prime**, $n = 2^a q$ satisfies $\sigma(n) = (2^{a+1}-1)(3\cdot 2^a) = 2n - 2^a$ with $2^a \mid n$ ($k = 2$ conditional infinite family!).
  - However, if **$v_2(n) \le A$ is bounded**, then $\frac{\sigma(2^{v_2(n)})}{2^{v_2(n)}} \le 2 - \frac{1}{2^A} < 2$! Freezing the 2-component reduces the odd part $m = n / 2^{v_2(n)}$ to a rational abundancy target $\frac{2^{v_2(n)+1}}{2^{v_2(n)+1}-1}$ with strictly positive prefix gaps — yielding **explicit finiteness for all fixed $(k, A)$**!

### Sketch B (Tier 1 / Stepping Stone S2 — Fixed-Rank `OreHarmonic` Finiteness & $\omega \in \{2,3\}$ Exclusion)
- Let `Odd N`, `OreHarmonic N` ($\sigma(N) \cdot M = N \cdot \tau(N)$), and $\omega(N) \le k$.
- Since $\tau(N) = \prod_{p \in S} (e_p + 1)$ grows only polynomially in $e_p$ while $p^{e_p}$ grows exponentially (and `CohenSorli` already gives $\tau(N)^4 \le N$ and $(p^{e_p})^8 < N^5$!),Wait: at fixed $\omega(N) \le k$, can $\tau(N)$ vary? No! Wait: in $\frac{\sigma(N)}{N} = \frac{\tau(N)}{M}$, $\frac{\sigma(N)}{N} < \prod_{i=1}^k \frac{p_i}{p_i - 1} \le \prod_{i=1}^k \frac{2i+1}{2i} < 2\sqrt{k}$, so the harmonic mean $M = \frac{N \tau(N)}{\sigma(N)}$ satisfies $\tau(N) / (2\sqrt{k}) < M < \tau(N)$! Even simpler: Kanold's recursive abundancy gap bounds the smallest remaining prime $p_r$ and exponent $e_r$ because $(e_r + 1)/p_r^{e_r} \to 0$! Formalizing this gives an unconditional Lean finiteness theorem for fixed-$k$ odd harmonic numbers, and small-$k$ ($\omega = 2, 3$) abundancy/2-adic bounds (`HarmonicComponents.lean`: every $e_p \equiv 0 \pmod 2$ or $p^e \equiv 1 \pmod 4$, odd prime divides $\tau(N)$) immediately crush $\omega = 2$!
  - *Check $\omega(N) = 2$ on the whiteboard right now*:
    Suppose $N = p^a q^b$ is odd harmonic ($p < q$ odd primes). By `HarmonicComponents.lean`, some odd prime $r \mid \tau(N) = (a+1)(b+1)$, and $p^a \equiv q^b \equiv 1 \pmod 4$. Also $v_2(\sigma(p^a)\sigma(q^b)) \le v_2(N \tau(N)) = v_2((a+1)(b+1))$! Wait: $\frac{\sigma(N)}{N} < \frac{3}{2} \cdot \frac{5}{4} = \frac{15}{8} < 2$! Since $\sigma(N) \mid N \tau(N)$, write $N \tau(N) = M \sigma(N)$, so $\frac{\tau(N)}{M} = \frac{\sigma(N)}{N} \in (1, \frac{15}{8})$! Combining $\gcd(p^a, \sigma(p^a)) = 1$ with $p^a \mid M \sigma(q^b)$ and $q^b \mid M \sigma(p^a) \implies q^b \le M \sigma(p^a) < \tau(N) \frac{3}{2} p^a$... wait: $p^a q^b$ vs $\tau(N)$! That's a super clean target for a Neon scout + prover round!

### Sketch C (Tier 1 / Stepping Stone S3 — Unconditional Prime-Power Index $i = p^j$ Attack)
- In `EvenIndexRepunits.lean`, $N = q(p^u s)^2$ with $q = \sigma(p^{2u})$, $q + 1 = 2s^2$, $\sigma(s^2) = p^{2u}$.
- Notice the **coupled quadratic relation**:
  $$2s^2 = q + 1 = 2 + p + p^2 + \dots + p^{2u} = 2 + p(1 + p)\frac{p^{2u}-1}{p^2-1}!$$
  Subtract $2$ from both sides:
  $$2(s - 1)(s + 1) = p \, \sigma(p^{2u-1})!$$
  LOOK AT THAT FACTORIZATION:
  1. $p \mid (s - 1)(s + 1)$, so $s \equiv \pm 1 \pmod p$! (Already connects $s \bmod p$ directly to $\sigma(s^2) = p^{2u}$!)
  2. Furthermore, $\sigma(p^{2u-1}) = (1 + p)(1 + p^2 + \dots + p^{2u-2})$. Every odd prime $w \mid 1 + p$ divides $2(s-1)(s+1)$, AND for every prime $r \mid s$, $r^{2v_r(s)+1} \equiv 1 \pmod p$ (since $\sigma(r^{2v_r(s)}) = p^{\beta_r}$)!
  3. Even better: modulo $8$, since $s$ is odd, $s^2 \equiv 1 \pmod 8$, wait: $q = 2s^2 - 1$: if $s^2 \equiv 1 \pmod 8$, wait — $q \equiv 1 \pmod 4$ ALWAYS (`2s^2 - 1 ≡ 1 mod 4`? Wait: $s$ odd $\implies s^2 \equiv 1 \pmod 8 \implies 2s^2 - 1 \equiv 1 \pmod 8$!!).
     WAIT A SECOND!
     Check that! Since $s$ is odd, $s^2 \equiv 1 \pmod 8 \implies 2s^2 \equiv 2 \pmod{16} \implies q = 2s^2 - 1 \equiv \mathbf{1 \pmod{16}}$?!
     HOLD ON: $s$ odd $\implies s = 2k+1 \implies s^2 = 4k(k+1) + 1 \equiv 1 \pmod 8 \implies 2s^2 \equiv 2 \pmod{16} \implies q = 2s^2 - 1 \equiv \mathbf{1 \pmod{16}}$ ALWAYS!!
     Now compute $q = 1 + p + p^2 + \dots + p^{2u} \pmod{16}$!
     Every even power $p^{2m} \equiv 1$ or $9 \pmod{16}$, and $\Phi_2 \dots$: when $q \equiv 1 \pmod{16}$, we get $p(1 + p + \dots + p^{2u-1}) = 2(s^2 - 1) \equiv 0 \pmod{16}$, so $16 \mid (1 + p)(1 + p^2 + \dots + p^{2u-2})$!
     AND for every prime divisor $\ell$ of $u$, $\Phi_\ell(p) \Phi_{2\ell}(p) \mid 2(s-1)(s+1)$!
  This coupled identity $2(s-1)(s+1) = p\,\sigma(p^{2u-1})$ + $\sigma(s^2) = p^{2u}$ has **never been fully mined** with Jacobi symbols and cyclotomic divisors in `OddPerfect/`!
  - **LIVE BREAKTHROUGH (Mod-$p^2$ Divisor-Power Harmonic Congruence — Unconditional Collapse of Nagell–Ljunggren Branch)**:
    Let $S_1 = \{r \in s.\text{primeFactors} \mid v_p(\sigma(r^{2 e_r})) = 1\}$ (`EvenIndexRepunits.lean`).
    1. **No $1 \pmod p$ or length-$p$ cofactor prime**: If $p \mid 2 e_r + 1$, then since $2 e_r + 1$ is prime (`prime_length_of_pure_even_component`), $2 e_r + 1 = p$; Fermat's Little Theorem on $(r-1)p^{v_r} = r^p - 1 \equiv r - 1 \pmod p$ forces $r \equiv 1 \pmod p$, whence $r \ge 2p + 1 > p$ and $\sigma(r^{p-1}) \equiv p \not\equiv 0 \pmod{p^2}$ ($v_r = 1$), impossible since $\sigma(r^{p-1}) > r > p$! Thus $\gcd(p, \tau(s^2)) = 1$ and $r \not\equiv 1 \pmod p$ for ALL $r \mid s$!
    2. **Exact mod-$p^2$ power identity**: For $r \in S_1$, $r^{2 e_r + 1} = 1 + (r - 1)p$; for $r \notin S_1$, $v_r \ge 3 \implies r^{2 e_r + 1} \equiv 1 \pmod{p^3}$. Raising $2 s^2 = q + 1 \equiv 2 + p \pmod{p^2}$ to $T = \tau(s^2) = \prod_{r \mid s} (2 e_r + 1)$ in `ZMod (p^2)` gives:
       $$2^T \left(1 + \sum_{r \in S_1} \frac{2 e_r T}{2 e_r + 1}(r - 1) p\right) \equiv (2 + p)^T \equiv 2^T + 2^{T-1} T p \pmod{p^2},$$
       cancelling $2^{T-1} p$ and dividing by $T \not\equiv 0 \pmod p$ in `ZMod p`:
       $$\sum_{r \in S_1} \frac{4 e_r (r - 1)}{2 e_r + 1} \equiv 1 \pmod p!!$$
    3. **Immediate unconditional exclusions (ZERO Nagell–Ljunggren needed!)**:
       - $|S_1| = 0$: gives $0 \equiv 1 \pmod p$, **refuting the entire pure-higher-power Nagell–Ljunggren branch unconditionally!**
       - $|S_1| = 1$ ($S_1 = \{r_0\}$): gives $4 e_0 (r_0 - 1) \equiv 2 e_0 + 1 \pmod p$, impossible because $0 < 2 e_0 + 1 < 4 e_0 (r_0 - 1) < 1 + r_0 + \dots + r_0^{2 e_0} = p$ for ALL $r_0 \ge 3, e_0 \ge 1$! **Refutes `even_index_multiple_repunit_witnesses`'s second disjunct unconditionally — forcing `HasTwoOddPrimeRepunits p` unconditionally!**
       - $|S_1| = 2$ ($S_1 = \{r_1, r_2\}$): clearing $(2e_1+1)(2e_2+1)$ still satisfies $0 < L < p$ across all prime pairs, **forcing $|S_1| \ge 3$ (and $|S_1| \ge 4$) simultaneous Goormaghtigh representations of the single prime $p$**!

### Sketch D (Tier 2 / Global Fronts Alpha & Beta — Unconditional OPN Collapse)
- **Dual Multiplicity Pinch (Via Bridge `B3`)**:
  For *every* $p \in S$, let $i_p = \sigma(N/p^{e_p})/p^{e_p}$. Then:
  $$\prod_{p \in S} i_p = \prod_{p \in S} \frac{\sigma(N) / \sigma(p^{e_p})}{p^{e_p}} = \frac{(2N)^{\omega(N)}}{N \cdot \sigma(N)} = 2^{\omega(N)-1} N^{\omega(N)-2}.$$
  Wait — check that identity!!
  Since $\sigma(N/p^{e_p}) \cdot \sigma(p^{e_p}) = \sigma(N) = 2N$:
  $$i_p = \frac{2N}{p^{e_p} \sigma(p^{e_p})}!$$
  Multiply over all $p \in S$ ($\omega = |S|$):
  $$\prod_{p \in S} i_p = \frac{(2N)^\omega}{\left(\prod p^{e_p}\right)\left(\prod \sigma(p^{e_p})\right)} = \frac{2^\omega N^\omega}{N \cdot (2N)} = 2^{\omega - 1} N^{\omega - 2}!!$$
  Take $\Omega(\cdot)$ (total prime factors with multiplicity!) of BOTH SIDES:
  $$\sum_{p \in S} \Omega(i_p) = (\omega - 1) + (\omega - 2)\,\Omega(N)!!$$
  WAIT A SECOND! Look at the **minimum** term on the LHS:
  By averaging over the $\omega$ primes $p \in S$, **there ALWAYS exists at least one component $p \in S$** with:
  $$\Omega(i_p) \le \frac{\omega - 1}{\omega} + \frac{\omega - 2}{\omega}\,\Omega(N) < \Omega(N)!$$
  Even sharper: for any subset or weighted sum (weighting by $e_p$ or $\log p$), $i_p = \frac{2N}{p^{e_p}\sigma(p^{e_p})}$ expresses *every* component index globally! Comparing $\Omega(i_p)$ and $\omega(i_p)$ against the incoming valuation edges to $p^{e_p}$ (`e_p = ∑_{r ≠ p} v_p(σ(r^{e_r}))`, hence $\Omega(N) - e_p - \Omega(i_p) = \Omega(\sigma(p^{e_p})) - 1$!) gives the **Exact Component-Index Conservation Law**:
  $$\Omega(i_p) = 1 + \Omega(N) - e_p - \Omega(\sigma(p^{e_p})) \quad (\forall p \in S)!!$$
  *(Verify: $i_p \cdot p^{e_p} \cdot \sigma(p^{e_p}) = 2N \implies \Omega(i_p) + e_p + \Omega(\sigma(p^{e_p})) = 1 + \Omega(N)$!)*
  Summing that exact identity over $p \in S$ just recovers $\sum \Omega(\sigma(p^{e_p})) = 1 + \Omega(N)$, while at ANY single component with large $e_p + \Omega(\sigma(p^{e_p}))$, $\Omega(i_p)$ drops! In particular, if *any* component accounts for all but $K$ prime factors of $2N$ ($e_p + \Omega(\sigma(p^{e_p})) \ge \Omega(N) + 1 - K$), then $\Omega(i_p) \le K \implies \omega(N) \le 4K + 4 \implies$ **FINITE BY DICKSON**!
  Keep mining exact global conservation laws of this form on the whiteboard in every Carbon round.

---

## 5. Newly Formalized & Audited Invariants (Waves 1–4 Lock-In)

1. **Unconditional Quintuple-Repunit Obstruction, `T`-Independent `ZMod (p^2)` Congruence, & $j \ge 30028$ Jump (`OddPerfect/PrimePowerObstruction.lean`, `OddPerfect/TripleRepunitObstruction.lean`, `OddPerfect/QuadrupleRepunitObstruction.lean`, `OddPerfect/PrimePowerExponent2308.lean`, `OddPerfect/PrimePowerHigherObstruction.lean`)**:
   - Every even prime-power component index $i = p^{2u}$ ($u \ge 1$) satisfies $p \parallel s - 1$, $4((s-1)/p) \equiv 1 \pmod p$, $\prod_{r \in S_1} (2 e_r + 1) \mid (p-1)/2$, $2(u+1)+r \equiv 0 \pmod{r^2}$ ($r \parallel u+1$ for all $r \in S_1$), $\sum_{r \in S_1} \frac{4 e_r (r-1)}{2 e_r + 1} \equiv 1 \pmod p$, the `ZMod (p^3)` divisor-power congruence (`even_index_mod_p_cube_congruence`), and the `T`-independent second-order `ZMod (p^2)` congruence (`even_index_mod_p_sq_second_order_congruence`).
   - Eliminates $|S_1| \in \{0, 1, 2, 3, 4\}$ unconditionally (`HasFiveOddPrimeRepunits p ∧ 8 ≤ ω(N)`), and lifts **all** prime-power component indices $i = p^j$ to **$30028 \le j \wedge 10^{17240} < i \wedge 10^{17240} < N$** (`10^300280 < i < N` for even $j$, `component_prime_power_index_exponent_ge_30028`).
2. **Universal Cyclotomic Root Saturation, Vieta Mod-3 Refinement, & Multi-Block `554/199` Slope (`OddPerfect/CyclotomicRootSlope.lean`, `OddPerfect/UniversalCyclotomicRoots.lean`, `OddPerfect/ZelinskySlope.lean`, `OddPerfect/ZelinskyFullSlope.lean`)**:
   - Kernel-checked `card_range_dvd_geometricBlock_le_pred` ($\le l - 1$), `geometricBlock_prime_root_unique`, and `card_twoModThree_dvd_sq_add_self_add_one_le_one` (at most one $u \equiv 2 \pmod 3$ root of $\Phi_3(x) \equiv 0 \pmod w$), proving **$8\omega(N) + 4|L_2| \le 3\Omega(N) + 7$** ($3 \nmid N$), **$21\omega(N) + 11|L_2| \le 8\Omega(N) + 39$** (all odd perfect $N$), sharpened quartic ($5/2$) & sextic ($l = 7$) root-slot bounds, cross-normalization identities (`four_mul_phi5_eq_sq_sub_five_mul_sq`, `phi3_comp_phi5_factorization`), and **`554 * ω(N) ≤ 199 * Ω(N) + 595`** (`multi_block_slope_above_zelinsky`, slope $2.7839 > 302/113$).
3. **Global Component-Index Conservation, Dual Bridge `B3` Finiteness, & Non-Spoofable `I1` Separation (`OddPerfect/GlobalObstruction.lean`, `OddPerfect/GlobalAbundancyObstruction.lean`, `OddPerfect/GlobalWave4Obstruction.lean`, `OddPerfect/DeficientFourClassification.lean`, `OddPerfect/PrimeFive.lean`)**:
   - Kernel-checked Yang–Togbé 4-prime odd deficient-perfect uniqueness (`odd_deficientPerfect_four_set = {(9018009, 819)}`, `toth_odd_pair_four_iff`), Gradshtein **`6 ≤ ω(N)`** (`six_le_distinct_prime_factor_count`), and `euler_exp_one_toth_pair_and_six_primes` (isolating `q.Prime` on $N = q m^2$ to separate genuine candidates from Descartes's spoof `198585576189 = 22021 * 9018009`).
   - Kernel-checked $\prod_{p \in S} i_p = 2^{\omega-1} N^{\omega-2}$, $\Omega(i_p) + e_p + \Omega(\sigma(p^{e_p})) = 1 + \Omega(N)$, unconditional $\exists p \in S,\; \Omega(i_p) + 5 \le \Omega(N)$ when $3 \nmid N$, $\Omega(N) \ge 88$, or $|L_2| \ge 2$ (`exists_componentIndex_cardFactors_add_five_le_of_two_twoModThreeLarge`), `near_full_componentIndex_caps_twoModThreeLarge` ($\Omega \le 59, \omega \le 23$ at $|L_2| = 1$), `three_free_sixthPowerFree_forces_147_largeSources`, and `odd_perfect_wave4_master_profile`.
4. **`OreHarmonic` Finiteness Boundary, Fifth-Power-Free $\omega \ge 4$, & Restrained Exponents (`OddPerfect/HarmonicFinite.lean`, `OddPerfect/HarmonicSupportFinite.lean`, `OddPerfect/HarmonicCubeFree.lean`, `OddPerfect/HarmonicBoundedExp.lean`, `OddPerfect/HarmonicRange.lean`, `OddPerfect/HarmonicSmooth.lean`, `OddPerfect/RestrainedExponents.lean`)**:
   - Kernel-checked **`odd_oreHarmonic_four_le_primeFactors_of_fifthPowerFree`** ($\omega(N) \ge 4$ for all fifth-power-free and fourth-power-free odd harmonic numbers), `HarmonicRange`/`HarmonicSmooth` exclusions, unconditional **`8 ≤ v₃(N)`** when `largeSources N q = ∅` (`eight_le_three_exponent_of_largeSources_empty`), Ochem–Zelinsky restrained bounds (`14 ≤ v_q + v_{r₀}` for $3 \nmid N, |L| \le 1$), and `finite_of_bounded_nonSquare_exponents`.
5. **Exceptional Euler Branch $I = \ell t^2$ Unconditional $10^{740} < N$ & Reciprocity Profile (`OddPerfect/DrisRegimes.lean`, `OddPerfect/EulerExceptionalObstruction.lean`, `OddPerfect/ExceptionalBlockSquare.lean`, `OddPerfect/ExceptionalBranchClosure.lean`)**:
   - Eliminated small odd $w$ at $d = 17$ (`15 ∣ w`, `65760 ≤ w`) via $(q^{17}+1)/(q+1) = 17 z^2$ and $q + 1 = 34 w^2$, proving **`exceptional_index_size_gt_ten_pow_740` ($10^{740} < N$ unconditionally across ALL $a > 1$ on $I = \ell t^2$)** alongside $J(d \mid \ell) = 1$ and odd-target parity across $m$ (`exceptional_euler_full_reciprocity_and_source_parity`).
