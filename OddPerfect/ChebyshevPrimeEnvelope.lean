module

public import OddPerfect.GlobalLogSlopePinch
public import OddPerfect.TotientOrderTower
public import OddPerfect.EvenIndexPrimorialObstruction
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Chebyshev Prime-Counting, Primorial, and `lcmUpto` Envelopes
(`OddPerfect.ChebyshevPrimeEnvelope`)

Connects `Mathlib.NumberTheory.Chebyshev` (`theta`, `psi`, `pi_le_log4_mul_div`, `pi_ge_of_four_le`,
`psi_ge_of_seven_le`, `psi_le_const_mul_self`) and `Mathlib.NumberTheory.PrimeCounting`
(`Nat.primesLE`, `Nat.primeCounting`) with `OddPerfect` support, least-prime, and even-index
primorial bounds:

1. `odd_perfect_support_chebyshev_and_pi_bounds`:
   Bounds `ω(N) + 1 ≤ π(P_max)` and `2 * rad(N) ≤ primorial P_max`, yielding the Chebyshev
   `π` upper bound and `log 2 + log (rad(N)) ≤ θ(P_max) ≤ log 4 * P_max`.
2. `odd_perfect_minFac_primeCounting_pinch`:
   Establishes the disjoint prime-counting gap `ω(N) + π(N.minFac - 1) ≤ π(P_max)`, and for
   `5 ≤ N.minFac` couples `Chebyshev.pi_ge_of_four_le` with `omega_gt_least_prime_mul_log_two`.
3. `chebyshev_psi_lcmUpto_two_sided_bounds`:
   Packages `n * log 2 ≤ log (Nat.lcmUpto n) ≤ (log 4 + 4) * n` for `7 ≤ n`.
4. `even_index_log_P_L_le_chebyshev_theta`:
   Lifts `even_index_P_L_le_two_mul_sixteen_pow` to `2 * P_L ≤ primorial (2 * e₀ + 1)` and
   `log 2 + log P_L ≤ θ(2 * e₀ + 1) ≤ log 4 * (2 * e₀ + 1)`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

private lemma odd_perfect_primeFactors_nonempty {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    N.primeFactors.Nonempty :=
  Finset.card_pos.mp (by have := five_le_distinct_prime_factor_count ho hN; omega)

private lemma odd_perfect_maxPrime_ge_three {N : ℕ} (ho : Odd N)
    (hne : N.primeFactors.Nonempty) :
    3 ≤ N.primeFactors.max' hne := by
  set P_max := N.primeFactors.max' hne
  have hmem : P_max ∈ N.primeFactors := Finset.max'_mem N.primeFactors hne
  have hp : P_max.Prime := Nat.prime_of_mem_primeFactors hmem
  have hdvd : P_max ∣ N := Nat.dvd_of_mem_primeFactors hmem
  have hodd : Odd P_max := ho.of_dvd_nat hdvd
  have h2 : 2 ≤ P_max := hp.two_le
  have hne2 : P_max ≠ 2 := fun h => hodd.not_two_dvd_nat (h ▸ dvd_rfl)
  omega

/-- For any odd perfect number `N`, `insert 2 N.primeFactors ⊆ Nat.primesLE P_max`, yielding the
prime-counting upper bound via `Chebyshev.pi_le_log4_mul_div` and the radical–primorial–Chebyshev
`theta` envelope `log 2 + log (rad(N)) ≤ θ(P_max) ≤ log 4 * P_max`. -/
theorem odd_perfect_support_chebyshev_and_pi_bounds {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ hne : N.primeFactors.Nonempty,
      let P_max := N.primeFactors.max' hne
      let rad := ∏ p ∈ N.primeFactors, p
      N.primeFactors.card + 1 ≤ Nat.primeCounting P_max ∧
        ((N.primeFactors.card + 1 : ℕ) : ℝ) ≤
          Real.log 4 * (P_max : ℝ) / Real.log (Real.sqrt (P_max : ℝ)) +
            Real.sqrt (P_max : ℝ) ∧
        2 * rad ≤ primorial P_max ∧
        (Real.log 2 + Real.log (rad : ℝ) ≤ Chebyshev.theta (P_max : ℝ) ∧
          Chebyshev.theta (P_max : ℝ) ≤ Real.log 4 * (P_max : ℝ)) := by
  have hne : N.primeFactors.Nonempty := odd_perfect_primeFactors_nonempty ho hN
  refine ⟨hne, ?_⟩
  dsimp only
  set P_max := N.primeFactors.max' hne
  set rad := ∏ p ∈ N.primeFactors, p
  have hP3 : 3 ≤ P_max := odd_perfect_maxPrime_ge_three ho hne
  have h2_not_mem : 2 ∉ N.primeFactors := by
    intro hmem
    exact ho.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)
  have hsub : insert 2 N.primeFactors ⊆ Nat.primesLE P_max := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hmem
    · exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    · exact Nat.mem_primesLE.mpr
        ⟨Finset.le_max' N.primeFactors p hmem, Nat.prime_of_mem_primeFactors hmem⟩
  have hpi_le : N.primeFactors.card + 1 ≤ Nat.primeCounting P_max := by
    calc
      N.primeFactors.card + 1 = (insert 2 N.primeFactors).card :=
        (Finset.card_insert_of_notMem h2_not_mem).symm
      _ ≤ (Nat.primesLE P_max).card := Finset.card_le_card hsub
      _ = Nat.primeCounting P_max := Nat.primesLE_card_eq_primeCounting P_max
  have hP1_real : (1 : ℝ) < (P_max : ℝ) := by exact_mod_cast (by omega : 1 < P_max)
  have hpi_real :
      ((N.primeFactors.card + 1 : ℕ) : ℝ) ≤
        Real.log 4 * (P_max : ℝ) / Real.log (Real.sqrt (P_max : ℝ)) +
          Real.sqrt (P_max : ℝ) := by
    have h1 : ((N.primeFactors.card + 1 : ℕ) : ℝ) ≤ (Nat.primeCounting P_max : ℝ) := by
      exact_mod_cast hpi_le
    have h2 := Chebyshev.pi_le_log4_mul_div hP1_real
    rw [Nat.floor_natCast] at h2
    exact h1.trans h2
  have hrad_le_prim : 2 * rad ≤ primorial P_max := by
    calc
      2 * rad = ∏ p ∈ insert 2 N.primeFactors, p :=
        (Finset.prod_insert (f := fun x => x) h2_not_mem).symm
      _ ≤ ∏ p ∈ Nat.primesLE P_max, p :=
        Finset.prod_le_prod_of_subset_of_one_le hsub fun p hp _ =>
          (Nat.prime_of_mem_primesLE hp).one_le
      _ = primorial P_max := (primorial_eq_prod_primesLE P_max).symm
  have hrad_pos : 0 < rad :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hrad_real_pos : (0 : ℝ) < (rad : ℝ) := by exact_mod_cast hrad_pos
  have hlog_le_theta : Real.log 2 + Real.log (rad : ℝ) ≤ Chebyshev.theta (P_max : ℝ) := by
    rw [← Real.log_mul (by norm_num) hrad_real_pos.ne']
    have hmul_le : (2 : ℝ) * (rad : ℝ) ≤ (primorial P_max : ℝ) := by
      exact_mod_cast hrad_le_prim
    have hlog_le : Real.log ((2 : ℝ) * (rad : ℝ)) ≤ Real.log (primorial P_max : ℝ) :=
      Real.log_le_log (by positivity) hmul_le
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    exact hlog_le
  have htheta_le : Chebyshev.theta (P_max : ℝ) ≤ Real.log 4 * (P_max : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  exact ⟨hpi_le, hpi_real, hrad_le_prim, hlog_le_theta, htheta_le⟩

/-- Disjoint prime-counting gap between the support of `N` and primes `< N.minFac`,
together with the `5 ≤ N.minFac` (`¬ 3 ∣ N`) analytic lower bound coupling
`Chebyshev.pi_ge_of_four_le` and `omega_gt_least_prime_mul_log_two`. -/
theorem odd_perfect_minFac_primeCounting_pinch {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    ∃ hne : N.primeFactors.Nonempty,
      let P_max := N.primeFactors.max' hne
      Disjoint N.primeFactors (Nat.primesLE (N.minFac - 1)) ∧
        N.primeFactors ∪ Nat.primesLE (N.minFac - 1) ⊆ Nat.primesLE P_max ∧
        N.primeFactors.card + Nat.primeCounting (N.minFac - 1) ≤ Nat.primeCounting P_max ∧
        (5 ≤ N.minFac →
          ((N.minFac : ℝ) - 1) * Real.log 2 +
            ((N.minFac - 1 : ℕ) : ℝ) * Real.log 2 / Real.log ((N.minFac - 1 : ℕ) : ℝ) <
              (Nat.primeCounting P_max : ℝ)) := by
  have hne : N.primeFactors.Nonempty := odd_perfect_primeFactors_nonempty ho hN
  refine ⟨hne, ?_⟩
  dsimp only
  set P_max := N.primeFactors.max' hne
  have hN1 : N ≠ 1 := by
    rintro rfl
    have := five_le_distinct_prime_factor_count ho hN
    simp at this
  have hmin_prime : N.minFac.Prime := Nat.minFac_prime hN1
  have hmin_mem : N.minFac ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hmin_prime, Nat.minFac_dvd N, hN.2.ne'⟩
  have hmin_le : ∀ s ∈ N.primeFactors, N.minFac ≤ s := fun s hs =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hs).two_le
      (Nat.dvd_of_mem_primeFactors hs)
  have hmin_le_Pmax : N.minFac ≤ P_max := Finset.le_max' N.primeFactors N.minFac hmin_mem
  have hdisj : Disjoint N.primeFactors (Nat.primesLE (N.minFac - 1)) := by
    rw [Finset.disjoint_left]
    intro p hpN hpLE
    have hge : N.minFac ≤ p := hmin_le p hpN
    have hle : p ≤ N.minFac - 1 := Nat.le_of_mem_primesLE hpLE
    have hpos : 0 < N.minFac := hmin_prime.pos
    omega
  have hunion_sub : N.primeFactors ∪ Nat.primesLE (N.minFac - 1) ⊆ Nat.primesLE P_max := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpN | hpLE
    · exact Nat.mem_primesLE.mpr
        ⟨Finset.le_max' N.primeFactors p hpN, Nat.prime_of_mem_primeFactors hpN⟩
    · have hp_le : p ≤ N.minFac - 1 := Nat.le_of_mem_primesLE hpLE
      have hp_prime : p.Prime := Nat.prime_of_mem_primesLE hpLE
      exact Nat.mem_primesLE.mpr ⟨by omega, hp_prime⟩
  have hgap : N.primeFactors.card + Nat.primeCounting (N.minFac - 1) ≤ Nat.primeCounting P_max := by
    calc
      N.primeFactors.card + Nat.primeCounting (N.minFac - 1)
          = N.primeFactors.card + (Nat.primesLE (N.minFac - 1)).card := by
            rw [Nat.primesLE_card_eq_primeCounting]
      _ = (N.primeFactors ∪ Nat.primesLE (N.minFac - 1)).card :=
            (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Nat.primesLE P_max).card := Finset.card_le_card hunion_sub
      _ = Nat.primeCounting P_max := Nat.primesLE_card_eq_primeCounting P_max
  refine ⟨hdisj, hunion_sub, hgap, fun h5 => ?_⟩
  have h4 : 4 ≤ N.minFac - 1 := by omega
  have hpi_ge := Chebyshev.pi_ge_of_four_le h4
  have homega := omega_gt_least_prime_mul_log_two ho hN hmin_mem hmin_le
  have hgap_real :
      (N.primeFactors.card : ℝ) + (Nat.primeCounting (N.minFac - 1) : ℝ) ≤
        (Nat.primeCounting P_max : ℝ) := by
    exact_mod_cast hgap
  linarith

/-- Two-sided Chebyshev `ψ` / `lcmUpto` envelope for all `7 ≤ n`. -/
theorem chebyshev_psi_lcmUpto_two_sided_bounds {n : ℕ} (hn : 7 ≤ n) :
    (n : ℝ) * Real.log 2 ≤ Real.log (Nat.lcmUpto n : ℝ) ∧
      Real.log (Nat.lcmUpto n : ℝ) ≤ (Real.log 4 + 4) * (n : ℝ) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto n]
  exact ⟨Chebyshev.psi_ge_of_seven_le hn, Chebyshev.psi_le_const_mul_self (by positivity)⟩

/-- Lifts `even_index_P_L_le_two_mul_sixteen_pow` to the primorial bound `2 * P_L ≤ primorial (2 * e₀ + 1)`
and the Chebyshev `θ` envelope `log 2 + log P_L ≤ θ(2 * e₀ + 1) ≤ log 4 * (2 * e₀ + 1)`. -/
theorem even_index_log_P_L_le_chebyshev_theta {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
    let S₁ := s.primeFactors.filter (v · = 1)
    let P_L := ∏ r ∈ S₁, (2 * s.factorization r + 1)
    ∃ hne : S₁.Nonempty,
      let e₀ := s.factorization (S₁.min' hne)
      2 * P_L ≤ primorial (2 * e₀ + 1) ∧
        Real.log 2 + Real.log (P_L : ℝ) ≤ Chebyshev.theta ((2 * e₀ + 1 : ℕ) : ℝ) ∧
        Chebyshev.theta ((2 * e₀ + 1 : ℕ) : ℝ) ≤ Real.log 4 * ((2 * e₀ + 1 : ℕ) : ℝ) := by
  intro v S₁ P_L
  obtain ⟨hne, hbounds⟩ := even_index_P_L_le_two_mul_sixteen_pow hp hpo hs hu hσq hplus hσs
  refine ⟨hne, ?_⟩
  dsimp only
  set e₀ := s.factorization (S₁.min' hne)
  obtain ⟨he₀_ge21, _, hPL_le_Podd, _⟩ := hbounds hne
  let P_odd := (Finset.Icc 3 (2 * e₀ + 1)).filter Nat.Prime
  have h2_not_mem : 2 ∉ P_odd := by
    intro hmem
    have h3 : 3 ≤ 2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
    omega
  have hsub_primesLE : insert 2 P_odd ⊆ Nat.primesLE (2 * e₀ + 1) := by
    intro q' hq'
    rcases Finset.mem_insert.mp hq' with rfl | hmem
    · have he21 : 21 ≤ e₀ := he₀_ge21
      exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    · obtain ⟨hIcc, hqp⟩ := Finset.mem_filter.mp hmem
      exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hIcc).2, hqp⟩
  have h2_mul_PL_le_prim : 2 * P_L ≤ primorial (2 * e₀ + 1) := by
    calc
      2 * P_L ≤ 2 * ∏ q' ∈ P_odd, q' := Nat.mul_le_mul_left 2 hPL_le_Podd
      _ = ∏ q' ∈ insert 2 P_odd, q' := (Finset.prod_insert (f := fun x => x) h2_not_mem).symm
      _ ≤ ∏ q' ∈ Nat.primesLE (2 * e₀ + 1), q' :=
        Finset.prod_le_prod_of_subset_of_one_le hsub_primesLE fun q' hq' _ =>
          (Nat.prime_of_mem_primesLE hq').one_le
      _ = primorial (2 * e₀ + 1) := (primorial_eq_prod_primesLE (2 * e₀ + 1)).symm
  have hPL_pos : 0 < P_L := Finset.prod_pos fun r _ => Nat.succ_pos _
  have hPL_real_pos : (0 : ℝ) < (P_L : ℝ) := by exact_mod_cast hPL_pos
  have hlog_le_theta :
      Real.log 2 + Real.log (P_L : ℝ) ≤ Chebyshev.theta ((2 * e₀ + 1 : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num) hPL_real_pos.ne']
    have hmul_le : (2 : ℝ) * (P_L : ℝ) ≤ (primorial (2 * e₀ + 1) : ℝ) := by
      exact_mod_cast h2_mul_PL_le_prim
    have hlog_le : Real.log ((2 : ℝ) * (P_L : ℝ)) ≤ Real.log (primorial (2 * e₀ + 1) : ℝ) :=
      Real.log_le_log (by positivity) hmul_le
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    exact hlog_le
  have htheta_le :
      Chebyshev.theta ((2 * e₀ + 1 : ℕ) : ℝ) ≤ Real.log 4 * ((2 * e₀ + 1 : ℕ) : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (by positivity)
  exact ⟨h2_mul_PL_le_prim, hlog_le_theta, htheta_le⟩

end OddPerfect
