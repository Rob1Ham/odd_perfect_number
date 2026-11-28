module

public import OddPerfect.Euler
public import OddPerfect.AcquaahKonyagin
public import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Factorial and Stirling Support Obstruction for Odd Perfect Numbers

Every set of odd primes `S` satisfies `2 * S.card + 1 ≤ S.max'` and
`2 ^ S.card * S.card.factorial < ∏ p ∈ S, p`. Combining this with Euler's form
and the Acquaah–Konyagin bound `q ^ 3 < 3 * N` yields `rad ^ 2 ≤ q * N` and
`rad ^ 6 < 3 * N ^ 4`, which via Stirling's lower bound produces the superlinear
support obstruction `6 * ω * (log (2 * ω) - 1) < log 3 + 4 * log N`.
-/

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Any nonempty finite set `S` of odd primes has `max' ≥ 2 * S.card + 1` and
`2 ^ S.card * S.card ! < ∏ p ∈ S, p`. -/
theorem two_pow_mul_factorial_lt_prod_odd_primes {S : Finset ℕ}
    (hne : S.Nonempty) (hodd : ∀ p ∈ S, p.Prime ∧ Odd p) :
    2 * S.card + 1 ≤ S.max' hne ∧
    2 ^ S.card * S.card.factorial < ∏ p ∈ S, p := by
  suffices h : ∀ n : ℕ, ∀ (T : Finset ℕ) (hneT : T.Nonempty),
      T.card = n → (∀ p ∈ T, p.Prime ∧ Odd p) →
      2 * T.card + 1 ≤ T.max' hneT ∧ 2 ^ T.card * T.card.factorial < ∏ p ∈ T, p from
    h S.card S hne rfl hodd
  intro n
  induction n with
  | zero =>
    intro T hneT hcard _
    exfalso
    have := hneT.card_pos
    omega
  | succ k ih =>
    intro T hneT hcard hoddT
    by_cases hk : k = 0
    · subst hk
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
      obtain ⟨hp, ho⟩ := hoddT p (mem_singleton_self p)
      have hp2 := hp.two_le
      have hp3 : 3 ≤ p := by
        obtain ⟨m, hm⟩ := ho
        omega
      simp only [card_singleton, max'_singleton, prod_singleton, Nat.factorial_one]
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      set M := T.max' hneT
      have hM_mem : M ∈ T := Finset.max'_mem T hneT
      set T' := T.erase M
      have hcard' : T'.card = k := by
        have := Finset.card_erase_add_one hM_mem
        dsimp only [T']
        omega
      have hne' : T'.Nonempty := Finset.card_pos.mp (by omega)
      have hodd' : ∀ p ∈ T', p.Prime ∧ Odd p :=
        fun p hp => hoddT p (Finset.mem_of_mem_erase hp)
      obtain ⟨ih1, ih2⟩ := ih T' hne' hcard' hodd'
      set M' := T'.max' hne'
      have hM'_mem' : M' ∈ T' := Finset.max'_mem T' hne'
      have hM'_mem : M' ∈ T := Finset.mem_of_mem_erase hM'_mem'
      have hM'_ne : M' ≠ M := Finset.ne_of_mem_erase hM'_mem'
      have hM'_lt : M' < M := lt_of_le_of_ne (Finset.le_max' T M' hM'_mem) hM'_ne
      have hM_odd : Odd M := (hoddT M hM_mem).2
      have hM'_odd : Odd M' := (hoddT M' hM'_mem).2
      have hM_ge : M' + 2 ≤ M := by
        obtain ⟨a, ha⟩ := hM_odd
        obtain ⟨b, hb⟩ := hM'_odd
        omega
      have h1 : 2 * T.card + 1 ≤ M := by omega
      have hprod : M * ∏ p ∈ T', p = ∏ p ∈ T, p :=
        Finset.mul_prod_erase T (fun p => p) hM_mem
      have h2 : 2 ^ T.card * T.card.factorial < ∏ p ∈ T, p := by
        rw [hcard, pow_succ', Nat.factorial_succ]
        have hmul_eq : 2 * 2 ^ k * ((k + 1) * k.factorial) =
            (2 * (k + 1)) * (2 ^ k * k.factorial) := by ring
        rw [hmul_eq, ← hprod]
        have h2k_lt_M : 2 * (k + 1) < M := by omega
        have hpos2 : 0 < 2 ^ k * k.factorial := by positivity
        rw [hcard'] at ih2
        calc (2 * (k + 1)) * (2 ^ k * k.factorial)
            < M * (2 ^ k * k.factorial) := Nat.mul_lt_mul_of_pos_right h2k_lt_M hpos2
          _ < M * ∏ p ∈ T', p := Nat.mul_lt_mul_of_pos_left ih2 (by omega)
      exact ⟨h1, h2⟩

/-- For an odd perfect number `N = q ^ a * m ^ 2` in Euler form, the radical
`rad = ∏ p ∈ N.primeFactors, p` satisfies `2 ^ ω * ω! < rad`, `rad ^ 2 ≤ q * N`,
and `rad ^ 6 < 3 * N ^ 4`. -/
theorem odd_perfect_radical_sq_le_euler_mul_and_pow_six_lt {N q a m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (ha : 0 < a)
    (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) :
    let rad := ∏ p ∈ N.primeFactors, p
    2 ^ N.primeFactors.card * N.primeFactors.card.factorial < rad ∧
    rad ^ 2 ≤ q * N ∧
    rad ^ 6 < 3 * N ^ 4 := by
  intro rad
  let _ := hqm
  have hNpos : 0 < N := hN.2
  have hq_dvd : q ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_left (dvd_pow_self q ha.ne') _
  have hq_mem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, hNpos.ne'⟩
  have hne : N.primeFactors.Nonempty := ⟨q, hq_mem⟩
  have hodd : ∀ p ∈ N.primeFactors, p.Prime ∧ Odd p := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)⟩
  have h1 : 2 ^ N.primeFactors.card * N.primeFactors.card.factorial < rad :=
    (two_pow_mul_factorial_lt_prod_odd_primes hne hodd).2
  let R' := ∏ p ∈ N.primeFactors.erase q, p
  have hrad_eq : q * R' = rad := Finset.mul_prod_erase N.primeFactors (fun p => p) hq_mem
  have hR'_dvd_m : R' ∣ m := by
    apply Finset.prod_primes_dvd m
    · intro p hp
      exact Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
    · intro p hp
      have hp_ne : p ≠ q := Finset.ne_of_mem_erase hp
      have hp_mem : p ∈ N.primeFactors := Finset.mem_of_mem_erase hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hp_dvd_N : p ∣ N := Nat.dvd_of_mem_primeFactors hp_mem
      rw [hform] at hp_dvd_N
      have hcop : Nat.Coprime p (q ^ a) :=
        (hp_prime.coprime_iff_not_dvd.mpr fun h =>
          hp_ne ((Nat.prime_dvd_prime_iff_eq hp_prime hq).mp h)).pow_right a
      exact hp_prime.dvd_of_dvd_pow (hcop.dvd_of_dvd_mul_left hp_dvd_N)
  have hm_ne : m ≠ 0 := by
    intro hm0
    rw [hm0, zero_pow two_ne_zero, mul_zero] at hform
    omega
  have hR'_le_m : R' ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm_ne) hR'_dvd_m
  have hq_le_qa : q ≤ q ^ a := Nat.le_self_pow ha.ne' q
  have hqR2 : q * R' ^ 2 ≤ N := by
    calc q * R' ^ 2 ≤ q ^ a * m ^ 2 := Nat.mul_le_mul hq_le_qa (Nat.pow_le_pow_left hR'_le_m 2)
      _ = N := hform.symm
  have hrad2 : rad ^ 2 ≤ q * N := by
    calc rad ^ 2 = (q * R') ^ 2 := by rw [hrad_eq]
      _ = q * (q * R' ^ 2) := by ring
      _ ≤ q * N := Nat.mul_le_mul_left q hqR2
  have hcube : q ^ 3 < 3 * N := prime_cube_lt_three_mul hN ho hq_mem
  have hN3pos : 0 < N ^ 3 := pow_pos hNpos 3
  have hrad6 : rad ^ 6 < 3 * N ^ 4 := by
    calc rad ^ 6 = (rad ^ 2) ^ 3 := by ring
      _ ≤ (q * N) ^ 3 := Nat.pow_le_pow_left hrad2 3
      _ = q ^ 3 * N ^ 3 := by ring
      _ < (3 * N) * N ^ 3 := Nat.mul_lt_mul_of_pos_right hcube hN3pos
      _ = 3 * N ^ 4 := by ring
  exact ⟨h1, hrad2, hrad6⟩

/-- Stirling superlinear support obstruction for odd perfect numbers:
`ω * (log (2 * ω) - 1) < log rad` and `6 * ω * (log (2 * ω) - 1) < log 3 + 4 * log N`. -/
theorem odd_perfect_stirling_superlinear_log_bound {N : ℕ} (ho : Odd N) (hN : N.Perfect) :
    let ω : ℝ := (N.primeFactors.card : ℝ)
    let rad := ∏ p ∈ N.primeFactors, p
    ω * (Real.log (2 * ω) - 1) < Real.log (rad : ℝ) ∧
    6 * ω * (Real.log (2 * ω) - 1) < Real.log 3 + 4 * Real.log (N : ℝ) := by
  intro ω rad
  obtain ⟨q, a, m, hq, _, ha4, hqm, hform⟩ := euler_form ho hN
  have ha : 0 < a := by omega
  obtain ⟨h1, _, h3⟩ := odd_perfect_radical_sq_le_euler_mul_and_pow_six_lt ho hN hq ha hqm hform
  have hNpos : 0 < N := hN.2
  have hq_dvd : q ∣ N := by
    rw [hform]
    exact dvd_mul_of_dvd_left (dvd_pow_self q ha.ne') _
  have hq_mem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, hNpos.ne'⟩
  have hk_pos : 0 < N.primeFactors.card := Finset.card_pos.mpr ⟨q, hq_mem⟩
  have hω_pos : (0 : ℝ) < ω := Nat.cast_pos.mpr hk_pos
  have hstirling : ω * Real.log ω - ω ≤ Real.log (N.primeFactors.card.factorial : ℝ) := by
    rw [← Real.sum_log_eq_log_factorial]
    exact Real.le_sum_log_nat N.primeFactors.card
  have h2k_pos : (0 : ℝ) < ((2 ^ N.primeFactors.card * N.primeFactors.card.factorial : ℕ) : ℝ) := by
    positivity
  have hlog_lt1 : Real.log ((2 ^ N.primeFactors.card * N.primeFactors.card.factorial : ℕ) : ℝ) <
      Real.log (rad : ℝ) :=
    Real.log_lt_log h2k_pos (Nat.cast_lt.mpr h1)
  have hlog_mul_2ω : Real.log (2 * ω) = Real.log 2 + Real.log ω :=
    Real.log_mul (by norm_num) hω_pos.ne'
  have hlog_eq : Real.log ((2 ^ N.primeFactors.card * N.primeFactors.card.factorial : ℕ) : ℝ) =
      ω * Real.log 2 + Real.log (N.primeFactors.card.factorial : ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hbound1 : ω * (Real.log (2 * ω) - 1) < Real.log (rad : ℝ) := by
    rw [hlog_mul_2ω]
    linarith
  have hrad_pos : 0 < rad := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hrad6_pos : (0 : ℝ) < ((rad ^ 6 : ℕ) : ℝ) := by positivity
  have hlog_lt2 : Real.log ((rad ^ 6 : ℕ) : ℝ) < Real.log ((3 * N ^ 4 : ℕ) : ℝ) :=
    Real.log_lt_log hrad6_pos (Nat.cast_lt.mpr h3)
  have hN_pos_real : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hlog_rad6 : Real.log ((rad ^ 6 : ℕ) : ℝ) = 6 * Real.log (rad : ℝ) := by
    push_cast
    rw [Real.log_pow]
    norm_num
  have hlog_3N4 : Real.log ((3 * N ^ 4 : ℕ) : ℝ) = Real.log 3 + 4 * Real.log (N : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hbound2 : 6 * ω * (Real.log (2 * ω) - 1) < Real.log 3 + 4 * Real.log (N : ℝ) := by
    linarith
  exact ⟨hbound1, hbound2⟩

end OddPerfect
