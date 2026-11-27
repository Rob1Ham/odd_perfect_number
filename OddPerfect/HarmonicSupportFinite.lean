module

public import OddPerfect.HarmonicFinite
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace OddPerfect

open ArithmeticFunction Finset

private lemma lt_sigma_one_of_one_lt' {a : ℕ} (ha : 1 < a) : a < sigma 1 a := by
  rw [sigma_one_apply]
  have hsub : ({1, a} : Finset ℕ) ⊆ a.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hsum := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  rw [Finset.sum_pair ha.ne] at hsum
  omega

private lemma sigma_prime_pow_mod_self_aux {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) % p = 1 := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ', pow_zero, add_comm]
  have hd : p ∣ ∑ x ∈ range a, p ^ (x + 1) := by
    apply Finset.dvd_sum
    intro x _
    rw [pow_succ']
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hd
  rw [ht, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hp.one_lt

private lemma pow_succ_le_pow_mul_two_pow (E d : ℕ) :
    (E + 1) ^ d ≤ d ^ d * 2 ^ E := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
    exact Nat.one_le_pow _ _ (by decide)
  · let m := E / d + 1
    have hmod : E % d < d := Nat.mod_lt E hd
    have hdiv : E = d * (E / d) + E % d := (Nat.div_add_mod E d).symm
    have hEm : E + 1 ≤ d * m := by
      dsimp [m]
      nlinarith
    have hm2 : m ≤ 2 ^ (E / d) := by
      dsimp [m]
      have := Nat.lt_two_pow_self (n := E / d)
      omega
    have hdm : d * (E / d) ≤ E := Nat.mul_div_le E d
    calc (E + 1) ^ d
        ≤ (d * m) ^ d := Nat.pow_le_pow_left hEm d
      _ = d ^ d * m ^ d := mul_pow d m d
      _ ≤ d ^ d * (2 ^ (E / d)) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm2 d)
      _ = d ^ d * 2 ^ (E / d * d) := by rw [← pow_mul]
      _ = d ^ d * 2 ^ (d * (E / d)) := by rw [mul_comm (E / d) d]
      _ ≤ d ^ d * 2 ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hdm)

private lemma exists_exp_cap (C d : ℕ) :
    ∃ E₀, ∀ E ≥ E₀, C * (E + 1) ^ d < 3 ^ E := by
  let A := C * d ^ d + 1
  have hA : 1 ≤ A := by omega
  refine ⟨2 * A, fun E hE => ?_⟩
  let r := E - 2 * A
  have hEr : E = 2 * A + r := by omega
  have h1 : C * (E + 1) ^ d ≤ C * (d ^ d * 2 ^ E) :=
    Nat.mul_le_mul_left C (pow_succ_le_pow_mul_two_pow E d)
  have h2 : C * (d ^ d * 2 ^ E) < A * 2 ^ E := by
    rw [← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right (by dsimp [A]; omega) (pow_pos (by decide) E)
  have hA2 : A ≤ 2 ^ A := (Nat.lt_two_pow_self (n := A)).le
  have h89 : 8 ^ A < 9 ^ A := Nat.pow_lt_pow_left (by decide) (by omega)
  have h23 : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by decide) r
  have h3 : A * 2 ^ E < 3 ^ E := by
    rw [hEr]
    calc A * 2 ^ (2 * A + r)
        = A * ((2 ^ 2) ^ A * 2 ^ r) := by rw [pow_add, pow_mul]
      _ = (A * 4 ^ A) * 2 ^ r := by norm_num; ring
      _ ≤ (2 ^ A * 4 ^ A) * 2 ^ r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hA2)
      _ = 8 ^ A * 2 ^ r := by rw [← mul_pow]; norm_num
      _ < 9 ^ A * 2 ^ r := Nat.mul_lt_mul_of_pos_right h89 (pow_pos (by decide) r)
      _ ≤ 9 ^ A * 3 ^ r := Nat.mul_le_mul_left _ h23
      _ = 3 ^ (2 * A + r) := by
          rw [show (9 : ℕ) = 3 ^ 2 by decide, ← pow_mul, ← pow_add]
  exact (h1.trans_lt h2).trans h3

/-- Only finitely many odd Ore harmonic numbers have at most `k` distinct prime
factors and all prime exponents bounded by `E`. -/
theorem finite_odd_oreHarmonic_of_bounded_prime_count_and_exponent (k E : ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ OreHarmonic N ∧ N.primeFactors.card ≤ k ∧ ∀ p, N.factorization p ≤ E} := by
  refine (finite_odd_oreHarmonic_of_bounded_divisor_count ((E + 1) ^ k)).subset ?_
  rintro N ⟨ho, hh, hk, hE⟩
  refine ⟨ho, hh, ?_⟩
  rw [Nat.card_divisors ho.pos.ne']
  calc ∏ p ∈ N.primeFactors, (N.factorization p + 1)
      ≤ ∏ _p ∈ N.primeFactors, (E + 1) :=
        Finset.prod_le_prod fun p _ => Nat.succ_le_succ (hE p)
    _ = (E + 1) ^ N.primeFactors.card := by simp
    _ ≤ (E + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos E) hk

/-- Kanold's Fixed-Prime-Support Finiteness: only finitely many odd Ore harmonic
numbers have all prime factors inside a fixed finite set `S`. -/
theorem finite_odd_oreHarmonic_of_primeFactors_subset (S : Finset ℕ) :
    Set.Finite {N : ℕ | Odd N ∧ OreHarmonic N ∧ N.primeFactors ⊆ S} := by
  let S' := S.filter (fun q => q.Prime ∧ Odd q)
  let k := S'.card
  let B_max := S'.sup id + 1
  let C := (B_max ^ B_max) ^ k
  obtain ⟨E₀, hE₀⟩ := exists_exp_cap C (2 * k)
  refine (finite_odd_oreHarmonic_of_bounded_prime_count_and_exponent k E₀).subset ?_
  rintro N ⟨ho, hh, hsub⟩
  have hsub' : N.primeFactors ⊆ S' := by
    intro p hp
    exact mem_filter.mpr ⟨hsub hp, Nat.prime_of_mem_primeFactors hp,
      ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)⟩
  have hk : N.primeFactors.card ≤ k := Finset.card_le_card hsub'
  have hPF_ne : N.primeFactors.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h1 : N = 1 := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization ho.pos.ne']
      rw [hne, Finset.prod_empty]
    have := hh.1
    omega
  let E := N.primeFactors.sup N.factorization
  obtain ⟨p₀, hp₀_mem, hE_eq⟩ := Finset.exists_mem_eq_sup N.primeFactors hPF_ne N.factorization
  have hp₀ : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀_mem
  have hp₀_odd : Odd p₀ := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp₀_mem)
  have hp₀_3 : 3 ≤ p₀ := by
    have := hp₀.two_le
    rcases eq_or_ne p₀ 2 with rfl | hne
    · exact (hp₀_odd.not_two_dvd_nat dvd_rfl).elim
    · omega
  have hE_pos : 1 ≤ E := by
    dsimp [E]
    rw [hE_eq]
    exact hp₀.factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors hp₀_mem)
  have hE_lt : E < E₀ := by
    by_contra! hE_ge
    let M := sigma 1 (p₀ ^ E)
    have hp₀E_gt1 : 1 < p₀ ^ E := one_lt_pow₀ (by omega) (by omega)
    have hp₀E_lt_M : p₀ ^ E < M := lt_sigma_one_of_one_lt' hp₀E_gt1
    have hM_pos : 0 < M := lt_trans (pow_pos hp₀.pos E) hp₀E_lt_M
    have hM_dvd_σ : M ∣ sigma 1 N := by
      have hM_eq : M = sigma 1 (p₀ ^ N.factorization p₀) := by
        dsimp [M, E]
        rw [hE_eq]
      rw [hM_eq, isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
      exact Finset.dvd_prod_of_mem _ hp₀_mem
    have hM_dvd_Nτ : M ∣ N * N.divisors.card := hM_dvd_σ.trans hh.2
    have hτ_le : N.divisors.card ≤ (E + 1) ^ k := by
      rw [Nat.card_divisors ho.pos.ne']
      calc ∏ p ∈ N.primeFactors, (N.factorization p + 1)
          ≤ ∏ _p ∈ N.primeFactors, (E + 1) :=
            Finset.prod_le_prod fun p hp => Nat.succ_le_succ (Finset.le_sup hp)
        _ = (E + 1) ^ N.primeFactors.card := by simp
        _ ≤ (E + 1) ^ k := Nat.pow_le_pow_right (Nat.succ_pos E) hk
    let A := M.primeFactors.filter (· ∈ S')
    let B := M.primeFactors.filter (· ∉ S')
    have hM_fact : M = (∏ r ∈ A, r ^ M.factorization r) * (∏ r ∈ B, r ^ M.factorization r) := by
      have h1 := (Nat.prod_primeFactors_pow_factorization hM_pos.ne').symm
      rw [← Finset.prod_filter_mul_prod_filter_not M.primeFactors (· ∈ S') (fun r => r ^ M.factorization r)] at h1
      exact h1.symm
    have hB_dvd_M : (∏ r ∈ B, r ^ M.factorization r) ∣ M := by
      conv_rhs => rw [hM_fact]
      exact dvd_mul_left _ _
    have hB_cop_N : Nat.Coprime (∏ r ∈ B, r ^ M.factorization r) N := by
      refine Nat.Coprime.prod_left fun r hr => ?_
      have hr_mem := (mem_filter.mp hr).1
      have hr_not_S' := (mem_filter.mp hr).2
      have hr_pr := Nat.prime_of_mem_primeFactors hr_mem
      have hr_not_N : ¬ r ∣ N := fun hd =>
        hr_not_S' (hsub' (Nat.mem_primeFactors.mpr ⟨hr_pr, hd, ho.pos.ne'⟩))
      exact (hr_pr.coprime_iff_not_dvd.mpr hr_not_N).pow_left _
    have hB_dvd_τ : (∏ r ∈ B, r ^ M.factorization r) ∣ N.divisors.card :=
      hB_cop_N.dvd_of_dvd_mul_left (hB_dvd_M.trans hM_dvd_Nτ)
    have hτ_pos : 0 < N.divisors.card :=
      card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩
    have hB_le : (∏ r ∈ B, r ^ M.factorization r) ≤ (E + 1) ^ k :=
      (Nat.le_of_dvd hτ_pos hB_dvd_τ).trans hτ_le
    have hA_term_le : ∀ q ∈ A, q ^ M.factorization q ≤ B_max ^ B_max * (E + 1) := by
      intro q hqA
      have hq_mem := (mem_filter.mp hqA).1
      have hq_S' := (mem_filter.mp hqA).2
      have hq_pr : q.Prime := (mem_filter.mp hq_S').2.1
      have hq_odd : Odd q := (mem_filter.mp hq_S').2.2
      have hq_dvd_M : q ∣ M := Nat.dvd_of_mem_primeFactors hq_mem
      have hq_ne_p₀ : q ≠ p₀ := by
        rintro rfl
        have hmod := sigma_prime_pow_mod_self_aux hp₀ E
        obtain ⟨t, ht⟩ := hq_dvd_M
        dsimp [M] at ht
        rw [ht, Nat.mul_mod_right] at hmod
        omega
      have hq_3 : 3 ≤ q := by
        have := hq_pr.two_le
        rcases eq_or_ne q 2 with rfl | hne
        · exact (hq_odd.not_two_dvd_nat dvd_rfl).elim
        · omega
      let x := p₀ ^ (q - 1)
      have hx_gt1 : 1 < x := one_lt_pow₀ (by omega) (by omega)
      have hq_ndvd_p₀ : ¬ q ∣ p₀ := fun hd =>
        hq_ne_p₀ ((Nat.prime_dvd_prime_iff_eq hq_pr hp₀).mp hd)
      have hq_ndvd_x : ¬ q ∣ x := fun hd => hq_ndvd_p₀ (hq_pr.dvd_of_dvd_pow hd)
      have hq_dvd_x_sub : q ∣ x - 1 := by
        let : Fact q.Prime := ⟨hq_pr⟩
        have hp₀_ne0 : (p₀ : ZMod q) ≠ 0 := by
          intro hz
          exact hq_ndvd_p₀ ((ZMod.natCast_eq_zero_iff p₀ q).mp hz)
        have hflt : (p₀ : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hp₀_ne0
        rw [← ZMod.natCast_eq_zero_iff]
        rw [Nat.cast_sub hx_gt1.le, Nat.cast_one]
        dsimp [x]
        rw [Nat.cast_pow, hflt, sub_self]
      have hM_dvd_pow : M ∣ p₀ ^ (E + 1) - 1 := by
        have hgeom := geom_sum_mul_add (p₀ - 1) (E + 1)
        rw [Nat.sub_add_cancel hp₀.one_lt.le, ← sigma_one_apply_prime_pow hp₀] at hgeom
        refine ⟨p₀ - 1, ?_⟩
        dsimp [M]
        omega
      have hpow_dvd_x : p₀ ^ (E + 1) - 1 ∣ x ^ (E + 1) - 1 ^ (E + 1) := by
        have hdvd := Nat.sub_dvd_pow_sub_pow (p₀ ^ (E + 1)) 1 (q - 1)
        rw [one_pow, ← pow_mul, mul_comm (E + 1) (q - 1), pow_mul] at hdvd
        simpa [x] using hdvd
      have hM_dvd_xpow : M ∣ x ^ (E + 1) - 1 ^ (E + 1) := hM_dvd_pow.trans hpow_dvd_x
      have hxpow_pos : 0 < x ^ (E + 1) - 1 ^ (E + 1) := by
        rw [one_pow]
        exact Nat.sub_pos_of_lt (one_lt_pow₀ hx_gt1 (Nat.succ_ne_zero E))
      have hfact_le : M.factorization q ≤ (x ^ (E + 1) - 1 ^ (E + 1)).factorization q :=
        (Nat.factorization_le_iff_dvd hM_pos.ne' hxpow_pos.ne').mpr hM_dvd_xpow q
      have hlte : multiplicity q (x ^ (E + 1) - 1 ^ (E + 1)) =
          multiplicity q (x - 1) + multiplicity q (E + 1) := by
        let : Fact q.Prime := ⟨hq_pr⟩
        exact Nat.multiplicity_pow_sub_pow hq_odd hx_gt1 hq_dvd_x_sub hq_ndvd_x (Nat.succ_ne_zero E)
      have hfact_sum : M.factorization q ≤ (x - 1).factorization q + (E + 1).factorization q := by
        rw [Nat.factorization_def (x ^ (E + 1) - 1 ^ (E + 1)) hq_pr, hlte,
          ← Nat.factorization_def (x - 1) hq_pr, ← Nat.factorization_def (E + 1) hq_pr] at hfact_le
        exact hfact_le
      have hq1_le : q ^ (x - 1).factorization q ≤ x - 1 :=
        Nat.le_of_dvd (Nat.sub_pos_of_lt hx_gt1) (Nat.ordProj_dvd (x - 1) q)
      have hq2_le : q ^ (E + 1).factorization q ≤ E + 1 :=
        Nat.le_of_dvd (Nat.succ_pos E) (Nat.ordProj_dvd (E + 1) q)
      have hp₀_le_B : p₀ ≤ B_max := by
        have hp₀_S' : p₀ ∈ S' := hsub' hp₀_mem
        exact (Finset.le_sup (f := id) hp₀_S').trans (Nat.le_succ _)
      have hq_le_B : q - 1 ≤ B_max := by
        have : q ≤ S'.sup id := Finset.le_sup (f := id) hq_S'
        omega
      have hx_le_B : x - 1 ≤ B_max ^ B_max := by
        calc x - 1 ≤ x := Nat.sub_le x 1
          _ = p₀ ^ (q - 1) := rfl
          _ ≤ B_max ^ (q - 1) := Nat.pow_le_pow_left hp₀_le_B _
          _ ≤ B_max ^ B_max := Nat.pow_le_pow_right (by dsimp [B_max]; omega) hq_le_B
      calc q ^ M.factorization q
          ≤ q ^ ((x - 1).factorization q + (E + 1).factorization q) :=
            Nat.pow_le_pow_right hq_pr.pos hfact_sum
        _ = q ^ (x - 1).factorization q * q ^ (E + 1).factorization q := pow_add _ _ _
        _ ≤ (x - 1) * (E + 1) := Nat.mul_le_mul hq1_le hq2_le
        _ ≤ B_max ^ B_max * (E + 1) := Nat.mul_le_mul_right _ hx_le_B
    have hA_sub : A ⊆ S' := fun _ hr => (mem_filter.mp hr).2
    have hA_card : A.card ≤ k := Finset.card_le_card hA_sub
    have hA_le : (∏ r ∈ A, r ^ M.factorization r) ≤ (B_max ^ B_max * (E + 1)) ^ k := by
      calc (∏ r ∈ A, r ^ M.factorization r)
          ≤ ∏ _r ∈ A, (B_max ^ B_max * (E + 1)) := Finset.prod_le_prod hA_term_le
        _ = (B_max ^ B_max * (E + 1)) ^ A.card := by simp
        _ ≤ (B_max ^ B_max * (E + 1)) ^ k := by
            refine Nat.pow_le_pow_right ?_ hA_card
            have hB1 : 1 ≤ B_max := by dsimp [B_max]; omega
            exact mul_pos (pow_pos hB1 _) (Nat.succ_pos E)
    have hM_le : M ≤ C * (E + 1) ^ (2 * k) := by
      calc M = (∏ r ∈ A, r ^ M.factorization r) * (∏ r ∈ B, r ^ M.factorization r) := hM_fact
        _ ≤ (B_max ^ B_max * (E + 1)) ^ k * (E + 1) ^ k := Nat.mul_le_mul hA_le hB_le
        _ = (B_max ^ B_max) ^ k * ((E + 1) ^ k * (E + 1) ^ k) := by rw [mul_pow]; ring
        _ = C * (E + 1) ^ (2 * k) := by rw [← pow_add, two_mul]
    have h3_le : 3 ^ E ≤ p₀ ^ E := Nat.pow_le_pow_left hp₀_3 E
    have hcap := hE₀ E hE_ge
    omega
  refine ⟨ho, hh, hk, fun p => ?_⟩
  by_cases hp : p ∈ N.primeFactors
  · exact (Finset.le_sup hp).trans hE_lt.le
  · have h0 : N.factorization p = 0 := Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    rw [h0]
    exact Nat.zero_le _

/-- No odd Ore harmonic number has a power of two as its divisor count. -/
theorem odd_oreHarmonic_divisor_count_not_pow_two {N : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (m : ℕ) : N.divisors.card ≠ 2 ^ m := by
  intro hτ
  obtain ⟨r, hr, hro, hd⟩ := odd_prime_dvd_card_divisors_of_odd_harmonic ho hh
  rw [hτ] at hd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd)
  exact hro.not_two_dvd_nat dvd_rfl

/-- For any odd Ore harmonic number with three distinct prime factors, the largest
prime `L` dividing `τ(N)` divides `e_p + 1` for some `p ∣ N`, and forces another
prime `q ∣ N` (`q ≠ p`) satisfying `q ≡ 1 [MOD L]`. -/
theorem odd_oreHarmonic_card_three_prime_congruence {N : ℕ} (ho : Odd N) (hh : OreHarmonic N)
    (_hc : N.primeFactors.card = 3) :
    ∃ L : ℕ, L.Prime ∧ Odd L ∧ L ∣ N.divisors.card ∧
      ∃ p ∈ N.primeFactors, L ∣ N.factorization p + 1 ∧
        ∃ q ∈ N.primeFactors.erase p, L ∣ q - 1 := by
  set τ := N.divisors.card with hτ_def
  have hτ_pos : 0 < τ := card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr ho.pos.ne'⟩
  obtain ⟨r₀, hr₀, hr₀_odd, hr₀_dvd⟩ := odd_prime_dvd_card_divisors_of_odd_harmonic ho hh
  have hr₀_mem : r₀ ∈ τ.primeFactors := Nat.mem_primeFactors.mpr ⟨hr₀, hr₀_dvd, hτ_pos.ne'⟩
  let L := τ.primeFactors.max' ⟨r₀, hr₀_mem⟩
  have hL_mem : L ∈ τ.primeFactors := Finset.max'_mem _ _
  have hL : L.Prime := Nat.prime_of_mem_primeFactors hL_mem
  have hL_dvd_τ : L ∣ τ := Nat.dvd_of_mem_primeFactors hL_mem
  have hr₀_le_L : r₀ ≤ L := Finset.le_max' _ _ hr₀_mem
  have hr₀_ge3 : 3 ≤ r₀ := by
    have := hr₀.two_le
    rcases eq_or_ne r₀ 2 with rfl | hne
    · exact (hr₀_odd.not_two_dvd_nat dvd_rfl).elim
    · omega
  have hL3 : 3 ≤ L := hr₀_ge3.trans hr₀_le_L
  have hL_odd : Odd L := hL.odd_of_ne_two (by omega)
  have hmax_τ : ∀ w : ℕ, w.Prime → w ∣ τ → w ≤ L := fun w hw hwd =>
    Finset.le_max' _ w (Nat.mem_primeFactors.mpr ⟨hw, hwd, hτ_pos.ne'⟩)
  have hτ_prod : L ∣ ∏ p ∈ N.primeFactors, (N.factorization p + 1) := by
    rwa [← Nat.card_divisors ho.pos.ne']
  obtain ⟨p, hp_mem, hL_dvd_ep⟩ := (Nat.prime_iff.mp hL).dvd_finsetProd_iff _ |>.mp hτ_prod
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  obtain ⟨q, hq, hord, hq_sub⟩ := exists_prime_order_prime_pow hp.one_lt hL hL_odd 0
  simp only [zero_add, pow_one] at hord hq_sub
  have hL_lt_q : L < q := by
    have := Nat.le_of_dvd (by have := hq.one_lt; omega) hq_sub
    omega
  have hqp : q ≠ p := by
    rintro rfl
    let : Fact q.Prime := ⟨hq⟩
    rw [ZMod.natCast_self, orderOf_zero] at hord
    omega
  have hp_ne1 : (p : ZMod q) ≠ 1 := by
    let : Fact q.Prime := ⟨hq⟩
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hq_σp : q ∣ sigma 1 (p ^ N.factorization p) := by
    rw [sigma_one_apply]
    apply (dvd_sum_divisors_prime_pow_iff hp hq (N.factorization p)).mpr
    simp [hp_ne1, hord, hL_dvd_ep]
  have hq_σN : q ∣ sigma 1 N := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne']
    exact hq_σp.trans (Finset.dvd_prod_of_mem _ hp_mem)
  have hq_Nτ : q ∣ N * τ := hq_σN.trans hh.2
  have hq_ndvd_τ : ¬ q ∣ τ := fun h => (hmax_τ q hq h).not_gt hL_lt_q
  have hq_N : q ∣ N := (hq.dvd_mul.mp hq_Nτ).resolve_right hq_ndvd_τ
  have hq_erase : q ∈ N.primeFactors.erase p :=
    Finset.mem_erase.mpr ⟨hqp, Nat.mem_primeFactors.mpr ⟨hq, hq_N, ho.pos.ne'⟩⟩
  exact ⟨L, hL, hL_odd, hL_dvd_τ, p, hp_mem, hL_dvd_ep, q, hq_erase, hq_sub⟩

end OddPerfect
