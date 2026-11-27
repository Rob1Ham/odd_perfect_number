module

public import OddPerfect.TothPrimeObstruction
public import OddPerfect.Reciprocal
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Structural Split Characterization and Linear Euler Prime-Source Isolation

This module characterizes when an odd coprime Tóth pair admits a non-absorbing
coprime split, and applies the unsplit criterion to isolate the unique prime-power
source of the Euler prime `q` in the linear Euler branch `N = q * m ^ 2`.
-/

public section

namespace OddPerfect

open ArithmeticFunction Finset

private theorem sigma_one_mul (a b : ℕ) (h : a.Coprime b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

private theorem sigma_one_sq_val {p n s : ℕ} (hp : p.Prime) (hn : n = p ^ 2)
    (hs : 1 + p + p ^ 2 = s) : sigma 1 n = s := by
  rw [hn, sigma_one_apply_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  exact hs

/-- Concrete witness showing Descartes's spoof cofactor `9018009 = 49 * 184041`
admits a coprime split in which neither block's divisor sum divides `σ(9018009) / 22021 = 819`. -/
theorem descartes_toth_split_witness :
    TothPair 9018009 22021 ∧
    9018009 = 49 * 184041 ∧
    Nat.Coprime 49 184041 ∧
    ¬ sigma 1 49 ∣ sigma 1 9018009 / 22021 ∧
    ¬ sigma 1 184041 ∣ sigma 1 9018009 / 22021 ∧
    Nat.gcd 22021 (sigma 1 49) = 19 := by
  have hpair : TothPair 9018009 22021 :=
    ⟨descartes_singleCompositeSpoof.odd_left, by norm_num, descartes_singleCompositeSpoof.balance⟩
  have h49 : sigma 1 49 = 57 := sigma_one_sq_val (p := 7) (by decide) (by norm_num) (by norm_num)
  have h9 : sigma 1 9 = 13 := sigma_one_sq_val (p := 3) (by decide) (by norm_num) (by norm_num)
  have h121 : sigma 1 121 = 133 :=
    sigma_one_sq_val (p := 11) (by decide) (by norm_num) (by norm_num)
  have h169 : sigma 1 169 = 183 :=
    sigma_one_sq_val (p := 13) (by decide) (by norm_num) (by norm_num)
  have h20449 : sigma 1 20449 = 24339 :=
    (congrArg (sigma 1) (by norm_num : 20449 = 121 * 169)).trans <|
      (sigma_one_mul 121 169 (by decide)).trans <|
        (congrArg₂ (· * ·) h121 h169).trans (by norm_num)
  have h184041 : sigma 1 184041 = 316407 :=
    (congrArg (sigma 1) (by norm_num : 184041 = 9 * 20449)).trans <|
      (sigma_one_mul 9 20449 (by decide)).trans <|
        (congrArg₂ (· * ·) h9 h20449).trans (by norm_num)
  have hsig : sigma 1 9018009 = 18035199 :=
    (congrArg (sigma 1) (by norm_num : 9018009 = 49 * 184041)).trans <|
      (sigma_one_mul 49 184041 (by decide)).trans <|
        (congrArg₂ (· * ·) h49 h184041).trans (by norm_num)
  have hdiv : sigma 1 9018009 / 22021 = 819 :=
    (congrArg (· / 22021) hsig).trans (by norm_num)
  refine ⟨hpair, by norm_num, by decide, ?_, ?_, ?_⟩
  · exact fun hd => (by norm_num : ¬ 57 ∣ 819) ((congrArg₂ (· ∣ ·) h49 hdiv).mp hd)
  · exact fun hd => (by norm_num : ¬ 316407 ∣ 819) ((congrArg₂ (· ∣ ·) h184041 hdiv).mp hd)
  · exact (congrArg (Nat.gcd 22021) h49).trans (by decide : Nat.gcd 22021 57 = 19)

/-- For an odd coprime Tóth pair with `1 < x`, the deficient divisor `σ(n) / x`
is coprime to `x` since it divides `n`. -/
theorem TothPair.coprime_index {n x : ℕ} (h : TothPair n x)
    (hx : Odd x) (h1 : 1 < x) (hc : n.Coprime x) :
    (sigma 1 n / x).Coprime x := by
  obtain ⟨d, t, hd, hnt, _⟩ := h.deficientDivisor hx h1
  have hsig : sigma 1 n = x * d := by
    have hmul : (sigma 1 n + d) * x = (2 * n) * x := congrArg (· * x) hd.2
    rw [add_mul, mul_assoc, ← h.2.2, mul_add, mul_one] at hmul
    exact (Nat.add_left_cancel hmul).symm.trans (Nat.mul_comm d x)
  rw [hsig, Nat.mul_div_cancel_left d h.2.1]
  exact hc.coprime_dvd_left ⟨t, hnt⟩

/-- In any coprime factorization `n = a * b` of an odd coprime Tóth pair, `σ(a)` divides
the deficient divisor `σ(n) / x` if and only if `σ(a)` is coprime to `x`. -/
theorem tothPair_sigma_dvd_index_iff_coprime {n x a b : ℕ} (h : TothPair n x)
    (hx : Odd x) (h1 : 1 < x) (hc : n.Coprime x) (hn : n = a * b) (hab : a.Coprime b) :
    sigma 1 a ∣ sigma 1 n / x ↔ (sigma 1 a).Coprime x := by
  have hidx := h.coprime_index hx h1 hc
  have hsplit := h.sigma_split_eq hx h1 hn hab
  constructor
  · intro hd
    exact hidx.coprime_dvd_left hd
  · intro hac
    exact hac.dvd_of_dvd_mul_left (hsplit ▸ dvd_mul_right _ _)

/-- If two distinct prime-power components of `n` both share a nontrivial factor with `x`,
then isolating the first component yields a coprime split `n = ordProj[p₁] n * ordCompl[p₁] n`
where neither block's divisor sum divides `σ(n) / x`, forcing `x` to be composite. -/
theorem tothPair_split_of_two_component_sources {n x p₁ p₂ : ℕ}
    (h : TothPair n x) (hx : Odd x) (h1 : 1 < x) (hc : n.Coprime x)
    (hp₁ : p₁ ∈ n.primeFactors) (hp₂ : p₂ ∈ n.primeFactors) (hne : p₁ ≠ p₂)
    (hnc₁ : ¬ (sigma 1 (ordProj[p₁] n)).Coprime x)
    (hnc₂ : ¬ (sigma 1 (ordProj[p₂] n)).Coprime x) :
    n = ordProj[p₁] n * ordCompl[p₁] n ∧
    (ordProj[p₁] n).Coprime (ordCompl[p₁] n) ∧
    ¬ sigma 1 (ordProj[p₁] n) ∣ sigma 1 n / x ∧
    ¬ sigma 1 (ordCompl[p₁] n) ∣ sigma 1 n / x ∧
    1 < x.gcd (sigma 1 (ordProj[p₁] n)) ∧
    x.gcd (sigma 1 (ordProj[p₁] n)) < x ∧
    x.gcd (sigma 1 (ordProj[p₁] n)) ∣ x ∧
    ¬ x.Prime := by
  have hn0 : n ≠ 0 := h.1.pos.ne'
  have hprime₁ : p₁.Prime := Nat.prime_of_mem_primeFactors hp₁
  have hprime₂ : p₂.Prime := Nat.prime_of_mem_primeFactors hp₂
  have hn : n = ordProj[p₁] n * ordCompl[p₁] n := (Nat.ordProj_mul_ordCompl_eq_self n p₁).symm
  have hab : (ordProj[p₁] n).Coprime (ordCompl[p₁] n) :=
    (Nat.coprime_ordCompl hprime₁ hn0).pow_left _
  have hndvd₁ : ¬ sigma 1 (ordProj[p₁] n) ∣ sigma 1 n / x :=
    mt (tothPair_sigma_dvd_index_iff_coprime h hx h1 hc hn hab).mp hnc₁
  have hb0 : ordCompl[p₁] n ≠ 0 := (Nat.ordCompl_pos p₁ hn0).ne'
  have hproj_b : ordProj[p₂] (ordCompl[p₁] n) = ordProj[p₂] n := by
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne hne.symm]
  have hsig_dvd : sigma 1 (ordProj[p₂] n) ∣ sigma 1 (ordCompl[p₁] n) := by
    have hbcop : (ordProj[p₂] (ordCompl[p₁] n)).Coprime (ordCompl[p₂] (ordCompl[p₁] n)) :=
      (Nat.coprime_ordCompl hprime₂ hb0).pow_left _
    have hsig_b : sigma 1 (ordCompl[p₁] n) =
        sigma 1 (ordProj[p₂] n) * sigma 1 (ordCompl[p₂] (ordCompl[p₁] n)) := by
      calc
        sigma 1 (ordCompl[p₁] n)
            = sigma 1 (ordProj[p₂] (ordCompl[p₁] n) * ordCompl[p₂] (ordCompl[p₁] n)) :=
            congrArg (sigma 1) (Nat.ordProj_mul_ordCompl_eq_self (ordCompl[p₁] n) p₂).symm
        _ = sigma 1 (ordProj[p₂] (ordCompl[p₁] n)) * sigma 1 (ordCompl[p₂] (ordCompl[p₁] n)) :=
            isMultiplicative_sigma.map_mul_of_coprime hbcop
        _ = sigma 1 (ordProj[p₂] n) * sigma 1 (ordCompl[p₂] (ordCompl[p₁] n)) := by
            rw [hproj_b]
    exact hsig_b ▸ dvd_mul_right _ _
  have hnc_b : ¬ (sigma 1 (ordCompl[p₁] n)).Coprime x :=
    fun hcb => hnc₂ (hcb.coprime_dvd_left hsig_dvd)
  have hndvd₂ : ¬ sigma 1 (ordCompl[p₁] n) ∣ sigma 1 n / x :=
    mt (tothPair_sigma_dvd_index_iff_coprime h hx h1 hc
      (hn.trans (mul_comm _ _)) hab.symm).mp hnc_b
  obtain ⟨hlo, hhi, hd⟩ := h.proper_factor_of_sigma_split hx h1 hn hab hndvd₁ hndvd₂
  have hnp : ¬ x.Prime := by
    intro hxp
    rcases hxp.eq_one_or_self_of_dvd _ hd with he | he <;> omega
  exact ⟨hn, hab, hndvd₁, hndvd₂, hlo, hhi, hd, hnp⟩

/-- An odd coprime Tóth pair has no non-absorbing coprime split if and only if a unique
prime-power component of `n` absorbs the entire multiplier `x` in its divisor sum while
the complementary divisor sum divides `σ(n) / x`. -/
theorem tothPair_unsplit_iff_single_component_absorbs_multiplier {n x : ℕ}
    (h : TothPair n x) (hx : Odd x) (h1 : 1 < x) (hc : n.Coprime x) :
    (∀ a b, n = a * b → a.Coprime b → sigma 1 a ∣ sigma 1 n / x ∨ sigma 1 b ∣ sigma 1 n / x) ↔
    ∃! r₀, r₀ ∈ n.primeFactors ∧ x ∣ sigma 1 (ordProj[r₀] n) ∧
      sigma 1 (ordCompl[r₀] n) ∣ sigma 1 n / x := by
  have hn0 : n ≠ 0 := h.1.pos.ne'
  constructor
  · intro hunsplit
    have hsig_prod : ∀ m : ℕ, m ≠ 0 → sigma 1 m = ∏ p ∈ m.primeFactors, sigma 1 (ordProj[p] m) := by
      intro m hm0
      rw [isMultiplicative_sigma.multiplicative_factorization _ hm0]
      exact Finset.prod_congr m.support_factorization fun _ _ => rfl
    have hex : ∃ r₀ ∈ n.primeFactors, ¬ (sigma 1 (ordProj[r₀] n)).Coprime x := by
      by_contra! hall
      have hcop_sig : (sigma 1 n).Coprime x := by
        rw [hsig_prod n hn0]
        exact Nat.Coprime.prod_left hall
      have hxdvd : x ∣ sigma 1 n := by
        have hs := h.sigma_split_eq hx h1 (mul_one n).symm (Nat.coprime_one_right n)
        rw [sigma_one 1, mul_one] at hs
        exact ⟨sigma 1 n / x, hs⟩
      have hx1 : x ∣ 1 := hcop_sig.symm.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hxdvd
      exact h1.ne' (Nat.dvd_one.mp hx1)
    obtain ⟨r₀, hr₀, hnc₀⟩ := hex
    have huniq_nc : ∀ r₁ ∈ n.primeFactors, ¬ (sigma 1 (ordProj[r₁] n)).Coprime x → r₁ = r₀ := by
      intro r₁ hr₁ hnc₁
      by_contra hne
      have hsplit := tothPair_split_of_two_component_sources h hx h1 hc hr₀ hr₁ (Ne.symm hne) hnc₀ hnc₁
      rcases hunsplit (ordProj[r₀] n) (ordCompl[r₀] n) hsplit.1 hsplit.2.1 with hdv | hdv
      · exact hsplit.2.2.1 hdv
      · exact hsplit.2.2.2.1 hdv
    let b := ordCompl[r₀] n
    have hb0 : b ≠ 0 := (Nat.ordCompl_pos r₀ hn0).ne'
    have hprime₀ : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
    have hbcop : (sigma 1 b).Coprime x := by
      rw [hsig_prod b hb0]
      refine Nat.Coprime.prod_left fun p hp => ?_
      have hpn : p ∈ n.primeFactors := Nat.primeFactors_mono (Nat.ordCompl_dvd n r₀) hn0 hp
      have hp_dvd_b : p ∣ b := Nat.dvd_of_mem_primeFactors hp
      have hp_ne : p ≠ r₀ := by
        rintro rfl
        exact Nat.not_dvd_ordCompl hprime₀ hn0 hp_dvd_b
      have hproj_eq : ordProj[p] b = ordProj[p] n := by
        dsimp [b]
        rw [Nat.factorization_ordCompl, Finsupp.erase_ne hp_ne]
      rw [hproj_eq]
      by_contra hncp
      exact hp_ne (huniq_nc p hpn hncp)
    have hn_split : n = ordProj[r₀] n * b := (Nat.ordProj_mul_ordCompl_eq_self n r₀).symm
    have hab : (ordProj[r₀] n).Coprime b := (Nat.coprime_ordCompl hprime₀ hn0).pow_left _
    have hcompl_dvd : sigma 1 b ∣ sigma 1 n / x :=
      (tothPair_sigma_dvd_index_iff_coprime h hx h1 hc
        (hn_split.trans (mul_comm _ _)) hab.symm).mpr hbcop
    have hxdvd_proj : x ∣ sigma 1 (ordProj[r₀] n) := by
      have hsplit := h.sigma_split_eq hx h1 hn_split hab
      exact hbcop.symm.dvd_of_dvd_mul_right (hsplit.symm ▸ dvd_mul_right _ _)
    refine ⟨r₀, ⟨hr₀, hxdvd_proj, hcompl_dvd⟩, ?_⟩
    rintro r₁ ⟨hr₁, hxd₁, _⟩
    apply huniq_nc r₁ hr₁
    intro hcop₁
    exact h1.ne' (Nat.dvd_one.mp (hcop₁.symm.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hxd₁))
  · rintro ⟨r₀, ⟨hr₀, _, hcomp⟩, _⟩ a b hn hab
    have hr₀p : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀
    have hr₀_dvd : r₀ ∣ n := Nat.dvd_of_mem_primeFactors hr₀
    have aux : ∀ u v, n = u * v → u.Coprime v → r₀ ∣ u → sigma 1 v ∣ sigma 1 n / x := by
      intro u v huv hcuv hru
      have hrnv : ¬ r₀ ∣ v := fun hrv =>
        hr₀p.not_dvd_one (hcuv.gcd_eq_one ▸ Nat.dvd_gcd hru hrv)
      obtain ⟨c, hc_eq⟩ := Nat.dvd_ordCompl_of_dvd_not_dvd (huv ▸ dvd_mul_left v u) hrnv
      have hv0 : 0 < v := Nat.pos_of_ne_zero fun hv => by simp [hv] at huv; exact hn0 huv
      have hcu : ordProj[r₀] n * c = u := by
        apply Nat.mul_right_cancel hv0
        calc
          ordProj[r₀] n * c * v = ordProj[r₀] n * (v * c) := by ring
          _ = ordProj[r₀] n * ordCompl[r₀] n := by rw [← hc_eq]
          _ = n := Nat.ordProj_mul_ordCompl_eq_self n r₀
          _ = u * v := huv
      have hvc : v.Coprime c := hcuv.symm.coprime_dvd_right ⟨ordProj[r₀] n, by rw [mul_comm, hcu]⟩
      have hsig_v : sigma 1 v ∣ sigma 1 (ordCompl[r₀] n) := by
        rw [hc_eq, isMultiplicative_sigma.map_mul_of_coprime hvc]
        exact dvd_mul_right _ _
      exact hsig_v.trans hcomp
    rcases hr₀p.dvd_mul.mp (hn ▸ hr₀_dvd) with hra | hrb
    · exact Or.inr (aux a b hn hab hra)
    · exact Or.inl (aux b a (hn.trans (mul_comm _ _)) hab.symm hrb)

/-- In the linear Euler branch `N = q * m ^ 2`, the Euler prime `q` divides `σ(m ^ 2)` to exact
power `1`, originates from a unique prime-power component `r₀ ^ (2 * v_{r₀}(m))` (with exact
`q`-adic valuation `1`), the complementary divisor sum divides `σ(m ^ 2) / q`, and
`2 * q < 3 * r₀ ^ (2 * v_{r₀}(m))`. -/
theorem linear_euler_unique_q_source_and_bound {N q m : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hq : q.Prime) (hqm : ¬ q ∣ m) (hform : N = q * m ^ 2) :
    (sigma 1 (m ^ 2)).factorization q = 1 ∧
    ∃ r₀ ∈ m.primeFactors,
      q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) ∧
      (sigma 1 (r₀ ^ (2 * m.factorization r₀))).factorization q = 1 ∧
      sigma 1 (ordCompl[r₀] (m ^ 2)) ∣ sigma 1 (m ^ 2) / q ∧
      2 * q < 3 * r₀ ^ (2 * m.factorization r₀) ∧
      ∀ r₁ ∈ m.primeFactors, q ∣ sigma 1 (r₁ ^ (2 * m.factorization r₁)) → r₁ = r₀ := by
  have hqodd : Odd q := ho.of_dvd_nat (hform ▸ dvd_mul_right q (m ^ 2))
  have hm2odd : Odd (m ^ 2) := ho.of_dvd_nat (hform ▸ dvd_mul_left (m ^ 2) q)
  have hmodd : Odd m :=
    ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left (m ^ 2) q))
  have hm0 : m ≠ 0 := hmodd.pos.ne'
  have hm20 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hqm2 : ¬ q ∣ m ^ 2 := fun h => hqm (hq.dvd_of_dvd_pow h)
  have hc : (m ^ 2).Coprime q := (hq.coprime_iff_not_dvd.mpr hqm2).symm
  have hperf : (m ^ 2 * q).Perfect := by rwa [mul_comm, ← hform]
  have hpair : TothPair (m ^ 2) q := tothPair_of_linear_euler hm2odd hq hc hperf
  have hform1 : N = q ^ 1 * m ^ 2 := by simpa only [pow_one] using hform
  obtain ⟨i, hi_pos, hsig_eq, hi_mul, _⟩ := exists_component_index hN hq hform1 hqm2
  have hqni : ¬ q ∣ i := by
    intro hqi
    have hq2m : q ∣ 2 * m ^ 2 := hi_mul ▸ dvd_mul_of_dvd_right hqi _
    rcases hq.dvd_mul.mp hq2m with hq2 | hqm2'
    · rcases Nat.prime_two.eq_one_or_self_of_dvd q hq2 with rfl | rfl
      · exact hq.ne_one rfl
      · exact hqodd.not_two_dvd_nat dvd_rfl
    · exact hqm2 hqm2'
  have hfact_m2 : (sigma 1 (m ^ 2)).factorization q = 1 := by
    rw [hsig_eq, pow_one, Nat.factorization_mul hq.ne_zero hi_pos.ne', Finsupp.add_apply,
      hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqni, add_zero]
  have hunsplit : ∀ a b, m ^ 2 = a * b → a.Coprime b →
      sigma 1 a ∣ sigma 1 (m ^ 2) / q ∨ sigma 1 b ∣ sigma 1 (m ^ 2) / q :=
    fun a b hm hab => linear_euler_sigma_split ho hN hq hqm hform hm hab
  obtain ⟨r₀, ⟨hr₀_mem, hq_dvd_proj, hcompl_dvd⟩, _⟩ :=
    (tothPair_unsplit_iff_single_component_absorbs_multiplier hpair hqodd hq.one_lt hc).mp hunsplit
  have hm2_pf : (m ^ 2).primeFactors = m.primeFactors := Nat.primeFactors_pow m (by decide : 2 ≠ 0)
  have hr₀_m : r₀ ∈ m.primeFactors := hm2_pf ▸ hr₀_mem
  have hproj_eq : ∀ r, ordProj[r] (m ^ 2) = r ^ (2 * m.factorization r) := fun r => by
    rw [pow_two, Nat.factorization_mul hm0 hm0, Finsupp.add_apply, ← two_mul]
  have hq_dvd_r0 : q ∣ sigma 1 (r₀ ^ (2 * m.factorization r₀)) := hproj_eq r₀ ▸ hq_dvd_proj
  have hr₀_prime : r₀.Prime := Nat.prime_of_mem_primeFactors hr₀_m
  have hfact_r0 : (sigma 1 (r₀ ^ (2 * m.factorization r₀))).factorization q = 1 := by
    have hsplit_sig : sigma 1 (m ^ 2) =
        sigma 1 (ordProj[r₀] (m ^ 2)) * sigma 1 (ordCompl[r₀] (m ^ 2)) := by
      have hcop_r0 : (ordProj[r₀] (m ^ 2)).Coprime (ordCompl[r₀] (m ^ 2)) :=
        (Nat.coprime_ordCompl hr₀_prime hm20).pow_left _
      rw [← isMultiplicative_sigma.map_mul_of_coprime hcop_r0,
        Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) r₀]
    have hsig_dvd : sigma 1 (ordProj[r₀] (m ^ 2)) ∣ sigma 1 (m ^ 2) :=
      hsplit_sig ▸ dvd_mul_right _ _
    have hle : (sigma 1 (ordProj[r₀] (m ^ 2))).factorization q ≤ (sigma 1 (m ^ 2)).factorization q :=
      Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd
        (sigma_pos 1 (ordProj[r₀] (m ^ 2)) (Nat.ordProj_pos (m ^ 2) r₀).ne').ne'
        (sigma_pos 1 (m ^ 2) hm20).ne').mpr hsig_dvd) q
    have hge : 1 ≤ (sigma 1 (ordProj[r₀] (m ^ 2))).factorization q :=
      (hq.dvd_iff_one_le_factorization
        (sigma_pos 1 (ordProj[r₀] (m ^ 2)) (Nat.ordProj_pos (m ^ 2) r₀).ne').ne').mp hq_dvd_proj
    rw [← hproj_eq r₀]
    omega
  have hbound : 2 * q < 3 * r₀ ^ (2 * m.factorization r₀) := by
    have hr₀_odd : Odd r₀ := hmodd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr₀_m)
    have hr₀_ge3 : 3 ≤ r₀ := by
      obtain ⟨t, ht⟩ := hr₀_odd
      have := hr₀_prime.two_le
      omega
    have hgeom : sigma 1 (r₀ ^ (2 * m.factorization r₀)) * (r₀ - 1) + 1 =
        r₀ ^ (2 * m.factorization r₀ + 1) := by
      rw [sigma_one_apply_prime_pow hr₀_prime]
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r₀)] using
        geom_sum_mul_add (r₀ - 1) (2 * m.factorization r₀ + 1)
    have hsig_lt : 2 * sigma 1 (r₀ ^ (2 * m.factorization r₀)) < 3 * r₀ ^ (2 * m.factorization r₀) := by
      apply (Nat.mul_lt_mul_right (by omega : 0 < r₀ - 1)).mp
      calc
        (2 * sigma 1 (r₀ ^ (2 * m.factorization r₀))) * (r₀ - 1)
            = 2 * (sigma 1 (r₀ ^ (2 * m.factorization r₀)) * (r₀ - 1)) := by ring
        _ < 2 * (r₀ ^ (2 * m.factorization r₀ + 1)) :=
            Nat.mul_lt_mul_of_pos_left (by omega) (by decide : 0 < 2)
        _ = r₀ ^ (2 * m.factorization r₀) * (2 * r₀) := by rw [pow_succ]; ring
        _ ≤ r₀ ^ (2 * m.factorization r₀) * (3 * (r₀ - 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ = (3 * r₀ ^ (2 * m.factorization r₀)) * (r₀ - 1) := by ring
    have hq_le : q ≤ sigma 1 (r₀ ^ (2 * m.factorization r₀)) :=
      Nat.le_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hr₀_prime.ne_zero)) hq_dvd_r0
    exact (Nat.mul_le_mul_left 2 hq_le).trans_lt hsig_lt
  have huniq : ∀ r₁ ∈ m.primeFactors, q ∣ sigma 1 (r₁ ^ (2 * m.factorization r₁)) → r₁ = r₀ := by
    intro r₁ hr₁_m hq_dvd_r1
    have hr₁_mem : r₁ ∈ (m ^ 2).primeFactors := hm2_pf.symm ▸ hr₁_m
    have hq_dvd_proj1 : q ∣ sigma 1 (ordProj[r₁] (m ^ 2)) := (hproj_eq r₁).symm ▸ hq_dvd_r1
    have hnc₀ : ¬ (sigma 1 (ordProj[r₀] (m ^ 2))).Coprime q := by
      intro hcop
      exact hq.ne_one (Nat.dvd_one.mp (hcop.symm.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hq_dvd_proj))
    have hnc₁ : ¬ (sigma 1 (ordProj[r₁] (m ^ 2))).Coprime q := by
      intro hcop
      exact hq.ne_one (Nat.dvd_one.mp (hcop.symm.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hq_dvd_proj1))
    by_contra hne
    exact (tothPair_split_of_two_component_sources hpair hqodd hq.one_lt hc
      hr₀_mem hr₁_mem (Ne.symm hne) hnc₀ hnc₁).2.2.2.2.2.2.2 hq
  exact ⟨hfact_m2, r₀, hr₀_m, hq_dvd_r0, hfact_r0, hcompl_dvd, hbound, huniq⟩

end OddPerfect
