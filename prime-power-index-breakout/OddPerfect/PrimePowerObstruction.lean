module

public import OddPerfect.EvenIndexRepunits
public import OddPerfect.EvenIndexHigherCongruence
public import OddPerfect.PureSigmaOrder
public import OddPerfect.PositiveHalfReturn
public import OddPerfect.OddIndexFeedback
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset
open scoped NumberTheorySymbols

/-- Coupled quadratic difference identity at an even prime-power index. -/
theorem coupled_repunit_diff_eq {q p s u : ℕ} (hp : p.Prime) (hu : 0 < u)
    (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2) :
    2 * (s - 1) * (s + 1) = p * sigma 1 (p ^ (2 * u - 1)) ∧
      2 * (s - 1) * (s + 1) = p * (p + 1) * geometricBlock (p ^ 2) u := by
  have hs : 1 ≤ s := by
    by_contra! h
    rw [show s = 0 by omega] at hplus
    omega
  have hdiff : 2 * (s - 1) * (s + 1) + 2 = 2 * s ^ 2 := by
    zify [hs]
    ring
  have hq : q = 1 + p * sigma 1 (p ^ (2 * u - 1)) := by
    rw [← hσq, sigma_one_apply_prime_pow hp, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', ← Finset.mul_sum]
    rw [sigma_one_apply_prime_pow hp, show 2 * u - 1 + 1 = 2 * u by omega]
    ring
  have hblock : sigma 1 (p ^ (2 * u - 1)) = (p + 1) * geometricBlock (p ^ 2) u := by
    rw [sigma_one_apply_prime_pow hp, show 2 * u - 1 + 1 = 2 * u by omega]
    change geometricBlock p (2 * u) = _
    rw [geometricBlock_mul, show geometricBlock p 2 = p + 1 by
      simp [geometricBlock, Finset.sum_range_succ, Nat.add_comm]]
  refine ⟨by omega, ?_⟩
  rw [show 2 * (s - 1) * (s + 1) = p * sigma 1 (p ^ (2 * u - 1)) by omega, hblock]
  ring

/-- The index prime `p` divides `s - 1` exactly once when `i = p ^ (2 * u)`. -/
theorem even_index_exact_p_dvd_cofactor_pred {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : 0 < s) (hu : 0 < u) (hσq : sigma 1 (p ^ (2 * u)) = q)
    (hplus : q + 1 = 2 * s ^ 2) (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    p ∣ s - 1 ∧ ¬ p ^ 2 ∣ s - 1 ∧ p.Coprime (s + 1) ∧ 4 * ((s - 1) / p) ≡ 1 [MOD p] := by
  have hsmod := even_index_cofactor_mod_index_prime hp hpo hs hσq hplus hσs
  have hpdvd : p ∣ s - 1 := (Nat.modEq_iff_dvd' hs).mp hsmod.symm
  set k := (s - 1) / p
  have hsk : s - 1 = p * k := (Nat.mul_div_cancel' hpdvd).symm
  have hs1 : s + 1 = 2 + p * k := by omega
  have hdiff := (coupled_repunit_diff_eq hp hu hσq hplus).1
  rw [hsk, hs1] at hdiff
  have hcancel : 2 * k * (2 + p * k) = sigma 1 (p ^ (2 * u - 1)) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc p * (2 * k * (2 + p * k)) = 2 * (p * k) * (2 + p * k) := by ring
      _ = p * sigma 1 (p ^ (2 * u - 1)) := hdiff
  have hsig : sigma 1 (p ^ (2 * u - 1)) ≡ 1 [MOD p] := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using sigma_prime_pow_mod_self hp (2 * u - 1)
  have h2pk : 2 + p * k ≡ 2 [MOD p] := by
    simp [Nat.ModEq, Nat.add_mod]
  have h4k : 4 * k ≡ 1 [MOD p] := by
    have hmul : 4 * k ≡ 2 * k * (2 + p * k) [MOD p] := by
      simpa only [show 2 * k * 2 = 4 * k by ring] using (Nat.ModEq.refl (2 * k)).mul h2pk.symm
    exact hmul.trans (hcancel ▸ hsig)
  have hnp2 : ¬ p ^ 2 ∣ s - 1 := by
    intro hp2
    rw [hsk, pow_two] at hp2
    have hpk : p ∣ k := Nat.dvd_of_mul_dvd_mul_left hp.pos hp2
    have hd4k : p ∣ 4 * k := hpk.trans (dvd_mul_left k 4)
    have hd1 : p ∣ 1 := (h4k.dvd_iff dvd_rfl).mp hd4k
    exact hp.not_dvd_one hd1
  have hcop : p.Coprime (s + 1) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hpdiv
    rw [hs1] at hpdiv
    have hp2 : p ∣ 2 := (Nat.dvd_add_left (dvd_mul_right p k)).mp hpdiv
    exact hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2 ▸ dvd_rfl)
  exact ⟨hpdvd, hnp2, hcop, h4k⟩

/-- Two-adic exponent constraints for `p % 4 = 3` at an even prime-power index. -/
theorem even_index_exponent_two_adic_of_three_mod_four {q p s u : ℕ} (hp : p.Prime)
    (hs : Odd s) (hu : 0 < u) (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2) :
    (p % 8 = 3 → 4 ∣ u) ∧ (p % 16 = 7 → 2 ∣ u) := by
  have hq16 := one_mod_sixteen_of_twice_odd_square hs hplus
  have hs1 : 1 ≤ s := hs.pos
  have hdiff := (coupled_repunit_diff_eq hp hu hσq hplus).2
  have h16 : 16 ∣ p * (p + 1) * geometricBlock (p ^ 2) u := by
    have hqsub : 2 * (s - 1) * (s + 1) = q - 1 := by
      have : 2 * (s - 1) * (s + 1) + 2 = 2 * s ^ 2 := by zify [hs1]; ring
      omega
    rw [← hdiff, hqsub]
    omega
  constructor
  · intro hp8
    have hpo : Odd p := Nat.odd_iff.mpr (by omega)
    have hp4 : Odd ((p + 1) / 4) := Nat.odd_iff.mpr (by omega)
    have hpp1 : p + 1 = 4 * ((p + 1) / 4) := by omega
    rw [hpp1, show p * (4 * ((p + 1) / 4)) * geometricBlock (p ^ 2) u =
      4 * (p * ((p + 1) / 4) * geometricBlock (p ^ 2) u) by ring] at h16
    have hd4 : 4 ∣ p * ((p + 1) / 4) * geometricBlock (p ^ 2) u :=
      Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) h16
    have hcop : Nat.Coprime 4 (p * ((p + 1) / 4)) :=
      (Nat.coprime_two_left.mpr (hpo.mul hp4)).pow_left 2
    have hG : 4 ∣ geometricBlock (p ^ 2) u := hcop.dvd_of_dvd_mul_left hd4
    have hsq8 : p ^ 2 ≡ 1 [MOD 8] := by
      change p ^ 2 % 8 = 1
      rw [pow_two, Nat.mul_mod, hp8]
    have hmod := (geom_modEq_of_one hsq8 u).of_dvd (by decide : 4 ∣ 8)
    exact (hmod.dvd_iff dvd_rfl).mp hG
  · intro hp16
    have hpo : Odd p := Nat.odd_iff.mpr (by omega)
    have hp8 : Odd ((p + 1) / 8) := Nat.odd_iff.mpr (by omega)
    have hpp1 : p + 1 = 8 * ((p + 1) / 8) := by omega
    rw [hpp1, show p * (8 * ((p + 1) / 8)) * geometricBlock (p ^ 2) u =
      8 * (p * ((p + 1) / 8) * geometricBlock (p ^ 2) u) by ring] at h16
    have hd2 : 2 ∣ p * ((p + 1) / 8) * geometricBlock (p ^ 2) u :=
      Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 8) h16
    have hcop : Nat.Coprime 2 (p * ((p + 1) / 8)) :=
      Nat.coprime_two_left.mpr (hpo.mul hp8)
    have hG : 2 ∣ geometricBlock (p ^ 2) u := hcop.dvd_of_dvd_mul_left hd2
    have hp8' : p % 8 = 7 := by omega
    have hsq8 : p ^ 2 ≡ 1 [MOD 8] := by
      change p ^ 2 % 8 = 1
      rw [pow_two, Nat.mul_mod, hp8']
    have hmod := (geom_modEq_of_one hsq8 u).of_dvd (by decide : 2 ∣ 8)
    exact (hmod.dvd_iff dvd_rfl).mp hG

private lemma jacobi_p_r_and_r_p {q p s u r : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hσq : sigma 1 (p ^ (2 * u)) = q) (hplus : q + 1 = 2 * s ^ 2)
    (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) (hr : r ∈ s.primeFactors) :
    J((p : ℤ) | r) = 1 ∧ J((r : ℤ) | p) = 1 := by
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrs := Nat.dvd_of_mem_primeFactors hr
  have hro : Odd r := hs.of_dvd_nat hrs
  obtain ⟨β, hβo, hσr⟩ := even_index_source_odd_power hp hs hσq hplus hσs hr
  have hmod : p ^ β ≡ 1 [MOD r] := by
    rw [← hσr]
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hrp.one_lt] using
      sigma_prime_pow_mod_self hrp (2 * s.factorization r)
  have hpow1 : J((p : ℤ) | r) ^ β = 1 := by
    rw [← jacobiSym.pow_left]
    calc J((p : ℤ) ^ β | r) = J(((p ^ β : ℕ) : ℤ) | r) := by push_cast; rfl
      _ = J((1 : ℤ) | r) := by
        apply jacobiSym.mod_left'
        exact Int.natCast_modEq_iff.mpr hmod
      _ = 1 := jacobiSym.one_left r
  have hJpr : J((p : ℤ) | r) = 1 := by
    rcases jacobiSym.trichotomy (p : ℤ) r with h0 | h1 | hn1
    · rw [h0, zero_pow hβo.pos.ne'] at hpow1; norm_num at hpow1
    · exact h1
    · rw [hn1, hβo.neg_one_pow] at hpow1; norm_num at hpow1
  have hJrp : J((r : ℤ) | p) = 1 := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with hp1 | hp3
    · exact (jacobiSym.quadratic_reciprocity_one_mod_four' hro hp1).trans hJpr
    · have hr1 := even_index_sources_one_mod_four hp hp3 hs hσq hplus hσs hr
      exact (jacobiSym.quadratic_reciprocity_one_mod_four hr1 hpo).trans hJpr
  exact ⟨hJpr, hJrp⟩

/-- Jacobi reciprocity relations at an even prime-power index. -/
theorem even_index_jacobi_reciprocity {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (hs : Odd s) (hσq : sigma 1 (p ^ (2 * u)) = q)
    (hplus : q + 1 = 2 * s ^ 2) (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    J((p : ℤ) | q) = 1 ∧ J((s : ℤ) | p) = 1 ∧
      ∀ r ∈ s.primeFactors,
        J((p : ℤ) | r) = 1 ∧ J((r : ℤ) | p) = 1 ∧ J((r : ℤ) | q) = ZMod.χ₄ r := by
  have _ := hq.one_lt
  have hq16 := one_mod_sixteen_of_twice_odd_square hs hplus
  have hq4 : q % 4 = 1 := by omega
  have hqmodp : q ≡ 1 [MOD p] := by
    rw [← hσq]
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using sigma_prime_pow_mod_self hp (2 * u)
  have hJqp : J((q : ℤ) | p) = 1 := by
    rw [jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hqmodp)]
    simp only [Nat.cast_one, jacobiSym.one_left]
  have hJpq : J((p : ℤ) | q) = 1 :=
    (jacobiSym.quadratic_reciprocity_one_mod_four' hpo hq4).trans hJqp
  have hsmodp := even_index_cofactor_mod_index_prime hp hpo hs.pos hσq hplus hσs
  have hJsp : J((s : ℤ) | p) = 1 := by
    rw [jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hsmodp)]
    simp only [Nat.cast_one, jacobiSym.one_left]
  refine ⟨hJpq, hJsp, fun r hr => ?_⟩
  obtain ⟨hJpr, hJrp⟩ := jacobi_p_r_and_r_p hp hpo hs hσq hplus hσs hr
  have hrs := Nat.dvd_of_mem_primeFactors hr
  have hro : Odd r := hs.of_dvd_nat hrs
  have hrq1 : r ∣ q + 1 := hplus ▸ dvd_mul_of_dvd_right (dvd_pow hrs (by decide : 2 ≠ 0)) _
  have hqneg : (q : ℤ) ≡ -1 [ZMOD r] := by
    rw [Int.modEq_iff_dvd]
    have : ((-1 : ℤ) - q) = -((q + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, dvd_neg]
    exact Int.natCast_dvd_natCast.mpr hrq1
  have hJrq : J((r : ℤ) | q) = ZMod.χ₄ r := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hro hq4,
      jacobiSym.mod_left' hqneg, jacobiSym.at_neg_one hro]
  exact ⟨hJpr, hJrp, hJrq⟩

/-- Every cofactor component at an even prime-power index has prime length
`n = 2 * v_r(s) + 1`, coprime to `p`, equal to the order of `r` mod `p`, dividing `(p - 1) / 2`. -/
theorem even_index_cofactor_component_order_dvd_pred {q p s u r : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hs : Odd s) (hσq : sigma 1 (p ^ (2 * u)) = q)
    (hplus : q + 1 = 2 * s ^ 2) (hσs : sigma 1 (s ^ 2) = p ^ (2 * u))
    (hr : r ∈ s.primeFactors) :
    let n := 2 * s.factorization r + 1
    n.Prime ∧ ¬ p ∣ n ∧ orderOf (r : ZMod p) = n ∧ n ∣ (p - 1) / 2 := by
  let : Fact p.Prime := ⟨hp⟩
  let e := 2 * s.factorization r
  let n := e + 1
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrs := Nat.dvd_of_mem_primeFactors hr
  have hro : Odd r := hs.of_dvd_nat hrs
  have hfac : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
  have hepos : 0 < e := by dsimp [e]; omega
  have heven : Even e := ⟨s.factorization r, by dsimp [e]; ring⟩
  obtain ⟨β, hβo, hσr⟩ := even_index_source_odd_power hp hs hσq hplus hσs hr
  have hβpos : 0 < β := hβo.pos
  have hnprime : n.Prime :=
    prime_length_of_pure_even_component hrp hro hp hepos heven
      (show sigma 1 (r ^ e) ∣ p ^ β from hσr.dvd)
  have hnpdvd : ¬ p ∣ n := by
    intro hpd
    have hpn : p = n := (Nat.prime_dvd_prime_iff_eq hp hnprime).mp hpd
    have hgeom : ∑ i ∈ range p, r ^ i = p ^ β := by
      conv_lhs => rw [hpn, ← sigma_one_apply_prime_pow hrp]
      exact hσr
    have hdiv : p ∣ ∑ i ∈ range p, r ^ i := hgeom ▸ dvd_pow_self p hβpos.ne'
    have hnsq := not_sq_dvd_geom_sum hp hpo hdiv
    rw [hgeom] at hnsq
    have hβ1 : β = 1 := by
      by_contra h
      exact hnsq (pow_dvd_pow p (by omega : 2 ≤ β))
    rw [hβ1, pow_one] at hgeom
    have hlt : p < ∑ i ∈ range p, r ^ i := by
      calc p = ∑ _i ∈ range p, 1 := by simp
        _ < ∑ i ∈ range p, r ^ i := Finset.sum_lt_sum
          (fun i _ => Nat.one_le_pow i r hrp.pos)
          ⟨1, Finset.mem_range.mpr hp.one_lt, by simpa using hrp.one_lt⟩
    omega
  have hpdivσ : p ∣ sigma 1 (r ^ e) := hσr ▸ dvd_pow_self p hβpos.ne'
  rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hrp hp e] at hpdivσ
  have hrne1 : (r : ZMod p) ≠ 1 := by
    intro h1
    rw [ite_eq_left h1] at hpdivσ
    exact hnpdvd hpdivσ
  rw [ite_eq_right hrne1] at hpdivσ
  have hord : orderOf (r : ZMod p) = n :=
    (Nat.dvd_prime hnprime).mp hpdivσ |>.resolve_left (fun h => hrne1 (orderOf_eq_one_iff.mp h))
  have hsmodp := even_index_cofactor_mod_index_prime hp hpo hs.pos hσq hplus hσs
  have hps : ¬ p ∣ s := by
    intro h
    have h01 : 0 ≡ 1 [MOD p] := (h.modEq_zero_nat).symm.trans hsmodp
    exact hp.not_dvd_one ((h01.dvd_iff dvd_rfl).mp (dvd_zero p))
  have hrnz : (r : ZMod p) ≠ 0 := by
    intro h0
    exact hps (((ZMod.natCast_eq_zero_iff r p).mp h0).trans hrs)
  have hJrp : J((r : ℤ) | p) = 1 := (jacobi_p_r_and_r_p hp hpo hs hσq hplus hσs hr).2
  have hsq : IsSquare (r : ZMod p) := by
    simpa using ZMod.isSquare_of_jacobiSym_eq_one (p := p) (a := (r : ℤ)) hJrp
  obtain ⟨a, ha⟩ := hsq
  have ha0 : a ≠ 0 := fun h => hrnz (by rw [ha, h, mul_zero])
  have hpowhalf : (r : ZMod p) ^ ((p - 1) / 2) = 1 := by
    have h2 : 2 * ((p - 1) / 2) = p - 1 := by
      have := Nat.odd_iff.mp hpo
      omega
    calc (r : ZMod p) ^ ((p - 1) / 2) = (a * a) ^ ((p - 1) / 2) := by rw [ha]
      _ = (a ^ 2) ^ ((p - 1) / 2) := by rw [pow_two]
      _ = a ^ (2 * ((p - 1) / 2)) := by rw [← pow_mul]
      _ = a ^ (p - 1) := by rw [h2]
      _ = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have hdvdhalf : n ∣ (p - 1) / 2 := hord ▸ orderOf_dvd_of_pow_eq_one hpowhalf
  exact ⟨hnprime, hnpdvd, hord, hdvdhalf⟩

/-- Jacobi reciprocity and exact cyclotomic order for odd prime-power Euler indices. -/
theorem odd_index_jacobi_and_cyclotomic_order {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m ^ 2) / q ^ a = p ^ j) :
    orderOf (p : ZMod q) = j + 2 ∧ 2 * (j + 2) ∣ q - 1 ∧
      J((p : ℤ) | q) = 1 ∧ J((q : ℤ) | p) = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨_, hp8, _, hjp, _, _, _, _⟩ :=
    odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨hd, hd8, _, _, hoq, hσp⟩ :=
    odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi
  set d := (a + 1) / 2
  have hpo : Odd p := Nat.odd_iff.mpr (by omega)
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hdo : Odd d := Nat.odd_iff.mpr (by omega)
  have hqd : q ∣ sigma 1 (p ^ (j + 1)) := hσp ▸ dvd_pow_self q hd.pos.ne'
  rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hq (j + 1)] at hqd
  have hpne1 : (p : ZMod q) ≠ 1 := by
    intro h1
    rw [ite_eq_left h1] at hqd
    have hqj : q = j + 2 := (Nat.prime_dvd_prime_iff_eq hq hjp).mp hqd
    have hgeom : ∑ i ∈ range q, p ^ i = q ^ d := by
      conv_lhs => rw [hqj, ← show j + 1 + 1 = j + 2 by ring, ← sigma_one_apply_prime_pow hp]
      exact hσp
    have hdiv : q ∣ ∑ i ∈ range q, p ^ i := hgeom ▸ dvd_pow_self q hd.pos.ne'
    have hnsq := not_sq_dvd_geom_sum hq hqo hdiv
    rw [hgeom] at hnsq
    exact hnsq (pow_dvd_pow q hd.two_le)
  rw [ite_eq_right hpne1] at hqd
  have hordp : orderOf (p : ZMod q) = j + 2 :=
    (Nat.dvd_prime hjp).mp hqd |>.resolve_left (fun h => hpne1 (orderOf_eq_one_iff.mp h))
  have hqpow : (q : ZMod p) ^ d = 1 := hoq ▸ pow_orderOf_eq_one (q : ZMod p)
  have hqmodd : q ^ d ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ 1 p).mp (by simpa using hqpow)
  have hJqp_pow : J((q : ℤ) | p) ^ d = 1 := by
    rw [← jacobiSym.pow_left]
    calc J((q : ℤ) ^ d | p) = J(((q ^ d : ℕ) : ℤ) | p) := by push_cast; rfl
      _ = J((1 : ℤ) | p) := jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr hqmodd)
      _ = 1 := jacobiSym.one_left p
  have hJqp : J((q : ℤ) | p) = 1 := by
    rcases jacobiSym.trichotomy (q : ℤ) p with h0 | h1 | hn1
    · rw [h0, zero_pow hd.pos.ne'] at hJqp_pow; norm_num at hJqp_pow
    · exact h1
    · rw [hn1, hdo.neg_one_pow] at hJqp_pow; norm_num at hJqp_pow
  have hJpq : J((p : ℤ) | q) = 1 :=
    (jacobiSym.quadratic_reciprocity_one_mod_four' hpo hq4).trans hJqp
  have hsq : IsSquare (p : ZMod q) := by
    simpa using ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := (p : ℤ)) hJpq
  obtain ⟨c, hc⟩ := hsq
  have hpnz : (p : ZMod q) ≠ 0 := by
    intro h0
    have h1 : (p : ZMod q) ^ (j + 2) = 1 := hordp ▸ pow_orderOf_eq_one (p : ZMod q)
    rw [h0, zero_pow (by omega : j + 2 ≠ 0)] at h1
    exact zero_ne_one h1
  have hc0 : c ≠ 0 := fun h => hpnz (by rw [hc, h, mul_zero])
  have hpowhalf : (p : ZMod q) ^ ((q - 1) / 2) = 1 := by
    have h2 : 2 * ((q - 1) / 2) = q - 1 := by omega
    calc (p : ZMod q) ^ ((q - 1) / 2) = (c * c) ^ ((q - 1) / 2) := by rw [hc]
      _ = (c ^ 2) ^ ((q - 1) / 2) := by rw [pow_two]
      _ = c ^ (2 * ((q - 1) / 2)) := by rw [← pow_mul]
      _ = c ^ (q - 1) := by rw [h2]
      _ = 1 := ZMod.pow_card_sub_one_eq_one hc0
  have hdvdhalf : j + 2 ∣ (q - 1) / 2 := hordp ▸ orderOf_dvd_of_pow_eq_one hpowhalf
  have hdvd2 : 2 * (j + 2) ∣ q - 1 := by
    rw [show q - 1 = 2 * ((q - 1) / 2) by omega]
    exact Nat.mul_dvd_mul_left 2 hdvdhalf
  exact ⟨hordp, hdvd2, hJpq, hJqp⟩

private lemma add_pow_of_sq_eq_zero {R : Type*} [CommRing R] (a b : R) (hb : b ^ 2 = 0) :
    ∀ m : ℕ, 1 ≤ m → (a + b) ^ m = a ^ m + (m : R) * a ^ (m - 1) * b := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · have ih' := ih (by omega)
      rw [pow_succ, ih']
      simp only [Nat.add_sub_cancel]
      have hsucc : m - 1 + 1 = m := by omega
      have hpow : a * a ^ (m - 1) = a ^ m := by rw [← pow_succ', hsucc]
      push_cast
      calc (a ^ m + (m : R) * a ^ (m - 1) * b) * (a + b)
          = a ^ m * a + (a ^ m + (m : R) * (a * a ^ (m - 1))) * b + (m : R) * a ^ (m - 1) * b ^ 2 := by
            ring
        _ = a ^ (m + 1) + ((m : R) + 1) * a ^ m * b := by
            rw [hpow, hb, mul_zero, add_zero, ← pow_succ]; ring

private lemma linear_lt_even_pow {r e : ℕ} (hr : 3 ≤ r) (he : 2 ≤ e) :
    4 * e * r ≤ r ^ (2 * e) := by
  induction e, he using Nat.le_induction with
  | base =>
    have h1 : 8 ≤ r ^ 3 := by
      rw [show r ^ 3 = r * r * r by ring]
      nlinarith
    calc 4 * 2 * r = 8 * r := by ring
      _ ≤ r ^ 3 * r := Nat.mul_le_mul_right r h1
      _ = r ^ (2 * 2) := by ring
  | succ k hk ih =>
    have h2 : 2 * (k + 1) ≤ 4 * k := by omega
    have h9 : 9 ≤ r ^ 2 := by rw [pow_two]; nlinarith
    calc 4 * (k + 1) * r ≤ 2 * (4 * k * r) := by nlinarith
      _ ≤ 2 * r ^ (2 * k) := Nat.mul_le_mul_left 2 ih
      _ ≤ r ^ 2 * r ^ (2 * k) := Nat.mul_le_mul_right _ (by omega)
      _ = r ^ (2 * (k + 1)) := by ring

/-- Unconditional elimination of the multiple-power Nagell–Ljunggren branch at an
even prime-power index: `p` must have two distinct odd prime-base repunit expressions. -/
theorem even_index_forces_two_repunits {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hu : 0 < u) (hσq : sigma 1 (p ^ (2 * u)) = q)
    (hplus : q + 1 = 2 * s ^ 2) (hσs : sigma 1 (s ^ 2) = p ^ (2 * u)) :
    HasTwoOddPrimeRepunits p := by
  let R := ZMod (p ^ 2)
  let v (r : ℕ) := (sigma 1 (r ^ (2 * s.factorization r))).factorization p
  let S₁ := s.primeFactors.filter (v · = 1)
  let T := (s ^ 2).divisors.card
  obtain ⟨_, hparts⟩ := even_index_source_valuation_budget hp hs hσq hplus hσs
  have hT_prod : T = ∏ r ∈ s.primeFactors, (2 * s.factorization r + 1) := by
    dsimp [T]
    rw [Nat.card_divisors (pow_ne_zero 2 hs.pos.ne'), Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hT_pos : 1 ≤ T := by
    dsimp [T]
    exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero 2 hs.pos.ne')⟩
  have hT_cop : p.Coprime T := by
    rw [hT_prod]
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    exact hp.coprime_iff_not_dvd.mpr
      (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).2.1
  have hp2_zero : (p : R) ^ 2 = 0 := by
    change (p : ZMod (p ^ 2)) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hq_cast : (q : R) = 1 + (p : R) := by
    have hq_expand : q = 1 + p + p ^ 2 * ∑ j ∈ range (2 * u - 1), p ^ j := by
      rw [← hσq, sigma_one_apply_prime_pow hp, show 2 * u + 1 = (2 * u - 1) + 2 by omega,
        Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, pow_succ', ← Finset.mul_sum]
      ring
    have hcast := congrArg (fun n : ℕ => (n : R)) hq_expand
    push_cast at hcast
    rw [hp2_zero, zero_mul, add_zero] at hcast
    exact hcast
  have h2s2_cast : (2 : R) * (s ^ 2 : R) = 2 + (p : R) := by
    have hcast := congrArg (fun n : ℕ => (n : R)) hplus
    push_cast at hcast
    rw [hq_cast] at hcast
    linear_combination -hcast
  have hpow_T : (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T =
      (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) := by
    calc (2 : R) ^ T * ((s ^ 2 : ℕ) : R) ^ T
        = ((2 : R) * (s ^ 2 : R)) ^ T := by push_cast; ring
      _ = (2 + (p : R)) ^ T := by rw [h2s2_cast]
      _ = (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) :=
        add_pow_of_sq_eq_zero 2 (p : R) hp2_zero T hT_pos
  have hs2_prod : s ^ 2 = ∏ r ∈ s.primeFactors, r ^ (2 * s.factorization r) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (pow_ne_zero 2 hs.pos.ne')]
    rw [Nat.primeFactors_pow s (by decide : 2 ≠ 0)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hs2_pow_T : ((s ^ 2 : ℕ) : R) ^ T =
      ∏ r ∈ s.primeFactors, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T := by
    conv_lhs => rw [hs2_prod]
    push_cast
    rw [Finset.prod_pow]
  have hlocal_not : ∀ r ∈ s.primeFactors, r ∉ S₁ →
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T = 1 := by
    intro r hr hnr
    have hvne : v r ≠ 1 := fun h => hnr (Finset.mem_filter.mpr ⟨hr, h⟩)
    obtain ⟨hvo, hσr⟩ := hparts r hr
    dsimp only at hvo hσr
    change Odd (v r) at hvo
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    have hv3 : 2 ≤ v r := by have := hvo.pos; omega
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p ^ (v r) := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 := by
      rw [hrel]
      push_cast
      have hpv : (p : R) ^ v r = 0 := by
        rw [show v r = 2 + (v r - 2) by omega, pow_add, hp2_zero, zero_mul]
      rw [hpv, mul_zero, add_zero]
    obtain ⟨Q, hTQ⟩ := (Finset.dvd_prod_of_mem (fun t => 2 * s.factorization t + 1) hr).trans
      hT_prod.symm.dvd
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ ((2 * s.factorization r + 1) * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        push_cast; ring
      _ = 1 ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 := one_pow _
  have hlocal_mem : ∀ r ∈ S₁,
      let Q := ∏ t ∈ s.primeFactors.erase r, (2 * s.factorization t + 1)
      ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T =
        1 + ((2 * s.factorization r * Q * (r - 1) : ℕ) : R) * (p : R) := by
    intro r hrS Q
    obtain ⟨hr, hv1⟩ := Finset.mem_filter.mp hrS
    obtain ⟨_, hσr⟩ := hparts r hr
    dsimp only at hσr
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at hσr
    rw [hv1, pow_one] at hσr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrs := Nat.dvd_of_mem_primeFactors hr
    have hepos : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
    have hrel : r ^ (2 * s.factorization r + 1) = 1 + (r - 1) * p := by
      rw [← hσr, sigma_one_apply_prime_pow hrp]
      zify [hrp.one_le]
      have hg := geom_sum_mul (r : ℤ) (2 * s.factorization r + 1)
      linarith
    have hrcast : ((r ^ (2 * s.factorization r + 1) : ℕ) : R) = 1 + ((r - 1 : ℕ) : R) * (p : R) := by
      rw [hrel]
      push_cast
      rfl
    have hTQ : T = (2 * s.factorization r + 1) * Q := by
      rw [hT_prod]
      exact (Finset.mul_prod_erase s.primeFactors (fun t => 2 * s.factorization t + 1) hr).symm
    have hQpos : 1 ≤ Q := Finset.one_le_prod fun _ _ => by omega
    have hexp : 1 ≤ 2 * s.factorization r * Q := by nlinarith
    have hb2 : (((r - 1 : ℕ) : R) * (p : R)) ^ 2 = 0 := by
      calc (((r - 1 : ℕ) : R) * (p : R)) ^ 2 = ((r - 1 : ℕ) : R) ^ 2 * (p : R) ^ 2 := by ring
        _ = 0 := by rw [hp2_zero, mul_zero]
    calc ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T
        = ((r ^ (2 * s.factorization r) : ℕ) : R) ^ ((2 * s.factorization r + 1) * Q) := by rw [hTQ]
      _ = ((r ^ (2 * s.factorization r + 1) : ℕ) : R) ^ (2 * s.factorization r * Q) := by
        push_cast; ring
      _ = (1 + ((r - 1 : ℕ) : R) * (p : R)) ^ (2 * s.factorization r * Q) := by rw [hrcast]
      _ = 1 ^ (2 * s.factorization r * Q) +
          ((2 * s.factorization r * Q : ℕ) : R) * 1 ^ (2 * s.factorization r * Q - 1) *
            (((r - 1 : ℕ) : R) * (p : R)) :=
        add_pow_of_sq_eq_zero 1 (((r - 1 : ℕ) : R) * (p : R)) hb2 (2 * s.factorization r * Q) hexp
      _ = 1 + ((2 * s.factorization r * Q * (r - 1) : ℕ) : R) * (p : R) := by
        simp only [one_pow, mul_one, Nat.cast_mul]; ring
  have hS1_ne0 : S₁.card ≠ 0 := by
    intro h0
    have hS1_empty : S₁ = ∅ := Finset.card_eq_zero.mp h0
    have hs2_one : ((s ^ 2 : ℕ) : R) ^ T = 1 := by
      rw [hs2_pow_T]
      refine Finset.prod_eq_one fun r hr => hlocal_not r hr (by simp [hS1_empty])
    rw [hs2_one, mul_one] at hpow_T
    have hzero : ((T * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
      push_cast
      linear_combination -hpow_T
    have hdvd : p ^ 2 ∣ T * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [pow_two] at hdvd
    have hdvd1 : p ∣ T * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
    have hdvd2 : p ∣ 2 ^ (T - 1) := hT_cop.dvd_of_dvd_mul_left hdvd1
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd2
    exact hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd2 ▸ dvd_rfl)
  have hS1_ne1 : S₁.card ≠ 1 := by
    intro h1
    obtain ⟨r₀, hS1_eq⟩ := Finset.card_eq_one.mp h1
    have hr₀S₁ : r₀ ∈ S₁ := by rw [hS1_eq]; exact Finset.mem_singleton_self r₀
    obtain ⟨hr₀, hv1⟩ := Finset.mem_filter.mp hr₀S₁
    have hr₀p := Nat.prime_of_mem_primeFactors hr₀
    have hr₀s := Nat.dvd_of_mem_primeFactors hr₀
    have hr₀o : Odd r₀ := hs.of_dvd_nat hr₀s
    have hr₀_ge3 : 3 ≤ r₀ := by
      have := hr₀p.two_le
      have := Nat.odd_iff.mp hr₀o
      omega
    set e₀ := s.factorization r₀
    have he₀ : 1 ≤ e₀ := (hr₀p.dvd_iff_one_le_factorization hs.pos.ne').mp hr₀s
    set Q := ∏ t ∈ s.primeFactors.erase r₀, (2 * s.factorization t + 1)
    have hTQ : T = (2 * e₀ + 1) * Q := by
      rw [hT_prod]
      exact (Finset.mul_prod_erase s.primeFactors (fun t => 2 * s.factorization t + 1) hr₀).symm
    have hQ_cop : p.Coprime Q := hT_cop.coprime_dvd_right ⟨2 * e₀ + 1, by rw [hTQ, mul_comm]⟩
    have hs2_val : ((s ^ 2 : ℕ) : R) ^ T = 1 + ((2 * e₀ * Q * (r₀ - 1) : ℕ) : R) * (p : R) := by
      rw [hs2_pow_T, ← Finset.mul_prod_erase s.primeFactors _ hr₀]
      have hrest : (∏ r ∈ s.primeFactors.erase r₀, ((r ^ (2 * s.factorization r) : ℕ) : R) ^ T) = 1 := by
        refine Finset.prod_eq_one fun r hr => ?_
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hr
        refine hlocal_not r hmem ?_
        rw [hS1_eq, Finset.mem_singleton]
        exact hne
      rw [hrest, mul_one]
      exact hlocal_mem r₀ hr₀S₁
    rw [hs2_val] at hpow_T
    have h2T : (2 : R) ^ T = (2 : R) * (2 : R) ^ (T - 1) := by
      rw [← pow_succ', show T - 1 + 1 = T by omega]
    have hcongr : (((4 * e₀ * (r₀ - 1) * Q * 2 ^ (T - 1) * p : ℕ)) : R) =
        (((2 * e₀ + 1) * Q * 2 ^ (T - 1) * p : ℕ) : R) := by
      have hA : (2 : R) ^ T * (1 + ((2 * e₀ * Q * (r₀ - 1) : ℕ) : R) * (p : R)) =
          (2 : R) ^ T + (((4 * e₀ * (r₀ - 1) * Q * 2 ^ (T - 1) * p : ℕ)) : R) := by
        push_cast
        calc (2 : R) ^ T * (1 + (2 : R) * (e₀ : R) * (Q : R) * ((r₀ - 1 : ℕ) : R) * (p : R))
            = (2 : R) ^ T + (2 : R) * ((2 : R) * (2 : R) ^ (T - 1)) * (e₀ : R) * (Q : R) *
                ((r₀ - 1 : ℕ) : R) * (p : R) := by rw [← h2T]; ring
          _ = (2 : R) ^ T + (4 : R) * (e₀ : R) * ((r₀ - 1 : ℕ) : R) * (Q : R) *
                (2 : R) ^ (T - 1) * (p : R) := by ring
      have hB : (2 : R) ^ T + (T : R) * (2 : R) ^ (T - 1) * (p : R) =
          (2 : R) ^ T + (((2 * e₀ + 1) * Q * 2 ^ (T - 1) * p : ℕ) : R) := by
        rw [hTQ]
        push_cast
        ring
      rw [hA, hB] at hpow_T
      exact add_left_cancel hpow_T
    have hr₀_sub : 2 ≤ r₀ - 1 := by omega
    have hlt_coeff : 2 * e₀ + 1 < 4 * e₀ * (r₀ - 1) := by nlinarith
    set Δ := 4 * e₀ * (r₀ - 1) - (2 * e₀ + 1)
    have hΔ_pos : 0 < Δ := by omega
    have hΔ_eq : 4 * e₀ * (r₀ - 1) = (2 * e₀ + 1) + Δ := by omega
    have hzero : ((Δ * Q * 2 ^ (T - 1) * p : ℕ) : R) = 0 := by
      have hcast := congrArg (fun n : ℕ => (n : R)) (by
        calc Δ * Q * 2 ^ (T - 1) * p + (2 * e₀ + 1) * Q * 2 ^ (T - 1) * p
            = ((2 * e₀ + 1) + Δ) * Q * 2 ^ (T - 1) * p := by ring
          _ = 4 * e₀ * (r₀ - 1) * Q * 2 ^ (T - 1) * p := by rw [← hΔ_eq])
      push_cast at hcast hcongr ⊢
      linear_combination hcast + hcongr
    have hdvd_prod : p ^ 2 ∣ Δ * Q * 2 ^ (T - 1) * p := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    rw [pow_two] at hdvd_prod
    have hdvd1 : p ∣ Δ * Q * 2 ^ (T - 1) := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd_prod
    have hdvd2 : p ∣ Δ * Q :=
      ((Nat.coprime_two_right.mpr hpo).pow_right (T - 1)).dvd_of_dvd_mul_right hdvd1
    have hp_dvd_Δ : p ∣ Δ := hQ_cop.dvd_of_dvd_mul_right hdvd2
    have hle_p : p ≤ Δ := Nat.le_of_dvd hΔ_pos hp_dvd_Δ
    obtain ⟨_, hσr₀⟩ := hparts r₀ hr₀
    dsimp only at hσr₀
    change sigma 1 (r₀ ^ (2 * e₀)) = p ^ v r₀ at hσr₀
    rw [hv1, pow_one] at hσr₀
    have hp_gt_Δ : Δ < p := by
      rcases eq_or_ne e₀ 1 with he1 | hene1
      · have hp_val : p = 1 + r₀ + r₀ ^ 2 := by
          rw [← hσr₀, he1, mul_one, sigma_one_apply_prime_pow hr₀p]
          simp [Finset.sum_range_succ]
        have hΔ_val : Δ = 4 * r₀ - 7 := by dsimp [Δ]; rw [he1]; omega
        rw [hp_val, hΔ_val] at hle_p
        have hle_nat : 1 + r₀ + r₀ ^ 2 + 7 ≤ 4 * r₀ := by omega
        rw [pow_two] at hle_nat
        nlinarith
      · have he2 : 2 ≤ e₀ := by omega
        have hlin := linear_lt_even_pow hr₀_ge3 he2
        have hσ_gt : r₀ ^ (2 * e₀) < p := by
          rw [← hσr₀]
          exact self_lt_sigma_of_one_lt (one_lt_pow₀ hr₀p.one_lt (by omega))
        have hΔ_lt : Δ < 4 * e₀ * r₀ := by
          dsimp [Δ]
          have : 4 * e₀ * (r₀ - 1) ≤ 4 * e₀ * r₀ := Nat.mul_le_mul_left _ (by omega)
          omega
        omega
    omega
  have hS1_gt1 : 1 < S₁.card := by omega
  obtain ⟨r, hrS, t, htS, hne⟩ := Finset.one_lt_card.mp hS1_gt1
  obtain ⟨hr, hvr⟩ := Finset.mem_filter.mp hrS
  obtain ⟨ht, hvt⟩ := Finset.mem_filter.mp htS
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hrs := Nat.dvd_of_mem_primeFactors hr
  have hro : Odd r := hs.of_dvd_nat hrs
  have htp := Nat.prime_of_mem_primeFactors ht
  have hts := Nat.dvd_of_mem_primeFactors ht
  have hto : Odd t := hs.of_dvd_nat hts
  have hl_prime := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs hr).1
  have hk_prime := (even_index_cofactor_component_order_dvd_pred hp hpo hs hσq hplus hσs ht).1
  have hfac_r : 1 ≤ s.factorization r := (hrp.dvd_iff_one_le_factorization hs.pos.ne').mp hrs
  have hfac_t : 1 ≤ s.factorization t := (htp.dvd_iff_one_le_factorization hs.pos.ne').mp hts
  have hgr : geometricBlock r (2 * s.factorization r + 1) = p := by
    dsimp only [geometricBlock]
    rw [← sigma_one_apply_prime_pow hrp]
    have H := (hparts r hr).2
    dsimp only at H
    change sigma 1 (r ^ (2 * s.factorization r)) = p ^ v r at H
    rwa [hvr, pow_one] at H
  have hgt : geometricBlock t (2 * s.factorization t + 1) = p := by
    dsimp only [geometricBlock]
    rw [← sigma_one_apply_prime_pow htp]
    have K := (hparts t ht).2
    dsimp only at K
    change sigma 1 (t ^ (2 * s.factorization t)) = p ^ v t at K
    rwa [hvt, pow_one] at K
  exact ⟨r, t, 2 * s.factorization r + 1, 2 * s.factorization t + 1,
    hrp, hro, htp, hto, hne, hl_prime, by omega, hk_prime, by omega, hgr, hgt⟩

/-- Unconditional elimination of the multiple-power Nagell–Ljunggren branch for any
even prime-power component index `i = p ^ (2 * u)` of an odd perfect number. -/
theorem even_prime_power_component_forces_two_repunits {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0 < a)
    (hform : N = q ^ a * b) (hqb : ¬ q ∣ b) (hl : sigma 1 b = q ^ a * i)
    (hr : sigma 1 (q ^ a) * i = 2 * b) (hp : p.Prime) (hu : 0 < u) (hi : i = p ^ (2 * u)) :
    HasTwoOddPrimeRepunits p := by
  obtain ⟨ha1, hσ⟩ := even_prime_power_index_eq_selected_sigma hN ho hq ha hform hqb hl hr hp hu hi
  have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ 2 * b := hr ▸ hi ▸ (pow_dvd_pow 2 (by omega : 2 ≤ 2 * u)).trans (dvd_mul_left _ _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m, _, _, _, rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr (hi ▸ hpo.pow)
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  rw [ha1, pow_one] at hl hr
  rw [hi] at hl hr
  obtain ⟨s, hso, _, _, _, hplus, hσs⟩ := even_prime_power_cofactor_split hq hp hmo hpo hu hl hr
  exact even_index_forces_two_repunits hp hpo hso hu hσ hplus hσs

end OddPerfect
