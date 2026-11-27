module

public import OddPerfect.OddPrimePowerBound
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction

set_option exponentiation.threshold 2000

private theorem next_exponent_screen :
    ∀ k : Fin 35, (16*k.val+17).Prime →
      ∀ t : Fin 73, (8*t.val+1).Prime → 8*t.val+1 ∣ 16*k.val+18 →
        16*k.val+15=191 ∧ 8*t.val+1=97 := by decide +kernel

private theorem numerical_large_branch : (10^1831:ℕ)^97 < (1553^192)^290 := by
  calc (10^1831:ℕ)^97 = 10^(1831*97) := (pow_mul ..).symm
       _ < 10^(319*556+255) := Nat.pow_lt_pow_right (by decide) (by decide)
       _ = (10^319)^556*10^255 := by rw [pow_add,pow_mul]
       _ ≤ (1553^100)^556*1553^80 := Nat.mul_le_mul
         (Nat.pow_le_pow_left (by decide : (10:ℕ)^319≤1553^100) 556) (by decide)
       _ = (1553^192)^290 := by rw [←pow_mul,←pow_add,←pow_mul]

/-- The least candidate in the base-and-exponent sieve is 1553^191.
The corresponding integer would exceed ten to the 1831st power. -/
theorem odd_prime_power_index_and_size {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) :
    1553^191≤sigma 1 (m^2)/q^a ∧ 10^1831<N := by
  obtain ⟨_,hp8,he,hjp,h16,_⟩ :=
    odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  let d := (a+1)/2
  obtain ⟨hd,hd8,hdj,hdp,_,hσ⟩ :=
    odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi
  change d.Prime at hd
  change d%8=1 at hd8
  change d ∣ j+3 at hdj
  change d ∣ p-1 at hdp
  change sigma 1 (p^(j+1))=q^d at hσ
  have hd2 := hd.one_lt
  have hlen : a+1=2*d := by dsimp [d]; omega
  have hmo := ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)
  have hm : 0<m := hmo.pos
  have hpq : p^(j+1)<q^d := by
    rw [← hσ]
    exact self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt (by omega))
  have hpm : p^(j+1) ≤ m^2 := by
    apply Nat.le_of_dvd (Nat.pow_pos hm)
    apply (hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hm.ne')).mpr
    simpa only [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] using he.ge
  have hpb := (odd_prime_power_euler_index_lower_bounds hN ho hq hq4 ha4 hqm hform hp hj hi).2.1
  rw [hi]
  by_cases hsmall : j<575
  · have hdle := Nat.le_of_dvd (by omega : 0<j+3) hdj
    let k : Fin 35 := ⟨j/16,by omega⟩
    let t : Fin 73 := ⟨d/8,by omega⟩
    have hk : 16*k.val+15=j := by dsimp [k]; omega
    have ht : 8*t.val+1=d := by dsimp [t]; omega
    obtain ⟨hj191,hd97⟩ := next_exponent_screen k (show (16*k.val+17).Prime from (by omega : 16*k.val+17=j+2) ▸ hjp)
      t (ht ▸ hd) (by rwa [ht,show 16*k.val+18=j+3 by omega])
    rw [hk] at hj191
    rw [ht] at hd97
    have hp97 : 776 ∣ p-1 :=
      (by decide : Nat.Coprime 97 8).mul_dvd_of_dvd_of_dvd (hd97 ▸ hdp) (show 8 ∣ p-1 by omega)
    have hpbig : 1553≤p := by
      have hp777 : p≠777 := fun h => by
        have := (h ▸ hp).eq_one_or_self_of_dvd 3 ⟨259, rfl⟩
        omega
      omega
    have ha193 : a=193 := by omega
    rw [hj191,hd97] at hpq
    rw [hj191] at hpm ⊢
    refine ⟨Nat.pow_le_pow_left hpbig _,?_⟩
    have hQ : (p^192)^290 < N^97 := by
      calc (p^192)^290 = (p^192)^193*(p^192)^97 := by rw [←pow_add]
           _ < (q^97)^193*(m^2)^97 := Nat.mul_lt_mul_of_lt_of_le
             (Nat.pow_lt_pow_left hpq (by decide)) (Nat.pow_le_pow_left hpm 97) (by positivity)
           _ = N^97 := by rw [hform,ha193,mul_pow]; ring
    by_contra! h
    have hup := Nat.pow_le_pow_left h 97
    have hlo := Nat.pow_le_pow_left (Nat.pow_le_pow_left hpbig 192) 290
    exact numerical_large_branch.not_ge (hlo.trans (hQ.trans_le hup).le)
  · have hj575 : 575≤j := by omega
    have hi' : 137^575≤p^j := (Nat.pow_le_pow_left hpb _).trans (Nat.pow_le_pow_right hp.pos hj575)
    refine ⟨(by decide : (1553:ℕ)^191≤137^575).trans hi',?_⟩
    have hda : d≤a := by omega
    have hx : (p^(j+1))^2<N := by
      rw [pow_two,hform]
      exact Nat.mul_lt_mul_of_lt_of_le (hpq.trans_le (Nat.pow_le_pow_right hq.pos hda)) hpm (by positivity)
    have hlow : 137^575 ≤ p^(j+1) := hi'.trans (Nat.pow_le_pow_right hp.pos (by omega))
    exact (by decide : (10:ℕ)^1831<(137^575)^2).trans_le (Nat.pow_le_pow_left hlow 2) |>.trans hx

end OddPerfect
