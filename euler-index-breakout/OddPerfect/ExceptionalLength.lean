module

public import OddPerfect.HalfLengthSupport
public import OddPerfect.AlternatingPell
public import OddPerfect.HalfBlockValuation

public section
namespace OddPerfect
open ArithmeticFunction

/-- Remaining shape of a prime-times-square Euler index at exponent greater
than one, expressed simultaneously through the Euler prime and exponent. -/
theorem prime_mul_square_index_forces_exceptional_prime_length
    {N q a m l t : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : l=1 ∨ l.Prime) (hs : sigma 1 (m^2)/q^a=l*t^2) :
    let s := (a+1)/2
    s.Prime ∧ s%8=1 ∧ q%16=1 ∧ ∃ w : ℕ, (q+1)/2=s*w^2 := by
  let d := (a+1)/2
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hB : IsSquare ((q^d+1)/2) := Classical.byContradiction
    (fun h => euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform h l t hl hs)
  have h16 : q%16=1 := Classical.byContradiction (fun h => half_pow_succ_not_square_of_mod_sixteen hq4 hdo h hB)
  obtain ⟨s,k,hsp,hk,hk2,hpow,hprev⟩ := prime_mul_square_index_forces_prime_power_half_length hN ho hq hq4 ha4 ha hqm hform hl hs
  change d=s^k at hpow
  have hso : Odd s := hdo.of_dvd_nat (hpow ▸ dvd_pow_self s hk.ne')
  have hk1 : k=1 := by
    by_contra hh
    have hk' : k=2 := by omega
    have hsm := hprev (by omega)
    have hqone : q ≡ 1 [MOD s] := (Nat.modEq_iff_dvd' hq.one_le).mpr hsm |>.symm
    have hx1 : q^s ≡ 1 [MOD s] := by simpa using hqone.pow s
    have hnot : ¬s ∣ q^s+1 := by
      intro h
      have hr := ((hx1.add_right 1).symm.trans (Nat.modEq_zero_iff_dvd.mpr h))
      have hs2 := Nat.modEq_zero_iff_dvd.mp hr
      exact hso.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hsp Nat.prime_two).mp hs2) ▸ dvd_refl _)
    have hx8 : q^s%8=1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 8] from (by change q%8=1; omega)).pow s
    have hC := alternatingBlock_not_square (one_lt_pow' hq.one_lt hsp.ne_zero) hsp.one_lt hso
    have hns := half_sum_not_square_of_alternatingBlock hx8 hsp hso hC (Or.inr hnot)
    apply hns
    rwa [hpow,hk',pow_two,pow_mul] at hB
  rw [hk1,pow_one] at hpow
  have hs8 : s%8=1 ∧ s ∣ q+1 := by
    by_contra! hn
    have hsep : s%8≠1 ∨ ¬s ∣ q+1 := by tauto
    apply half_sum_not_square_of_alternatingBlock (by omega : q%8=1) hsp hso
      (alternatingBlock_not_square hq.one_lt hsp.one_lt hso) hsep
    rwa [hpow] at hB
  let H := (q+1)/2
  have hH : q+1=2*H := by dsimp [H]; omega
  have hsH : s ∣ H := (hsp.dvd_mul.mp (hH ▸ hs8.2)).resolve_left (fun h =>
    hso.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hsp Nat.prime_two).mp h) ▸ dvd_refl _))
  obtain ⟨u,hu⟩ := hsH
  have hu0 : u ≠ 0 := by intro h; rw [h,mul_zero] at hu; omega
  have hsq : IsSquare u := Nat.isSquare_iff_even_factorization.mpr (by
    intro r hr
    by_contra he
    have hodd := (Nat.even_or_odd _).resolve_left he
    by_cases hrs : r=s
    · subst r
      have hi := euler_half_length_valuation_parity hN ho hq hq4 ha4 ha hqm hform hl hs hsp
        (show s ∣ (q+1)/2 from ⟨u,hu⟩)
      change Even (H.factorization s+d.factorization s) at hi
      rw [hu,hpow,Nat.factorization_mul hsp.ne_zero hu0,Finsupp.add_apply,hsp.factorization_self] at hi
      have := Nat.even_iff.mp hi
      have := Nat.odd_iff.mp hodd
      omega
    · have hsr : ¬ r ∣ s := fun h => hrs ((Nat.prime_dvd_prime_iff_eq hr hsp).mp h)
      have hoddH : Odd (H.factorization r) := by
        rwa [hu,Nat.factorization_mul hsp.ne_zero hu0,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hsr,zero_add]
      have hrd := euler_odd_valuation_prime_dvd_half_length hN ho hq hq4 ha4 ha hqm hform hl hs hr hoddH
      exact hsr (hpow ▸ hrd))
  obtain ⟨w,hw⟩ := hsq
  change d.Prime ∧ d%8=1 ∧ q%16=1 ∧ ∃ w, H=d*w^2
  exact ⟨hpow ▸ hsp,hpow ▸ hs8.1,h16,w,by rw [hpow,hu,hw,pow_two]⟩

end OddPerfect
