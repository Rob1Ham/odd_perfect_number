module

public import OddPerfect.FermatIndexValuation
import OddPerfect.Cuts
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction

/-- At any odd prime the cofactor exponent is the sum of the outgoing Euler
valuation and the index valuation. -/
theorem index_prime_return_valuation {p q a m i : ℕ} (hp : p.Prime) (hpo : Odd p) (hq : q.Prime)
    (hm : 0 < m) (hi : 0 < i) (hr : sigma 1 (q^a)*i=2*m^2) :
    2*m.factorization p = (sigma 1 (q^a)).factorization p + i.factorization p := by
  have h := congrArg (fun n : ℕ => n.factorization p) hr
  change (sigma 1 (q^a)*i).factorization p = (2*m^2).factorization p at h
  have hp2 : ¬p ∣ 2 := fun hd => hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd ▸ dvd_rfl)
  rw [Nat.factorization_mul (sigma_pos 1 _ (pow_ne_zero a hq.ne_zero)).ne' hi.ne',
    Nat.factorization_mul (by decide : 2 ≠ 0) (pow_ne_zero 2 hm.ne'), Finsupp.add_apply,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp2] at h
  simpa [Nat.factorization_pow] using h.symm

/-- A component feeding only the Euler prime can lose its index multiplicity
and one further power when forcing its own prime into the Euler length. -/
theorem pure_component_index_return_length {p q a m i β : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hq : q.Prime) (hm : 0 < m) (hi : 0 < i) (hepos : 0 < 2*m.factorization p)
    (hout : sigma 1 (p^(2*m.factorization p))=q^β) (hr : sigma 1 (q^a)*i=2*m^2) :
    p^(2*m.factorization p-i.factorization p-1) ∣ a+1 := by
  have hv := index_prime_return_valuation hp hpo hq hm hi hr
  apply reciprocal_return_length hp hpo hq hepos hout
  exact (hp.pow_dvd_iff_le_factorization (sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)).ne').mpr (by omega)

/-- At Euler exponent one, a prime-power index is an exact square-cofactor
component and its divisor sum equals the Euler prime. -/
theorem prime_power_index_data_at_one {q m p j : ℕ} (hq : q.Prime)
    (hm : 0 < m) (hp : p.Prime) (hpo : Odd p) (hj : 0 < j)
    (hleft : sigma 1 (m^2)=q*p^j) (hright : sigma 1 q*p^j=2*m^2) : 2*m.factorization p=j ∧ sigma 1 (p^j)=q := by
  have hr : sigma 1 (q^1)*p^j=2*m^2 := by simpa
  have hv := index_prime_return_valuation hp hpo hq hm (Nat.pow_pos hp.pos) hr
  rw [hp.factorization_pow,Finsupp.single_eq_same] at hv
  let e := 2*m.factorization p
  have he : 0 < e := by dsimp [e]; omega
  have hs : sigma 1 (p^e) ∣ q*p^j := by
    simpa using cofactor_component_sum_dvd_index_product (a:=1) hm hp (e:=e) rfl he (by simpa using hleft)
  have hpc : ¬p ∣ sigma 1 (p^e) := by rw [Nat.dvd_iff_mod_eq_zero,sigma_prime_pow_mod_self hp]; decide
  have hd := ((hp.coprime_iff_not_dvd.mpr hpc).symm.pow_right j).dvd_of_dvd_mul_right hs
  have hσ : sigma 1 (p^e) = q := by
    rcases (Nat.dvd_prime hq).mp hd with h | h
    · have hlarge := self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt he.ne')
      have := one_lt_pow₀ hp.one_lt he.ne'
      omega
    · exact h
  have hpmod := sigma_prime_pow_mod_self hp e
  rw [hσ] at hpmod
  have hneg : ¬ p ∣ sigma 1 (q^1) := by
    rw [sigma_one_apply_prime_pow hq]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,zero_add]
    intro hd2
    have hcon : q ≡ 1 [MOD p] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt] using hpmod
    have h2 : p ∣ 1+1 := (hcon.add_left 1).dvd_iff dvd_rfl |>.mp hd2
    exact hpo.not_two_dvd_nat ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2 ▸ dvd_rfl)
  rw [Nat.factorization_eq_zero_of_not_dvd hneg,zero_add] at hv
  exact ⟨hv,by rwa [←hv]⟩

/-- If the Euler exponent is one and its index is a power of a single odd
prime, that index power has even exponent. -/
theorem even_prime_power_index_at_euler_exponent_one {q m p j : ℕ} (hq : q.Prime)
    (hm : 0 < m) (hp : p.Prime) (hpo : Odd p) (hj : 0 < j)
    (hleft : sigma 1 (m^2)=q*p^j) (hright : sigma 1 q*p^j=2*m^2) : Even j := by
  have h := (prime_power_index_data_at_one hq hm hp hpo hj hleft hright).1
  exact ⟨m.factorization p,by omega⟩

end OddPerfect
