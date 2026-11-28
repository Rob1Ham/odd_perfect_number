module

public import OddPerfect.SmallBaseIndexSieve
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction

/-- The component at `p` is pure if all index primes besides `p` are a
single prime `r` with even order for the base `p`. -/
theorem pure_component_at_index_prime_of_even_order {p r q a m i j k : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hq : q.Prime) (hm : 0<m) (hi : i=p^j*r^k)
    (hpos : 0<2*m.factorization p) (hord : Even (orderOf (p : ZMod r)))
    (hl : sigma 1 (m^2)=q^a*i) : ∃ β : ℕ, sigma 1 (p^(2*m.factorization p))=q^β := by
  let e := 2*m.factorization p
  have hs := cofactor_component_sum_dvd_index_product hm hp (e:=e) rfl hpos hl
  have hself : ¬p ∣ sigma 1 (p^e) := by rw [Nat.dvd_iff_mod_eq_zero,sigma_prime_pow_mod_self hp]; decide
  have hother := not_dvd_even_exponent_component_of_even_order hp hr (show Even e from ⟨m.factorization p,by simp [e,two_mul]⟩) hord
  have hc := ((hp.coprime_iff_not_dvd.mpr hself).symm.pow_right j).mul_right ((hr.coprime_iff_not_dvd.mpr hother).symm.pow_right k)
  rw [hi] at hs
  obtain ⟨β,_,hβ⟩ := (Nat.dvd_prime_pow hq).mp (hc.dvd_of_dvd_mul_right hs)
  exact ⟨β,hβ⟩

/-- A finite family of residue certificates for `p²r`: for each possible
exponent at `r`, supply a prime divisor of its sum outside `p` and outside
one modulo sixteen. -/
theorem small_square_times_prime_excluded_of_component_factors {N q a m p r k : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hp : p.Prime) (hr : r.Prime)
    (hro : Odd r) (hpr : p ≠ r) (hk : p-1=2^k) (hsmall : p^2*r < 22971)
    (hl : sigma 1 (m^2)=q^a*(p^2*r)) (hret : sigma 1 (q^a)*(p^2*r)=2*m^2)
    (hc : ∀ e : ℕ, e=2 ∨ e=4 ∨ e+1=p →
      ∃ u : ℕ, u.Prime ∧ ¬u ∣ p ∧ u ∣ sigma 1 (r^e) ∧ u%16≠1) : False := by
  have hquot : sigma 1 (m^2)/q^a=p^2*r := by rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)]
  have hagt : 1<a := by
    by_contra! h
    have h1 : a=1 := by omega
    have := euler_exponent_one_index_ge_22971 hN ho hq hqm (by simpa [h1] using hform)
    simp only [h1,pow_one] at hquot
    omega
  have hao : Odd a := Nat.odd_iff.mpr (by omega)
  obtain ⟨_,hs,hd⟩ := square_times_prime_index_source_exponent hN ho hq hao hqm hform hp hr hro hpr hk hl hret
  obtain ⟨u,hu,hup,hud,hu16⟩ := hc _ (by rcases hd with h|h; exact .inr (.inr h.2); exact h.1.elim Or.inl (fun he => .inr (.inl he)))
  have huq := forced_euler_prime_of_component_factor hu hq hup hud hs
  subst q
  exact euler_index_ne_prime_mul_square_of_residue_or_length hN ho hu hq4 ha4 hagt hqm hform
    (.inl hu16) r p (.inr hr) (hquot.trans (mul_comm _ _))

end OddPerfect
