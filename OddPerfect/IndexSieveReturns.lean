module

public import OddPerfect.IndexSieveExactRows
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Log

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- An odd prime of the Euler successor occurs in the square cofactor. -/
theorem successor_prime_dvd_cofactor {q a m i p : ℕ} (hq : q.Prime) (ha : Odd a)
    (hp : p.Prime) (hpo : Odd p) (hd : p ∣ q+1) (hr : sigma 1 (q^a)*i=2*m^2) : p ∣ m :=
  hp.dvd_of_dvd_pow ((Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left
    (hr ▸ (hd.trans (succ_dvd_sigma_prime_pow hq ha)).trans (dvd_mul_right _ _)))

/-- The copies supplied by the Euler successor and by the index both fit
inside the true cofactor exponent. -/
theorem successor_valuation_le_component {q a m i p : ℕ} (hq : q.Prime) (ha : Odd a)
    (hp : p.Prime) (hpo : Odd p) (hm : 0<m) (hi : 0< i) (hr : sigma 1 (q^a)*i=2*m^2) :
    (q+1).factorization p + i.factorization p ≤ 2*m.factorization p := by
  have hv := index_prime_return_valuation hp hpo hq hm hi hr
  have hle := (Nat.factorization_le_iff_dvd (show q+1≠0 by omega)
    (sigma_pos 1 _ (pow_ne_zero a hq.ne_zero)).ne').mpr (succ_dvd_sigma_prime_pow hq ha) p
  omega

/-- When the cofactor prime divides the Euler predecessor, its exponent
outside the index is the full length valuation. Together with the divisor
two this costs twice one more than that exponent in the divisor count. -/
theorem predecessor_excess_le_half_length {q a m i p : ℕ} (hq : q.Prime) (ha : Odd a)
    (hp : p.Prime) (hpo : Odd p) (hm : 0<m) (hi : 0< i) (hd : p∣q-1)
    (hr : sigma 1 (q^a)*i=2*m^2) : 2*m.factorization p-i.factorization p+1 ≤ (a+1).divisors.card/2 := by
  have hv := index_prime_return_valuation hp hpo hq hm hi hr
  rw [sigma_factorization_of_dvd_pred hp hpo hq hd] at hv
  let t := (a+1).factorization p
  have hpd : p^t ∣ a+1 := Nat.ordProj_dvd _ _
  have hcop := (Nat.coprime_two_right.mpr (hpo.pow (n:=t))).symm
  have hfull := hcop.mul_dvd_of_dvd_of_dvd (by have := Nat.odd_iff.mp ha; omega : 2∣a+1) hpd
  have hc := Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.succ_ne_zero a) hfull)
  have hcard : (p^t).divisors.card=t+1 := by rw [←sigma_zero_apply,sigma_zero_apply_prime_pow hp]
  rw [Nat.Coprime.card_divisors_mul hcop,show (2:ℕ).divisors.card=2 by decide,hcard] at hc
  dsimp [t] at hc
  omega

/-- Divisibility by a certified trial prime identifies the Euler prime at
a nontrivial residual. The exact-power check uses the integer logarithm. -/
theorem forced_euler_prime_of_residual {q r j x : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hx : x=q^j) (hd : r∣x) : r=q ∧ r^(Nat.log r x)=x := by
  have he := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow (hx ▸ hd))
  subst r
  exact ⟨rfl,by rw [hx,Nat.log_pow hq.one_lt]⟩

/-- The exponent at a specific cofactor base must satisfy all three tests
when the Euler prime is known. -/
@[expose] def acceptsEuler (i p d q H : ℕ) : Prop :=
  let e := d-1
  let R := residual (repunit p d) i
  q^(Nat.log q R)=R ∧ ¬p^(e-i.factorization p+1) ∣ q+1 ∧
    (p ∣ q-1 → e-i.factorization p+1 ≤ H)

instance (i p d q H : ℕ) : Decidable (acceptsEuler i p d q H) :=
  inferInstanceAs (Decidable (let e := d-1; let R := residual (repunit p d) i
    q^(Nat.log q R)=R ∧ ¬p^(e-i.factorization p+1) ∣ q+1 ∧
      (p ∣ q-1 → e-i.factorization p+1 ≤ H)))

theorem actual_component_accepts_euler {q a m i p H : ℕ} (hq : q.Prime) (ha : Odd a)
    (hp : p.Prime) (hpo : Odd p) (hm : 0<m) (hi : 0< i) (hpm : p∣m) (hH : (a+1).divisors.card/2 ≤ H)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) :
    acceptsEuler i p (2*m.factorization p+1) q H := by
  simp only [acceptsEuler,Nat.add_sub_cancel,repunit_eq_sigma hp]
  have hpos := (hp.dvd_iff_one_le_factorization hm.ne').mp hpm
  obtain ⟨j,hj⟩ := residual_eq_prime_pow hq hi (cofactor_component_sum_dvd_index_product hm hp rfl (by omega) hl)
  refine ⟨by rw [hj,Nat.log_pow hq.one_lt],?_,fun hd => (predecessor_excess_le_half_length hq ha hp hpo hm hi hd hr).trans hH⟩
  intro hbad
  have hval := (hp.pow_dvd_iff_le_factorization (show q+1≠0 by omega)).mp hbad
  have hsum := successor_valuation_le_component hq ha hp hpo hm hi hr
  omega

end OddPerfect.IndexSieve
