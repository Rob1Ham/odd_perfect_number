module

public import OddPerfect.OddPrimePowerReturn
public import OddPerfect.ChenChenIndex
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction

set_option exponentiation.threshold 1000

private theorem exponent_screen :
    ∀ j : Fin 191, 16 ∣ j.val+1 → (j.val+2).Prime →
      ∀ d : Fin 194, d.val.Prime → d.val%8=1 → ¬d.val ∣ j.val+3 := by
  decide +kernel

/-- An odd prime-power Euler index has exponent at least 191. The prime
base exceeds 136, so the index exceeds ten to the 408th power. -/
theorem odd_prime_power_euler_index_lower_bounds {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) :
    191≤j ∧ 137≤p ∧ 10^408 < sigma 1 (m^2)/q^a := by
  obtain ⟨_,hp8,_,hjp,h16,_⟩ :=
    odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  let d := (a+1)/2
  obtain ⟨hd,hd8,hdj,hdp,_,_⟩ :=
    odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi
  change d.Prime at hd
  change d%8=1 at hd8
  change d ∣ j+3 at hdj
  change d ∣ p-1 at hdp
  have hjb : 191≤j := by
    by_contra! h
    have hdle := Nat.le_of_dvd (by omega : 0<j+3) hdj
    exact exponent_screen ⟨j,h⟩ h16 hjp ⟨d,by omega⟩ hd hd8 hdj
  have hd17 : 17≤d := by
    have h9 : d≠9 := fun h => (by decide : ¬Nat.Prime 9) (h ▸ hd)
    have := hd.one_lt
    omega
  have hd8c : d.Coprime 8 := by
    apply hd.coprime_iff_not_dvd.mpr
    intro h
    have := Nat.le_of_dvd (by decide : 0<8) h
    omega
  have hprod := hd8c.mul_dvd_of_dvd_of_dvd hdp (show 8 ∣ p-1 by omega)
  have hle := Nat.le_of_dvd (by have := hp.one_lt; omega : 0<p-1) hprod
  have hpb : 137≤p := by omega
  refine ⟨hjb,hpb,?_⟩
  rw [hi]
  exact (by decide : (10:ℕ)^408<137^191).trans_le
    ((Nat.pow_le_pow_left hpb 191).trans (Nat.pow_le_pow_right hp.pos hjb))

/-- At any exact component, an odd exponent in a prime-power index is at
least 191. This includes bases equal to two and both Euler and ordinary
components. -/
theorem component_index_ne_small_odd_prime_power {N q a b i p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hj : Odd j) (hjlim : j<191) : i≠p^j := by
  intro heq
  subst i
  by_cases hj1 : j=1
  · rw [hj1,pow_one] at hl hr
    exact component_index_not_prime hN ho hq ha hform hqb hl hr hp
  have hp2 : p≠2 := by
    rintro rfl
    have h4 : 4 ∣ 2*b := hr ▸ (show 2^2 ∣ 2^j from pow_dvd_pow 2 (by have := hj.pos; omega)).trans (dvd_mul_left _ _)
    have hbo := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
    have := hbo.not_two_dvd_nat
    omega
  have hpo := hp.odd_of_ne_two hp2
  obtain ⟨m,hq4,ha4,hqm,rfl⟩ := euler_form_of_odd_component_index hN ho hq ha hform hqb hl hr hpo.pow
  have hi : sigma 1 (m^2)/q^a=p^j := by rw [hl,Nat.mul_div_cancel_left _ (Nat.pow_pos hq.pos)]
  exact hjlim.not_ge (odd_prime_power_euler_index_lower_bounds hN ho hq hq4 ha4 hqm hform hp hj hi).1

/-- In particular, the index of an exact component is never a prime cube. -/
theorem component_index_ne_prime_cube {N q a b i p : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) : i≠p^3 :=
  component_index_ne_small_odd_prime_power hN ho hq ha hform hqb hl hr hp (by decide) (by decide)

end OddPerfect
