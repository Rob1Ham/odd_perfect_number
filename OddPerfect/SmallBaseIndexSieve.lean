module

public import OddPerfect.Hirakawa
public import OddPerfect.ExponentOneIndex
public import OddPerfect.MixedIndexSources
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- An even multiplicative order prevents an odd-length prime-power sum from
containing the target prime. -/
theorem not_dvd_even_exponent_component_of_even_order {p r e : ℕ} (hp : p.Prime)
    (hr : r.Prime) (he : Even e) (horder : Even (orderOf (p : ZMod r))) :
    ¬r ∣ sigma 1 (p^e) := by
  have hn : (p : ZMod r) ≠ 1 := by intro h; rw [h,orderOf_one] at horder; exact (by decide : ¬ Even 1) horder
  intro hd
  rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hp hr] at hd
  simp only [hn,ite_false] at hd
  have := horder.two_dvd.trans hd
  have := Nat.even_iff.mp he
  omega

/-- At a small prime-times-square Euler index, purity of the component at
three or five is impossible when that base has index valuation one or two. -/
theorem small_prime_times_square_index_not_pure {N q a m i p l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q ∣ m) (hform : N=q^a*m^2) (hl : l.Prime) (hshape : i=l*t^2)
    (hp : p=3 ∨ p=5) (hi : i < 22971) (hval : i.factorization p=1 ∨ i.factorization p=2)
    (hleft : sigma 1 (m^2)=q^a*i) (hret : sigma 1 (q^a)*i=2*m^2)
    (hpure : ∃ β : ℕ, sigma 1 (p^(2*m.factorization p))=q^β) : False := by
  have hquot : sigma 1 (m^2)/q^a=i := by rw [hleft,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have ha : 1<a := by
    by_contra! h
    have h1 : a=1 := by omega
    have := euler_exponent_one_index_ge_22971 hN ho hq hqm (by simpa [h1] using hform)
    simp only [h1,pow_one] at hquot
    omega
  have hreject (h : q%16≠1 ∨ 3 ∣ (a+1)/2 ∨ 5 ∣ (a+1)/2) : False :=
    euler_index_ne_prime_mul_square_of_residue_or_length hN ho hq hq4 ha4 ha hqm hform h l t (.inr hl) (hquot.trans hshape)
  have hpP : p.Prime := by rcases hp with rfl|rfl <;> decide
  have hpo : Odd p := by rcases hp with rfl|rfl <;> decide
  have hnlen : ¬p ∣ a+1 := by
    intro h
    have h2 : a+1=2*((a+1)/2) := by omega
    have hhalf := (Nat.coprime_two_right.mpr hpo).dvd_of_dvd_mul_left (h2 ▸ h)
    rcases hp with rfl|rfl
    · exact hreject (.inr (.inl hhalf))
    · exact hreject (.inr (.inr hhalf))
  have hm := (ho.of_dvd_nat (hform ▸ (dvd_pow_self m (by decide : 2 ≠ 0)).trans (dvd_mul_left _ _))).pos
  have hipos : 0 < i := by
    by_contra! h
    have hi0 : i=0 := by omega
    simp [hi0] at hval
  have hv := index_prime_return_valuation hpP hpo hq hm hipos hret
  have hepos : 0<2*m.factorization p := by rcases hval with h|h <;> omega
  obtain ⟨β,hβ⟩ := hpure
  have hlen := pure_component_index_return_length hpP hpo hq hm hipos hepos hβ hret
  have he : 2*m.factorization p=2 := by
    by_contra h
    apply hnlen
    exact (dvd_pow_self p (by rcases hval with h|h <;> omega : 2*m.factorization p-i.factorization p-1 ≠ 0)).trans hlen
  rw [he] at hβ
  rcases hp with rfl|rfl
  · have h13 : 13 ∣ q^β := hβ ▸ (show 13 ∣ sigma 1 (3^2) by rw [sigma_one_apply_prime_pow hpP]; decide)
    have heq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 13) hq).mp ((by decide : Nat.Prime 13).dvd_of_dvd_pow h13)
    exact hreject (.inl (heq ▸ (by decide : 13%16≠1)))
  · have h31 : 31 ∣ q^β := hβ ▸ (show 31 ∣ sigma 1 (5^2) by rw [sigma_one_apply_prime_pow hpP]; decide)
    have heq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 31) hq).mp ((by decide : Nat.Prime 31).dvd_of_dvd_pow h31)
    omega

/-- If a prime `u` must appear in all possible component sums at a second
index base, with `u` outside the index, then `u` is the Euler prime. -/
theorem forced_euler_prime_of_component_factor {u q a p k e r : ℕ}
    (hu : u.Prime) (hq : q.Prime) (hup : ¬u ∣ p) (hd : u ∣ sigma 1 (r^e))
    (hs : sigma 1 (r^e) ∣ p^k*q^a) : u=q := by
  exact (Nat.prime_dvd_prime_iff_eq hu hq).mp (hu.dvd_of_dvd_pow
    ((hu.dvd_mul.mp (hd.trans hs)).resolve_left (fun h => hup (hu.dvd_of_dvd_pow h))))

end OddPerfect
