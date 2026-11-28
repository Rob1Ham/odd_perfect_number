module

public import OddPerfect.EvenIndexRoots
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- If a prime divides the divisor sum of every exact component of n,
the order of any factor made from those prime bases divides τ(n). -/
theorem order_dvd_divisor_count_of_component_sigma {n p m : ℕ} (hn : 0<n) (hm : 0<m)
    (hp : p.Prime) (hsub : m.primeFactors⊆n.primeFactors)
    (hcomp : ∀r ∈ n.primeFactors, p ∣ sigma 1 (r^n.factorization r)) :
    orderOf (m:ZMod p) ∣ n.divisors.card := by
  let k := n.divisors.card
  apply orderOf_dvd_of_pow_eq_one
  have loc (r : ℕ) (hr : r ∈ m.primeFactors) : (r:ZMod p)^k=1 := by
    have hN := hsub hr
    have h := hcomp r hN
    rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff (Nat.prime_of_mem_primeFactors hN) hp] at h
    by_cases he : (r:ZMod p)=1
    · rw [he,one_pow]
    rw [ite_eq_right he] at h
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply h.trans
    dsimp [k]
    rw [Nat.card_divisors hn.ne']
    exact Finset.dvd_prod_of_mem _ hN
  have H := congrArg (fun x:ℕ => (x:ZMod p)) (Nat.prod_primeFactors_pow_factorization hm.ne')
  simp only [Nat.cast_prod,Nat.cast_pow] at H
  rw [show n.divisors.card=k from rfl,H,←Finset.prod_pow]
  exact Finset.prod_eq_one (fun r hr => by rw [←pow_mul,Nat.mul_comm,pow_mul,loc r hr,one_pow])

/-- If the entire divisor sum is a prime power, every exact component
contributes that prime. This includes the empty support of n=1. -/
theorem order_dvd_divisor_count_of_pure_sigma {n p j m : ℕ} (hn : 0<n) (hm : 0<m)
    (hp : p.Prime) (hsub : m.primeFactors⊆n.primeFactors) (hσ : sigma 1 n=p^j) :
    orderOf (m:ZMod p) ∣ n.divisors.card := by
  apply order_dvd_divisor_count_of_component_sigma hn hm hp hsub
  intro r hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  have he := (hrp.dvd_iff_one_le_factorization hn.ne').mp (Nat.dvd_of_mem_primeFactors hr)
  have hbig := self_lt_sigma_of_one_lt (one_lt_pow₀ hrp.one_lt (by omega : n.factorization r≠0))
  have hd : sigma 1 (r^n.factorization r) ∣ p^j := by
    rw [←hσ,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ hn.ne']
    exact Finset.dvd_prod_of_mem _ hr
  obtain ⟨v,_,hv⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [hv]
  apply dvd_pow_self
  rintro rfl
  rw [pow_zero] at hv
  have := Nat.one_le_pow (n.factorization r) r hrp.pos
  omega

/-- The square cofactor s is on the positive square-root branch
s≡1 (mod p) for every odd index prime, regardless of p mod 4. -/
theorem even_index_cofactor_mod_index_prime {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : 0<s) (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2)
    (hσs : sigma 1 (s^2)=p^(2*u)) : s ≡ 1 [MOD p] := by
  let : Fact p.Prime := ⟨hp⟩
  have hdr := order_dvd_divisor_count_of_pure_sigma (n:=s^2) (m:=s)
    (pow_pos hs _) hs hp (by rw [Nat.primeFactors_pow _ (by decide : 2≠0)]) hσs
  have ht : Odd (s^2).divisors.card := by
    rw [Nat.card_divisors (pow_ne_zero _ hs.ne')]
    apply Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
    intro r _
    rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    exact ⟨s.factorization r,by omega⟩
  have ho := ht.of_dvd_nat hdr
  have q1 : (q:ZMod p)=1 := by
    rw [←hσq]
    have hh := (ZMod.natCast_eq_natCast_iff _ 1 p).mpr
      (show sigma 1 (p^(2*u)) ≡ 1 [MOD p] by simpa [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt] using sigma_prime_pow_mod_self hp (2*u))
    simpa only [Nat.cast_one] using hh
  have two : (2:ZMod p)≠0 := by
    intro h
    rw [← Nat.cast_two] at h
    exact hpo.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h)) ▸ dvd_rfl)
  have hsquare : (s:ZMod p)^2=1 := by
    have H := congrArg (fun x:ℕ => (x:ZMod p)) hplus
    push_cast at H
    rw [q1] at H
    apply mul_left_cancel₀ two
    simpa only [mul_one,one_add_one_eq_two] using H.symm
  have hdiv := orderOf_dvd_of_pow_eq_one hsquare
  have hc := (Nat.coprime_two_right.mpr ho).gcd_eq_one
  rw [Nat.gcd_eq_left hdiv] at hc
  have h1 := orderOf_eq_one_iff.mp hc
  exact (ZMod.natCast_eq_natCast_iff s 1 p).mp (by simpa only [Nat.cast_one] using h1)

end OddPerfect
