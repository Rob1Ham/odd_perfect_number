module

public import OddPerfect.NearPerfect
public import OddPerfect.GeometricSquareClass
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- A quasiperfect number is the sum of its divisors other than one and itself. -/
@[expose] def Quasiperfect (n : ℕ) : Prop := sigma 1 n = 2*n+1

theorem quasiperfect_iff_redundant_one {N : ℕ} : Quasiperfect N ↔ NearPerfectWith N 1 := by
  constructor
  · intro h
    have hgt : 1<N := by
      by_contra! hs
      interval_cases N <;> simp [Quasiperfect] at h
    exact (nearPerfectWith_iff_erase).mpr ⟨Nat.mem_properDivisors.mpr ⟨one_dvd _,hgt⟩, by
      have hsum := Finset.add_sum_erase N.properDivisors (fun i => i)
        (Nat.mem_properDivisors.mpr ⟨one_dvd N,hgt⟩)
      change sigma 1 N = 2*N+1 at h
      rw [sigma_one_apply,Nat.sum_divisors_eq_sum_properDivisors_add_self] at h
      omega⟩
  · intro h
    have he := (nearPerfectWith_iff_erase.mp h)
    have hsum := Finset.add_sum_erase N.properDivisors (fun i => i) he.1
    unfold Quasiperfect
    rw [sigma_one_apply,Nat.sum_divisors_eq_sum_properDivisors_add_self]
    have := he.2
    omega

/-- Cattaneo's odd-square restriction for the quasiperfect equation. -/
theorem quasiperfect_odd_square {N : ℕ} (h : Quasiperfect N) : Odd N ∧ IsSquare N := by
  have hn : N ≠ 0 := by rintro rfl; simp [Quasiperfect] at h
  obtain ⟨a,m,hm,hform⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hc : (2^a).Coprime m := hm.coprime_two_left.pow_left a
  have hsum : sigma 1 (2^a) * sigma 1 m = 2*N+1 := by
    rw [← isMultiplicative_sigma.map_mul_of_coprime hc, ← hform]
    exact h
  have hsodd : Odd (sigma 1 m) :=
    (show Odd (2*N+1) from ⟨N,rfl⟩).of_dvd_nat (hsum ▸ dvd_mul_left _ _)
  obtain ⟨s,hs⟩ := (odd_sigma_iff_square_of_odd hm).mp hsodd
  have ha : a=0 := by
    by_contra ha
    let M := 2^(a+1)-1
    have hM : sigma 1 (2^a) = M := by
      rw [sigma_one_apply_prime_pow Nat.prime_two]
      have hg : (∑ i ∈ range (a+1), 2^i)+1 = 2^(a+1) := by
        simpa only [one_add_one_eq_two, mul_one] using geom_sum_mul_add (1:ℕ) (a+1)
      change _ = 2^(a+1)-1
      omega
    have hM4 : M%4=3 := by
      obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero ha
      have hpow : 2^(a+1) = 4*2^t := by rw [ht, pow_succ, pow_succ]; ring
      dsimp [M]
      rw [hpow]
      have := Nat.two_pow_pos t
      omega
    obtain ⟨r,hr,hr4,_⟩ := exists_three_mod_four_odd_valuation hM4
    have hrp := Nat.prime_of_mem_primeFactors hr
    let : Fact r.Prime := ⟨hrp⟩
    have hrM := Nat.dvd_of_mem_primeFactors hr
    have htot : r ∣ 2*N+1 := hrM.trans (by rw [← hM, ← hsum]; exact dvd_mul_right _ _)
    have hP : 2^(a+1) = M+1 := by
      have := Nat.two_pow_pos (a+1)
      dsimp [M]; omega
    have hprod : 2*N+1 = M*(s*s)+(s*s+1) := by rw [hform,hs]; nlinarith [congrArg (fun n => n*(s*s)) (show 2*2^a=M+1 by simpa [pow_succ, Nat.mul_comm] using hP)]
    rw [hprod] at htot
    have hd : r ∣ s*s+1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hrM _)).mp htot
    have hz : (s:ZMod r)^2 + 1 = 0 := by
      simpa [pow_two] using (ZMod.natCast_eq_zero_iff _ _).mpr hd
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (eq_neg_of_add_eq_zero_left hz) hr4
  rw [ha,pow_zero,one_mul] at hform
  exact ⟨hform ▸ hm, hform ▸ ⟨s,hs⟩⟩

/-- Cattaneo's divisor test (Hagis–Cohen, property B). A proper divisor of
a quasiperfect number is deficient, including when it shares prime factors
with its complementary divisor. -/
theorem quasiperfect_proper_divisor_deficient {N d : ℕ} (h : Quasiperfect N)
    (hd : d ∈ N.properDivisors) : d.Deficient := by
  have hnear := quasiperfect_iff_redundant_one.mp h
  have hgt : 1 < N := (Nat.mem_properDivisors.mp (nearPerfectWith_iff_erase.mp hnear).1).2
  have hnon := Nat.not_isPrimePow_iff_nontrivial_of_two_le hgt |>.mp
    (fun hpp => ((Nat.deficient_iff_not_abundant_and_not_perfect (by omega)).mp hpp.deficient).1 hnear.abundant)
  rcases Nat.mem_properDivisors.mp hd with ⟨⟨k,hn⟩, hlt⟩
  have hk : 1 < k := by by_contra! hs; interval_cases k <;> simp_all
  have prime : ∃ p ∈ N.primeFactors, p ≠ k := by
    obtain ⟨u,hu,v,hv,huv⟩ := hnon
    by_cases he : u=k
    · exact ⟨v,hv,he ▸ huv.symm⟩
    · exact ⟨u,hu,he⟩
  obtain ⟨p,hp,hpk⟩ := prime
  have hprime := Nat.prime_of_mem_primeFactors hp
  let S := d.divisors.image (fun i => k*i)
  have hskip (r : ℕ) (h : r ∈ S) : k ∣ r := by
    obtain ⟨j,_,rfl⟩ := mem_image.mp h
    exact dvd_mul_right _ _
  have h1 : 1 ∉ S := fun h => hk.ne' (Nat.dvd_one.mp (hskip 1 h))
  have hps : p ∉ insert 1 S := by
    intro hmem
    rcases mem_insert.mp hmem with h1 | hs
    · exact hprime.ne_one h1
    · rcases (Nat.dvd_prime hprime).mp (hskip p hs) with h | h <;> omega
  have hsub : insert 1 S ⊆ N.divisors := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact Nat.mem_divisors.mpr ⟨one_dvd _,by omega⟩
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hr
      apply Nat.mem_divisors.mpr
      refine ⟨?_,by omega⟩
      rw [hn,Nat.mul_comm d k]
      exact Nat.mul_dvd_mul_left k (Nat.dvd_of_mem_divisors hj)
  have hsum := sum_lt_sum_of_subset hsub (Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp,by omega⟩)
    hps hprime.pos (fun i _ _ => Nat.zero_le i)
  have himage : (∑ i ∈ S, i) = k * sigma 1 d := by
    rw [sigma_one_apply, mul_sum]
    exact sum_image (f := id) (by intro i _ j _ h; exact Nat.mul_left_cancel (by omega) h)
  change (∑ i ∈ insert 1 S, i) < ∑ i ∈ N.divisors, i at hsum
  rw [sum_insert h1,himage,← sigma_one_apply,h,hn] at hsum
  have hstrict : sigma 1 d < 2*d := by
    by_contra! hbad
    have := Nat.mul_le_mul_left k hbad
    nlinarith
  rw [sigma_one_apply,Nat.sum_divisors_eq_sum_properDivisors_add_self] at hstrict
  exact (show (∑ i ∈ d.properDivisors, i) < d by omega)

/-- Each divisor of σ(N) is 1 or 3 modulo eight (Hagis–Cohen, property C). -/
theorem quasiperfect_sigma_divisors_mod_eight {N r : ℕ} (h : Quasiperfect N)
    (hr : r ∣ sigma 1 N) : r%8=1 ∨ r%8=3 := by
  obtain ⟨_,s,hs⟩ := quasiperfect_odd_square h
  have hσ : sigma 1 N = 2*N+1 := h
  have ho : Odd (sigma 1 N) := hσ ▸ (show Odd (2*N+1) from ⟨N,rfl⟩)
  have hprime (p : ℕ) (hp : p.Prime) (hd : p ∣ sigma 1 N) : p%8=1 ∨ p%8=3 := by
    let : Fact p.Prime := ⟨hp⟩
    have hpo := ho.of_dvd_nat hd
    rw [hσ,hs] at hd
    have hz : 2*(s:ZMod p)^2+1 = 0 := by
      simpa [pow_two] using (ZMod.natCast_eq_zero_iff _ _).mpr hd
    apply (ZMod.exists_sq_eq_neg_two_iff (by have := Nat.odd_iff.mp hpo; omega)).mp
    exact ⟨2*(s:ZMod p),by linear_combination -2*hz⟩
  have hr0 : r ≠ 0 := (Nat.pos_of_dvd_of_pos hr ho.pos).ne'
  have hlist (L : List ℕ) (hL : ∀ p ∈ L, p%8=1 ∨ p%8=3) : L.prod%8=1 ∨ L.prod%8=3 := by
    induction L with
    | nil => decide
    | cons a tl ih =>
      have ha := hL a (.head _)
      have ht := ih (fun p hp => hL p (.tail _ hp))
      rw [List.prod_cons,Nat.mul_mod]
      rcases ha with h | h <;> rcases ht with h'|h' <;> simp [h,h']
  exact (Nat.prod_primeFactorsList hr0) ▸ hlist r.primeFactorsList (fun p hp =>
    hprime p (Nat.prime_of_mem_primeFactorsList hp) ((Nat.dvd_of_mem_primeFactorsList hp).trans hr))

end OddPerfect
