module

public import OddPerfect.IndexSieveLengths
public import OddPerfect.Hirakawa
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open ArithmeticFunction Finset

/-- Remove the part of an integer already accounted for by the index. -/
@[expose] def residual (b i : ℕ) : ℕ := b / b.gcd i

/-- A block dividing `q^a i` has a residual that is a pure power of `q`. -/
theorem residual_eq_prime_pow {b q a i : ℕ} (hq : q.Prime) (hi : 0 < i) (hd : b ∣ q^a*i) :
    ∃ j : ℕ, residual b i=q^j := by
  let g := b.gcd i
  have hg : 0<g := Nat.gcd_pos_of_pos_right b hi
  have h1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left b i)
  have h2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right b i)
  have hfull : g*(b/g) ∣ g*(q^a*(i/g)) := by
    rw [show g*(q^a*(i/g))=q^a*(g*(i/g)) by ac_rfl]
    simpa only [g,h1,h2] using hd
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨j,_,h⟩ := (Nat.dvd_prime_pow hq).mp (hcop.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_left hg hfull))
  exact ⟨j,h⟩

/-- Residuals compatible with the Euler congruence modulo `M`. Trial
primes through thirteen allow a composite with the right residue to be
rejected when it has a prime divisor in the wrong residue class. -/
@[expose] def residuals (i p H M : ℕ) : Finset ℕ :=
  ((blockLengths i p H).image fun d => residual (∑ j ∈ Finset.range d, p^j) i).filter fun x : ℕ =>
    x.Coprime i ∧ x%M=1 ∧ ∀ u : Fin 14, (u:ℕ).Prime → (u:ℕ) ∣ x → (u:ℕ)%M=1

/-- Two index primes must allow residuals that are both powers of the same
Euler prime. Distinct nontrivial residuals therefore share a prime divisor. -/
@[expose] def Compatible (i p r H M : ℕ) : Prop :=
  ∃ x ∈ residuals i p H M, ∃ y ∈ residuals i r H M, x=1 ∨ y=1 ∨ x.gcd y ≠ 1

instance (i p r H M : ℕ) : Decidable (Compatible i p r H M) :=
  inferInstanceAs (Decidable (∃ x ∈ residuals i p H M, ∃ y ∈ residuals i r H M, x=1 ∨ y=1 ∨ x.gcd y ≠ 1))

/-- An actual Euler index passes the two-source residual test for every
pair of its prime divisors. -/
theorem compatible_of_euler_index {q a m i p r H M : ℕ} (hq : q.Prime) (ha : Odd a)
    (hm : 0<m) (hio : Odd i) (hqi : q.Coprime i) (hM : 1<M) (hqM : q%M=1)
    (hpI : p ∈ i.primeFactors) (hrI : r ∈ i.primeFactors) (hH : (a+1).divisors.card/2 ≤ H)
    (hl : sigma 1 (m^2)=q^a*i) (hr : sigma 1 (q^a)*i=2*m^2) : Compatible i p r H M := by
  have one (u : ℕ) (hu : u ∈ i.primeFactors) : ∃ j : ℕ, q^j ∈ residuals i u H M := by
    obtain ⟨d,hd,_,hblock⟩ := exists_block hq ha hm hio hu hH hl hr
    obtain ⟨j,heq⟩ := residual_eq_prime_pow hq hio.pos hblock
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d,hd,heq⟩,hqi.pow_left _,?_,?_⟩⟩
    · have hcon : q ≡ 1 [MOD M] := by simpa [Nat.ModEq,Nat.mod_eq_of_lt hM] using hqM
      simpa [Nat.ModEq,Nat.mod_eq_of_lt hM] using hcon.pow j
    · intro z hz hdq
      exact ((Nat.prime_dvd_prime_iff_eq hz hq).mp (hz.dvd_of_dvd_pow hdq)) ▸ hqM
  obtain ⟨j,hj⟩ := one p hpI
  obtain ⟨k,hk⟩ := one r hrI
  refine ⟨_,hj,_,hk,?_⟩
  by_cases h0 : j=0
  · exact .inl (by simp [h0])
  by_cases h0' : k=0
  · exact .inr (.inl (by simp [h0']))
  exact .inr (.inr (fun h => hq.not_dvd_one (h ▸ Nat.dvd_gcd (dvd_pow_self q h0) (dvd_pow_self q h0'))))

/-- The Hirakawa prime-times-square exclusion gives modulus sixteen for these
indices when the Euler exponent exceeds one. The universal modulus is four. -/
@[expose] def residueModulus (i : ℕ) : ℕ :=
  if ∃ l ∈ i.primeFactors, l*(i/l).sqrt^2=i then 16 else 4

theorem euler_modulus {N q a m i : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime)
    (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : sigma 1 (m^2)=q^a*i) : 1 < residueModulus i ∧ q%(residueModulus i)=1 := by
  unfold residueModulus
  split_ifs with h
  · refine ⟨by decide,?_⟩
    by_contra! hn
    obtain ⟨l,hlI,hshape⟩ := h
    apply euler_index_ne_prime_mul_square_of_residue_or_length hN ho hq hq4 ha4 ha hqm hform (.inl hn)
      l _ (.inr (Nat.prime_of_mem_primeFactors hlI))
    rw [hl,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos),hshape]
  · exact ⟨by decide,hq4⟩

end OddPerfect.IndexSieve
