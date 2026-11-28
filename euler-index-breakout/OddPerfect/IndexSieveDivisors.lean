module

public import OddPerfect.IndexSieveExactLengths
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.IndexSieve

open Finset

/-- Extend a divisor set by multiplying any of its elements by a new prime factor. -/
@[expose] def extendDivisors (p : ℕ) (S : Finset ℕ) : Finset ℕ := S ∪ S.image (p*·)

private theorem extend_divisors_prime {p n : ℕ} (hp : p.Prime) (hn : n≠0) :
    extendDivisors p n.divisors=(p*n).divisors := by
  ext d
  simp only [extendDivisors,Finset.mem_union,Finset.mem_image,Nat.mem_divisors]
  constructor
  · rintro (hd|⟨z,hz,rfl⟩)
    · exact ⟨hd.1.trans (dvd_mul_left _ _),mul_ne_zero hp.ne_zero hn⟩
    · exact ⟨Nat.mul_dvd_mul_left _ hz.1,mul_ne_zero hp.ne_zero hn⟩
  · rintro ⟨hd,_⟩
    by_cases hpd : p ∣ d
    · obtain ⟨z,rfl⟩ := hpd
      exact .inr ⟨z,⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hd,hn⟩,rfl⟩
    · exact .inl ⟨(hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left hd,hn⟩

/-- Divisor enumeration via the prime factor list. In particular it avoids
testing every integer through the large candidate product of two lengths. -/
@[expose] def fastDivisors (n : ℕ) : Finset ℕ :=
  if n=0 then ∅ else n.primeFactorsList.foldr extendDivisors {1}

theorem fastDivisors_eq (n : ℕ) : fastDivisors n=n.divisors := by
  by_cases hn : n=0
  · simp [fastDivisors,hn]
  have list (L : List ℕ) (hL : ∀ p ∈ L, p.Prime) : L.foldr extendDivisors {1}=L.prod.divisors := by
    induction L with
    | nil => simp
    | cons p L ih =>
      have hp := hL p List.mem_cons_self
      have hrest (u : ℕ) (hu : u ∈ L) : u.Prime := hL u (List.mem_cons_of_mem _ hu)
      have hpos : L.prod≠0 := List.prod_ne_zero fun h0 => (hrest 0 h0).ne_zero rfl
      simpa only [List.foldr_cons,List.prod_cons,ih hrest] using extend_divisors_prime hp hpos
  simpa [fastDivisors,hn,Nat.prod_primeFactorsList hn] using list n.primeFactorsList (fun _ hp => Nat.prime_of_mem_primeFactorsList hp)

end OddPerfect.IndexSieve
