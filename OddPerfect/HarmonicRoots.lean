module

public import OddPerfect.HarmonicChain
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.HarmonicChain
open FactorBudget ArithmeticFunction Finset

/-- A finite list of exponents suffices when p^E meets the component cap. -/
theorem allowed_list {p r E e : ℕ} (xs : List ℕ) (hp : 0<p) (hE : 10^15 ≤ p^E)
    (tests : ∀ j : Fin E, 0<j.val → r∣j.val+1 → p^j.val%4=1 → j.val ∈ xs)
    (he : Allowed p e) (hr : r∣e+1) : e ∈ xs := by
  have hlt : e<E := by
    by_contra! h
    exact he.2.1.not_ge (hE.trans (Nat.pow_le_pow_right hp h))
  exact tests ⟨e,hlt⟩ he.1 hr he.2.2

/-- A trial divisor supplied for every skipped integer proves that the
prime list covers its entire half-open interval. -/
theorem prime_mem_of_witnesses {a p : ℕ} (primes factors : List ℕ)
    (check : ∀ j : Fin factors.length, a+j.val ∈ primes ∨
       (1<factors[j] ∧ factors[j]<a+j.val ∧ factors[j]∣a+j.val))
    (hp : p.Prime) (hlo : a≤p) (hhi : p<a+factors.length) : p ∈ primes := by
  let j : Fin factors.length := ⟨p-a,by omega⟩
  have eq : a+j.val=p := by dsimp [j]; omega
  have hc := check j
  rw [eq] at hc
  rcases hc with hm|⟨h1,hlt,hd⟩
  · exact hm
  · rcases (Nat.dvd_prime hp).mp hd with h|h <;> omega

@[expose] def RootAt (r p : ℕ) : Prop :=
  ∀ e, Allowed p e → r∣e+1 → Closed r (root.extend p e)

@[expose] def RootRange (r lo hi : ℕ) : Prop := ∀ p, lo≤p → p<hi → p.Prime → RootAt r p

theorem root_join {r lo mid hi : ℕ} (l : RootRange r lo mid) (u : RootRange r mid hi) :
    RootRange r lo hi := by
  intro p h1 h2 hp
  by_cases h : p<mid
  · exact l p h1 h hp
  · exact u p (by omega) h2 hp

/-- A prime in the divisor count must divide the length of an actual
prime component. The size of that component bounds the base. -/
theorem impossible_of_roots {n r M : ℕ} (hr : r.Prime) (hM : 10^15≤M^(r-1))
    (tree : RootRange r 3 M) (H : Small n r) (hd : r∣n.divisors.card) : False := by
  rw [Nat.card_divisors H.odd.pos.ne'] at hd
  obtain ⟨p,hp,hdiv⟩ := (hr.prime.dvd_finsetProd_iff _).mp hd
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  obtain ⟨he,v,hv⟩ := split_at H (root_realizes n) hpr hpn
  have hmin := Nat.le_of_dvd (Nat.succ_pos (n.factorization p)) hdiv
  have hlt : p<M := by
    by_contra! h
    exact he.2.1.not_ge (hM.trans ((Nat.pow_le_pow_left h _).trans
      (Nat.pow_le_pow_right hpr.pos (by omega))))
  have h3 : 3≤p := by
    have := hpr.two_le
    have := Nat.odd_iff.mp (H.odd.of_dvd_nat hpn)
    omega
  exact tree p h3 hlt hpr _ he hdiv n v H hv

end OddPerfect.HarmonicChain
