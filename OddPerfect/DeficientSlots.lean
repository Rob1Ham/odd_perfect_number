module

public import OddPerfect.DeficientLargeSecond
public import OddPerfect.PrimeCover
import all OddPerfect.PrimeSlots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

public section
namespace OddPerfect.DeficientSlots
open Finset ArithmeticFunction SpoofBox

/-- The first four slots are actual prime powers of even exponent.
The fifth has Euler residues and is unordered with respect to the four
primes. The deficient-perfect case fixes its exponent to one. -/
structure Real (z : Fin 5 → ℕ × ℕ) : Prop where
  prime : ∀ i : Fin 4, (z i.castSucc).1.Prime
  increasing : StrictMono (fun i : Fin 4 => (z i.castSucc).1)
  evenExp : ∀ i : Fin 4, Even (z i.castSucc).2
  multiplier : (z 4).1%4=1
  specialExponent : (z 4).2%4=1
  balance : formalSigma univ (fun i => (z i).1) (fun i => (z i).2) =
    2*∏ i, (z i).1^(z i).2

@[expose] def historical (i : Fin 5) : ℕ × ℕ := ![(3,2),(7,2),(11,2),(13,2),(22021,1)] i

@[expose] def root (p : ℕ) : Vector Slot 5 :=
  #v[⟨false,3,3,2,0⟩,⟨false,p,p,2,0⟩,⟨false,3,0,2,0⟩,⟨false,3,0,2,0⟩,⟨true,5,0,1,1⟩]

/-- A divisor required by an actual or formal slot either occurs among
the four prime bases or divides the multiplier, even if the latter has
repeated prime factors. -/
theorem Real.forces {z : Fin 5 → ℕ × ℕ} (h : Real z) {r : ℕ} (hr : r.Prime) (ho : Odd r)
    (i : Fin 5) (hs : r ∣ ∑ j ∈ range ((z i).2+1), (z i).1^j) :
    (∃ j : Fin 4, (z j.castSucc).1 = r) ∨ r ∣ (z 4).1 := by
  have hd : r ∣ formalSigma univ (fun j => (z j).1) (fun j => (z j).2) :=
    hs.trans (dvd_prod_of_mem _ (mem_univ i))
  rw [h.balance] at hd
  obtain ⟨j,_,hj⟩ := (hr.prime.dvd_finsetProd_iff _).mp (ho.coprime_two_right.dvd_of_dvd_mul_left hd)
  have hb := hr.dvd_of_dvd_pow hj
  by_cases last : j=4
  · exact Or.inr (last ▸ hb)
  · have ne : j.val≠4 := fun eq => last (Fin.ext eq)
    let k : Fin 4 := ⟨j.val,by have := j.isLt; omega⟩
    exact Or.inl ⟨k,((Nat.prime_dvd_prime_iff_eq hr (h.prime k)).mp hb).symm⟩

@[expose] def Closed (rows : Vector Slot 5) (multiple : ℕ) : Prop :=
  ∀ z, Real z → (∀ i : Fin 5, rows[i].Fits (z i)) → multiple∣(z 4).1 → z=historical

set_option maxHeartbeats 1000000 in
/-- Ordered true prime powers of a square and a single formal Euler component. -/
theorem fourPrimeRepresentation {n x e : ℕ} (ho : Odd n) (card : n.primeFactors.card=4)
    (sq : IsSquare n) (mod4 : x%4=1) (emod : e%4=1)
    (balance : sigma 1 n * (∑ j∈range (e+1),x^j) = 2*(n*x^e)) :
    ∃ z : Fin 5 → ℕ × ℕ, Real z ∧
      (∀ i : Fin 4, z i.castSucc = primeSlots n card i) ∧ z 4=(x,e) ∧
      (∏ i : Fin 4, (z i.castSucc).1^(z i.castSucc).2)=n := by
  let P := n.primeFactors.orderEmbOfFin card
  let f (i : Fin 4) : ℕ × ℕ := (P i,n.factorization (P i))
  let z : Fin 5 → ℕ × ℕ := Fin.snoc f (x,e)
  have slots (i : Fin 4) : z i.castSucc = f i := Fin.snoc_castSucc ..
  have last : z (Fin.last 4) = (x,e) := Fin.snoc_last ..
  have mem (i : Fin 4) : P i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem card i
  have prime (i : Fin 4) := Nat.prime_of_mem_primeFactors (mem i)
  have embprod (g : ℕ→ℕ) : (∏ i : Fin 4, g (P i))=∏ p∈n.primeFactors,g p := by
    rw [←n.primeFactors.map_orderEmbOfFin_univ card,prod_map]; rfl
  have value : (∏ i : Fin 4, (f i).1^(f i).2)=n :=
    (embprod (fun p => p^n.factorization p)).trans (Nat.prod_primeFactors_pow_factorization ho.pos.ne').symm
  have sum : (∏ i : Fin 4, ∑ j∈range ((f i).2+1),(f i).1^j)=sigma 1 n := by
    trans ∏ p∈n.primeFactors, sigma 1 (p^n.factorization p)
    · rw [←embprod (fun p => sigma 1 (p^n.factorization p))]
      apply prod_congr rfl
      intro i _
      change (∑ j∈range (n.factorization (P i)+1),(P i)^j)=sigma 1 ((P i)^n.factorization (P i))
      exact (sigma_one_apply_prime_pow (prime i)).symm
    · exact (isMultiplicative_sigma.multiplicative_factorization _ ho.pos.ne').symm
  refine ⟨z,?_,slots,last,by simpa only [slots] using value⟩
  refine ⟨fun i => (slots i).symm ▸ prime i,?_,?_,?_,?_,?_⟩
  · intro i j lt
    simpa only [slots] using P.strictMono lt
  · intro i
    rw [slots]
    exact Nat.isSquare_iff_even_factorization.mp sq (P i) (prime i)
  · change (z (Fin.last 4)).1%4=1
    simpa only [last] using mod4
  · change (z (Fin.last 4)).2%4=1
    simpa only [last] using emod
  · unfold formalSigma
    rw [Fin.prod_univ_castSucc,Fin.prod_univ_castSucc (fun i : Fin 5 => (z i).1^(z i).2)]
    simp only [slots,last]
    rw [sum,value]
    exact balance

/-- Realization of the unbounded four-prime problem in the five slots.
Only the positions of the four true primes have been sorted. -/
theorem realization {n d : ℕ} (h : DeficientPerfectWith n d) (ho : Odd n)
    (card : n.primeFactors.card=4) :
    ∃ p ∈ ([5,7,11,13,17] : List ℕ), ∃ z : Fin 5 → ℕ × ℕ,
      Real z ∧ (∀ i : Fin 5, (root p)[i].Fits (z i)) ∧
      (∏ i : Fin 4, (z i.castSucc).1^(z i.castSucc).2)=n := by
  obtain ⟨x,hx,h1,hpair,_⟩ := h.tothPair ho
  obtain ⟨sq,mod4⟩ := toth_odd_cofactor_square hpair hx
  have balance : sigma 1 n*(∑ j∈range (1+1),x^j)=2*(n*x^1) := by
    simpa only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,Nat.add_comm 1 x] using hpair.2.2
  obtain ⟨z,R,sz,last,value⟩ := fourPrimeRepresentation ho card sq mod4 (by decide : 1%4=1) balance
  let P := n.primeFactors.orderEmbOfFin card
  let f (i : Fin 4) : ℕ × ℕ := (P i,n.factorization (P i))
  have slots (i : Fin 4) : z i.castSucc=f i := sz i
  have mem (i : Fin 4) : P i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem card i
  have prime (i : Fin 4) := Nat.prime_of_mem_primeFactors (mem i)
  have surj (p) (hp : p∈n.primeFactors) : ∃ i : Fin 4, P i=p := by
    change p∈Set.range (n.primeFactors.orderEmbOfFin card)
    rwa [n.primeFactors.range_orderEmbOfFin card]
  have lower (i : Fin 4) : 3≤P i := by
    have := (prime i).two_le
    have oddp := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem i)))
    omega
  have pzero : P 0=3 := by
    obtain ⟨i,hi⟩ := surj 3 (Nat.mem_primeFactors.mpr ⟨by decide,
      three_dvd_of_deficientPerfect_four h ho card.le,ho.pos.ne'⟩)
    exact le_antisymm ((P.monotone (Fin.zero_le i)).trans_eq hi) (lower 0)
  obtain ⟨p,hp,hp3,hp17⟩ := second_prime_le_seventeen_of_deficientPerfect_four h ho card.le
  obtain ⟨j,rfl⟩ := surj p hp
  have jpos : (1:Fin 4)≤j := by
    by_contra! lt
    have hz : j=0 := Fin.ext (by change j.val<1 at lt; omega)
    rw [hz,pzero] at hp3; omega
  have p1lo : 3<P 1 := lt_of_eq_of_lt pzero.symm (P.strictMono (by decide : (0:Fin 4)<1))
  have p1hi := (P.monotone jpos).trans hp17
  have candidates : ∀ j : Fin 18, j.val.Prime → 3<j.val → j.val∈([5,7,11,13,17] : List ℕ) :=
    by decide +kernel
  refine ⟨P 1,candidates ⟨_,by omega⟩ (prime 1) p1lo,z,R,?_,value⟩
  have ordinary (i : Fin 4) (lo hi : ℕ) (hl : lo≤P i) (hh : hi=0 ∨ P i≤hi) :
      (⟨false,lo,hi,2,0⟩ : Slot).Fits (z i.castSucc) := by
    have he := (prime i).factorization_pos_of_dvd ho.pos.ne' (Nat.dvd_of_mem_primeFactors (mem i))
    have even := Nat.even_iff.mp (Nat.isSquare_iff_even_factorization.mp sq (P i) (prime i))
    have oddp := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem i)))
    rw [slots]
    exact ⟨(prime i).one_lt,he,hl,hh,by dsimp [f]; omega,Or.inl rfl,oddp,even⟩
  intro i
  fin_cases i
  · exact ordinary 0 3 3 (lower 0) (.inr pzero.le)
  · exact ordinary 1 _ _ le_rfl (.inr le_rfl)
  · exact ordinary 2 3 0 (lower 2) (.inl rfl)
  · exact ordinary 3 3 0 (lower 3) (.inl rfl)
  · change (⟨true,5,0,1,1⟩ : Slot).Fits (z (Fin.last 4))
    change (⟨true,5,0,1,1⟩ : Slot).Fits (z 4)
    rw [last]
    exact ⟨h1,(by decide : 0<1),(by omega : 5≤x),.inl rfl,le_rfl,.inr le_rfl,mod4,(by decide : 1%4=1)⟩

/-- A complete interval cover implies the classification, including the
actual omitted divisor. -/
theorem classification_of_covers
    (cover : ∀ p ∈ ([5,7,11,13,17] : List ℕ), Closed (root p) 1)
    {n d : ℕ} (ho : Odd n) (card : n.primeFactors.card=4) :
    DeficientPerfectWith n d ↔ n=9018009 ∧ d=819 := by
  constructor
  · intro h
    obtain ⟨p,hp,z,R,fit,value⟩ := realization h ho card
    rw [cover p hp z R fit (one_dvd _)] at value
    have n0 : n=9018009 := value.symm.trans (by decide +kernel)
    refine ⟨n0,?_⟩
    rw [n0] at h
    exact Nat.add_left_cancel (h.2.trans descartes_cofactor_deficientPerfect.2.symm)
  · rintro ⟨rfl,rfl⟩
    exact descartes_cofactor_deficientPerfect

end OddPerfect.DeficientSlots
