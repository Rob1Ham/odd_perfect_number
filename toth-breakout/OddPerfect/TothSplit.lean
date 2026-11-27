module

public import OddPerfect.TothCandidates
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect.Toth

open Finset ArithmeticFunction

@[expose] def squaredSum (p e : ℕ) : ℕ := ∑ j ∈ range (2*e+1),p^j

/-- Split the residual square root at a prime p using its exact exponent.
The original cofactor thus contributes the length 2e+1 geometric sum. -/
theorem closed_split {B D S p a : ℕ} (hp : p.Prime) (gap : ∀ j ∈ Ioo p a, ¬j.Prime)
    (next : ∀ e, D*p^e≤B → Closed B (D*p^e) (S*squaredSum p e) a) : Closed B D S p := by
  intro m x h
  obtain ⟨e,r,hr,hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd h.pos.ne' p hp.ne_one
  have hrpos : 0<r := by by_contra! he; have := h.pos; simp [hm,Nat.eq_zero_of_le_zero he] at this
  have hc : (p^e).Coprime r := (hp.coprime_pow_of_not_dvd hr).symm
  have hx : D*m=(D*p^e)*r := by rw [hm,mul_assoc]
  have he : D*p^e≤B := (Nat.le_mul_of_pos_right _ hrpos).trans (hx ▸ h.bound)
  have hs : sigma 1 (m^2)=squaredSum p e * sigma 1 (r^2) := by
    rw [hm,mul_pow,isMultiplicative_sigma.map_mul_of_coprime ((hc.pow_left 2).pow_right 2),
      ←pow_mul,sigma_one_apply_prime_pow hp,squaredSum,Nat.mul_comm e 2]
  have hP : 0<squaredSum p e := by
    apply sum_pos' (by intros; omega)
    exact ⟨0,mem_range.mpr (Nat.succ_pos _),by simp⟩
  have sub := next e he r x
  have bound : (D*p^e)*r≤B := hx ▸ h.bound
  rw [hx]
  apply sub ⟨hrpos,Nat.mul_pos h.prefix_pos (pow_pos hp.pos e),Nat.mul_pos h.sumpos hP,
    h.large,h.residue,?_,bound,?_⟩
  · intro q hq
    have hd := Nat.dvd_of_mem_primeFactors hq
    have hqm : q∣m := hm ▸ hd.trans (dvd_mul_left _ _)
    have hq' := Nat.prime_of_mem_primeFactors hq
    have hpq := h.least q (Nat.mem_primeFactors.mpr ⟨hq',hqm,h.pos.ne'⟩)
    by_contra! hl
    exact gap q (mem_Ioo.mpr ⟨lt_of_le_of_ne hpq (fun hh => hr (hh ▸ hd)),hl⟩) hq'
  · simpa only [hs,hx,mul_assoc] using h.balance

theorem small_odd_pair_of_closed {b n x : ℕ} (hc : Closed b 1 1 3) (h : TothPair n x)
    (ho : Odd x) (h1 : 1<x) (hb : n≤b^2) : n=9018009 ∧ x=22021 := by
  obtain ⟨m,hm,hmb,hmn,hx,hres⟩ := toth_odd_square_root h ho h1 hb
  have hh : Candidate b 1 1 3 m x := by
    refine ⟨hm.pos,by decide,by decide,hx,hres,?_,by simpa using hmb,?_⟩
    · intro p hp
      have := Nat.odd_iff.mp (Odd.of_dvd_nat hm (Nat.dvd_of_mem_primeFactors hp))
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      omega
    · simpa [←hmn,mul_assoc] using h.2.2
  obtain ⟨u,v⟩ := hc m x hh
  simp only [one_mul] at u
  exact ⟨by simp [hmn,u],v⟩

end OddPerfect.Toth
