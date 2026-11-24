module

public import OddPerfect.OddIndexLocal
public import OddPerfect.OddIndexSquareLift
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- Over an odd prime field, a geometric sum of length one modulo r−1
can take the value minus one only at base one and length minus one. -/
theorem residue_of_geometric_minus_one {p q n d r : ℕ} (hp : 1≤p)
    (hr : r.Prime) (hro : Odd r) (hdo : Odd d) (hn : 0<n) (hstep : r-1∣n-1)
    (hq : r∣q+1) (hret : geometricBlock p n=q^d) : r∣p-1 ∧ r∣n+1 := by
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨k,hk⟩ := hstep
  have hlen : n=1+(r-1)*k := by omega
  have hpw : (p:ZMod r)^n=p := by
    by_cases hz : (p:ZMod r)=0
    · simp [hz,zero_pow hn.ne']
    rw [hlen,pow_add,pow_one,pow_mul,ZMod.pow_card_sub_one_eq_one hz,one_pow,mul_one]
  have hqneg : (q:ZMod r)= -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa using (ZMod.natCast_eq_zero_iff _ _).mpr hq
  have hG : ((geometricBlock p n:ℕ):ZMod r)= -1 := by rw [hret,Nat.cast_pow,hqneg,hdo.neg_one_pow]
  have hgeom : ((geometricBlock p n:ℕ):ZMod r)*((p:ZMod r)-1) = (p:ZMod r)^n-1 := by
    simpa [geometricBlock] using geom_sum_mul (p:ZMod r) n
  rw [hG,hpw] at hgeom
  have hr2 : (2:ZMod r)≠0 := by
    intro H
    exact hro.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 r).mp H)) ▸ dvd_rfl)
  have hprod : (2:ZMod r)*((p:ZMod r)-1)=0 := by linear_combination -hgeom
  have hp1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hr2)
  have hn1 : (n:ZMod r) = -1 := by simpa [geometricBlock,hp1] using hG
  exact ⟨(ZMod.natCast_eq_zero_iff _ r).mp (by simp [Nat.cast_sub hp,hp1]),
    (ZMod.natCast_eq_zero_iff _ r).mp (by simp [hn1])⟩

/-- Every simultaneous nonresidue and order-length obstruction forces
the residue prime into both p−1 and j+3. -/
theorem odd_prime_power_index_forced_congruences {N q a m p j r : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) (hr : r.Prime) (hro : Odd r)
    (hlen : r-1∣(a+1)/2-1) (hstep : r-1∣j+1)
    (hn : ¬IsSquare (((a+1)/2:ℕ):ZMod r)) : r∣p-1 ∧ r∣j+3 := by
  let d := (a+1)/2
  obtain ⟨w,y,hbase,hsq,hret⟩ := odd_prime_power_index_three_equations hN ho hq hq4 ha4 hqm hform hp hj hi
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hw := dvd_root_of_exceptional_nonresidue hr hro hdo.pos hlen hn hbase hsq
  have hrq : r∣q+1 := hbase ▸ dvd_mul_of_dvd_right (hw.trans (dvd_pow_self w (by decide : 2≠0))) _
  exact residue_of_geometric_minus_one hp.one_le hr hro hdo (by omega : 0<j+2)
    (by simpa using hstep) hrq hret

/-- Every nonresidue prime selected by the shared order condition
occurs twice in the sum of the index prime and the feedback length. -/
theorem odd_prime_power_index_forced_square_congruence {N q a m p j r : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) (hr : r.Prime) (hro : Odd r)
    (hlen : r-1∣(a+1)/2-1) (hstep : r-1∣j+1)
    (hn : ¬IsSquare (((a+1)/2:ℕ):ZMod r)) : r^2 ∣ p+(j+2) := by
  let d := (a+1)/2
  obtain ⟨w,y,hbase,hsq,hret⟩ := odd_prime_power_index_three_equations hN ho hq hq4 ha4 hqm hform hp hj hi
  have hdo : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hw := dvd_root_of_exceptional_nonresidue hr hro hdo.pos hlen hn hbase hsq
  have hrq : r^2∣q+1 := hbase ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hw 2) _
  have hd := odd_prime_power_index_forced_congruences hN ho hq hq4 ha4 hqm hform hp hj hi hr hro hlen hstep hn
  apply geometric_minus_one_sq_lift hp.one_le hro hd.1 hd.2
  rw [hret]
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  have hqneg : (q:ZMod (r^2))= -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa using (ZMod.natCast_eq_zero_iff _ _).mpr hrq
  change (((q^d+1:ℕ)):ZMod (r^2))=0
  simp [hqneg,hdo.neg_one_pow]

private theorem product_prime_squares_dvd {z : ℕ} (R : Finset ℕ)
    (h : ∀ r∈R, r.Prime ∧ r^2∣z) : (∏ r∈R,r)^2∣z := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert r R hr ih =>
    have hR (s : ℕ) (hs : s∈R) := h s (mem_insert_of_mem hs)
    have hpr := h r (mem_insert_self _ _)
    have hc : r.Coprime (∏ s∈R,s) := Nat.coprime_prod_right_iff.mpr (fun s hs =>
      (Nat.coprime_primes hpr.1 (hR s hs).1).mpr (fun he => hr (he ▸ hs)))
    simpa [prod_insert hr,mul_pow] using ((hc.pow_left 2).pow_right 2).mul_dvd_of_dvd_of_dvd hpr.2 (ih hR)

/-- The pairwise coprime squares of the Euler half-length and every
selected nonresidue prime simultaneously divide p+j+2. -/
theorem odd_prime_power_index_product_square_dvd {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) (R : Finset ℕ)
    (hR : ∀ r∈R, r.Prime ∧ Odd r ∧ r-1∣(a+1)/2-1 ∧ r-1∣j+1 ∧ ¬IsSquare (((a+1)/2:ℕ):ZMod r)) :
    (∏ r∈insert ((a+1)/2) R,r)^2 ∣ p+(j+2) := by
  apply product_prime_squares_dvd
  intro r hr
  rcases mem_insert.mp hr with h|h
  · subst r
    exact ⟨(odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi).1,
      odd_prime_power_index_half_length_sq_dvd hN ho hq hq4 ha4 hqm hform hp hj hi⟩
  · obtain ⟨hr,hro,hlen,hstep,hn⟩ := hR r h
    exact ⟨hr,odd_prime_power_index_forced_square_congruence hN ho hq hq4 ha4 hqm hform hp hj hi hr hro hlen hstep hn⟩

end OddPerfect
