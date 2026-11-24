module

public import OddPerfect.IndexBaseField
public import OddPerfect.ExceptionalOrder

public section
namespace OddPerfect.IndexObstruction
open ArithmeticFunction

structure BaseRow where
  p : ℕ
  d : ℕ
  r : ℕ
  deriving Repr, DecidableEq

@[expose] def baseCover (K : ℕ) (ts : List BaseRow) : Bool :=
  (List.range K).all fun k =>
    let p := 8*k+1
    !(decide p.Prime) || (p-1).primeFactorsList.all fun d =>
      d%8 != 1 || ts.any fun c => c.p==p && c.d==d

theorem mem_of_base_cover {K p d : ℕ} {ts : List BaseRow} (hcover : baseCover K ts=true)
    (hp : p.Prime) (hp8 : p%8=1) (hd : d.Prime) (hd8 : d%8=1) (hdp : d∣p-1)
    (hlo : p<8*K+1) : ∃ c∈ts,c.p=p ∧ c.d=d := by
  let k := p/8
  have hk : k<K := by dsimp [k]; omega
  have H := List.all_eq_true.mp hcover k (List.mem_range.mpr hk)
  dsimp only at H
  rw [show 8*k+1=p by dsimp [k]; omega,decide_eq_true hp,Bool.not_true,Bool.false_or] at H
  have hm := List.all_eq_true.mp H d (Nat.mem_primeFactorsList'.mpr ⟨hd,hdp,by have := hp.one_lt; omega⟩)
  rw [hd8] at hm
  change (ts.any fun c => c.p==p && c.d==d)=true at hm
  simpa only [Bool.and_eq_true,beq_iff_eq] using List.any_eq_true.mp hm

@[expose] def BaseRow.validSquarefree (c : BaseRow) : Bool :=
  decide (c.r.Prime ∧ Odd c.r ∧ c.r<2*c.d-1) && squarefreeBaseTest c.p c.d c.r

@[expose] def BaseRow.validFixed (c : BaseRow) : Bool :=
  decide (c.r.Prime ∧ Odd c.r ∧ c.r<2*c.d-1) && fixedBaseTest c.p c.d c.r

private theorem least_euler_base_of_shape {q d w : ℕ} (qpos : 0<q)
    (h : q+1=2*d*w^2) : 2*d-1≤q := by
  have hw : 0<w := by by_contra! hn; simp_all
  have hle := Nat.le_mul_of_pos_right (2*d) (pow_pos hw 2)
  omega

/-- A covered list of empty residue fields excludes its entire range
of squarefree prime parts of prime-times-square Euler indices. -/
theorem prime_mul_square_index_prime_bound_of_cover {K : ℕ} {ts : List BaseRow}
    (hcover : baseCover K ts=true) (hgood : ∀ c∈ts,c.validSquarefree=true)
    {N q a m p t : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q∣m) (hform : N=q^a*m^2)
    (hp : p.Prime) (hi : sigma 1 (m^2)/q^a=p*t^2) : 8*K+1≤p := by
  let d := (a+1)/2
  obtain ⟨_,_,hmod⟩ := prime_mul_square_euler_index_order hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hi
  obtain ⟨hd,hd8,_,_⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hi
  have hfull : 8*d∣p-1 := (Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm
  have hp8 : p%8=1 := by
    have h8 := (dvd_mul_right 8 d).trans hfull
    have hpos := hp.one_lt
    omega
  by_contra! hlo
  obtain ⟨c,hc,hcp,hcd⟩ := mem_of_base_cover hcover hp hp8 hd hd8 ((dvd_mul_left d 8).trans hfull) hlo
  obtain ⟨⟨hr,hro,hrd⟩,ht⟩ := (show (c.r.Prime ∧ Odd c.r ∧ c.r<2*c.d-1) ∧ squarefreeBaseTest c.p c.d c.r=true by
    simpa [BaseRow.validSquarefree] using hgood c hc)
  obtain ⟨w,y,v,hw,hy,hv⟩ := prime_mul_square_euler_block_equations hN ho hq hq4 ha4 ha hqm hform hp hi
  rw [hcp,hcd] at ht
  rw [hcd] at hrd
  exact squarefreeBaseTest_excludes hr hro hq (hrd.trans_le (least_euler_base_of_shape hq.pos hw)) ht hw hy hv

/-- With the geometric return, a second finite certificate excludes
index primes at every odd prime-power index exponent. -/
theorem odd_index_prime_bound_of_base_cover {K : ℕ} {ts : List BaseRow}
    (hcover : baseCover K ts=true) (hgood : ∀ c∈ts,c.validFixed=true)
    {N q a m p j : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1)
    (ha4 : a%4=1) (hqm : ¬q∣m) (hform : N=q^a*m^2)
    (hp : p.Prime) (hj : Odd j) (hi : sigma 1 (m^2)/q^a=p^j) : 8*K+1≤p := by
  obtain ⟨_,hp8,_,_,h16,_⟩ := odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  let d := (a+1)/2
  obtain ⟨hd,hd8,_,hdp,_,_⟩ := odd_prime_power_euler_index_return hN ho hq hq4 ha4 hqm hform hp hj hi
  by_contra! hlo
  obtain ⟨c,hc,hcp,hcd⟩ := mem_of_base_cover hcover hp hp8 hd hd8 hdp hlo
  obtain ⟨⟨hr,hro,hrd⟩,ht⟩ := (show (c.r.Prime ∧ Odd c.r ∧ c.r<2*c.d-1) ∧ fixedBaseTest c.p c.d c.r=true by
    simpa [BaseRow.validFixed] using hgood c hc)
  obtain ⟨w,y,v,hw,hy,hrep,hv⟩ := odd_prime_power_index_four_equations hN ho hq hq4 ha4 hqm hform hp hj hi
  rw [hcp,hcd] at ht
  rw [hcd] at hrd
  exact fixedBaseTest_excludes hr hro hq (hrd.trans_le (least_euler_base_of_shape hq.pos hw))
    (by omega) (by simpa using h16) ht hw hy hv hrep

end OddPerfect.IndexObstruction
