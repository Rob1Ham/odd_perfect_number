module

public import OddPerfect.OddIndexLocal
import all OddPerfect.EulerSquareClass
import all OddPerfect.GeometricSquareClass

public section
namespace OddPerfect
open ArithmeticFunction

private theorem square_of_square_times_square {A m k : ℕ} (hm : m≠0)
    (he : m^2=A*k^2) : IsSquare A := by
  have hA : A≠0 := fun h => (pow_ne_zero 2 hm) (by simpa [h] using he)
  have hk : k≠0 := fun h => (pow_ne_zero 2 hm) (by simpa [h] using he)
  apply Nat.isSquare_iff_even_factorization.mpr
  intro r _
  have h := congrArg (fun n : ℕ => n.factorization r) he
  rw [Nat.factorization_mul hA (pow_ne_zero 2 hk),Finsupp.add_apply,
    Nat.factorization_pow,Nat.factorization_pow,Finsupp.smul_apply,Finsupp.smul_apply,smul_eq_mul,smul_eq_mul] at h
  exact Nat.even_iff.mpr (by omega)

/-- At a prime-times-square Euler index, the divisor sum of the first
half has exactly the same squarefree part as the index. -/
theorem prime_mul_square_euler_first_block {N q a m p t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hi : sigma 1 (m^2)/q^a=p*t^2) :
    ∃ v : ℕ, geometricBlock q ((a+1)/2)=p*v^2 := by
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _)).pos
  obtain ⟨i,_,hl,hr, _⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  have hshape := hi
  rw [hl,Nat.mul_div_cancel_left i (pow_pos hq.pos _)] at hshape
  obtain ⟨hblocks,_,_,_,_⟩ := euler_half_blocks hq hq4 ha4 hr
  change m^2=A*B*i at hblocks
  have hB : IsSquare B := Classical.byContradiction (fun h =>
    euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform h p t (Or.inr hp) hi)
  obtain ⟨y,hy⟩ := hB
  have hs : m^2=(p*A)*(y*t)^2 := by rw [hblocks,hshape,hy]; ring
  obtain ⟨z,hz⟩ := square_of_square_times_square hm.ne' hs
  have hd : p∣z^2 := ⟨A,by rw [pow_two,←hz]⟩
  obtain ⟨v,hv⟩ := hp.dvd_of_dvd_pow hd
  refine ⟨v,Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
  change p*A=p*(p*v^2)
  rw [hz,hv]
  ring

/-- Three simultaneous equations constrain the squarefree part p of
every prime-times-square Euler index with nontrivial half-length. -/
theorem prime_mul_square_euler_block_equations {N q a m p t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hi : sigma 1 (m^2)/q^a=p*t^2) :
    let d := (a+1)/2
    ∃ w y v, q+1=2*d*w^2 ∧ q^d+1=2*y^2 ∧ geometricBlock q d=p*v^2 := by
  let d := (a+1)/2
  obtain ⟨_,_,hq16,w,hw⟩ := prime_mul_square_index_forces_exceptional_prime_length
    hN ho hq hq4 ha4 ha hqm hform (Or.inr hp) hi
  have hB : IsSquare ((q^d+1)/2) := Classical.byContradiction (fun h =>
    euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform h p t (Or.inr hp) hi)
  obtain ⟨y,hy⟩ := hB
  obtain ⟨v,hv⟩ := prime_mul_square_euler_first_block hN ho hq hq4 ha4 ha hqm hform hp hi
  have hpodd : q^d%2=1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 2] from (by change q%2=1; omega)).pow d
  exact ⟨w,y,v,by rw [mul_assoc,←hw]; omega,by change q^d+1=2*y^2; rw [pow_two]; omega,hv⟩

/-- A fourth integral equation augments the three local screening
conditions at an odd prime-power index. -/
theorem odd_prime_power_index_four_equations {N q a m p j : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hj : Odd j)
    (hi : sigma 1 (m^2)/q^a=p^j) :
    let d := (a+1)/2
    ∃ w y v, q+1=2*d*w^2 ∧ q^d+1=2*y^2 ∧ geometricBlock p (j+2)=q^d ∧ geometricBlock q d=p*v^2 := by
  obtain ⟨w,y,h1,h2,h3⟩ := odd_prime_power_index_three_equations hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨ha,_,_,_,_,_⟩ := odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj hi
  obtain ⟨k,hk⟩ := hj
  have hshape : sigma 1 (m^2)/q^a=p*(p^k)^2 := by rw [hi,show j=k*2+1 by omega,pow_succ,pow_mul,mul_comm]
  obtain ⟨v,h4⟩ := prime_mul_square_euler_first_block hN ho hq hq4 ha4 ha hqm hform hp hshape
  exact ⟨w,y,v,h1,h2,h3,h4⟩

private theorem alternating_ones {q d : ℕ} (hd : Odd d) :
    geometricBlock q d ≡ 1 [MOD q+1] := by
  let R := ZMod (q+1)
  have hq : (q:R) = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add,Nat.cast_one] using (ZMod.natCast_self (q+1))
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp only [geometricBlock,Nat.cast_sum,Nat.cast_pow,hq,Nat.cast_one,
    neg_one_geom_sum,ite_eq_right (Nat.not_even_iff_odd.mpr hd)]

/-- The same square root tests both neighboring moduli. In particular the
index prime is a quadratic residue modulo every prime divisor of q+1. -/
theorem prime_mul_square_euler_neighbor_congruences {N q a m p t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a)
    (hqm : ¬q∣m) (hform : N=q^a*m^2) (hp : p.Prime) (hi : sigma 1 (m^2)/q^a=p*t^2) :
    let d := (a+1)/2
    ∃ v, p*v^2 ≡ 1 [MOD q+1] ∧ p*v^2 ≡ d [MOD q-1] ∧
      ∀ r, r∣q+1 → IsSquare (p:ZMod r) := by
  let d := (a+1)/2
  obtain ⟨v,hv⟩ := prime_mul_square_euler_first_block hN ho hq hq4 ha4 ha hqm hform hp hi
  change geometricBlock q d=p*v^2 at hv
  have hoD : Odd d := Nat.odd_iff.mpr (by dsimp [d]; omega)
  have hplus : p*v^2 ≡ 1 [MOD q+1] := hv ▸ alternating_ones (q:=q) hoD
  have hq1 : q ≡ 1 [MOD q-1] := ((Nat.modEq_iff_dvd' hq.one_le).mpr dvd_rfl).symm
  have hminus : geometricBlock q d ≡ d [MOD q-1] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hq1
    simp only [Nat.cast_one] at he
    simp [geometricBlock,he]
  refine ⟨v,hplus,hv ▸ hminus,?_⟩
  intro r hr
  have hrel := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hplus.of_dvd hr)
  push_cast at hrel
  refine ⟨(p:ZMod r)*v,?_⟩
  calc (p:ZMod r) = p*((p:ZMod r)*v^2) := by rw [hrel,mul_one]
       _ = _ := by ring

end OddPerfect
