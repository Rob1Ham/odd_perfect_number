module

public import OddPerfect.ExceptionalLength
public import OddPerfect.ChenLuo

public section
namespace OddPerfect
open ArithmeticFunction

/-- In the exceptional prime-times-square case, the full Euler index is
one modulo eight. Both exceptional half-length factors are one modulo eight. -/
theorem prime_mul_square_euler_index_one_mod_eight {N q a m : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (l t : ℕ) (hl : l=1 ∨ l.Prime) (hs : sigma 1 (m^2)/q^a=l*t^2) :
    sigma 1 (m^2)/q^a %8=1 := by
  obtain ⟨_,hd8,hq16,_⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform hl hs
  have hq8 : q ≡ 1 [MOD 8] := by change q%8=1; omega
  have hhalf : (q+1)/2 ≡ 1 [MOD 8] := by change ((q+1)/2)%8=1; omega
  have hd : (a+1)/2 ≡ 1 [MOD 8] := hd8
  have hσ := sigma_square_mod_eight_of_euler hN ho hq hq4 ha4 hqm hform
  have hone : sigma 1 (m^2) ≡ 1 [MOD 8] := by
    simpa using hσ.trans (hq8.mul (hhalf.mul hd))
  obtain ⟨i,_,hi,_,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hi,Nat.mul_div_cancel_left i (Nat.pow_pos hq.pos)]
  have hqi : q^a*i ≡ i [MOD 8] := by simpa using (hq8.pow a).mul_right i
  exact hqi.symm.trans (hi ▸ hone)

end OddPerfect
