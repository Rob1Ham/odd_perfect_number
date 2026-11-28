module

public import OddPerfect.EvenIndexHigherBound
public import OddPerfect.EvenIndexRadicalCutoff
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction

/-- The even-index base is subexponential in its exponent, obtained
by lifting to the integer square root of the exponent. -/
theorem even_index_base_subexponential {q p s u : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    p≤8*(u+1)*128^(2*u).sqrt := by
  let j := 2*u
  let k := j.sqrt
  have hk : 0<k := Nat.sqrt_pos.mpr (by dsimp [j]; omega)
  have hj : k≤j := Nat.sqrt_le_self _
  rcases even_index_base_higher_lift_bound hp hpo hs hk hj hσq hplus hσs with h|h
  · exact h
  have hrad := (even_index_cofactor_radical_le hp hs hσq hplus hσs).trans
    (Nat.mul_le_mul_left (u+1) (Nat.pow_le_pow_right (by decide : 0<4) (Nat.sub_le _ _)))
  have hj2 : j≤(k+1)*(k+1) := (Nat.lt_succ_sqrt j).le
  have hw : u+1≤(u+1)^(k+1) := Nat.le_self_pow (Nat.succ_ne_zero _) _
  have H : p^(k+1)≤(2*(u+1)*4^(k+1))^(k+1) := by
    calc p^(k+1) ≤ 2^(k+1)*((u+1)*4^j) := h.trans (Nat.mul_le_mul_left _ hrad)
         _ ≤ 2^(k+1)*((u+1)^(k+1)*4^((k+1)*(k+1))) :=
           Nat.mul_le_mul_left _ (Nat.mul_le_mul hw (Nat.pow_le_pow_right (by decide) hj2))
         _ = _ := by simp only [mul_pow,pow_mul]; ring
  have hbase : p≤2*(u+1)*4^(k+1) := by
    by_contra! hlt
    exact H.not_gt (Nat.pow_lt_pow_left hlt (Nat.succ_ne_zero _))
  calc p ≤ 2*(u+1)*4^(k+1) := hbase
       _ = 8*(u+1)*4^k := by rw [pow_succ]; ring
       _ ≤ 8*(u+1)*128^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)

/-- At any exact component having even prime-power index the
subexponential base bound gives the corresponding ambient size bound. -/
theorem even_prime_power_component_subexponential_bounds {N q a b i p u : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (ha : 0<a)
    (hform : N=q^a*b) (hqb : ¬q ∣ b) (hl : sigma 1 b=q^a*i)
    (hr : sigma 1 (q^a)*i=2*b) (hp : p.Prime) (hu : 0<u) (hi : i=p^(2*u)) :
    let B := 8*(u+1)*128^(2*u).sqrt
    p≤B ∧ N<2*B^(6*u) := by
  obtain ⟨hpo,s,hs,hcop,hqm,hform',hσ,hplus,hσs,_⟩ :=
    even_prime_power_component_cofactor_data hN ho hq ha hform hqb hl hr hp hu hi
  have hb := even_index_base_subexponential hp hpo hs hu hσ hplus hσs
  have hQ := (exponent_one_size_lt_twice_index_cube hN ho hq hqm hform').2.2
  have hσm : sigma 1 ((p^u*s)^2)=q*p^(2*u) := by
    rw [mul_pow,isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left u |>.pow_left 2 |>.pow_right 2),
      ←pow_mul,show u*2=2*u by omega,hσ,hσs]
  rw [hσm,Nat.mul_div_cancel_left _ hq.pos,←pow_mul,show 2*u*3=6*u by omega] at hQ
  exact ⟨hb,hQ.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _))⟩

end OddPerfect
