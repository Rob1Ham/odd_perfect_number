module

public import OddPerfect.EvenPrimePowerParity
public import OddPerfect.ProductGap
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

public section
namespace OddPerfect
open ArithmeticFunction Finset

/-- An even prime-power Euler index p^(2u) with cofactor s bounds p in
terms of the radical of s. The only removed labels are the opening
labels of the cofactor primes, so repeated numerical labels cause no loss. -/
theorem even_index_base_le_cofactor_radical {p q s u : ℕ}
    (hp : p.Prime) (hs : Odd s) (hu : 0<u) (hσq : sigma 1 (p^(2*u))=q)
    (hplus : q+1=2*s^2) (hσs : sigma 1 (s^2)=p^(2*u)) :
    p≤2*(s.primeFactors.card+3)*s.primeFactors.prod id := by
  let S := s.primeFactors
  let j := 2*u
  let c (r : ℕ) := r^(2*s.factorization r+1)
  let f (r : ℕ) := sigma 1 (r^(2*s.factorization r))
  let P := S.prod id
  let R := S.prod (fun r => r-1)
  have hcen (r : ℕ) (hr : r∈S) : c r-1=f r*(r-1) := by
    have hrp := Nat.prime_of_mem_primeFactors hr
    dsimp [c,f]
    rw [sigma_one_apply_prime_pow hrp]
    exact (geom_sum_mul_of_one_le hrp.one_le _).symm
  have hfp : S.prod f=p^j := by
    rw [←hσs,(isMultiplicative_sigma (k:=1)).multiplicative_factorization _ (pow_ne_zero _ hs.pos.ne')]
    change _ = ∏ r ∈ (s^2).primeFactors,sigma 1 (r^((s^2).factorization r))
    simp [S,f,Nat.primeFactors_pow s (by decide : 2≠0),Nat.factorization_pow]
  have hcprod : S.prod c=s^2*P := by
    have h := (Nat.prod_primeFactors_pow_factorization hs.pos.ne').symm
    change (∏ r ∈ S,r^s.factorization r)=s at h
    calc S.prod c = ∏ r ∈ S,(r^s.factorization r)^2*r := by
            apply Finset.prod_congr rfl
            intro r _
            change r^(2*s.factorization r+1)=(r^s.factorization r)^2*r
            rw [pow_succ,pow_mul']
         _ = s^2*P := by rw [Finset.prod_mul_distrib,Finset.prod_pow,h]; rfl
  have hpred : S.prod (fun r => c r-1)=p^j*R := by
    rw [Finset.prod_congr rfl hcen,Finset.prod_mul_distrib,hfp]
  have hqmul : q*(p-1)=p^(j+1)-1 := by
    rw [←hσq,sigma_one_apply_prime_pow hp]
    exact geom_sum_mul_of_one_le hp.one_le _
  let L : Finset ℕ := {0,1,2}
  let opening (t : ℕ) := if t=0 then p else if t=1 then p^(j+1) else q+1
  let up (t : ℕ) := if t=0 then p else if t=1 then p^(j+1)-1 else q+1
  let down (t : ℕ) := if t=0 then p-1 else if t=1 then p^(j+1) else q
  let T := S.disjSum L
  let label : ℕ ⊕ ℕ → ℕ := Sum.elim c opening
  let a : ℕ ⊕ ℕ → ℕ := Sum.elim (fun r => c r-1) up
  let b : ℕ ⊕ ℕ → ℕ := Sum.elim c down
  have hLup : L.prod up=p*((p^(j+1)-1)*(q+1)) := by simp [L,up]
  have hLdown : L.prod down=(p-1)*(p^(j+1)*q) := by simp [L,down]
  have hbal : P*T.prod a=(2*R)*T.prod b := by
    simp only [T,a,b,Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr]
    rw [hpred,hcprod,hLup,hLdown,←hqmul,hplus,pow_succ]
    ring
  have hpo : Odd P := Finset.prod_induction id Odd (fun _ _ => Odd.mul) odd_one
    (fun r hr => hs.of_dvd_nat (Nat.dvd_of_mem_primeFactors hr))
  have hne : P≠2*R := by have := Nat.odd_iff.mp hpo; omega
  have hR : R≤P := Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun r _ => Nat.sub_le r 1)
  have hsize (r : ℕ) (hr : r∈S) : p≤c r := by
    obtain ⟨β,hβ,hout⟩ := even_index_source_odd_power hp hs hσq hplus hσs hr
    have hple : p≤f r := by rw [show f r=p^β from hout]; exact Nat.le_pow hβ.pos
    have h1 := (Nat.prime_of_mem_primeFactors hr).one_lt
    have hbound := Nat.le_mul_of_pos_right (f r) (by omega : 0<r-1)
    rw [←hcen r hr] at hbound
    omega
  have hqle : p≤q := by
    have hpow : p≤p^(2*u) := Nat.le_pow (by omega)
    have hbig := self_lt_sigma_of_one_lt (one_lt_pow₀ hp.one_lt (by omega : 2*u≠0))
    omega
  have ht (x : ℕ ⊕ ℕ) (hx : x∈T) : p≤label x ∧
      ((a x=label x ∧ b x=label x-1) ∨ (a x=label x-1 ∧ b x=label x)) := by
    cases x with
    | inl r => exact ⟨hsize r (Finset.inl_mem_disjSum.mp hx),.inr ⟨rfl,rfl⟩⟩
    | inr n =>
      have hn := Finset.inr_mem_disjSum.mp hx
      simp [L] at hn
      rcases hn with rfl|rfl|rfl <;>
        simp [label,opening,a,b,up,down,Nat.le_pow (Nat.succ_pos j),hqle.trans (Nat.le_succ _)]
  obtain ⟨x,hx,hsmall⟩ := exists_small_label_of_balance T label a b hne hbal
    (fun x hx => ⟨hp.one_lt.trans_le (ht x hx).1,(ht x hx).2⟩)
  have hcard : T.card=S.card+3 := by simp [T,L]
  have hm : max P (2*R)≤2*P := max_le (by omega) (Nat.mul_le_mul_left _ hR)
  rw [hcard] at hsmall
  exact (ht x hx).1.trans (hsmall.trans ((Nat.mul_le_mul_left _ hm).trans_eq (by dsimp [S,P]; ring)))

end OddPerfect
