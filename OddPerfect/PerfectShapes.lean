module

public import OddPerfect.Even
public import OddPerfect.NearPerfect
import Mathlib.Algebra.Order.Ring.Abs

public section

namespace OddPerfect

/-- Every even perfect number is a hexagonal number, equivalently a
triangular number whose row has odd length. -/
theorem even_perfect_hexagonal {N : ℕ} (he : Even N) (hN : N.Perfect) :
    ∃ t : ℕ, 0<t ∧ N=t*(2*t-1) ∧ N=(2*t).choose 2 := by
  obtain ⟨k, _, hn⟩ := Theorems100.Nat.even_and_perfect_iff.mp ⟨he,hN⟩
  have hhex : N=2^k*(2*2^k-1) := by simpa [mersenne,pow_succ',Nat.mul_comm] using hn
  refine ⟨2^k,Nat.two_pow_pos _,hhex,?_⟩
  rw [hhex,Nat.choose_two_right,Nat.mul_assoc,Nat.mul_div_cancel_left _ (by decide : 0<2)]

theorem sum_odd_cubes_add_square (t : ℕ) :
    (∑ j ∈ Finset.range t, (2*j+1)^3) + t^2 = 2*t^4 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- Except for six, every even perfect number is a sum of consecutive odd
cubes beginning with one, with a power of two summands. -/
theorem even_perfect_sum_odd_cubes {N : ℕ} (he : Even N) (hN : N.Perfect) (hne : N≠6) :
    ∃ k : ℕ, N = ∑ j ∈ Finset.range (2^k), (2*j+1)^3 := by
  obtain ⟨a,hp,hn⟩ := Theorems100.Nat.even_and_perfect_iff.mp ⟨he,hN⟩
  have ha1 : a+1≠2 := by
    intro h
    have ha : a=1 := by omega
    subst a
    exact hne hn
  have ha2 := (hp.of_mersenne.eq_two_or_odd).resolve_left ha1
  obtain ⟨k,hk⟩ := Nat.even_iff.mpr (show a%2=0 by omega)
  refine ⟨k,?_⟩
  let t := 2^k
  have ht : 0 < t := Nat.two_pow_pos _
  have hhalf : 2^a=t^2 := by rw [hk,pow_add,pow_two]
  have hM : mersenne (a+1)+1 = 2*t^2 := by
    rw [mersenne,Nat.sub_add_cancel (Nat.two_pow_pos _),pow_succ',hhalf]
  have hv := congrArg (fun v => t^2*v) hM
  rw [hn,hhalf]
  nlinarith [sum_odd_cubes_add_square t]

/-- No natural perfect number is a square. The even case has an actual
Mersenne prime to valuation one; the odd case uses Euler parity. -/
theorem perfect_not_square {N : ℕ} (hN : N.Perfect) : ¬ IsSquare N := by
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨k,hq,hn⟩ := Theorems100.Nat.even_and_perfect_iff.mp ⟨he,hN⟩
    let q := mersenne (k+1)
    have hodd : Odd q := by simp [q]
    have hq2 : ¬ q ∣ 2 := by
      intro h
      have heq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h
      exact hodd.not_two_dvd_nat (by rw [show q=2 from heq])
    intro hs
    have hev := (Nat.isSquare_iff_even_factorization.mp hs) q hq
    change N=2^k*q at hn
    rw [hn,Nat.factorization_mul (by positivity) hq.ne_zero,Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hq2 (hq.dvd_of_dvd_pow hd)),
      hq.factorization_self,zero_add] at hev
    exact (by decide : ¬Even 1) hev
  · exact odd_perfect_not_square ho hN

end OddPerfect
