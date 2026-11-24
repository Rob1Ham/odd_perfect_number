module
public import OddPerfect.LargeOrderPrime
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-! A cubic size bound and a quadratic discriminant can complete a partial order certificate. -/

public section

namespace OddPerfect

@[expose] def cubicGap (n F : ℕ) : Bool :=
  let R := (n-1)/F
  let S := (R-1)%F+1
  let P := (R-S)/F
  decide (n < F^3 ∧ S^2 ≠ 4*P + (Nat.sqrt (S^2-4*P))^2)

private theorem prime_of_cubicGap {n F : ℕ} (hn : 1<n) (hF : 0<F)
    (hall : ∀ r, r.Prime → r ∣ n → F ∣ r-1) (test : cubicGap n F = true) : n.Prime := by
  let R := (n-1)/F
  let S := (R-1)%F+1
  let P := (R-S)/F
  have hg : n < F^3 ∧ S^2 ≠ 4*P + (Nat.sqrt (S^2-4*P))^2 := of_decide_eq_true test
  have lo (q : ℕ) (hq : q.Prime) (hd : q∣n) : F < q := by
    have := Nat.le_of_dvd (by have := hq.one_lt; omega : 0<q-1) (hall q hq hd)
    omega
  by_contra hcomp
  let r := n.minFac
  let s := n/r
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrd : r ∣ n := Nat.minFac_dvd n
  have hmul : r*s=n := Nat.mul_div_cancel' hrd
  have hsd : s ∣ n := hmul ▸ Nat.dvd_mul_left s r
  have hrs : r ≤ s := by
    apply Nat.le_of_mul_le_mul_left (c := r) _ hr.pos
    rw [hmul, ←sq]
    exact Nat.minFac_sq_le_self (by omega) hcomp
  have hspos : 0<s := hr.pos.trans_le hrs
  have hs : s.Prime := by
    by_contra hn'
    have hsmall := Nat.minFac_sq_le_self hspos hn'
    have hq := lo s.minFac (Nat.minFac_prime (by have := hr.one_lt; omega))
      ((Nat.minFac_dvd s).trans hsd)
    have hpow := (Nat.pow_le_pow_left hq.le 2).trans hsmall
    have hbad : F^3 ≤ n := by
      calc F^3 = F*F^2 := by ring
           _ ≤ r*s := Nat.mul_le_mul (lo r hr hrd).le hpow
           _ = n := hmul
    exact hg.1.not_ge hbad
  obtain ⟨a,ha⟩ := hall r hr hrd
  obtain ⟨b,hb⟩ := hall s hs hsd
  have rform : r=1+F*a := by have := hr.one_lt; omega
  have sform : s=1+F*b := by have := hs.one_lt; omega
  have apos : 0<a := by by_contra! he; have := hr.one_lt; simp [show a=0 by omega] at rform; omega
  have bpos : 0<b := by by_contra! he; have := hs.one_lt; simp [show b=0 by omega] at sform; omega
  have hab : a ≤ b := by
    apply Nat.le_of_mul_le_mul_left (c := F) _ hF
    omega
  have nexp : n=1+F*(a+b+F*(a*b)) := by rw [← hmul,rform,sform]; ring
  have hR : R=a+b+F*(a*b) := by
    dsimp [R]
    rw [nexp, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hF]
  have hprod : a*b < F := by
    by_contra! hle
    have hl := Nat.mul_le_mul_left (F^2) hle
    have hbad : F^3 ≤ n := by
      rw [nexp]
      nlinarith [Nat.zero_le (F*a),Nat.zero_le (F*b)]
    exact hg.1.not_ge hbad
  have hsle : a+b ≤ F := by
    have haux : a+b ≤ a*b+1 := by
      obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero apos.ne'
      obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero bpos.ne'
      nlinarith [Nat.zero_le (x*y)]
    omega
  have hS : S=a+b := by
    dsimp only [S]
    rw [hR, show a+b+F*(a*b)-1=(a+b-1)+F*(a*b) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hP : P=a*b := by
    dsimp only [P]
    rw [hR,hS,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ hF]
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hab
  have hid : S^2 = 4*P+k^2 := by rw [hS,hP,hk]; ring
  apply hg.2
  rw [hid, Nat.add_sub_cancel_left, show (Nat.sqrt (k ^ 2)) = k by simpa only [sq] using Nat.sqrt_eq k]

/-- A conservative cubic form of the Brillhart–Lehmer–Selfridge test. A composite
below F³ would be a product of two primes congruent to one modulo F, with the
sum and the product of their quotients determined by division. -/
@[expose] def largeOrderCubeCheck (n b : ℕ) (factors : List (ℕ × ℕ)) : Bool :=
  let F := knownOrder factors
  decide (1 < n ∧ 0 < F) && cubicGap n F && orderTests n b factors

theorem prime_of_largeOrderCubeCheck {n b : ℕ} {factors : List (ℕ × ℕ)}
    (hp : ∀ f ∈ factors, f.1.Prime) (h : largeOrderCubeCheck n b factors = true) : n.Prime := by
  simp only [largeOrderCubeCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hF⟩, hg⟩, hc⟩ := h
  exact prime_of_cubicGap hn hF (fun _ hr hd => knownOrder_dvd_prime_pred hn hF hp hc hr hd) hg

end OddPerfect
