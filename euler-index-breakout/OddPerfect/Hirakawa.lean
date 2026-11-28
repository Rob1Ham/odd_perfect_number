module

public import OddPerfect.GeometricNonSquare
public import OddPerfect.EulerSquareClass
public import OddPerfect.EulerIndex

public section

namespace OddPerfect

open ArithmeticFunction Finset

/-- Hirakawa, Theorem 2.1. No divisor sum of a prime power with prime one
modulo four and exponent greater than one can be twice a square. -/
theorem sigma_prime_pow_ne_twice_square {q a : ℕ} (hq : q.Prime) (hq4 : q%4=1)
    (ha : 1<a) (n : ℕ) : sigma 1 (q^a) ≠ 2*n^2 := by
  intro h
  have hmod := sigma_modEq_of_one hq (show q ≡ 1 [MOD 4] from hq4) a
  change sigma 1 (q^a)%4=(a+1)%4 at hmod
  rw [h] at hmod
  let d := (a+1)/2
  have hd : 1<d := by dsimp [d]; omega
  have hal : a+1=2*d := by dsimp [d]; omega
  let A := geometricBlock q d
  let B := (q^d+1)/2
  have hqd : q^d%4=1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 4] from hq4).pow d
  have hB : q^d+1=2*B := by dsimp [B]; omega
  have hBodd : Odd B := Nat.odd_iff.mpr (by dsimp [B]; omega)
  have hpow : sigma 1 (q^a)=A*(q^d+1) := by
    rw [sigma_one_apply_prime_pow hq]
    change geometricBlock q (a+1)=_
    rw [hal,mul_comm 2 d,geometricBlock_mul]
    simp [geometricBlock,sum_range_succ,A,Nat.add_comm]
  rw [hpow,hB] at h
  have hAB : A*B=n^2 := Nat.mul_left_cancel (by decide : 0<2) (by simpa [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using h)
  have hcop : A.Coprime B := by
    by_contra hn
    obtain ⟨r,hr,hrA,hrB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hmin : r ∣ q^d-1 := by
      rw [←geom_sum_mul_of_one_le hq.one_le]
      exact dvd_mul_of_dvd_left hrA _
    have hplus : r ∣ q^d+1 := by rw [hB]; exact dvd_mul_of_dvd_right hrB _
    have ht := Nat.dvd_sub hplus hmin
    rw [show q^d+1-(q^d-1)=2 by have := Nat.pow_pos hq.pos (n:=d); omega] at ht
    exact hBodd.not_two_dvd_nat (((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp ht) ▸ hrB)
  have hu : IsUnit (gcd A B) := by
    change IsUnit (Nat.gcd A B)
    rw [hcop.gcd_eq_one]
    exact isUnit_one
  obtain ⟨v,hv⟩ := exists_eq_pow_of_mul_eq_pow hu hAB
  exact geometricBlock_not_square_of_prime_one_mod_four hq hq4 hd ⟨v,by simpa [pow_two] using hv⟩

/-- The two common definitions of the Euler component index agree. -/
theorem euler_index_eq_gcd {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    sigma 1 (m^2)/q^a = (m^2).gcd (sigma 1 (m^2)) := by
  obtain ⟨_,i,hio,_,hleft,hright⟩ := euler_component_index_bound hN ho hq hq4 ha4 hqm hform
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hdiv : i ∣ m^2 := (Nat.coprime_two_right.mpr hio).dvd_of_dvd_mul_left
    (hright ▸ dvd_mul_left i _)
  apply Nat.dvd_antisymm (Nat.dvd_gcd hdiv (dvd_mul_left _ _))
  let g := (m^2).gcd (q^a*i)
  have hcop : g.Coprime (q^a) :=
    ((hq.coprime_iff_not_dvd.mpr (fun hd => hqm (hq.dvd_of_dvd_pow hd))).pow_left a).symm.of_dvd_left
      (Nat.gcd_dvd_left _ _)
  exact hcop.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)

/-- Gallardo's Proposition 2, in the divisor-sum quotient convention. -/
theorem euler_index_not_square_of_exponent_gt_one {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    ¬IsSquare (sigma 1 (m^2)/q^a) :=
  euler_index_not_square_of_nonsquare_first_block hN ho hq hq4 ha4 hqm hform
    (geometricBlock_not_square_of_prime_one_mod_four hq hq4 (by omega))

/-- Gallardo, Proposition 2, exactly in the gcd convention used in the paper. -/
theorem euler_gcd_index_not_square_of_exponent_gt_one {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    ¬IsSquare ((m^2).gcd (sigma 1 (m^2))) := by
  rw [←euler_index_eq_gcd hN ho hq hq4 ha4 hqm hform]
  exact euler_index_not_square_of_exponent_gt_one hN ho hq hq4 ha4 ha hqm hform

/-- A square second half-block at odd length forces the base to be one modulo
sixteen throughout Euler's one-modulo-four residue class. -/
theorem half_pow_succ_not_square_of_mod_sixteen {q d : ℕ} (hq4 : q%4=1) (hd : Odd d) (hq16 : q%16≠1) :
    ¬IsSquare ((q^d+1)/2) := by
  rintro ⟨w,hw⟩
  have hfour : q^d%4=1 := by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 4] from hq4).pow d
  have hw8 : w*w%8=0 ∨ w*w%8=1 ∨ w*w%8=4 := by
    rw [Nat.mul_mod]
    have h := Nat.mod_lt w (by decide : 0<8)
    interval_cases (w%8) <;> decide
  have hq16d : q^d ≡ 1 [MOD 16] := by change q^d%16=1; omega
  have hcases : q ≡ 5 [MOD 16] ∨ q ≡ 9 [MOD 16] ∨ q ≡ 13 [MOD 16] := by
    change q%16=5 ∨ q%16=9 ∨ q%16=13
    omega
  have h4 : q^4 ≡ 1 [MOD 16] := by
    rcases hcases with h | h | h <;> exact (h.pow 4).trans (by decide)
  have hdmod := Nat.odd_iff.mp hd
  have hm : d*d%4=1 := by
    rw [Nat.mul_mod]
    rcases (by omega : d%4=1 ∨ d%4=3) with h | h <;> simp [h]
  let j := d*d/4
  have hj : d*d=4*j+1 := by dsimp [j]; omega
  have hp : q^(d*d) ≡ 1 [MOD 16] := by rw [pow_mul]; simpa using hq16d.pow d
  rw [hj,pow_succ,pow_mul] at hp
  have hq : q ≡ 1 [MOD 16] := by
    have he := ((h4.pow j).mul_right q).symm
    have htrans := he.trans hp
    simpa using htrans
  exact hq16 hq

/-- The square/prime-times-square theorem reduces to finding a nonsquare in
the second half-block. The first block is always nonsquare when a>1. -/
theorem euler_index_ne_prime_mul_square_of_second_block {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hB : ¬IsSquare ((q^((a+1)/2)+1)/2)) (l t : ℕ) (hl : l=1 ∨ l.Prime) :
    sigma 1 (m^2)/q^a ≠ l*t^2 :=
  euler_index_ne_prime_mul_square_of_nonsquare_blocks hN ho hq hq4 ha4 hqm hform
    (geometricBlock_not_square_of_prime_one_mod_four hq hq4 (by omega)) hB l t hl

/-- The complete prime-times-square exclusion for Euler primes outside one mod
sixteen, and for half-lengths divisible by three or five at all Euler primes. -/
theorem euler_index_ne_prime_mul_square_of_residue_or_length {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hcase : q%16≠1 ∨ 3 ∣ (a+1)/2 ∨ 5 ∣ (a+1)/2)
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^a ≠ l*t^2 := by
  apply euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform _ l t hl
  let d := (a+1)/2
  have hd : 1 < d := by dsimp [d]; omega
  have hob (f : ℕ) (hf : f ∣ d) (hn : ∀ x : ℕ, 1<x → x%4=1 → ¬IsSquare ((x^f+1)/2)) :
      ¬IsSquare ((q^d+1)/2) := by
    obtain ⟨j,hj⟩ := hf
    have hdj : d=j*f := hj.trans (mul_comm _ _)
    have hj0 : j ≠ 0 := by rintro rfl; simp at hdj; omega
    rw [hdj,pow_mul]
    exact hn _ (one_lt_pow₀ hq.one_lt hj0)
      (by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 4] from hq4).pow j)
  rcases hcase with h | h | h
  · exact half_pow_succ_not_square_of_mod_sixteen hq4 (Nat.odd_iff.mpr (by omega)) h
  · exact hob 3 h (fun _ => half_cube_succ_not_square)
  · exact hob 5 h (fun _ => half_fifth_succ_not_square)

end OddPerfect
