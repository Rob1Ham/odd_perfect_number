module

public import OddPerfect.HarmonicComponents

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- Cohen–Sorli's component estimate before inserting a bound for τ.
It holds for every harmonic integer, every prime-power divisor, and all
positive exponents, including those below the exact exponent. -/
theorem harmonic_prime_power_square_lt {N p a : ℕ} (hN : OreHarmonic N) (hp : p.Prime) (ha : 0<a)
    (hd : p^a ∣ N) : (p^a)^2 < N*N.divisors.card := by
  have hn := zero_lt_one.trans hN.1
  let e := N.factorization p
  have he : a≤e := (hp.pow_dvd_iff_le_factorization hn.ne').mp hd
  have hx : p^e ∣ N := (hp.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
  have hne : ¬p^(e+1) ∣ N := fun h => Nat.not_succ_le_self e ((hp.pow_dvd_iff_le_factorization hn.ne').mp h)
  obtain ⟨m,hm,hc⟩ := exists_coprime_cofactor_of_exact_prime_pow hp hx hne
  let S := sigma 1 (p^e)
  have hσ : S ∣ sigma 1 N := by
    rw [hm,isMultiplicative_sigma.map_mul_of_coprime hc]
    exact dvd_mul_right _ _
  have hcop : (p^e).Coprime S := by
    dsimp [S]
    rw [sigma_one_apply_prime_pow hp]
    exact coprime_power_geometric_sum p e
  have hmul := hcop.mul_dvd_of_dvd_of_dvd (hx.trans (dvd_mul_right N N.divisors.card)) (hσ.trans hN.2)
  have hτ : 0 < N.divisors.card := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hn.ne'⟩
  have hbig : p^e < S := by
    dsimp [S]
    rw [sigma_one_apply_prime_pow hp,sum_range_succ]
    have : 0 < ∑ j ∈ range e, p^j := sum_pos' (by intros; omega)
      ⟨0,mem_range.mpr (ha.trans_le he),by simp⟩
    omega
  calc (p^a)^2 ≤ (p^e)^2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right hp.pos he) 2
       _ = p^e*p^e := pow_two _
       _ < p^e*S := Nat.mul_lt_mul_of_pos_left hbig (pow_pos hp.pos _)
       _ ≤ _ := Nat.le_of_dvd (Nat.mul_pos hn hτ) hmul

/-- A bound τ(N)^d≤N yields a bound on every prime power dividing N.
Taking d=3 and d=4 gives the exponents in Cohen–Sorli's Lemma 2 and Theorem 5. -/
theorem harmonic_prime_power_of_divisor_bound {N p a d : ℕ} (hN : OreHarmonic N) (hp : p.Prime)
    (ha : 0<a) (hdiv : p^a ∣ N) (hd : 0<d) (hτ : N.divisors.card^d ≤ N) :
    (p^a)^(2*d) < N^(d+1) := by
  rw [pow_mul,pow_succ]
  calc ((p^a)^2)^d < (N*N.divisors.card)^d :=
         Nat.pow_lt_pow_left (harmonic_prime_power_square_lt hN hp ha hdiv) hd.ne'
       _ ≤ _ := by rw [mul_pow]; exact Nat.mul_le_mul_left _ hτ

end OddPerfect
