module

public import OddPerfect.EulerExceptionalObstruction
public import OddPerfect.GlobalObstruction
public import OddPerfect.OddPrimePowerIndex

public section

namespace OddPerfect

open ArithmeticFunction

/-- The two nontrivial cube roots of one modulo seven cannot have a noncube
exponent whose power is one less than twice a square. -/
theorem pow_add_one_ne_twice_sq_of_mod_seven {q d y : ℕ}
    (hq : q % 7 = 2 ∨ q % 7 = 4) (hd : ¬ 3 ∣ d) : q ^ d + 1 ≠ 2 * y ^ 2 := by
  have hcycle : q ^ 3 ≡ 1 [MOD 7] := by
    change q ^ 3 % 7 = 1
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h]
  have hreduce : q ^ d ≡ q ^ (d % 3) [MOD 7] := by
    calc
      q ^ d = q ^ (3 * (d / 3) + d % 3) := congrArg (q ^ ·) (Nat.div_add_mod d 3).symm
      _ ≡ 1 ^ (d / 3) * q ^ (d % 3) [MOD 7] := by
        rw [pow_add, pow_mul]
        exact (hcycle.pow _).mul_right _
      _ = _ := by simp
  have hres : ∀ x : Fin 7, ∀ k : Fin 3, ∀ z : Fin 7,
      (x.val = 2 ∨ x.val = 4) → k.val ≠ 0 →
        ¬ (x.val ^ k.val + 1 ≡ 2 * z.val ^ 2 [MOD 7]) := by decide
  intro heq
  apply hres ⟨q % 7, Nat.mod_lt _ (by decide)⟩ ⟨d % 3, Nat.mod_lt _ (by decide)⟩
    ⟨y % 7, Nat.mod_lt _ (by decide)⟩ hq (fun h => hd (Nat.dvd_of_mod_eq_zero h))
  calc
    (q % 7) ^ (d % 3) + 1 ≡ q ^ (d % 3) + 1 [MOD 7] :=
      ((Nat.mod_modEq q 7).pow _).add_right 1
    _ ≡ q ^ d + 1 [MOD 7] := hreduce.symm.add_right 1
    _ = 2 * y ^ 2 := heq
    _ ≡ 2 * (y % 7) ^ 2 [MOD 7] := ((Nat.mod_modEq y 7).symm.pow 2).mul_left 2

/-- An exceptional Euler index supplies a primitive solution with the
actual Euler prime and half-length, outside the two excluded residues. -/
theorem exceptional_index_fermat_witness {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (hi : sigma 1 (m ^ 2) / q ^ a = l * t ^ 2) :
    let d := (a + 1) / 2
    d.Prime ∧ 17 ≤ d ∧ d % 8 = 1 ∧ q % 16 = 1 ∧ q % 7 ≠ 2 ∧ q % 7 ≠ 4 ∧
      ∃ y : ℕ, 0 < y ∧ q.Coprime y ∧ q ^ d + 1 = 2 * y ^ 2 := by
  let d := (a + 1) / 2
  obtain ⟨hd, hd8, hq16, _⟩ :=
    prime_mul_square_index_forces_exceptional_prime_length hN ho hq hq4 ha4 ha hqm hform
      (Or.inr hl) hi
  obtain ⟨hd17, _⟩ := exceptional_index_parameter_floors hN ho hq hq4 ha4 ha hqm hform hl hi
  obtain ⟨w, y, v, _, hpow, _, hm, _⟩ :=
    exceptional_index_cofactor_factorization hN ho hq hq4 ha4 ha hqm hform hl hi
  have hd3 : ¬ 3 ∣ d := by
    intro h
    rcases hd.eq_one_or_self_of_dvd 3 h with h1 | h3 <;> omega
  have hmod : ¬ (q % 7 = 2 ∨ q % 7 = 4) := fun h =>
    pow_add_one_ne_twice_sq_of_mod_seven h hd3 hpow
  have hcop : q.Coprime y := hq.coprime_iff_not_dvd.mpr fun h =>
    hqm (h.trans ⟨l * v * t, by rw [hm]; ring⟩)
  exact ⟨hd, hd17, hd8, hq16, fun h => hmod (Or.inl h), fun h => hmod (Or.inr h),
    y, Nat.pos_of_ne_zero (fun h => by simp [h] at hpow), hcop, hpow⟩

/-- At either excluded Euler-prime residue, the exceptional index is impossible
for every prime multiplier and every exponent greater than one. -/
theorem euler_index_ne_prime_mul_square_of_mod_seven {N q a m l t : ℕ}
    (hN : N.Perfect) (ho : Odd N) (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m) (hform : N = q ^ a * m ^ 2)
    (hl : l.Prime) (h7 : q % 7 = 2 ∨ q % 7 = 4) : sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  obtain ⟨_, _, _, _, h2, h4, _⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  exact h7.elim h2 h4

/-- The outstanding generalized Fermat specialization on the residual Euler classes. -/
def ExceptionalFermatObstruction : Prop :=
  ∀ q d y : ℕ, q.Prime → q % 16 = 1 → q % 7 ≠ 2 → q % 7 ≠ 4 →
    d.Prime → 17 ≤ d → d % 8 = 1 → 0 < y → q.Coprime y → q ^ d + 1 ≠ 2 * y ^ 2

/-- A proof of the residual Diophantine statement closes every exceptional Euler index. -/
theorem euler_index_ne_prime_mul_square_of_fermat_obstruction (hF : ExceptionalFermatObstruction)
    {N q a m l t : ℕ} (hN : N.Perfect) (ho : Odd N) (hq : q.Prime)
    (hq4 : q % 4 = 1) (ha4 : a % 4 = 1) (ha : 1 < a) (hqm : ¬ q ∣ m)
    (hform : N = q ^ a * m ^ 2) (hl : l.Prime) : sigma 1 (m ^ 2) / q ^ a ≠ l * t ^ 2 := by
  intro hi
  obtain ⟨hd, hd17, hd8, hq16, h2, h4, y, hy, hcop, hpow⟩ :=
    exceptional_index_fermat_witness hN ho hq hq4 ha4 ha hqm hform hl hi
  exact hF q _ y hq hq16 h2 h4 hd hd17 hd8 hy hcop hpow

/-- The same residual problem controls odd powers of primes at every exact component. -/
theorem componentIndex_ne_odd_prime_power_of_fermat_obstruction (hF : ExceptionalFermatObstruction)
    {N q p j : ℕ} (ho : Odd N) (hN : N.Perfect) (hqN : q ∈ N.primeFactors)
    (hp : p.Prime) (hj : Odd j) : componentIndex N q ≠ p ^ j := by
  intro hi
  let a := N.factorization q
  let b := ordCompl[q] N
  have hq := Nat.prime_of_mem_primeFactors hqN
  have ha : 0 < a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqN)
  have hform : N = q ^ a * b := (Nat.ordProj_mul_ordCompl_eq_self N q).symm
  have hqb : ¬ q ∣ b := Nat.not_dvd_ordCompl hq hN.2.ne'
  obtain ⟨i, _, hleft, hright, _⟩ := exists_component_index hN hq hform hqb
  have hci : componentIndex N q = i := by
    rw [componentIndex, show sigma 1 (ordCompl[q] N) = q ^ a * i from hleft]
    exact Nat.mul_div_cancel_left i (pow_pos hq.pos _)
  have hip : i = p ^ j := hci.symm.trans hi
  have hp2 : p ≠ 2 := by
    rintro rfl
    by_cases hj1 : j = 1
    · have hi2 : i = 2 := by simpa [hj1] using hip
      exact component_index_not_prime hN ho hq ha hform hqb hleft hright (hi2 ▸ Nat.prime_two)
    have h4 : 4 ∣ i := hip ▸ pow_dvd_pow 2 (by have := hj.pos; omega : 2 ≤ j)
    have h4b : 4 ∣ 2 * b := hright ▸ h4.trans (dvd_mul_left _ _)
    have hbodd := ho.of_dvd_nat (hform ▸ dvd_mul_left b _)
    exact hbodd.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h4b)
  obtain ⟨m, hq4, ha4, hqm, hbm⟩ :=
    euler_form_of_odd_component_index hN ho hq ha hform hqb hleft hright (hip ▸ (hp.odd_of_ne_two hp2).pow)
  rw [hbm] at hform hleft
  have heq : sigma 1 (m ^ 2) / q ^ a = p ^ j := by
    rw [hleft, Nat.mul_div_cancel_left i (pow_pos hq.pos _), hip]
  have ha' := (odd_prime_power_euler_index_constraints hN ho hq hq4 ha4 hqm hform hp hj heq).1
  obtain ⟨k, hk⟩ := hj
  apply euler_index_ne_prime_mul_square_of_fermat_obstruction hF hN ho hq hq4 ha4 ha' hqm hform
    (t := p ^ k) hp
  rw [heq, hk]
  ring

end OddPerfect
