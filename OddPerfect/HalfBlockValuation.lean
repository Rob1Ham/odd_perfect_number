module

public import OddPerfect.Hirakawa
import Mathlib.NumberTheory.Multiplicity

public section

namespace OddPerfect

open ArithmeticFunction

private theorem valuation_half_of_even {n r : ℕ} (hp : r.Prime) (hro : Odd r) (he : Even n) :
    (n/2).factorization r = n.factorization r := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hdouble : n=2*(n/2) := by have := Nat.even_iff.mp he; omega
  have hd : ¬r ∣ 2 := fun h => hro.not_two_dvd_nat
    (((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) ▸ dvd_refl _)
  conv_rhs => rw [hdouble,Nat.factorization_mul (by decide : (2:ℕ) ≠ 0) (by omega),
    Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hd,zero_add]

/-- Exact lifting at an odd prime of x+1, for any odd base and any odd
positive exponent. -/
theorem half_sum_valuation {x d r : ℕ} (hx : Odd x) (hd : Odd d) (hr : r.Prime) (hro : Odd r)
    (hrx : r ∣ x+1) :
    ((x^d+1)/2).factorization r = ((x+1)/2).factorization r + d.factorization r := by
  let : Fact r.Prime := ⟨hr⟩
  have hx0 : ¬r ∣ x := fun h => hr.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hrx)
  have h := Nat.multiplicity_pow_add_pow hro hrx hx0 hd
  simp only [one_pow,Nat.multiplicity_eq_factorization hr] at h
  rw [valuation_half_of_even hr hro ((hx.pow).add_odd odd_one),
    valuation_half_of_even hr hro (hx.add_odd odd_one)]
  exact h

/-- Under a prime-times-square Euler index, every odd prime of the base
half-sum has matching valuation parity in the half-length. -/
theorem euler_half_length_valuation_parity {N q a m r l t : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : l=1 ∨ l.Prime) (hshape : sigma 1 (m^2)/q^a = l*t^2)
    (hr : r.Prime) (hrH : r ∣ (q+1)/2) :
    Even (((q+1)/2).factorization r + ((a+1)/2).factorization r) := by
  have hB : IsSquare ((q^((a+1)/2)+1)/2) := Classical.byContradiction
    (fun h => euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform h l t hl hshape)
  have hro := (Nat.odd_iff.mpr (show ((q+1)/2)%2=1 by omega)).of_dvd_nat hrH
  have hrx : r ∣ q+1 := hrH.trans ⟨2, by omega⟩
  have h := Nat.isSquare_iff_even_factorization.mp hB r hr
  rwa [half_sum_valuation (Nat.odd_iff.mpr (by omega)) (Nat.odd_iff.mpr (by omega)) hr hro hrx] at h

/-- Every prime of the squarefree part of (q+1)/2 must divide (a+1)/2
when the Euler component index is a square times at most one prime. -/
theorem euler_odd_valuation_prime_dvd_half_length {N q a m r l t : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hl : l=1 ∨ l.Prime) (hshape : sigma 1 (m^2)/q^a = l*t^2)
    (hr : r.Prime) (hrv : Odd (((q+1)/2).factorization r)) : r ∣ (a+1)/2 := by
  have hrH := (hr.dvd_iff_one_le_factorization (by omega : (q+1)/2 ≠ 0)).mpr hrv.pos
  have h := euler_half_length_valuation_parity hN ho hq hq4 ha4 ha hqm hform hl hshape hr hrH
  by_contra hn
  rw [Nat.factorization_eq_zero_of_not_dvd hn,add_zero] at h
  exact (Nat.not_even_iff_odd.mpr hrv) h

/-- If three or five occurs to odd valuation in (q+1)/2, the entire
exponent-greater-than-one branch excludes a prime times a square. -/
theorem euler_index_ne_prime_mul_square_of_small_base_valuation {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hv : Odd (((q+1)/2).factorization 3) ∨ Odd (((q+1)/2).factorization 5))
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^a ≠ l*t^2 := by
  intro hs
  apply euler_index_ne_prime_mul_square_of_residue_or_length hN ho hq hq4 ha4 ha hqm hform _ l t hl hs
  right
  rcases hv with h | h
  · exact Or.inl (euler_odd_valuation_prime_dvd_half_length hN ho hq hq4 ha4 ha hqm hform hl hs (by decide) h)
  · exact Or.inr (euler_odd_valuation_prime_dvd_half_length hN ho hq hq4 ha4 ha hqm hform hl hs (by decide) h)

end OddPerfect
