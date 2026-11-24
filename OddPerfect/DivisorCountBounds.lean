module

public import OddPerfect.DivisorCountSearch
public import OddPerfect.DivisorMoments

public section

namespace OddPerfect.DivisorCountSearch

open Finset

@[expose] def ResidualBound (a k s : ℕ) (W : ℚ) : Prop :=
  ∀ m : ℕ, 0<m → (∀ p ∈ m.primeFactors, a≤p) → moment m m.divisors.card k s ≤ W

theorem residual_envelope {a k s C : ℕ} {W : ℚ} (ha : 3≤a) (hC : 2^k≤C^s)
    (hp : ∀ p ∈ DivisorMoments.smallPrimes a C, 10^k≤p^s*9^k)
    (he : DivisorMoments.envelope a k s C ≤ W) : ResidualBound a k s W := by
  intro m hm hr
  exact (DivisorMoments.divisor_moment_le_envelope hm ha hr hC hp).trans he

theorem close_envelope {d B D T a k s : ℕ} {W : ℚ} (hk : 0<k) (hs : s*d≤k)
    (env : ResidualBound a k s W)
    (cut : (moment D T k s * W)^d ≤ ((max B D:ℕ):ℚ)^(k-s*d)) : Closed d B D T a := by
  intro m h
  have hL : max B D ≤ D*m := max_le h.size (Nat.le_mul_of_pos_right D h.pos)
  apply no_candidate_of_moment h hk hs hL
    (mul_le_mul_of_nonneg_left (env m h.pos h.lower) (moment_nonneg ..))
  exact cut

/-- At the point where every remaining prime incurs a loss, retain that
loss for one guaranteed factor or check the empty remainder explicitly. -/
theorem close_nonempty {d B D T a k s : ℕ} (ha : 3≤a) (hk : 0<k) (hs : s*d≤k)
    (hlarge : 2^k≤a^s) (empty : D<B ∨ T^d≤D)
    (cut : (moment D T k s * ((2:ℚ)^k/(a:ℚ)^s))^d ≤ ((max B D:ℕ):ℚ)^(k-s*d)) :
    Closed d B D T a := by
  intro m h
  rcases lt_or_eq_of_le (show 1≤m from h.pos) with hm | hm
  · have hL := max_le h.size (Nat.le_mul_of_pos_right D h.pos)
    apply no_candidate_of_moment h hk hs hL _ cut
    exact mul_le_mul_of_nonneg_left (DivisorMoments.divisor_moment_le_first_prime hm ha h.lower hlarge)
      (moment_nonneg ..)
  · have hsize := h.size
    have hbad := h.bad
    subst m
    simp only [Nat.divisors_one,Finset.card_singleton,mul_one] at hsize hbad
    omega

/-- A single comparison covers every exponent e≥H in the last branch.
The small prime has already been removed from the remaining cofactor. -/
theorem close_exponent_tail {d B D T p a H k s : ℕ} {W : ℚ} (hp : 0<p)
    (hk : 0<k) (hs : s*d≤k) (hpeak : 10^k≤p^s*9^k) (hH : 8≤H)
    (env : ResidualBound a k s W)
    (cut : ((moment D T k s * DivisorMoments.component p k s H) * W)^d ≤
      ((max B (D*p^H):ℕ):ℚ)^(k-s*d)) :
    ∀ e, H≤e → Closed d B (D*p^e) (T*(e+1)) a := by
  intro e he m h
  have hL : max B (D*p^H) ≤ D*p^e*m := max_le h.size
    ((Nat.mul_le_mul_left D (Nat.pow_le_pow_right hp he)).trans (Nat.le_mul_of_pos_right _ h.pos))
  apply no_candidate_of_moment h hk hs hL _ cut
  rw [moment_mul]
  have hcomp : moment (p^e) (e+1) k s = DivisorMoments.component p k s e := by
    simp only [moment,DivisorMoments.component,Nat.cast_pow,←pow_mul,Nat.mul_comm e s]
  rw [hcomp]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (DivisorMoments.local_moment_tail hp hpeak hH he)
    (moment_nonneg ..)) (env m h.pos h.lower) (moment_nonneg ..)
    (mul_nonneg (moment_nonneg ..) (by unfold DivisorMoments.component; positivity))

end OddPerfect.DivisorCountSearch
