module

public import OddPerfect.Harmonic

public section

namespace OddPerfect.DivisorCountSearch

open Finset ArithmeticFunction

/-- Search states split n=D*m and τ(n)=T*τ(m). All remaining prime
divisors are at least a. The final condition describes a counterexample. -/
structure Candidate (d B D T a m : ℕ) : Prop where
  pos : 0 < m
  prefix_pos : 0 < D
  lower : ∀ p ∈ m.primeFactors, a ≤ p
  size : B ≤ D*m
  bad : D*m < (T*m.divisors.card)^d

@[expose] def Closed (d B D T a : ℕ) : Prop := ∀ m, ¬ Candidate d B D T a m

/-- Normalize the divisor-count power by a power of the represented integer. -/
@[expose] def moment (n t k s : ℕ) : ℚ := (t:ℚ)^k/(n:ℚ)^s

theorem moment_nonneg (n t k s : ℕ) : 0 ≤ moment n t k s := by unfold moment; positivity

theorem moment_mul (n m t u k s : ℕ) :
    moment (n*m) (t*u) k s = moment n t k s * moment m u k s := by
  simp only [moment, Nat.cast_mul, mul_pow, div_mul_div_comm]

/-- If τ(n)^d exceeds n then every moment with k≥ds yields a strict
lower bound. All numerical certificates compare rationals exactly. -/
theorem strict_moment {n t d k s : ℕ} (hn : 0<n) (hk : 0<k) (hs : s*d≤k)
    (h : n < t^d) : (n:ℚ)^(k-s*d) < (moment n t k s)^d := by
  have ht : (n:ℚ) < (t:ℚ)^d := by exact_mod_cast h
  have hnq : (0:ℚ) < n := by exact_mod_cast hn
  rw [moment, div_pow, lt_div_iff₀ (pow_pos (pow_pos hnq s) d), ← pow_mul, ← pow_add,
    Nat.sub_add_cancel hs, ← pow_mul, Nat.mul_comm k d, pow_mul]
  exact pow_lt_pow_left₀ ht hnq.le hk.ne'

theorem no_candidate_of_moment {d B D T a m k s L : ℕ} {W : ℚ}
    (h : Candidate d B D T a m) (hk : 0<k) (hs : s*d≤k) (hL : L≤D*m)
    (hW : moment D T k s * moment m m.divisors.card k s ≤ W)
    (cut : W^d ≤ (L:ℚ)^(k-s*d)) : False := by
  have u := strict_moment (Nat.mul_pos h.prefix_pos h.pos) hk hs h.bad
  rw [moment_mul] at u
  have hl : (L:ℚ) ≤ (D*m:ℕ) := by exact_mod_cast hL
  exact u.not_ge ((pow_le_pow_left₀ (mul_nonneg (moment_nonneg ..) (moment_nonneg ..)) hW _).trans
    (cut.trans (pow_le_pow_left₀ (Nat.cast_nonneg L) hl _)))

/-- Split a candidate by its exact exponent of p, including exponent zero.
The finite gap condition certifies the new least allowed prime. -/
theorem closed_of_split {d B D T p a : ℕ} (hp : p.Prime)
    (gap : ∀ j ∈ Ioo p a, ¬ j.Prime)
    (branches : ∀ e, Closed d B (D*p^e) (T*(e+1)) a) : Closed d B D T p := by
  intro m h
  obtain ⟨e,r,hr,hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd h.pos.ne' p hp.ne_one
  have hc : (p^e).Coprime r := (hp.coprime_pow_of_not_dvd hr).symm
  have ht : m.divisors.card = (e+1)*r.divisors.card := by
    rw [hm,hc.card_divisors_mul,←sigma_zero_apply,sigma_zero_apply_prime_pow hp]
  have hx : D*m=(D*p^e)*r := by rw [hm,mul_assoc]
  refine branches e r ⟨?_,Nat.mul_pos h.prefix_pos (pow_pos hp.pos _),?_,hx ▸ h.size,?_⟩
  · by_contra! hz
    have := h.pos
    simp [hm,Nat.eq_zero_of_le_zero hz] at this
  · intro q hq
    have hpr := Nat.prime_of_mem_primeFactors hq
    have hqr := Nat.dvd_of_mem_primeFactors hq
    have hqm : q ∣ m := hm ▸ hqr.trans (dvd_mul_left _ _)
    have hpq := h.lower q (Nat.mem_primeFactors.mpr ⟨hpr,hqm,h.pos.ne'⟩)
    by_contra! hlt
    have hne : q ≠ p := fun he => hr (he ▸ hqr)
    exact gap q (mem_Ioo.mpr ⟨lt_of_le_of_ne hpq (Ne.symm hne),hlt⟩) hpr
  · simpa only [←hx,ht,mul_assoc] using h.bad

/-- An odd integer of the target size supplies an initial candidate if it
violates the divisor estimate. -/
theorem divisor_bound_of_closed {d B : ℕ} (h : Closed d B 1 1 3) {n : ℕ}
    (ho : Odd n) (hB : B≤n) : n.divisors.card^d ≤ n := by
  by_contra! hb
  apply h n
  refine ⟨ho.pos,by decide,?_,by simpa using hB,by simpa using hb⟩
  intro p hp
  have := Nat.odd_iff.mp (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  omega

end OddPerfect.DivisorCountSearch
