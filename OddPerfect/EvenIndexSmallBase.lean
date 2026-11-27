module

public import OddPerfect.EvenPrimePowerSixteen
import Mathlib.Algebra.Order.Ring.Abs

public section
namespace OddPerfect
open ArithmeticFunction

private def halfRepunit (p u : ℕ) : ℕ := ((p^(2*u+1)-1)/(p-1)+1)/2
private def squareRootCandidate (n : ℕ) : ℕ :=
  (fun x : ℕ => min x ((x+n/x)/2))^[12] (2^(n.log2/2+1))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem small_index_half_repunit_check :
    ∀ p : Fin 61, p.val.Prime → Odd p.val →
      ∀ u : Fin 128, 0<u.val → (2*u.val+1).Prime →
        (p.val%4=3 ∨ 2*u.val=96 ∨ 2*u.val=112 ∨ 2*u.val=192 ∨ 2*u.val=240) →
        let n := halfRepunit p.val u.val
        let x := squareRootCandidate n
        x^2<n ∧ n<(x+1)^2 := by decide +kernel

/-- Up to index exponent 254 the relevant 505 small-base half-repunits
all lie strictly between consecutive squares. -/
theorem sixty_one_le_small_even_index_base {q p s u : ℕ}
    (hp : p.Prime) (hpo : Odd p) (hq : q.Prime) (hu : 0<u) (hcut : 2*u<256)
    (h : p%4=3 ∨ 2*u=96 ∨ 2*u=112 ∨ 2*u=192 ∨ 2*u=240)
    (hσq : sigma 1 (p^(2*u))=q) (hplus : q+1=2*s^2) : 61≤p := by
  by_contra! hsmall
  have hlen := prime_length_of_prime_sigma hp (by omega : 0<2*u) (hσq ▸ hq)
  have hcheck := small_index_half_repunit_check ⟨p,hsmall⟩ hp hpo ⟨u,by omega⟩ hu hlen h
  have hrep : (p^(2*u+1)-1)/(p-1)=q := by
    rw [←hσq,sigma_one_apply_prime_pow hp]
    exact (Nat.eq_div_of_mul_eq_left (by have := hp.one_lt; omega)
      (geom_sum_mul_of_one_le hp.one_le (2*u+1))).symm
  have heq : halfRepunit p u=s^2 := by rw [halfRepunit,hrep,hplus,Nat.mul_div_cancel_left _ (by decide)]
  let x := squareRootCandidate (halfRepunit p u)
  change x^2<halfRepunit p u ∧ halfRepunit p u<(x+1)^2 at hcheck
  rw [heq] at hcheck
  rcases le_or_gt s x with hle|hlt
  · exact hcheck.1.not_ge (Nat.pow_le_pow_left hle 2)
  · exact hcheck.2.not_ge (Nat.pow_le_pow_left hlt 2)

end OddPerfect
