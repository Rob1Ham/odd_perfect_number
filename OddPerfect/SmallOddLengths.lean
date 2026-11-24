module

public import OddPerfect.AlternatingBlock

public section
namespace OddPerfect
open Finset ArithmeticFunction


set_option maxRecDepth 10000 in
/-- The alternating factor at length 7 is nonsquare at every natural base
greater than one. The polynomial inequalities cover x ≥ 4. -/
theorem alternatingBlock_seven_not_square {x : ℕ} (hx : 1 < x) :
    ¬IsSquare (alternatingBlock x 7) := by
  by_cases hx0 : x < 4
  · have hsmall : ∀ j : Fin 4, 1 < j.val → ¬IsSquare (alternatingBlock j.val 7) := by
      change ∀ j : Fin 4, 1 < j.val → ¬IsSquare ((j.val^7+1)/(j.val+1))
      decide +kernel
    exact hsmall ⟨x,hx0⟩ hx
  let u := ((x:ℤ)-4)
  let y := (x:ℤ)
  let P : ℤ := 16*y^3-8*y^2+6*y-5
  have hU : 0 ≤ u := by dsimp [u]; omega
  have hY : y=u+4 := by dsimp [y,u]; ring
  apply not_square_of_scaled_interval (P:=P) (D:=16)
  · dsimp only [P]
    rw [hY]
    ring_nf
    positivity
  · decide
  · exact ⟨8*y^3-4*y^2+3*y-3, by dsimp [P]; ring⟩
  · decide
  · rw [alternatingBlock_cast (by decide : Odd 7)]
    norm_num [sum_range_succ]
    dsimp only [P,y]
    rw [show (x:ℤ)=u+4 from hY]
    apply sub_pos.mp
    ring_nf
    positivity
  · rw [alternatingBlock_cast (by decide : Odd 7)]
    norm_num [sum_range_succ]
    dsimp only [P,y]
    rw [show (x:ℤ)=u+4 from hY]
    apply sub_pos.mp
    ring_nf
    positivity

set_option maxRecDepth 10000 in
/-- The alternating factor at length 11 is nonsquare at every natural base
greater than one. The polynomial inequalities cover x ≥ 57. -/
theorem alternatingBlock_eleven_not_square {x : ℕ} (hx : 1 < x) :
    ¬IsSquare (alternatingBlock x 11) := by
  by_cases hx0 : x < 57
  · have hsmall : ∀ j : Fin 57, 1 < j.val → ¬IsSquare (alternatingBlock j.val 11) := by
      change ∀ j : Fin 57, 1 < j.val → ¬IsSquare ((j.val^11+1)/(j.val+1))
      decide +kernel
    exact hsmall ⟨x,hx0⟩ hx
  let u := ((x:ℤ)-57)
  let y := (x:ℤ)
  let P : ℤ := 256*y^5-128*y^4+96*y^3-80*y^2+70*y-63
  have hU : 0 ≤ u := by dsimp [u]; omega
  have hY : y=u+57 := by dsimp [y,u]; ring
  apply not_square_of_scaled_interval (P:=P) (D:=256)
  · dsimp only [P]
    rw [hY]
    ring_nf
    positivity
  · decide
  · exact ⟨128*y^5-64*y^4+48*y^3-40*y^2+35*y-32, by dsimp [P]; ring⟩
  · decide
  · rw [alternatingBlock_cast (by decide : Odd 11)]
    norm_num [sum_range_succ]
    dsimp only [P,y]
    rw [show (x:ℤ)=u+57 from hY]
    apply sub_pos.mp
    ring_nf
    positivity
  · rw [alternatingBlock_cast (by decide : Odd 11)]
    norm_num [sum_range_succ]
    dsimp only [P,y]
    rw [show (x:ℤ)=u+57 from hY]
    apply sub_pos.mp
    ring_nf
    positivity

set_option maxRecDepth 10000 in
/-- The alternating factor at length 13 is nonsquare at every natural base
greater than one. The polynomial inequalities cover x ≥ 214. -/
theorem alternatingBlock_thirteen_not_square {x : ℕ} (hx : 1 < x) :
    ¬IsSquare (alternatingBlock x 13) := by
  by_cases hx0 : x < 214
  · have hsmall : ∀ j : Fin 214, 1 < j.val → ¬IsSquare (alternatingBlock j.val 13) := by
      change ∀ j : Fin 214, 1 < j.val → ¬IsSquare ((j.val^13+1)/(j.val+1))
      decide +kernel
    exact hsmall ⟨x,hx0⟩ hx
  let u := ((x:ℤ)-214)
  let y := (x:ℤ)
  let P : ℤ := 1024*y^6-512*y^5+384*y^4-320*y^3+280*y^2-252*y+231
  have hU : 0 ≤ u := by dsimp [u]; omega
  have hY : y=u+214 := by dsimp [y,u]; ring
  apply not_square_of_scaled_interval (P:=P) (D:=1024)
  · dsimp only [P]
    rw [hY]
    ring_nf
    positivity
  · decide
  · exact ⟨512*y^6-256*y^5+192*y^4-160*y^3+140*y^2-126*y+115, by dsimp [P]; ring⟩
  · decide
  · rw [alternatingBlock_cast (by decide : Odd 13)]
    norm_num [sum_range_succ]
    dsimp only [P,y]
    rw [show (x:ℤ)=u+214 from hY]
    apply sub_pos.mp
    ring_nf
    positivity
  · rw [alternatingBlock_cast (by decide : Odd 13)]
    norm_num [sum_range_succ]
    dsimp only [P,y]
    rw [show (x:ℤ)=u+214 from hY]
    apply sub_pos.mp
    ring_nf
    positivity

/-- The nonsquare second half-block at lengths seven, eleven, and thirteen,
uniformly over Euler bases. -/
theorem half_sum_not_square_at_small_lengths {x s : ℕ} (hx : 1 < x) (hx4 : x%4=1)
    (hs : s=7 ∨ s=11 ∨ s=13) : ¬IsSquare ((x^s+1)/2) := by
  have hso : Odd s := by rcases hs with rfl | rfl | rfl <;> decide
  by_cases hx16 : x%16=1
  · have hsp : s.Prime := by rcases hs with rfl | rfl | rfl <;> decide
    apply half_sum_not_square_of_alternatingBlock (by omega) hsp hso
    · rcases hs with rfl | rfl | rfl
      · exact alternatingBlock_seven_not_square hx
      · exact alternatingBlock_eleven_not_square hx
      · exact alternatingBlock_thirteen_not_square hx
    · left
      rcases hs with rfl | rfl | rfl <;> decide
  · exact half_pow_succ_not_square_of_mod_sixteen hx4 hso hx16

/-- These three prime divisors of the Euler half-length rule out every square
or prime times a square as the component index, at all Euler primes. -/
theorem euler_index_ne_prime_mul_square_of_small_half_length_factor {N q a m s : ℕ} (hN : N.Perfect)
    (ho : Odd N) (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (ha : 1<a) (hqm : ¬q ∣ m)
    (hform : N=q^a*m^2) (hs : s=7 ∨ s=11 ∨ s=13) (hd : s ∣ (a+1)/2)
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^a ≠ l*t^2 :=
  euler_index_ne_prime_mul_square_of_second_block hN ho hq hq4 ha4 ha hqm hform
    (half_pow_succ_not_square_of_factor hq.one_lt hq4 (by omega) hd
      (fun _ hx hx4 => half_sum_not_square_at_small_lengths hx hx4 hs)) l t hl

end OddPerfect
