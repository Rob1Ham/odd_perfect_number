module

public import OddPerfect.Reciprocity
public import OddPerfect.GeometricSquareClass
public import OddPerfect.Reciprocal
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! # Prime square classes forced in the Euler index -/

public section
namespace OddPerfect
open ArithmeticFunction Finset

private theorem sum_split (q d : ℕ) :
    (∑ j ∈ range (d+d), q^j) = (∑ j ∈ range d, q^j)*(q^d+1) := by
  rw [sum_range_add]
  simp_rw [pow_add]
  rw [← mul_sum]
  ring

private theorem odd_valuation_transfer {r A B i m : ℕ} (hm : m ≠ 0)
    (h : m^2=A*B*i) (hA : Odd (A.factorization r)) (hB : ¬r ∣ B) : Odd (i.factorization r) := by
  have hp : A*B*i ≠ 0 := h ▸ pow_ne_zero 2 hm
  have hAB := left_ne_zero_of_mul hp
  have hx := congrArg (fun x : ℕ => x.factorization r) h
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_mul hAB (right_ne_zero_of_mul hp), Nat.factorization_mul (left_ne_zero_of_mul hAB) (right_ne_zero_of_mul hAB),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hB, add_zero] at hx
  exact Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hA; omega)

private theorem prime_not_dvd_other {r A B : ℕ} (hr : r.Prime) (hc : A.Coprime B) (hd : r ∣ A) : ¬r ∣ B :=
  fun h => hr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hd h)

private theorem euler_half_blocks {q a m i : ℕ} (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1)
    (hret : sigma 1 (q^a)*i=2*m^2) :
    let d := (a+1)/2
    let A := geometricBlock q d
    let B := (q^d+1)/2
    m^2=A*B*i ∧ A.Coprime B ∧ A%4=d%4 ∧ 2*B=q^d+1 ∧ B%4=((q+1)/2)%4 := by
  dsimp only
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  change m^2=A*B*i ∧ A.Coprime B ∧ A%4=d%4 ∧ 2*B=q^d+1 ∧ B%4=((q+1)/2)%4
  have hd1 : d%2=1 := by dsimp [d]; omega
  have hd0 : 0<d := by omega
  have hsigma : sigma 1 (q^a) = A*(q^d+1) := by
    rw [sigma_one_apply_prime_pow hq, show a+1=d+d by dsimp [d]; omega, sum_split]
    rfl
  have hAd : A = sigma 1 (q^(d-1)) := by rw [sigma_one_apply_prime_pow hq, Nat.sub_add_cancel hd0]; rfl
  have hA : A%4=d%4 := by
    have h := sigma_modEq_of_one hq (show q ≡ 1 [MOD 4] from hq4) (d-1)
    rw [hAd]
    rwa [show d-1+1=d by omega] at h
  have hqd : q^d %8=q%8 := by
    have h8 : q%8=1 ∨ q%8=5 := by omega
    have hs : q^2 ≡ 1 [MOD 8] := by
      change q^2%8=1
      rw [pow_two,Nat.mul_mod]
      rcases h8 with h | h <;> simp [h]
    have h := (hs.pow (d/2)).mul_right q
    simpa [← pow_mul, show 2*(d/2)=d-1 by omega, ← pow_succ, Nat.sub_add_cancel hd0, Nat.ModEq] using h
  have hBmul : 2*B=q^d+1 := by dsimp [B]; omega
  have hB : B%4=((q+1)/2)%4 := by dsimp [B]; omega
  refine ⟨?_,?_,hA,hBmul,hB⟩
  · apply Nat.eq_of_mul_eq_mul_left (by decide : 0<2)
    rw [← hret,hsigma,← hBmul]
    ac_rfl
  · by_contra hh
    obtain ⟨s,hs,hsA,hsB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    have hsminus : s ∣ q^d-1 := by
      rw [← geom_sum_mul_of_one_le hq.one_le]
      exact dvd_mul_of_dvd_left hsA _
    have hsplus : s ∣ q^d+1 := hsB.trans (hBmul ▸ dvd_mul_left B 2)
    have ht : s ∣ 2 := by
      have h := Nat.dvd_sub hsplus hsminus
      rwa [show q^d+1-(q^d-1)=2 by have := Nat.pow_pos hq.pos (n := d); omega] at h
    have heq := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp ht
    subst s
    omega

/-- The two half-length geometric factors force two distinct odd valuations
with opposite quadratic characters modulo the Euler prime. -/
theorem five_mod_eight_index_odd_valuations {q a m i : ℕ} (hq : q.Prime) (hq5 : q%8=5)
    (ha5 : a%8=5) (hm : 0 < m) (hret : sigma 1 (q^a)*i = 2*m^2) :
    ∃ r ∈ i.primeFactors, ∃ s ∈ i.primeFactors, r ≠ s ∧ r%4=3 ∧ s%4=3 ∧
      IsSquare (r : ZMod q) ∧ ¬ IsSquare (s : ZMod q) ∧ Odd (i.factorization r) ∧ Odd (i.factorization s) := by
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  have hd3 : d%4=3 := by dsimp [d]; omega
  have hd0 : 0<d := by omega
  have hAd : A = sigma 1 (q^(d-1)) := by rw [sigma_one_apply_prime_pow hq, Nat.sub_add_cancel hd0]; rfl
  obtain ⟨hbal,hcop,hA,hBmul,hB⟩ := euler_half_blocks hq (by omega : q%4=1) (by omega : a%4=1) hret
  have hA3 : A%4=3 := hA.trans hd3
  have hB3 : B%4=3 := hB.trans (by omega)
  obtain ⟨r,hr,hr4,hvA⟩ := exists_three_mod_four_odd_valuation hA3
  obtain ⟨s,hs,hs4,hvB⟩ := exists_three_mod_four_odd_valuation hB3
  have hrp := Nat.prime_of_mem_primeFactors hr
  have hsp := Nat.prime_of_mem_primeFactors hs
  have hrA := Nat.dvd_of_mem_primeFactors hr
  have hsB := Nat.dvd_of_mem_primeFactors hs
  have hri := odd_valuation_transfer hm.ne' hbal hvA (prime_not_dvd_other hrp hcop hrA)
  have hsi := odd_valuation_transfer hm.ne' (hbal.trans (by ac_rfl : A*B*i=B*A*i)) hvB (prime_not_dvd_other hsp hcop.symm hsB)
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hrp⟩
  let : Fact s.Prime := ⟨hsp⟩
  have hqr : IsSquare (r : ZMod q) := by
    apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by omega : q%4=1) (by omega : r ≠ 2)).mpr
    apply isSquare_of_dvd_sigma_even hq hrp (Nat.even_iff.mpr (by omega : (d-1)%2=0))
    rwa [← hAd]
  have hqs : ¬IsSquare (s : ZMod q) := by
    intro h
    have hx := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (by omega : q%4=1) (by omega : s ≠ 2)).mp h
    have hsplus : s ∣ q^d+1 := hsB.trans (hBmul ▸ dvd_mul_left B 2)
    have hneg : (q : ZMod s)^d = -1 := by
      have hz := (ZMod.natCast_eq_zero_iff (q^d+1) s).mpr hsplus
      simpa [Nat.cast_add, Nat.cast_pow, eq_neg_iff_add_eq_zero] using hz
    exact ZMod.exists_sq_eq_neg_one_iff.mp (hneg ▸ hx.pow d) hs4
  refine ⟨r,Finsupp.mem_support_iff.mpr hri.pos.ne',s,Finsupp.mem_support_iff.mpr hsi.pos.ne',
    fun heq => hqs (heq ▸ hqr),hr4,hs4,hqr,hqs,hri,hsi⟩

private theorem even_valuation_mul_square {r l t : ℕ} (ht : t ≠ 0) (hl : l ≠ 0) (hnd : ¬ r ∣ l) :
    Even ((l*t^2).factorization r) := by
  rw [Nat.factorization_mul hl (pow_ne_zero _ ht), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, Nat.factorization_pow, Finsupp.smul_apply, zero_add, smul_eq_mul]
  exact ⟨t.factorization r, by omega⟩

private theorem ne_prime_mul_square_of_two_odd {i r s : ℕ} (hi : 0 < i) (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hrv : Odd (i.factorization r)) (hsv : Odd (i.factorization s))
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : i ≠ l*t^2 := by
  intro heq
  have hl0 : l ≠ 0 := by rintro rfl; simp [heq] at hi
  have ht0 : t ≠ 0 := by rintro rfl; simp [heq] at hi
  have hind {w : ℕ} (hw : Odd (i.factorization w)) : w ∣ l := by
    by_contra hn
    have he := Nat.even_iff.mp (even_valuation_mul_square ht0 hl0 hn)
    have hh := Nat.odd_iff.mp hw
    rw [heq] at hh
    omega
  rcases hl with rfl | hl
  · exact hr.not_dvd_one (hind hrv)
  · exact hrs (((Nat.prime_dvd_prime_iff_eq hr hl).mp (hind hrv)).trans
      ((Nat.prime_dvd_prime_iff_eq hs hl).mp (hind hsv)).symm)

/-- In this Euler residue class the index is neither a square nor one prime times
any square. This is an elementary subcase of Hirakawa's general theorem. -/
theorem euler_index_ne_prime_mul_square_of_five_mod_eight {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq5 : q%8=5) (ha5 : a%8=5) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2)
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^a ≠ l*t^2 := by
  obtain ⟨i,hip,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  obtain ⟨r,hr,s,hs,hrs,_,_,_,_,hri,hsi⟩ := five_mod_eight_index_odd_valuations hq hq5 ha5 hm hright
  exact ne_prime_mul_square_of_two_odd hip (Nat.prime_of_mem_primeFactors hr)
    (Nat.prime_of_mem_primeFactors hs) hrs hri hsi l t hl

private theorem threeOddFactors_eq_of_square_product {m H i : ℕ} (hm : m ≠ 0) (h : m^2=H*i) :
    threeOddFactors H = threeOddFactors i := by
  have hh : H*i ≠ 0 := h ▸ pow_ne_zero _ hm
  ext r
  have he := congrArg (fun x : ℕ => x.factorization r) h
  simp only [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul,Nat.factorization_mul
    (left_ne_zero_of_mul hh) (right_ne_zero_of_mul hh),Finsupp.add_apply] at he
  have hf : Odd (H.factorization r) ↔ Odd (i.factorization r) := by
    simp only [Nat.odd_iff]; omega
  constructor
  · intro hr
    obtain ⟨_,hr3,hrv⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (hf.mp hrv).pos.ne',hr3,hf.mp hrv⟩
  · intro hr
    obtain ⟨_,hr3,hrv⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (hf.mpr hrv).pos.ne',hr3,hf.mpr hrv⟩

/-- Every `3 mod 4` prime of odd valuation in the half-length forces a distinct
such prime in the Euler index. An Euler prime `5 mod 8` adds one further prime. -/
theorem euler_index_three_odd_factor_count {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2) :
    (threeOddFactors ((a+1)/2)).card + (if q%8=5 then 1 else 0) ≤
      (threeOddFactors (sigma 1 (m^2)/q^a)).card := by
  obtain ⟨i,_,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  obtain ⟨hbal,hcop,_,_,hB⟩ := euler_half_blocks hq hq4 ha4 hright
  have hh : A*B*i ≠ 0 := hbal ▸ pow_ne_zero _ hm.ne'
  have hAB := left_ne_zero_of_mul hh
  have hBs : (if q%8=5 then 1 else 0) ≤ (threeOddFactors B).card := by
    split_ifs with h5
    · obtain ⟨p,hp,hp3,ho⟩ := exists_three_mod_four_odd_valuation (show B%4=3 from hB.trans (by omega))
      exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp,hp3,ho⟩⟩
    · omega
  rw [← threeOddFactors_eq_of_square_product hm.ne' hbal, threeOddFactors_card_mul (left_ne_zero_of_mul hAB) (right_ne_zero_of_mul hAB) hcop]
  exact Nat.add_le_add (threeOddFactors_card_geometricBlock hq4 d (by dsimp [d]; omega)) hBs

/-- Two index factors supplied by the half-length count already exclude every
square or prime times a square, with no fixed upper bound on the Euler exponent. -/
theorem euler_index_ne_prime_mul_square_of_count {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬q ∣ m) (hform : N=q^a*m^2)
    (hc : 2 ≤ (threeOddFactors ((a+1)/2)).card + (if q%8=5 then 1 else 0))
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^a ≠ l*t^2 := by
  let i := sigma 1 (m^2)/q^a
  have h := euler_index_three_odd_factor_count hN ho hq hq4 ha4 hqm hform
  obtain ⟨r,hr,s,hs,hrs⟩ := Finset.one_lt_card.mp (hc.trans h : 1 < (threeOddFactors i).card)
  obtain ⟨hrm,_,hrv⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsm,_,hsv⟩ := Finset.mem_filter.mp hs
  exact ne_prime_mul_square_of_two_odd (Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hrm).2.2)
    (Nat.prime_of_mem_primeFactors hrm) (Nat.prime_of_mem_primeFactors hsm) hrs hrv hsv l t hl

private theorem exists_odd_valuation_of_nonsquare {n : ℕ} (hn : ¬ IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ Odd (n.factorization p) := by
  by_contra h
  apply hn
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  exact (Nat.even_or_odd _).resolve_right (fun ho => h ⟨p,hp,ho⟩)

private theorem exists_odd_valuation_away_three {n : ℕ} (hn4 : n%4=1) (hn : ¬IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ Odd (n.factorization p) := by
  by_contra h
  have heven {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : Even (n.factorization p) :=
    (Nat.even_or_odd _).resolve_right (fun ho => h ⟨p,hp,hp3,ho⟩)
  obtain ⟨p,hp,ho⟩ := exists_odd_valuation_of_nonsquare hn
  have heq : p=3 := Classical.byContradiction (fun hp3 => h ⟨p,hp,hp3,ho⟩)
  subst p
  have hsq : IsSquare (ordCompl[3] n) := by
    apply Nat.isSquare_iff_even_factorization.mpr
    intro r hr
    rw [Nat.factorization_ordCompl]
    rcases eq_or_ne r 3 with rfl | hne
    · simp
    · rw [Finsupp.erase_ne hne]
      exact heven hr hne
  obtain ⟨v,hv⟩ := hsq
  obtain ⟨k,hk⟩ := ho
  let w := 3^k*v
  have hshape : n=3*w^2 := by
    calc n = 3^(n.factorization 3) * ordCompl[3] n := (Nat.ordProj_mul_ordCompl_eq_self n 3).symm
      _ = _ := by rw [hv,show n.factorization 3=k*2+1 by omega,pow_succ,pow_mul]; dsimp [w]; ring
  have hr : w%4=0 ∨ w%4=1 ∨ w%4=2 ∨ w%4=3 := by omega
  rw [hshape,pow_two,Nat.mul_mod 3 _ 4,Nat.mul_mod w w 4] at hn4
  rcases hr with h | h | h | h <;> simp [h] at hn4

/-- The cubic half-sum is never square at an integer base `1 mod 4` greater
than one. The only possible common prime of `(x+1)/2` and `x²−x+1` is three. -/
theorem half_cube_succ_not_square {x : ℕ} (hx : 1<x) (hx4 : x%4=1) : ¬IsSquare ((x^3+1)/2) := by
  let C := x*(x-1)+1
  let H := (x+1)/2
  have hCpos : 0<C := by dsimp [C]; omega
  have hHpos : 0<H := by dsimp [H]; omega
  have hCx : C+x=x^2+1 := by
    dsimp [C]
    have h := congrArg (x*·) (Nat.sub_add_cancel (by omega : 1≤x))
    nlinarith
  have hCt : C=(x+1)*(x-2)+3 := by
    have h := congrArg ((x+1)*·) (Nat.sub_add_cancel (by omega : 2≤x))
    nlinarith
  have hC4 : C%4=1 := by
    dsimp [C]
    rw [Nat.add_mod, Nat.mul_mod, hx4, show (x-1)%4=0 by omega]
  have hCn : ¬IsSquare C := by
    rintro ⟨t,ht⟩
    rcases le_or_gt x t with h | h
    · have hh := Nat.mul_self_le_mul_self h
      nlinarith
    · have hh := Nat.mul_self_le_mul_self (by omega : t≤x-1)
      have he := congrArg (fun n : ℕ => n^2) (Nat.sub_add_cancel (by omega : 1 ≤ x))
      nlinarith
  have hprod : H*C=(x^3+1)/2 := by
    have hf : (x+1)*C=x^3+1 := by
      have h := congrArg (x*·) hCx
      nlinarith
    have hH : 2*H=x+1 := by dsimp [H]; omega
    rw [← hf,← hH,mul_assoc,Nat.mul_div_cancel_left _ (by decide)]
  obtain ⟨p,hp,hp3,hv⟩ := exists_odd_valuation_away_three hC4 hCn
  have hdC : p ∣ C := (hp.dvd_iff_one_le_factorization hCpos.ne').mpr hv.pos
  have hnH : ¬p ∣ H := by
    intro hd
    have hpplus : p ∣ x+1 := hd.trans ⟨2,by dsimp [H]; omega⟩
    rw [hCt] at hdC
    have h3 := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hpplus (x-2))).mpr hdC
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3)
  intro hsq
  rw [← hprod] at hsq
  have he := Nat.isSquare_iff_even_factorization.mp hsq p hp
  rw [Nat.factorization_mul hHpos.ne' hCpos.ne', Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnH, zero_add] at he
  have := Nat.odd_iff.mp hv
  have := Nat.even_iff.mp he
  omega

/-- If the Euler half-length is divisible by three and has a `3 mod 4` prime of
odd valuation, the index has at least two distinct primes of odd valuation. -/
theorem euler_index_ne_prime_mul_square_of_cubic_length {N q a m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (ha4 : a%4=1) (hqm : ¬ q ∣ m) (hform : N=q^a*m^2)
    (h3 : 3 ∣ (a+1)/2) (hodd : (threeOddFactors ((a+1)/2)).Nonempty)
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^a ≠ l*t^2 := by
  obtain ⟨i,hip,hleft,hright,_⟩ := exists_component_index hN hq hform (fun h => hqm (hq.dvd_of_dvd_pow h))
  rw [hleft,Nat.mul_div_cancel_left i (pow_pos hq.pos _)]
  have hm := (ho.of_dvd_nat (hform ▸ dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0)) _)).pos
  let d := (a+1)/2
  let A := geometricBlock q d
  let B := (q^d+1)/2
  have hdpos : 0<d := by dsimp [d]; omega
  obtain ⟨hbal,hcop,_,_,_⟩ := euler_half_blocks hq hq4 ha4 hright
  have hAB : A*B*i ≠ 0 := hbal ▸ pow_ne_zero _ hm.ne'
  have hA0 := left_ne_zero_of_mul (left_ne_zero_of_mul hAB)
  have hB0 := right_ne_zero_of_mul (left_ne_zero_of_mul hAB)
  have hAC : (threeOddFactors A).Nonempty := Finset.card_pos.mp ((Finset.card_pos.mpr hodd).trans_le
    (threeOddFactors_card_geometricBlock hq4 d hdpos))
  obtain ⟨r,hr⟩ := hAC
  obtain ⟨hrm,_,hrv⟩ := Finset.mem_filter.mp hr
  have hrp := Nat.prime_of_mem_primeFactors hrm
  have hBn : ¬IsSquare B := by
    obtain ⟨j,hj⟩ := h3
    have hdj : d=j*3 := hj.trans (mul_comm _ _)
    have hj0 : j ≠ 0 := by rintro rfl; simp at hdj; omega
    change ¬IsSquare ((q^d+1)/2)
    rw [hdj,pow_mul]
    exact half_cube_succ_not_square (one_lt_pow₀ hq.one_lt hj0)
      (by simpa [Nat.ModEq] using (show q ≡ 1 [MOD 4] from hq4).pow j)
  obtain ⟨s,hsp,hsv⟩ := exists_odd_valuation_of_nonsquare hBn
  have hsB : s ∣ B := (hsp.dvd_iff_one_le_factorization hB0).mpr hsv.pos
  have hrB := prime_not_dvd_other hrp hcop (Nat.dvd_of_mem_primeFactors hrm)
  have hrs : r ≠ s := fun h => hrB (h ▸ hsB)
  have hri := odd_valuation_transfer hm.ne' hbal hrv hrB
  have hsi := odd_valuation_transfer hm.ne' (hbal.trans (by ac_rfl : A*B*i=B*A*i)) hsv
    (prime_not_dvd_other hsp hcop.symm hsB)
  exact ne_prime_mul_square_of_two_odd hip hrp hsp hrs hri hsi l t hl

/-- Hirakawa's square/prime-times-square exclusion for the entire Euler
exponent-five case, using only elementary geometric factors. -/
theorem euler_five_index_ne_prime_mul_square {N q m : ℕ} (hN : N.Perfect) (ho : Odd N)
    (hq : q.Prime) (hq4 : q%4=1) (hqm : ¬q ∣ m) (hform : N=q^5*m^2)
    (l t : ℕ) (hl : l=1 ∨ l.Prime) : sigma 1 (m^2)/q^5 ≠ l*t^2 := by
  apply euler_index_ne_prime_mul_square_of_cubic_length hN ho hq hq4 (by decide : 5%4=1) hqm hform (by decide)
  · refine ⟨3,Finset.mem_filter.mpr ⟨?_,by decide,?_⟩⟩
    · exact Nat.mem_primeFactors.mpr ⟨by decide,by decide,by decide⟩
    · change Odd ((3:ℕ).factorization 3)
      rw [Nat.Prime.factorization_self (by decide : Nat.Prime 3)]
      exact ⟨0,rfl⟩
  · exact hl

end OddPerfect
