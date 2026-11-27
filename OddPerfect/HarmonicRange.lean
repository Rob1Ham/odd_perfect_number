module

public import OddPerfect.HarmonicForest
public import OddPerfect.HarmonicThirdLength

public section

namespace OddPerfect.HarmonicChain
open FactorBudget

@[expose] def rootTest (bank : PrimeBank) (fuel p : ℕ) (ts : List (ℕ × Tree)) : Bool :=
  let visit := fun e => run bank fuel (root.extend p e) (1*(e+1)) false ((ts.lookup e).getD .done)
  if 1000≤p then visit 2 else allExps p 3 visit

theorem rootTest_sound {bank : PrimeBank} (hp : bank.Certified) {fuel p : ℕ} {ts : List (ℕ × Tree)}
    (test : rootTest bank fuel p ts) : RootThree p := by
  apply root_three
  intro e ha hg hdiv
  by_cases hlarge : 1000≤p
  · have he : e<5 := by
      by_contra! h
      exact ha.2.1.not_ge ((show (10:ℕ)^15 ≤ 1000^5 by decide +kernel).trans
        ((Nat.pow_le_pow_left hlarge 5).trans (Nat.pow_le_pow_right (by omega) h)))
    have eq : e=2 := by have := ha.1; omega
    subst e
    exact run_sound bank hp _ _ (by simpa only [rootTest,ite_eq_left hlarge] using test)
  · exact run_sound bank hp _ _ (allExps_sound (by simpa only [rootTest,ite_eq_right hlarge] using test) ha hg hdiv)

@[expose] def Range (lo hi : ℕ) : Prop := ∀ p, lo≤p → p<hi → Odd p → RootThree p

theorem range_join {lo mid hi : ℕ} (low : Range lo mid) (high : Range mid hi) : Range lo hi := by
  intro p hl hh ho
  by_cases h : p<mid
  · exact low p hl h ho
  · exact high p (by omega) hh ho

/-- Each slot corresponds to one consecutive odd integer. A zero takes
a supplied root tree, a one requests the default terminal, and a larger
entry exhibits a proper divisor. -/
@[expose] def scan (bank : PrimeBank) (fuel p : ℕ) : List ℕ → List (List (ℕ × Tree)) → Bool
  | [], ts => ts.isEmpty
  | d::ds, ts =>
    if d=0 then match ts with
      | [] => false
      | t::rest => rootTest bank fuel p t && scan bank fuel (p+2) ds rest
    else if d=1 then rootTest bank fuel p [] && scan bank fuel (p+2) ds ts
    else decide (1<d ∧ d<p ∧ d∣p) && scan bank fuel (p+2) ds ts

theorem scan_sound (bank : PrimeBank) (hb : bank.Certified) (fuel p : ℕ) (ds : List ℕ)
    (ts : List (List (ℕ × Tree))) (ho : Odd p) (test : scan bank fuel p ds ts) :
    Range p (p+2*ds.length) := by
  induction ds generalizing p ts with
  | nil => intro q hl hh; simp at hh; omega
  | cons d ds ih =>
    have combine (hroot : RootThree p) (next : Range (p+2) (p+2+2*ds.length)) :
        Range p (p+2*(d::ds).length) := by
      intro q hl hh hq
      by_cases eq : q=p
      · exact eq ▸ hroot
      have oddp := Nat.odd_iff.mp ho
      have oddq := Nat.odd_iff.mp hq
      simp only [List.length_cons] at hh
      exact next q (by omega) (by omega) hq
    have oddnext : Odd (p+2) := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
    by_cases hd : d=0
    · cases ts with
      | nil => simp [scan,hd] at test
      | cons t ts =>
        simp only [scan,hd,if_true,Bool.and_eq_true] at test
        exact combine (rootTest_sound hb test.1) (ih _ _ oddnext test.2)
    · by_cases h1 : d=1
      · simp only [scan,ite_eq_right hd,ite_eq_left h1,Bool.and_eq_true] at test
        exact combine (rootTest_sound hb test.1) (ih _ _ oddnext test.2)
      · simp only [scan,ite_eq_right hd,ite_eq_right h1,Bool.and_eq_true,decide_eq_true_eq] at test
        apply combine _ (ih _ _ oddnext test.2)
        intro n _ hp
        rcases (Nat.dvd_prime hp).mp test.1.2.2 with h|h <;> have := test.1 <;> omega

/-- Together with Proposition 2 and Garcia, this finite interval covers
every possible component whose length is divisible by three. -/
theorem impossible_small_harmonic_of_range (all : Range 3 1316099) {n : ℕ}
    (H : Small n 3) (hd : 3∣n.divisors.card) : False := by
  rw [Nat.card_divisors H.odd.pos.ne'] at hd
  obtain ⟨p,hp,hdiv⟩ := (show Nat.Prime 3 by decide).prime.dvd_finsetProd_iff _ |>.mp hd
  have pr := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have po := H.odd.of_dvd_nat pd
  have h3 : 3≤p := by have := pr.two_le; have := Nat.odd_iff.mp po; omega
  exact all p h3 (H.base_lt_of_three_dvd_length hp hdiv) po n H pr pd hdiv

end OddPerfect.HarmonicChain
