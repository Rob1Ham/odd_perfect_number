module

public import OddPerfect.CyclotomicOrders
import OddPerfect.Euler
import OddPerfect.Thirteen
import Mathlib.Algebra.Ring.GeomSum

/-! # A finite sieve for the prime support of odd perfect numbers -/

public section

namespace OddPerfect.SupportSieve

/-- Test powers consecutively by updating a single small residue. -/
@[expose] def orderLoop (p r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel+1, i, x => if x = 1 then i else orderLoop p r fuel (i+1) ((x*p)%r)

@[expose] def orderMod (p r : ℕ) : ℕ := orderLoop p r (r-1) 1 (p%r)

private theorem orderLoop_correct {p r d : ℕ} (hr : r.Prime) (hor : orderOf (p : ZMod r) = d)
    (fuel i : ℕ) (hi : 0 < i) (hle : i ≤ d) (hlt : d < i + fuel) :
    orderLoop p r fuel i (p^i % r) = d := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    have htest : p^i %r = 1 ↔ d ∣ i := by
      rw [← hor, orderOf_dvd_iff_pow_eq_one, ← Nat.cast_pow]
      rw [← Nat.cast_one (R := ZMod r), ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr.one_lt]
    by_cases heq : i = d
    · rw [orderLoop, ite_eq_left (htest.mpr (heq ▸ dvd_rfl)), heq]
    · have hn : p^i %r ≠ 1 := fun h => heq (by have := Nat.le_of_dvd hi (htest.mp h); omega)
      rw [orderLoop, ite_eq_right hn, Nat.mod_mul_mod, ← pow_succ]
      apply ih <;> omega

private theorem orderMod_correct {p r d : ℕ} (hr : r.Prime) (hor : orderOf (p : ZMod r) = d)
    (hd : 0 < d) (hcon : d ∣ r-1) : orderMod p r = d := by
  have := Nat.le_of_dvd (by have := hr.one_lt; omega) hcon
  simpa [orderMod] using orderLoop_correct hr hor (r-1) 1 (by decide) hd (by omega)

/-- Return false as soon as a remaining factor is coprime to the support product.
When fuel runs out, keep the candidate. -/
@[expose] def smoothCheck (mask : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel+1, n => if n = 1 then true else
      let g := n.gcd mask
      if g = 1 then false else smoothCheck mask fuel (n/g)

private theorem smoothCheck_correct (mask fuel n : ℕ) (hn : 0 < n)
    (h : ∀ r, r.Prime → r ∣ n → r ∣ mask) : smoothCheck mask fuel n = true := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    by_cases hone : n = 1
    · simp [smoothCheck, hone]
    · obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hone
      have hdiv := Nat.dvd_gcd hrn (h r hr hrn)
      have hg : n.gcd mask ≠ 1 := fun hg => hr.not_dvd_one (hg ▸ hdiv)
      simp only [smoothCheck, hone, hg, ↓reduceIte]
      have hd := Nat.gcd_dvd_left n mask
      apply ih _ (Nat.div_pos (Nat.le_of_dvd hn hd) (Nat.gcd_pos_of_pos_left _ hn))
      intro s hs hsn
      exact h s hs (hsn.trans (Nat.div_dvd_of_dvd hd))

@[expose] def geomValue (p d : ℕ) : ℕ := (p^d-1)/(p-1)

private theorem geomValue_eq {p : ℕ} (hp : p.Prime) (e : ℕ) :
    geomValue p (e+1) = ArithmeticFunction.sigma 1 (p^e) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, geomValue, ← geom_sum_mul_of_one_le hp.one_le,
    Nat.mul_div_cancel _ (by have := hp.one_lt; omega)]

private theorem smooth_of_dvd_sigma {N p n : ℕ} (hN : N.Perfect) (hp : p.Prime) (hn : 0 < n)
    (hdiv : n ∣ ArithmeticFunction.sigma 1 (p^(N.factorization p))) (S : List ℕ)
    (hS : ∀ r ∈ N.primeFactors, r ∈ S) : smoothCheck (2*S.prod) 12 n = true := by
  have hσ : ArithmeticFunction.sigma 1 (p^(N.factorization p)) ∣ 2*N := by
    rw [ArithmeticFunction.sigma_one_apply]
    apply sum_divisors_dvd_two_mul hN (Nat.ordProj_mul_ordCompl_eq_self N p).symm
    exact (Nat.coprime_ordCompl hp hN.2.ne').pow_left _
  apply smoothCheck_correct _ _ _ hn
  intro r hr hrn
  rcases hr.dvd_mul.mp ((hrn.trans hdiv).trans hσ) with h2 | hd
  · exact dvd_mul_of_dvd_left h2 _
  · exact dvd_mul_of_dvd_right (List.dvd_prod (hS r (Nat.mem_primeFactors.mpr ⟨hr,hd,hN.2.ne'⟩))) _

@[expose] def viable (p r mask : ℕ) : Bool :=
  let d := orderMod p r
  d > 1 && (d%2 == 1 || (p%4 == 1 && d%4 == 2)) && smoothCheck mask 12 (geomValue p d)

/-- Keep bases for which at least one other modulus still supplies an admissible exponent. -/
@[expose] def round (S : List ℕ) : List ℕ :=
  let mask := 2*S.prod
  S.filter fun p => S.any fun r => r != p && viable p r mask

private theorem round_correct {N : ℕ} (hN : N.Perfect) (ho : Odd N) (S : List ℕ)
    (hS : ∀ p ∈ N.primeFactors, p ∈ S) : ∀ p ∈ N.primeFactors, p ∈ round S := by
  intro p hpm
  have hp := Nat.prime_of_mem_primeFactors hpm
  let e := N.factorization p
  have he : 0 < e := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpm)
  obtain ⟨r, hr, hor, hcon⟩ := exists_forced_order_of_length hN ho hp (e := e) rfl
    (by omega : 1 < e+1) dvd_rfl
  obtain ⟨hrp, hrm⟩ := Finset.mem_erase.mp hr
  have hrprime := Nat.prime_of_mem_primeFactors hrm
  have hd := orderMod_correct hrprime hor (by omega) hcon
  have hpar : (e+1)%2 = 1 ∨ p%4 = 1 ∧ (e+1)%4 = 2 := by
    obtain ⟨q, _, hq4, hqv, hrest⟩ := euler_exponents ho hN
    rcases eq_or_ne p q with rfl | h
    · right; exact ⟨hq4, by change (N.factorization p+1)%4=2; omega⟩
    · have := Nat.even_iff.mp (hrest p h)
      left; change (N.factorization p+1)%2=1; omega
  have hsmooth : smoothCheck (2*S.prod) 12 (geomValue p (e+1)) = true := by
    rw [geomValue_eq hp]
    exact smooth_of_dvd_sigma hN hp (ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.ne_zero))
      dvd_rfl S hS
  apply List.mem_filter.mpr
  refine ⟨hS p hpm, List.any_eq_true.mpr ⟨r, hS r hrm, ?_⟩⟩
  simp [viable, hrp, hd, hsmooth, he, hpar]

/-- Candidate odd primes up to and including the bound. -/
@[expose] def initial (B : ℕ) : List ℕ := (List.range (B+1)).filter fun p => p.Prime ∧ p ≠ 2

@[expose] def rounds (S : List ℕ) : ℕ → List ℕ
  | 0 => S
  | n+1 => round (rounds S n)

private theorem rounds_correct {N : ℕ} (hN : N.Perfect) (ho : Odd N)
    {S : List ℕ} (hS : ∀ p ∈ N.primeFactors, p ∈ S) (n : ℕ) :
    ∀ p ∈ N.primeFactors, p ∈ rounds S n := by
  induction n with
  | zero => exact hS
  | succ n ih => exact round_correct hN ho _ ih

/-- The surviving odd primes after a prescribed number of certified elimination rounds. -/
@[expose] def run (B n : ℕ) : List ℕ := rounds (initial B) n

private theorem exists_large_of_empty {B N : ℕ} (hN : N.Perfect) (ho : Odd N)
    (h : (∀ p ∈ N.primeFactors, p ∈ initial B) → ∀ p ∈ N.primeFactors, False) :
    ∃ p ∈ N.primeFactors, B < p := by
  by_contra! hall
  have hS : ∀ p ∈ N.primeFactors, p ∈ initial B := by
    intro p hp
    have hr := Nat.prime_of_mem_primeFactors hp
    have hh : p ≠ 2 := fun h => ho.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (by have := hall p hp; omega), by simp [hr,hh]⟩
  have hone : N ≠ 1 := by rintro rfl; simp [Nat.Perfect] at hN
  obtain ⟨p,hp,hdiv⟩ := Nat.exists_prime_and_dvd hone
  exact h hS p (Nat.mem_primeFactors.mpr ⟨hp,hdiv,hN.2.ne'⟩)

/-- An empty computed support excludes that entire interval of largest primes. -/
theorem exists_large_prime_of_empty_sieve {B n : ℕ} (hempty : run B n = [])
    {N : ℕ} (hN : N.Perfect) (ho : Odd N) : ∃ p ∈ N.primeFactors, B < p := by
  apply exists_large_of_empty hN ho
  intro hS p hp
  have h : p ∈ run B n := rounds_correct hN ho hS n p hp
  rw [hempty] at h
  exact List.not_mem_nil h

/-- Check only the primes dropped from a proposed successor support. -/
@[expose] def validStep (S T : List ℕ) : Bool :=
  let mask := 2*S.prod
  S.all fun p => T.contains p || !(S.any fun r => r != p && viable p r mask)

private theorem validStep_correct {N : ℕ} (hN : N.Perfect) (ho : Odd N) {S T : List ℕ}
    (hstep : validStep S T = true) (hS : ∀ p ∈ N.primeFactors, p ∈ S) :
    ∀ p ∈ N.primeFactors, p ∈ T := by
  intro p hp
  have hc := (List.mem_filter.mp (round_correct hN ho S hS p hp)).2
  have hh := List.all_eq_true.mp hstep p (hS p hp)
  simpa [hc] using hh

/-- A sequence of explicitly proposed supports lets the kernel verify each removal once. -/
@[expose] def certify (S : List ℕ) : List (List ℕ) → Bool
  | [] => S.isEmpty
  | T::rows => validStep S T && certify T rows

private theorem certify_correct {N : ℕ} (hN : N.Perfect) (ho : Odd N) (rows : List (List ℕ))
    (S : List ℕ) (hcheck : certify S rows = true) (hS : ∀ p ∈ N.primeFactors, p ∈ S) :
    ∀ p ∈ N.primeFactors, False := by
  induction rows generalizing S with
  | nil =>
    have hnil : S = [] := by simpa [certify] using hcheck
    subst S
    exact fun p hp => List.not_mem_nil (hS p hp)
  | cons T rest ih =>
    obtain ⟨hs, hc⟩ := Bool.and_eq_true_iff.mp hcheck
    exact ih T hc (validStep_correct hN ho hs hS)

theorem exists_large_prime_of_certificate {B N : ℕ} (rows : List (List ℕ))
    (hcheck : certify (initial B) rows = true) (hN : N.Perfect) (ho : Odd N) :
    ∃ p ∈ N.primeFactors, B < p :=
  exists_large_of_empty hN ho (certify_correct hN ho rows _ hcheck)

/-- The finite support sieve excludes every odd perfect number whose primes are at most 19. -/
theorem exists_prime_gt_nineteen {N : ℕ} (hN : N.Perfect) (ho : Odd N) :
    ∃ p ∈ N.primeFactors, 19 < p := exists_large_prime_of_empty_sieve (n := 5) (by decide) hN ho

/-- Proposed prime divisors of component lengths, and the support to retain. -/
@[expose] def validIndexStep (S L T : List ℕ) : Bool :=
  let cover := L.prod ^ 16
  let mask := 2 * S.prod
  L.all (fun l => decide l.Prime) &&
    (S.all (fun r => cover % (r-1) == 0) &&
    S.all (fun p => T.contains p || !(L.any fun l =>
      (l != 2 || p%4 == 1) && smoothCheck mask 12 (geomValue p l))))

private theorem prime_mem_of_dvd_prod {l : ℕ} (hl : l.Prime) (L : List ℕ)
    (hL : ∀ a ∈ L, Nat.Prime a) (hd : l ∣ L.prod) : l ∈ L := by
  induction L with
  | nil => exact (hl.not_dvd_one hd).elim
  | cons a L ih =>
    rcases hl.dvd_mul.mp hd with ha | ht
    · exact List.mem_cons.mpr (.inl ((Nat.prime_dvd_prime_iff_eq hl (hL a (.head _))).mp ha))
    · exact .tail _ (ih (fun j hj => hL j (.tail _ hj)) ht)

private theorem validIndexStep_correct {N : ℕ} (hN : N.Perfect) (ho : Odd N) {S L T : List ℕ}
    (hcheck : validIndexStep S L T = true) (hS : ∀ p ∈ N.primeFactors, p ∈ S) :
    ∀ p ∈ N.primeFactors, p ∈ T := by
  obtain ⟨hprime, hrest⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hcover, hnext⟩ := Bool.and_eq_true_iff.mp hrest
  intro p hpN
  have hp := Nat.prime_of_mem_primeFactors hpN
  let e := N.factorization p
  have he : 0 < e := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpN)
  obtain ⟨l, hl, hlen⟩ := Nat.exists_prime_and_dvd (by omega : e+1 ≠ 1)
  obtain ⟨r, hr, _, hcon⟩ := exists_forced_order_of_length hN ho hp (e := e) rfl hl.one_lt hlen
  have hc : L.prod^16 % (r-1) = 0 := by
    simpa using List.all_eq_true.mp hcover r (hS r (Finset.mem_erase.mp hr).2)
  have hlL := prime_mem_of_dvd_prod hl L (fun l h => of_decide_eq_true (List.all_eq_true.mp hprime l h))
    (hl.dvd_of_dvd_pow (hcon.trans (Nat.dvd_of_mod_eq_zero hc)))
  have hpar : l ≠ 2 ∨ p%4 = 1 := by
    rcases eq_or_ne l 2 with rfl | h
    · right
      obtain ⟨q, _, hq4, _, hrest⟩ := euler_exponents ho hN
      rcases eq_or_ne p q with rfl | hpq
      · exact hq4
      · have h := Nat.even_iff.mp (hrest p hpq)
        change 2 ∣ N.factorization p + 1 at hlen
        omega
    · exact Or.inl h
  have hgeom : geomValue p l = ∑ i ∈ Finset.range l, p ^ i := by
    rw [geomValue, ← geom_sum_mul_of_one_le hp.one_le, Nat.mul_div_cancel _ (by have := hp.one_lt; omega)]
  have hdiv : geomValue p l ∣ ArithmeticFunction.sigma 1 (p^e) := by
    rw [hgeom, ArithmeticFunction.sigma_one_apply_prime_pow hp,
      dvd_geom_sum_iff_remainder (dvd_refl (∑ i ∈ Finset.range l, p^i)), Nat.mod_eq_zero_of_dvd hlen]
    simp
  have pos : 0 < geomValue p l := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
    rw [hj, geomValue_eq hp]
    exact ArithmeticFunction.sigma_pos _ _ (pow_ne_zero _ hp.ne_zero)
  have hsmooth := smooth_of_dvd_sigma hN hp pos hdiv S hS
  have hany : L.any (fun l => (l != 2 || p%4 == 1) && smoothCheck (2*S.prod) 12 (geomValue p l)) = true :=
    List.any_eq_true.mpr ⟨l,hlL,by simp [hsmooth, hpar]⟩
  simpa [hany] using List.all_eq_true.mp hnext p (hS p hpN)

/-- Kernel certificate with a short list of possible prime lengths for each support. -/
@[expose] def certifyIndices (S : List ℕ) : List (List ℕ × List ℕ) → Bool
  | [] => S.isEmpty
  | (L,T)::rows => validIndexStep S L T && certifyIndices T rows

private theorem certifyIndices_correct {N : ℕ} (hN : N.Perfect) (ho : Odd N)
    (rows : List (List ℕ × List ℕ)) (S : List ℕ) (hcheck : certifyIndices S rows = true)
    (hS : ∀ p ∈ N.primeFactors, p ∈ S) : ∀ p ∈ N.primeFactors, False := by
  induction rows generalizing S with
  | nil =>
    have hnil : S = [] := by simpa [certifyIndices] using hcheck
    subst S
    exact fun p hp => List.not_mem_nil (hS p hp)
  | cons row rest ih =>
    obtain ⟨L,T⟩ := row
    obtain ⟨hs,hc⟩ := Bool.and_eq_true_iff.mp hcheck
    exact ih T hc (validIndexStep_correct hN ho hs hS)

theorem exists_large_prime_of_index_certificate {B N : ℕ} (rows : List (List ℕ × List ℕ))
    (hcheck : certifyIndices (initial B) rows = true) (hN : N.Perfect) (ho : Odd N) :
    ∃ p ∈ N.primeFactors, B < p :=
  exists_large_of_empty hN ho (certifyIndices_correct hN ho rows _ hcheck)

private def rows257 : List (List ℕ × List ℕ) :=
  [([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 41, 43, 53, 83, 89, 113], [3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 41, 47, 53, 59, 61, 67, 73, 79, 89, 97, 101, 107, 109, 113, 137, 149, 157, 163, 173, 181, 191, 193, 197, 211, 229, 233, 241, 257]),
   ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 43, 53], [3, 5, 7, 11, 13, 17, 23, 29, 37, 41, 47, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 163, 173, 181, 193, 197, 229, 233, 241]),
   ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 43], [3, 5, 13, 17, 29, 41, 47, 53, 61, 73, 89, 97, 101, 109, 137, 149, 173, 181, 193, 197, 229, 233, 241]),
   ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 43], [3, 5, 13, 17, 29, 53, 61, 89, 101, 149, 173, 193, 229, 233]),
   ([2, 3, 5, 7, 11, 13, 19, 29, 37, 43], [3, 5, 13, 17, 29, 53, 89, 101, 149, 173, 233]),
   ([2, 3, 5, 7, 11, 13, 29, 37, 43], [3, 5, 17, 29, 53, 89, 101, 149, 173, 233]),
   ([2, 5, 7, 11, 13, 29, 37, 43], [5, 17, 29, 53, 89, 101, 149, 173]),
   ([2, 5, 7, 11, 13, 37, 43], [])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Every odd perfect number has a prime factor strictly exceeding 257. -/
theorem exists_prime_gt_257 {N : ℕ} (hN : N.Perfect) (ho : Odd N) :
    ∃ p ∈ N.primeFactors, 257 < p := by
  apply exists_large_prime_of_index_certificate rows257 _ hN ho
  decide

end OddPerfect.SupportSieve
