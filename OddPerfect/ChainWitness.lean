module

public import OddPerfect.ChainArithmetic

/-! Exact-exponent replay with modular witnesses for residual coprimality. -/

public section

namespace OddPerfect.FactorBudget
open ArithmeticFunction

private theorem divisorSum_dvd {N m B w : ℕ} {s : Node} (H : Conditions N B w)
    (h : Realizes s N m) : s.divisorSum ∣ 2*N := by
  rw [← (Nat.perfect_iff_sum_divisors_eq_two_mul H.perfect.2).mp H.perfect, ← sigma_one_apply,
    h.value,isMultiplicative_sigma.map_mul_of_coprime h.coprime,h.sigma]
  exact Nat.dvd_mul_right _ _

private theorem oddPart_dvd {a N : ℕ} (h : a∣2*N) : a/a.gcd 2∣N := by
  have hg := Nat.dvd_gcd (Nat.dvd_mul_right a N) h
  rw [Nat.gcd_mul_right] at hg
  exact (Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left a 2) (Nat.gcd_pos_of_pos_right a (by decide : 0<2))).2 hg

/-- A previous prime power has already exceeded the valuation available in the
exact component. The supplied path is checked even when it starts at a checkpoint. -/
@[expose] def Node.pathClash (s : Node) (path : List (ℕ × ℕ)) : Bool :=
  path.any fun (p,e) => decide (p^(e+1) ∣ s.divisorSum ∧ ¬ p^(e+1) ∣ 2*s.component ∧ p∣s.component)

private theorem pathClash_false {N m B w : ℕ} {s : Node} (H : Conditions N B w)
    (h : Realizes s N m) (path : List (ℕ × ℕ)) (test : s.pathClash path = true) : False := by
  obtain ⟨⟨p,e⟩,_,hg⟩ := List.any_eq_true.mp test
  obtain ⟨hs,hnd,hd⟩ := of_decide_eq_true hg
  apply hnd
  apply ((h.coprime.coprime_dvd_left hd).pow_left _).dvd_of_dvd_mul_right
  simpa only [h.value,Nat.mul_assoc] using hs.trans (divisorSum_dvd H h)

@[expose] def Node.directWitness (s : Node) (B w avoid : ℕ) (path : List (ℕ × ℕ)) : Bool :=
  decide (4∣s.divisorSum ∨ 2*s.component<s.divisorSum ∨
    (B≤s.spent+1 ∧ s.divisorSum<2*s.component ∧ ¬ (2*s.component-s.divisorSum)∣s.divisorSum) ∨
    B+1<s.spent+2*(w-s.closed)+s.spent%2) ||
  (avoid != 1 && decide (¬(avoid.Coprime s.component ∧ avoid.Coprime (s.divisorSum/s.divisorSum.gcd 2)))) ||
  s.pathClash path

/-- The state budget still holds for a virtual support target when increasing the
target above the actual support receives two budget places for every extra target. -/
theorem budget_bound_of_offset {N m B actual W : ℕ} {s : Node} (H : Conditions N B actual)
    (h : Realizes s N m) (offset : 2*W + cardFactors N ≤ B + 2*N.primeFactors.card)
    {k : ℕ} (hk : k ≤ m.primeFactors.card) :
    s.spent + 2 * max k (W-s.closed) + s.spent%2 ≤ B+1 := by
  have ordinary := budget_bound H h hk
  have sharp : Conditions N (cardFactors N) N.primeFactors.card := ⟨H.odd,H.perfect,le_rfl,le_rfl⟩
  have actual := budget_bound sharp h (k:=0) (Nat.zero_le _)
  simp only [Nat.zero_max] at actual
  have splitCount : N.primeFactors.card = s.closed + m.primeFactors.card := by
    rw [← cardDistinctFactors_eq_card_primeFactors,h.value,cardDistinctFactors_mul h.coprime,
      h.closed,cardDistinctFactors_eq_card_primeFactors]
  omega

private theorem admissible_of_offset {N m B actual W p : ℕ} {s : Node}
    (H : Conditions N B actual) (h : Realizes s N m) (hp : p.Prime) (hd : p∣m)
    (offset : 2*W + cardFactors N ≤ B + 2*N.primeFactors.card) :
    s.admissible p (m.factorization p) B W = true := by
  have allowed := of_decide_eq_true (admissible_of_realizes H h hp hd)
  have next := extend_realizes H.odd.pos.ne' h hp hd
  have bound := budget_bound_of_offset H next offset (k:=0) (Nat.zero_le _)
  simp only [Nat.zero_max,Node.extend] at bound
  exact decide_eq_true ⟨allowed.1,bound⟩

private theorem groups_of_offset {N m B actual W c : ℕ} {s : Node}
    (H : Conditions N B actual) (h : Realizes s N m) (hc : 18*N.primeFactors.card ≤ 7*B+c)
    (offset : 2*W + cardFactors N ≤ B + 2*N.primeFactors.card) (gs : List ℕ)
    (test : s.closesGroups B W c gs = true) : False := by
  simp only [Node.closesGroups,Bool.and_eq_true,decide_eq_true_eq] at test
  obtain ⟨hg,hd,hb | hx⟩ := test
  · exact hb.not_ge (budget_bound_of_offset H h offset (groups_le_support H.perfect h gs hg hd))
  · apply extraGroupCheck_false H h hc gs
    simpa only [Node.extraGroupCheck,Bool.and_eq_true,decide_eq_true_eq] using And.intro hg (And.intro hd hx)

private theorem directWitness_false {N m B actual w avoid : ℕ} {s : Node} (H : Conditions N B actual)
    (h : Realizes s N m) (hav : avoid.Coprime N) (offset : 2*w + cardFactors N ≤ B + 2*N.primeFactors.card)
    (path : List (ℕ × ℕ)) (test : s.directWitness B w avoid path = true) : False := by
  simp only [Node.directWitness,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at test
  rcases test with ((h4 | hab | hlast | hw) | ⟨_,hbad⟩) | hpath
  · exact automatic_false H h (decide_eq_true (Or.inl h4))
  · exact automatic_false H h (decide_eq_true (Or.inr (Or.inl hab)))
  · exact automatic_false H h (decide_eq_true (Or.inr (Or.inr (Or.inr (Or.inl hlast)))))
  · have bound := budget_bound_of_offset H h offset (k:=0) (Nat.zero_le _)
    simp only [Nat.zero_max] at bound
    exact hw.not_ge bound
  · exact hbad ⟨hav.coprime_dvd_right (h.value ▸ Nat.dvd_mul_right _ _),
      hav.coprime_dvd_right (oddPart_dvd (divisorSum_dvd H h))⟩
  · exact pathClash_false H h path hpath

/-- Witnesses for each internal split and each terminal factor group. -/
inductive ArithmeticTree where
  | automatic
  | groups (inv : ℕ) (groups : List ℕ)
  | split (p : ℕ) (children : List (ℕ × ArithmeticTree))
  | cut (a L g inv roughInv : ℕ) (children : List (ℕ × ArithmeticTree))

@[expose] def Node.splitWitness (s : Node) (primes : List ℕ) (seed p : ℕ) : Bool :=
  decide (p ∈ primes ∧ p ≠ 2 ∧ ¬p∣s.component ∧ (p∣s.divisorSum ∨ p∣seed))

private theorem splitWitness_dvd {N m B w seed p : ℕ} {s : Node} (H : Conditions N B w)
    (h : Realizes s N m) (hs : seed∣N) (primes : List ℕ) (valid : ∀ p∈primes,p.Prime)
    (test : s.splitWitness primes seed p = true) : p.Prime ∧ p∣m := by
  obtain ⟨hin,h2,hnew,hdiv⟩ := of_decide_eq_true test
  have hp := valid p hin
  refine ⟨hp, (hp.coprime_iff_not_dvd.mpr hnew).dvd_of_dvd_mul_left ?_⟩
  rw [← h.value]
  rcases hdiv with hσ | hd
  · exact (hp.dvd_mul.mp (hσ.trans (divisorSum_dvd H h))).resolve_left
      (fun hp2 => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2))
  · exact hd.trans hs


private theorem cutWitness_cover {N m B w seed avoid a L g inv roughInv : ℕ} {s : Node}
    (H : Conditions N B w) (h : Realizes s N m) (hs : seed∣N) (hav : avoid.Coprime N)
    (primes : List ℕ) (hp : ∀ p∈primes,p.Prime)
    (test : s.cutWitness B a L g inv roughInv = true) :
    ∃ p ∈ s.belowPrimes avoid a, p.Prime ∧ p∣m := by
  apply prepareChoices_correct H hs hav primes hp (fun _ => some (.cut a L g)) h
  have hc : avoid.Coprime s.component ∧ avoid.Coprime s.forcedPart :=
    ⟨hav.coprime_dvd_right (h.value ▸ Nat.dvd_mul_right _ _),
     hav.coprime_dvd_right ((forcedPart_dvd h H.perfect).trans (h.value ▸ Nat.dvd_mul_left _ _))⟩
  simp [prepareChoices,hc,Node.cutWitness_valid test]

@[expose] def enumerateArithmetic (B w : ℕ) (s : Node) (path : List (ℕ × ℕ))
    (children : List (ℕ × ArithmeticTree)) (ps : List ℕ)
    (next : List (ℕ × ℕ) → Node → ArithmeticTree → Bool) : Bool :=
  ps.all fun p => (List.range (B-s.spent)).all fun i =>
    let e := i+1
    if s.admissible p e B w then
      next ((p,e)::path) (s.extend p e) ((children.lookup (ps.idxOf p*(B+1)+e)).getD .automatic)
    else true

@[expose] def replayArithmetic (earlier : List Node) (primes : List ℕ) (seed avoid B w c : ℕ) :
    ℕ → List (ℕ × ℕ) → Node → ArithmeticTree → Bool
  | 0, _, _, _ => false
  | fuel+1, path, s, t =>
    match t with
    | .automatic => s.directWitness B w avoid path || earlier.any s.same
    | .groups inv gs => s.groupWitness B w c inv gs
    | .split p children =>
      s.splitWitness primes seed p && enumerateArithmetic B w s path children [p]
        (replayArithmetic earlier primes seed avoid B w c fuel)
    | .cut a L g inv roughInv children =>
      s.cutWitness B a L g inv roughInv && enumerateArithmetic B w s path children (s.belowPrimes avoid a)
        (replayArithmetic earlier primes seed avoid B w c fuel)

/-- The optional initial path and every modular inverse are untrusted input. -/
theorem replayArithmetic_correct_of_offset {N B actual w seed avoid c : ℕ} (H : Conditions N B actual)
    (offset : 2*w + cardFactors N ≤ B + 2*N.primeFactors.card)
    (hs : seed∣N) (hav : avoid.Coprime N) (hc : 18*N.primeFactors.card≤7*B+c)
    (earlier : List Node) (prior : ∀ t∈earlier, ∀ m, Realizes t N m → False)
    (primes : List ℕ) (hp : ∀ p∈primes, p.Prime) (fuel : ℕ) (path : List (ℕ × ℕ))
    {s : Node} {m : ℕ} (h : Realizes s N m) (tree : ArithmeticTree)
    (test : replayArithmetic earlier primes seed avoid B w c fuel path s tree = true) : False := by
  induction fuel generalizing path s m tree with
  | zero => simp [replayArithmetic] at test
  | succ fuel ih =>
    have descend (ps : List ℕ) (children : List (ℕ × ArithmeticTree))
        (cover : ∃ p ∈ ps, p.Prime ∧ p∣m)
        (ok : enumerateArithmetic B w s path children ps
          (replayArithmetic earlier primes seed avoid B w c fuel) = true) : False := by
      obtain ⟨p,hm,hp',hd⟩ := cover
      obtain ⟨he,hmax⟩ := exponent_bounds H h hp' hd
      simp only [enumerateArithmetic,List.all_eq_true,List.mem_range] at ok
      have hv := ok p hm (m.factorization p-1) (by omega)
      rw [Nat.sub_add_cancel he,ite_eq_left (admissible_of_offset H h hp' hd offset)] at hv
      exact ih _ (extend_realizes H.odd.pos.ne' h hp' hd) _ hv
    cases tree with
    | automatic =>
      simp only [replayArithmetic,Bool.or_eq_true,List.any_eq_true] at test
      rcases test with hd | ⟨t, ht, he⟩
      · exact directWitness_false H h hav offset path hd
      · have hst : s=t := by
          cases s
          cases t
          simpa [Node.same] using he
        exact prior t ht m (hst ▸ h)
    | groups inv gs => exact groups_of_offset H h hc offset gs (Node.groupWitness_closes test)
    | split p cs =>
      simp only [replayArithmetic,Bool.and_eq_true] at test
      obtain ⟨hv,hr⟩ := test
      exact descend [p] cs ⟨p, by simp, splitWitness_dvd H h hs primes hp hv⟩ hr
    | cut a L g inv ri cs =>
      simp only [replayArithmetic,Bool.and_eq_true] at test
      obtain ⟨hv,hr⟩ := test
      exact descend _ cs (cutWitness_cover H h hs hav primes hp hv) hr

/-- An ordinary lower bound on support is one way to meet the offset condition. -/
theorem replayArithmetic_correct {N B w seed avoid c : ℕ} (H : Conditions N B w)
    (hs : seed∣N) (hav : avoid.Coprime N) (hc : 18*N.primeFactors.card≤7*B+c)
    (earlier : List Node) (prior : ∀ t∈earlier, ∀ m, Realizes t N m → False)
    (primes : List ℕ) (hp : ∀ p∈primes, p.Prime) (fuel : ℕ) (path : List (ℕ × ℕ))
    {s : Node} {m : ℕ} (h : Realizes s N m) (tree : ArithmeticTree)
    (test : replayArithmetic earlier primes seed avoid B w c fuel path s tree = true) : False := by
  apply replayArithmetic_correct_of_offset H ?_ hs hav hc earlier prior primes hp fuel path h tree test
  have := H.distinct
  have := H.count
  omega

end OddPerfect.FactorBudget
