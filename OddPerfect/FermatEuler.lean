module

public import OddPerfect.ReciprocalValuation
public import OddPerfect.Reciprocity
public import OddPerfect.Primitive
public import OddPerfect.Valuations
import Mathlib.FieldTheory.Finite.Basic

public section

namespace OddPerfect

open Finset ArithmeticFunction

/-- The true prime divisors of N which are one modulo q. -/
def oneModSupport (N q : ℕ) : Finset ℕ := N.primeFactors.filter (fun p => q ∣ p-1)

private theorem cast_eq_one_of_fermat_sigma {p q e k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : q-1 = 2^k) (he : Even e) (hd : q ∣ sigma 1 (p^e)) : (p : ZMod q) = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  by_contra hn
  rw [sigma_one_apply, dvd_sum_divisors_prime_pow_iff hp hq, ite_eq_right hn] at hd
  have hz : (p : ZMod q) ≠ 0 := by
    intro hz
    rw [hz,orderOf_zero,zero_dvd_iff] at hd
    omega
  have hpow := ZMod.orderOf_dvd_card_sub_one hz
  rw [hk] at hpow
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
  have hodd : Odd (e+1) := by obtain ⟨t,ht⟩ := he; exact ⟨t, by omega⟩
  by_cases hj0 : j = 0
  · exact hn (orderOf_eq_one_iff.mp (by simpa [hj0] using hj))
  · exact hodd.not_two_dvd_nat ((dvd_pow_self 2 hj0).trans (hj ▸ hd))

/-- An Euler prime with power-of-two predecessor receives its entire valuation
from the lengths of the components whose bases are one modulo that prime. -/
theorem fermat_euler_valuation_eq_sum {N q k : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hqN : q ∈ N.primeFactors) (ha : Odd (N.factorization q)) (hk : q-1 = 2^k) :
    N.factorization q = ∑ p ∈ oneModSupport N q, (N.factorization p+1).factorization q := by
  have hq := Nat.prime_of_mem_primeFactors hqN
  have hqo := hNo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hqN)
  obtain ⟨u,_,_,_,hrest⟩ := euler_exponents hNo hN
  have hu : q = u := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr ha) (hrest q h)
  subst u
  rw [factorization_eq_sum_sigma_factorizations hN hqo hq,oneModSupport,sum_filter]
  apply sum_congr rfl
  intro p hpN
  have hp := Nat.prime_of_mem_primeFactors hpN
  split_ifs with hpq
  · exact sigma_factorization_of_dvd_pred hq hqo hp hpq
  · apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    by_cases heq : p = q
    · subst p
      have h1 := sigma_prime_pow_mod_self hq (N.factorization q)
      rw [Nat.mod_eq_zero_of_dvd hd] at h1
      contradiction
    · have hcast := cast_eq_one_of_fermat_sigma hp hq hk (hrest p heq) hd
      have hcon := (ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hcast)
      exact hpq ((Nat.modEq_iff_dvd' hp.one_lt.le).mp hcon.symm)

/-- Each power of q in the component length needs a distinct actual divisor-sum
edge from p into the primes one modulo q. -/
theorem length_valuation_le_oneModEdges {N q p : ℕ} (hN : N.Perfect) (hq : q.Prime) (hqo : Odd q)
    (hpN : p ∈ N.primeFactors) :
    (N.factorization p+1).factorization q ≤ (((oneModSupport N q).erase p).filter
      (fun r => r ∣ sigma 1 (p^N.factorization p))).card := by
  classical
  let e := N.factorization p
  let dest := ((oneModSupport N q).erase p).filter (fun r => r ∣ sigma 1 (p^e))
  let orders := dest.image (fun r => orderOf (p : ZMod r))
  let hp := Nat.prime_of_mem_primeFactors hpN
  have hcount : (range ((e+1).factorization q)).card ≤ orders.card := by
    apply card_le_card_of_injOn (fun j : ℕ => q^(j+1))
    · intro j hj
      have hlen := (hq.pow_dvd_iff_le_factorization (Nat.succ_ne_zero e)).mpr
        (mem_range.mp hj : j+1 ≤ (e+1).factorization q)
      obtain ⟨r,hrN,hrp,hor,hd⟩ := exists_forced_prime_order_prime_pow hN hp rfl hq hqo j hlen
      have hz : (p : ZMod r) ≠ 1 := by
        intro h
        have hgt := one_lt_pow₀ hq.one_lt (by omega : j+1 ≠ 0)
        simp [h] at hor
        omega
      have he : r ∣ sigma 1 (p^e) := by
        rw [sigma_one_apply,dvd_sum_divisors_prime_pow_iff hp (Nat.prime_of_mem_primeFactors hrN),ite_eq_right hz,hor]
        exact hlen
      exact mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_erase.mpr ⟨hrp,mem_filter.mpr
        ⟨hrN,(dvd_pow_self q (by omega : j+1 ≠ 0)).trans hd⟩⟩,he⟩,hor⟩
    · intro i _ j _ heq
      exact Nat.succ.inj ((pow_right_injective₀ hq.pos hq.ne_one) heq)
  simpa [orders, dest, e] using hcount.trans card_image_le

/-- The loopless divisor-sum graph induced by a set of primes. -/
noncomputable def inducedSigmaEdges (N : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact S.offDiag.filter (fun z => sigmaEdge N z.1 z.2)

/-- The Fermat Euler exponent counts at most the actual edges amongst the
one-modulo-q prime factors, with each ordered pair counted just once. -/
theorem fermat_euler_valuation_le_edges {N q k : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hqN : q ∈ N.primeFactors) (ha : Odd (N.factorization q)) (hk : q-1 = 2^k) :
    N.factorization q ≤ (inducedSigmaEdges N (oneModSupport N q)).card := by
  classical
  let S := oneModSupport N q
  let E := inducedSigmaEdges N S
  have hq := Nat.prime_of_mem_primeFactors hqN
  have hqo := hNo.of_dvd_nat (Nat.dvd_of_mem_primeFactors hqN)
  have hsub : S ⊆ N.primeFactors := filter_subset _ _
  have hrow (p : ℕ) (hp : p ∈ S) :
      (N.factorization p+1).factorization q ≤ (E.filter (fun z => z.1 = p)).card := by
    apply (length_valuation_le_oneModEdges hN hq hqo (hsub hp)).trans
    apply card_le_card_of_injOn (fun r : ℕ => (p,r))
    · intro r hr
      obtain ⟨hrm, hdiv⟩ := mem_filter.mp hr
      obtain ⟨hrp, hrs⟩ := mem_erase.mp hrm
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_offDiag.mpr ⟨hp,hrs,Ne.symm hrp⟩,hsub hp,hsub hrs,hdiv⟩,rfl⟩
    · intro i _ j _ h
      exact Prod.mk.inj h |>.2
  have hcover : E.filter (fun z => z.1 ∈ S) = E := filter_eq_self.mpr
    (fun _ hm => (mem_offDiag.mp (mem_filter.mp hm).1).1)
  rw [fermat_euler_valuation_eq_sum hN hNo hqN ha hk]
  exact (sum_le_sum hrow).trans_eq ((sum_card_fiberwise_eq_card_filter E S Prod.fst).trans (congrArg card hcover))

private theorem offDiag_card_mul_pred (S : Finset ℕ) : S.offDiag.card = S.card*(S.card-1) := by
  rw [offDiag_card,Nat.mul_sub,Nat.mul_one]

/-- Quadratic reciprocity removes at least half of the off-diagonal ordered pairs
whose two endpoints are both three modulo four. -/
theorem two_induced_edges_add_three_pairs_le {N : ℕ} (hN : N.Perfect) (hNo : Odd N) (S : Finset ℕ) :
    2 * (inducedSigmaEdges N S).card +
      (S.filter (fun p => p%4=3)).card * ((S.filter (fun p => p%4=3)).card-1) ≤
    2 * (S.card * (S.card-1)) := by
  classical
  let E := inducedSigmaEdges N S
  let T := S.filter (fun p => p%4=3)
  let C := T.offDiag
  let U := S.offDiag
  have hCU : C ⊆ U := offDiag_mono (filter_subset _ _)
  have hEU : E ⊆ U := filter_subset _ _
  have hswap : (C ∩ E).card ≤ (C \ E).card := by
    apply card_le_card_of_injOn Prod.swap
    · rintro ⟨p,r⟩ hm
      obtain ⟨hC,hE⟩ := mem_inter.mp hm
      obtain ⟨hp,hr,hne⟩ := mem_offDiag.mp hC
      exact mem_sdiff.mpr ⟨mem_offDiag.mpr ⟨hr,hp,Ne.symm hne⟩, fun rev =>
        not_sigmaEdge_reverse_of_three_mod_four hN hNo (mem_filter.mp hE).2 hne
          (mem_filter.mp hp).2 (mem_filter.mp hr).2 (mem_filter.mp rev).2⟩
    · exact Prod.swap_injective.injOn
  have hcc := card_sdiff_add_card_inter C E
  have hU := card_sdiff_of_subset hEU
  have hE := card_le_card hEU
  have hh : (C \ E).card ≤ (U \ E).card := card_le_card (fun _ h =>
    mem_sdiff.mpr ⟨hCU (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)
  change 2*E.card + T.card*(T.card-1) ≤ 2*(S.card*(S.card-1))
  rw [←offDiag_card_mul_pred,←offDiag_card_mul_pred]
  change 2*E.card + C.card ≤ 2*U.card
  omega

/-- For a Fermat Euler prime q, write h for the number of prime factors one
modulo q and t for those also three modulo four. Then 2a+t(t-1) ≤ 2h(h-1). -/
theorem fermat_euler_exponent_count_bound {N q k : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hqN : q ∈ N.primeFactors) (ha : Odd (N.factorization q)) (hk : q-1 = 2^k) :
    let S := oneModSupport N q
    let t := (S.filter (fun p => p%4=3)).card
    2*N.factorization q + t*(t-1) ≤ 2*(S.card*(S.card-1)) := by
  dsimp only
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (fermat_euler_valuation_le_edges hN hNo hqN ha hk)) _).trans
    (two_induced_edges_add_three_pairs_le hN hNo _)

/-- An Euler exponent of at least five forces three different primes one modulo
the Fermat Euler prime. If every such prime is three modulo four, it forces four. -/
theorem three_le_fermat_euler_support {N q k : ℕ} (hN : N.Perfect) (hNo : Odd N)
    (hqN : q ∈ N.primeFactors) (ha : Odd (N.factorization q)) (hk : q-1 = 2^k)
    (h5 : 5 ≤ N.factorization q) :
    3 ≤ (oneModSupport N q).card ∧
    ((∀ p ∈ oneModSupport N q, p%4=3) → 4 ≤ (oneModSupport N q).card) := by
  let S := oneModSupport N q
  let t := (S.filter (fun p => p%4=3)).card
  have h : 2*N.factorization q + t*(t-1) ≤ 2*(S.card*(S.card-1)) :=
    fermat_euler_exponent_count_bound hN hNo hqN ha hk
  constructor
  · change 3 ≤ S.card
    by_contra! hn
    have hcap : S.card*(S.card-1) ≤ 2*1 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · intro hall
    change 4 ≤ S.card
    have ht : t=S.card := congrArg card (filter_eq_self.mpr hall)
    rw [ht] at h
    by_contra! hn
    have hcap : S.card*(S.card-1) ≤ 3*2 := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- Both orientations can occur with actual length five, even when the bases
are themselves one modulo five. These identities use only the local factors. -/
theorem five_order_reciprocal_local_example :
    61%5=1 ∧ 131%5=1 ∧ 61 ∣ sigma 1 (131^4) ∧ 131 ∣ sigma 1 (61^4) := by
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 131),sigma_one_apply_prime_pow (by decide : Nat.Prime 61)]
  norm_num [sum_range_succ]

end OddPerfect
