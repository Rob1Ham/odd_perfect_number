module

public import OddPerfect.CyclotomicOrders
public import OddPerfect.SixthPowerFreeEuler
public import OddPerfect.OddValuationCycleObstruction
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cyclotomic Factorization Supply over Finite Fields and Odd Perfect Numbers

Connects `Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization` and
`Mathlib.NumberTheory.PrimesCongruentOne` to `OddPerfect`:

1. `zmod_cyclotomic_irreducible_degree_and_factor_card`: Over `ZMod p` with `p.Coprime n`,
   every irreducible factor of `cyclotomic n (ZMod p)` has degree `orderOf (ZMod.unitOfCoprime p hcop)`,
   the number of distinct normalized irreducible factors is `n.totient / orderOf u`, and
   `orderOf u ∣ n.totient`.
2. `zmod_cyclotomic_splits_linear_iff_modEq_one` and
   `zmod_cyclotomic_irreducible_iff_orderOf_eq_totient`: Complete linear splitting occurs iff
   `p ≡ 1 [MOD n]`, and irreducibility of `cyclotomic n (ZMod p)` occurs iff
   `orderOf (ZMod.unitOfCoprime p hcop) = n.totient`.
3. `exists_arbitrarily_large_prime_splitting_cyclotomic`: For every `n ≥ 1` and `M`, there exists
   a prime `p > M` with `p ≡ 1 [MOD n]` over which `cyclotomic n (ZMod p)` splits into `n.totient`
   linear factors.
4. `cyclotomic_dual_splitting_of_dvd_eval_cyclotomic`,
   `odd_perfect_component_cyclotomic_dual_splitting`, and
   `odd_perfect_component_cyclotomic_factor_count_and_sixth_power_free_order`:
   Dual cyclotomic reciprocity between `cyclotomic d (ZMod r)` (splitting into `d.totient` linear
   factors) and `cyclotomic r (ZMod p)` (splitting into `(r - 1) / d` irreducible factors of
   degree `d`), specialized to odd perfect number components and sixth-power-free `S₅₁` (`d = 3`)
   and `Q₁₃` (`d = 5`) components.
-/

public section

namespace OddPerfect

open Polynomial Finset ArithmeticFunction

private lemma neZero_of_prime_coprime {p n : ℕ} [hp : Fact p.Prime] (hcop : p.Coprime n) :
    NeZero n := by
  refine ⟨fun hn0 => ?_⟩
  subst hn0
  exact hp.out.ne_one (by simpa using hcop)

private lemma coprime_of_modEq_one {p n : ℕ} (hmod : p ≡ 1 [MOD n]) : p.Coprime n := by
  refine Nat.coprime_of_dvd fun k hk hkp hkn => ?_
  have h1 : 1 % k = 0 := by
    calc
      1 % k = (1 % n) % k := (Nat.mod_mod_of_dvd 1 hkn).symm
      _ = (p % n) % k := by rw [hmod]
      _ = p % k := Nat.mod_mod_of_dvd p hkn
      _ = 0 := Nat.mod_eq_zero_of_dvd hkp
  exact hk.ne_one (Nat.dvd_one.mp (Nat.dvd_of_mod_eq_zero h1))

private lemma modEq_one_of_dvd_sub_one {r d : ℕ} (hr : r.Prime) (hd : d ∣ r - 1) :
    r ≡ 1 [MOD d] :=
  ((Nat.modEq_iff_dvd' hr.pos).2 hd).symm

/-- Over `ZMod p` with `p.Prime` and `p.Coprime n`, every irreducible factor of
`cyclotomic n (ZMod p)` has degree `orderOf (ZMod.unitOfCoprime p hcop)`, the count of distinct
normalized irreducible factors is `n.totient / orderOf u`, and `orderOf u ∣ n.totient`. -/
theorem zmod_cyclotomic_irreducible_degree_and_factor_card {p n : ℕ} [Fact p.Prime]
    (hcop : p.Coprime n) :
    (∀ P : (ZMod p)[X], P ∣ cyclotomic n (ZMod p) → Irreducible P →
      P.natDegree = orderOf (ZMod.unitOfCoprime p hcop)) ∧
    (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
      n.totient / orderOf (ZMod.unitOfCoprime p hcop) ∧
    orderOf (ZMod.unitOfCoprime p hcop) ∣ n.totient ∧
    orderOf (ZMod.unitOfCoprime p hcop) *
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
        n.totient := by
  classical
  have : NeZero n := neZero_of_prime_coprime hcop
  have hK : Fintype.card (ZMod p) = p ^ 1 := by simp [ZMod.card]
  have hdeg : ∀ P : (ZMod p)[X], P ∣ cyclotomic n (ZMod p) → Irreducible P →
      P.natDegree = orderOf (ZMod.unitOfCoprime p hcop) := by
    intro P hP hPirr
    simpa using Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (f := 1) hK hcop hP hPirr
  have hcard :
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
        n.totient / orderOf (ZMod.unitOfCoprime p hcop) := by
    simpa using Polynomial.normalizedFactors_cyclotomic_card (K := ZMod p) (f := 1) hK hcop
  have hdvd : orderOf (ZMod.unitOfCoprime p hcop) ∣ n.totient := by
    simpa [ZMod.card_units_eq_totient] using
      orderOf_dvd_card (x := ZMod.unitOfCoprime p hcop)
  have hmul :
      orderOf (ZMod.unitOfCoprime p hcop) *
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
          n.totient := by
    rw [hcard, Nat.mul_div_cancel' hdvd]
  exact ⟨hdeg, hcard, hdvd, hmul⟩

/-- Over `ZMod p` with `1 ≤ n` and `p.Coprime n`, `orderOf (ZMod.unitOfCoprime p hcop) = 1` iff
`p ≡ 1 [MOD n]`, in which case `cyclotomic n (ZMod p)` splits into `n.totient` distinct monic
linear factors. -/
theorem zmod_cyclotomic_splits_linear_iff_modEq_one {p n : ℕ} [Fact p.Prime]
    (_hn : 1 ≤ n) (hcop : p.Coprime n) :
    (orderOf (ZMod.unitOfCoprime p hcop) = 1 ↔ p ≡ 1 [MOD n]) ∧
    (p ≡ 1 [MOD n] →
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
        n.totient ∧
      (∀ P : (ZMod p)[X], P ∣ cyclotomic n (ZMod p) → Irreducible P → P.natDegree = 1) ∧
      (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p)),
        P.natDegree = 1 ∧ P.Monic)) := by
  classical
  have hiff : orderOf (ZMod.unitOfCoprime p hcop) = 1 ↔ p ≡ 1 [MOD n] := by
    rw [orderOf_eq_one_iff, Units.ext_iff, Units.val_one, ZMod.coe_unitOfCoprime,
      ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  refine ⟨hiff, fun hmod => ?_⟩
  have hord : orderOf (ZMod.unitOfCoprime p hcop) = 1 := hiff.mpr hmod
  obtain ⟨hdeg, hcard, _, _⟩ := zmod_cyclotomic_irreducible_degree_and_factor_card hcop
  have hcard1 :
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
        n.totient := by
    simpa [hord] using hcard
  have hdeg1 : ∀ P : (ZMod p)[X], P ∣ cyclotomic n (ZMod p) → Irreducible P → P.natDegree = 1 := by
    intro P hP hPirr
    simpa [hord] using hdeg P hP hPirr
  have hmem1 :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p)),
        P.natDegree = 1 ∧ P.Monic := by
    intro P hP
    have hP' := (Polynomial.mem_normalizedFactors_iff (cyclotomic_ne_zero n (ZMod p))).mp hP
    exact ⟨hdeg1 P hP'.2.2 hP'.1, hP'.2.1⟩
  exact ⟨hcard1, hdeg1, hmem1⟩

/-- Over `ZMod p` with `1 ≤ n` and `p.Coprime n`, `cyclotomic n (ZMod p)` is irreducible iff
`p` generates `(ZMod n)ˣ` up to order `n.totient`. -/
theorem zmod_cyclotomic_irreducible_iff_orderOf_eq_totient {p n : ℕ} [hp : Fact p.Prime]
    (_hn : 1 ≤ n) (hcop : p.Coprime n) :
    Irreducible (cyclotomic n (ZMod p)) ↔ orderOf (ZMod.unitOfCoprime p hcop) = n.totient := by
  constructor
  · intro hirr
    have hdeg :=
      (zmod_cyclotomic_irreducible_degree_and_factor_card hcop).1 _ (dvd_refl _) hirr
    simpa [Polynomial.natDegree_cyclotomic] using hdeg.symm
  · intro hord
    have hpn : ¬ p ∣ n := hp.out.coprime_iff_not_dvd.mp hcop
    refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hpn (dvd_refl _) ?_
    rw [Polynomial.natDegree_cyclotomic]
    simpa using hord.symm

/-- For every `n ≥ 1` and threshold `M`, there exists a prime `p > M` with `p ≡ 1 [MOD n]` and
`p.Coprime n` such that `cyclotomic n (ZMod p)` splits completely into `n.totient` linear factors
over `ZMod p`. -/
theorem exists_arbitrarily_large_prime_splitting_cyclotomic {n M : ℕ} (hn : 1 ≤ n) :
    ∃ p : ℕ, ∃ hp : p.Prime, M < p ∧ p ≡ 1 [MOD n] ∧ p.Coprime n ∧
      letI : Fact p.Prime := ⟨hp⟩
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p))).toFinset.card =
        n.totient ∧
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic n (ZMod p)),
        P.natDegree = 1 := by
  classical
  obtain ⟨p, hp, hMp, hmod⟩ := Nat.exists_prime_gt_modEq_one M (by omega : n ≠ 0)
  have hcop : p.Coprime n := coprime_of_modEq_one hmod
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcard, _, hmem⟩ :=
    (zmod_cyclotomic_splits_linear_iff_modEq_one (p := p) (n := n) hn hcop).2 hmod
  exact ⟨p, hp, hMp, hmod, hcop, hcard, fun P hP => (hmem P hP).1⟩

/-- **Dual Cyclotomic Reciprocity**: If `p` and `r` are primes, `2 ≤ d`, `¬ r ∣ d`, and
`(r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ)`, then:
1. `p ≠ r`, `p.Coprime r`, `r.Coprime d`, `orderOf (p : ZMod r) = d`, `d ∣ r - 1`, and
   `r ≡ 1 [MOD d]`.
2. Over `ZMod r`, `(p : ZMod r)` is a root of `cyclotomic d (ZMod r)` and `cyclotomic d (ZMod r)`
   splits completely into `d.totient` distinct monic linear factors.
3. Over `ZMod p`, `cyclotomic r (ZMod p)` factors into `(r - 1) / d` distinct monic irreducible
   polynomials, each of degree `d`. -/
theorem cyclotomic_dual_splitting_of_dvd_eval_cyclotomic {p r d : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hd : 2 ≤ d) (hnd : ¬ r ∣ d)
    (hdvd : (r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ)) :
    p ≠ r ∧ p.Coprime r ∧ r.Coprime d ∧
    orderOf (p : ZMod r) = d ∧ d ∣ r - 1 ∧ r ≡ 1 [MOD d] ∧
    (letI : Fact r.Prime := ⟨hr⟩;
      IsRoot (cyclotomic d (ZMod r)) (p : ZMod r) ∧
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic d (ZMod r))).toFinset.card =
        d.totient ∧
      (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic d (ZMod r)),
        P.natDegree = 1 ∧ P.Monic)) ∧
    (letI : Fact p.Prime := ⟨hp⟩;
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
        (r - 1) / d ∧
      d * (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
        r - 1 ∧
      (∀ P : (ZMod p)[X], P ∣ cyclotomic r (ZMod p) → Irreducible P → P.natDegree = d) ∧
      (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
        P.natDegree = d ∧ P.Monic)) := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  have hroot : IsRoot (cyclotomic d (ZMod r)) (p : ZMod r) := by
    rw [IsRoot.def, ← map_cyclotomic_int, eval_map, ← Int.cast_natCast]
    change eval₂ (Int.castRingHom (ZMod r)) ((Int.castRingHom (ZMod r)) (p : ℤ)) _ = 0
    rw [eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  have hroot_hom : IsRoot (cyclotomic d (ZMod r)) (Nat.castRingHom (ZMod r) p) := by
    simpa using hroot
  have hpr : p.Coprime r := coprime_of_root_cyclotomic hroot_hom
  have hpner : p ≠ r := by
    rintro rfl
    exact hp.ne_one (by simpa using hpr)
  have hrd : r.Coprime d := hr.coprime_iff_not_dvd.mpr hnd
  have : NeZero (d : ZMod r) := NeZero.of_not_dvd (ZMod r) hnd
  have hord_val : orderOf (p : ZMod r) = d :=
    (isRoot_cyclotomic_iff.mp hroot).eq_orderOf.symm
  have hord_unit : orderOf (ZMod.unitOfCoprime p hpr) = d := by
    rw [← orderOf_units, ZMod.coe_unitOfCoprime, hord_val]
  have hdvd_sub : d ∣ r - 1 := by
    simpa [hord_unit] using ZMod.orderOf_units_dvd_card_sub_one (ZMod.unitOfCoprime p hpr)
  have hmod_r : r ≡ 1 [MOD d] := modEq_one_of_dvd_sub_one hr hdvd_sub
  obtain ⟨hcard_r, _, hmem_r⟩ :=
    (zmod_cyclotomic_splits_linear_iff_modEq_one (p := r) (n := d) (by omega) hrd).2 hmod_r
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hdeg_p, hcard_p, _, hmul_p⟩ :=
    zmod_cyclotomic_irreducible_degree_and_factor_card (p := p) (n := r) hpr
  have htot_r : r.totient = r - 1 := Nat.totient_prime hr
  have hcard_p' :
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
        (r - 1) / d := by
    simpa [hord_unit, htot_r] using hcard_p
  have hmul_p' :
      d * (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
        r - 1 := by
    simpa [hord_unit, htot_r] using hmul_p
  have hdeg_p' : ∀ P : (ZMod p)[X], P ∣ cyclotomic r (ZMod p) → Irreducible P → P.natDegree = d := by
    intro P hP hPirr
    simpa [hord_unit] using hdeg_p P hP hPirr
  have hmem_p' :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
        P.natDegree = d ∧ P.Monic := by
    intro P hP
    have hP' := (Polynomial.mem_normalizedFactors_iff (cyclotomic_ne_zero r (ZMod p))).mp hP
    exact ⟨hdeg_p' P hP'.2.2 hP'.1, hP'.2.1⟩
  exact ⟨hpner, hpr, hrd, hord_val, hdvd_sub, hmod_r,
    ⟨hroot, hcard_r, hmem_r⟩, ⟨hcard_p', hmul_p', hdeg_p', hmem_p'⟩⟩

private lemma odd_and_dvd_sigma_of_dvd_eval_cyclotomic {p e d r : ℕ}
    (hp : p.Prime) (hp_odd : Odd p) (hd : 1 < d) (hlen : d ∣ e + 1)
    (hr : r.Prime) (hnd : ¬ r ∣ d)
    (hdvd : (r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ)) :
    Odd r ∧ r ∣ sigma 1 (p ^ e) := by
  have hdual := cyclotomic_dual_splitting_of_dvd_eval_cyclotomic hp hr hd hnd hdvd
  have hord : orderOf (p : ZMod r) = d := hdual.2.2.2.1
  have hr_odd : Odd r := by
    apply hr.odd_of_ne_two
    rintro rfl
    have hp2 : (p : ZMod 2) = 1 := by
      have hp_mod : p % 2 = 1 := Nat.odd_iff.mp hp_odd
      rw [← ZMod.natCast_mod p 2, hp_mod]
      norm_num
    rw [hp2, orderOf_one] at hord
    omega
  obtain ⟨k, hk⟩ := hlen
  have hdvd_pow : (r : ℤ) ∣ (p : ℤ) ^ (e + 1) - 1 := by
    have hcyc_dvd : cyclotomic d ℤ ∣ X ^ d - 1 := cyclotomic.dvd_X_pow_sub_one d ℤ
    have heval_dvd : eval (p : ℤ) (cyclotomic d ℤ) ∣ (p : ℤ) ^ d - 1 := by
      simpa using Polynomial.eval_dvd (x := (p : ℤ)) hcyc_dvd
    have hpow_dvd : (p : ℤ) ^ d - 1 ∣ (p : ℤ) ^ (e + 1) - 1 := by
      rw [hk, pow_mul]
      simpa using sub_dvd_pow_sub_pow ((p : ℤ) ^ d) 1 k
    exact hdvd.trans (heval_dvd.trans hpow_dvd)
  have hgeom : (p : ℤ) ^ (e + 1) - 1 = ((p : ℤ) - 1) * (sigma 1 (p ^ e) : ℤ) := by
    rw [sigma_one_apply_prime_pow hp, Nat.cast_sum]
    simp only [Nat.cast_pow]
    rw [mul_comm, geom_sum_mul]
  rw [hgeom] at hdvd_pow
  rcases Int.Prime.dvd_mul' hr hdvd_pow with hpm1 | hsig
  · exfalso
    have hp_eq : (p : ZMod r) = 1 := by
      rw [← sub_eq_zero, ← Int.cast_natCast, ← Int.cast_one, ← Int.cast_sub,
        ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hpm1
    rw [hp_eq, orderOf_one] at hord
    omega
  · exact ⟨hr_odd, Int.ofNat_dvd.mp hsig⟩

/-- For any odd perfect number `N`, prime `p ∈ N.primeFactors`, divisor `d ∣ N.factorization p + 1`
with `1 < d`, and prime `r` with `¬ r ∣ d` and `(r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ)`:
- `r` is automatically odd and lies in `N.primeFactors` with `p ≠ r`;
- `r ≡ 1 [MOD d]` and `cyclotomic d (ZMod r)` splits into `d.totient` linear factors over `ZMod r`;
- `cyclotomic r (ZMod p)` factors into `(r - 1) / d` monic irreducible factors of degree `d` over
  `ZMod p`. -/
theorem odd_perfect_component_cyclotomic_dual_splitting {N p d r : ℕ}
    (ho : Odd N) (hN : N.Perfect) (hp : p ∈ N.primeFactors)
    (hd : 1 < d) (hlen : d ∣ N.factorization p + 1)
    (hr : r.Prime) (hnd : ¬ r ∣ d)
    (hdvd : (r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ)) :
    Odd r ∧ r ∈ N.primeFactors ∧ p ≠ r ∧ p.Coprime r ∧ r.Coprime d ∧
    orderOf (p : ZMod r) = d ∧ d ∣ r - 1 ∧ r ≡ 1 [MOD d] ∧
    (letI : Fact r.Prime := ⟨hr⟩;
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic d (ZMod r))).toFinset.card =
        d.totient ∧
      (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic d (ZMod r)),
        P.natDegree = 1 ∧ P.Monic)) ∧
    (letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩;
      (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
        (r - 1) / d ∧
      d * (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
        r - 1 ∧
      (∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
        P.natDegree = d ∧ P.Monic)) := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨hr_odd, hr_sig⟩ :=
    odd_and_dvd_sigma_of_dvd_eval_cyclotomic hp_prime hp_odd hd hlen hr hnd hdvd
  have hr_dvd_N : r ∣ N := by
    apply dvd_perfect_of_exact_prime_pow hN hp_prime (Nat.ordProj_dvd N p)
      ((hp_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)) hr hr_odd
    rwa [← sigma_one_apply]
  have hr_mem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hr_dvd_N, hN.2.ne'⟩
  have hdual := cyclotomic_dual_splitting_of_dvd_eval_cyclotomic hp_prime hr hd hnd hdvd
  exact ⟨hr_odd, hr_mem, hdual.1, hdual.2.1, hdual.2.2.1, hdual.2.2.2.1, hdual.2.2.2.2.1,
    hdual.2.2.2.2.2.1, ⟨hdual.2.2.2.2.2.2.1.2.1, hdual.2.2.2.2.2.2.1.2.2⟩,
    ⟨hdual.2.2.2.2.2.2.2.1, hdual.2.2.2.2.2.2.2.2.1, hdual.2.2.2.2.2.2.2.2.2.2⟩⟩

private lemma eval_cyclotomic_three_int (p : ℕ) :
    eval (p : ℤ) (cyclotomic 3 ℤ) = (p : ℤ) ^ 2 + p + 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [cyclotomic_prime ℤ 3]
  simp [Finset.sum_range_succ]
  ring

private lemma eval_cyclotomic_five_int (p : ℕ) :
    eval (p : ℤ) (cyclotomic 5 ℤ) = (p : ℤ) ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [cyclotomic_prime ℤ 5]
  simp [Finset.sum_range_succ]
  ring

private lemma sigma_one_sq_eq {p : ℕ} (hp : p.Prime) : sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

private lemma sigma_one_four_eq {p : ℕ} (hp : p.Prime) :
    sigma 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

/-- Combines the general odd-perfect component cyclotomic reciprocity theorem with its
sixth-power-free specialization on `S₅₁` (`d = 3`) and `Q₁₃` (`d = 5`):
- For `p ∈ S₅₁` and every prime `r ∣ sigma 1 (p ^ 2)`, automatically `r ∈ N.primeFactors`,
  `53 ≤ r`, `r ≠ 3`, `p ≠ r`, `r ≡ 1 [MOD 3]`, `cyclotomic 3 (ZMod r)` splits into `2` linear
  factors over `ZMod r`, and `cyclotomic r (ZMod p)` factors into `(r - 1) / 3` cubic
  irreducibles over `ZMod p`.
- For `p ∈ Q₁₃` and every prime `r ∣ sigma 1 (p ^ 4)`, automatically `r ∈ N.primeFactors`,
  `53 ≤ r`, `r ≠ 5`, `p ≠ r`, `r ≡ 1 [MOD 5]`, `cyclotomic 5 (ZMod r)` splits into `4` linear
  factors over `ZMod r`, and `cyclotomic r (ZMod p)` factors into `(r - 1) / 5` quintic
  irreducibles over `ZMod p`. -/
theorem odd_perfect_component_cyclotomic_factor_count_and_sixth_power_free_order {N q : ℕ}
    (ho : Odd N) (hN : N.Perfect)
    (hq : q ∈ N.primeFactors) (hq4 : q % 4 = 1) (he : N.factorization q % 4 = 1)
    (hev : ∀ r : ℕ, r ≠ q → Even (N.factorization r))
    (hfree : ∀ p : ℕ, p.Prime → ¬ p ^ 6 ∣ N) :
    let S₅₁ := (squareSources N).filter (· % 5 = 1)
    let Q₁₃ := oneModThreeLargeSources N q
    (∀ (p : ℕ) (hp : p ∈ N.primeFactors), ∀ d : ℕ, 1 < d → d ∣ N.factorization p + 1 →
      ∀ (r : ℕ) (hr : r.Prime), ¬ r ∣ d → (r : ℤ) ∣ eval (p : ℤ) (cyclotomic d ℤ) →
      r ∈ N.primeFactors ∧ 53 ≤ r ∧ p ≠ r ∧ r ≡ 1 [MOD d] ∧ orderOf (p : ZMod r) = d ∧
      (letI : Fact r.Prime := ⟨hr⟩;
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic d (ZMod r))).toFinset.card =
          d.totient) ∧
      (letI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩;
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
          (r - 1) / d ∧
        ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
          P.natDegree = d ∧ P.Monic)) ∧
    (∀ (p : ℕ) (hp : p ∈ S₅₁), ∀ (r : ℕ) (hr : r.Prime), r ∣ sigma 1 (p ^ 2) →
      r ∈ N.primeFactors ∧ 53 ≤ r ∧ r ≠ 3 ∧ p ≠ r ∧ r ≡ 1 [MOD 3] ∧
      orderOf (p : ZMod r) = 3 ∧
      (letI : Fact r.Prime := ⟨hr⟩;
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic 3 (ZMod r))).toFinset.card = 2 ∧
        ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic 3 (ZMod r)),
          P.natDegree = 1 ∧ P.Monic) ∧
      (letI : Fact p.Prime :=
          ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1⟩;
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
          (r - 1) / 3 ∧
        3 * (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
          r - 1 ∧
        ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
          P.natDegree = 3 ∧ P.Monic)) ∧
    (∀ (p : ℕ) (hp : p ∈ Q₁₃), ∀ (r : ℕ) (hr : r.Prime), r ∣ sigma 1 (p ^ 4) →
      r ∈ N.primeFactors ∧ 53 ≤ r ∧ r ≠ 5 ∧ p ≠ r ∧ r ≡ 1 [MOD 5] ∧
      orderOf (p : ZMod r) = 5 ∧
      (letI : Fact r.Prime := ⟨hr⟩;
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic 5 (ZMod r))).toFinset.card = 4 ∧
        ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic 5 (ZMod r)),
          P.natDegree = 1 ∧ P.Monic) ∧
      (letI : Fact p.Prime :=
          ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1⟩;
        (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
          (r - 1) / 5 ∧
        5 * (UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p))).toFinset.card =
          r - 1 ∧
        ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors (cyclotomic r (ZMod p)),
          P.natDegree = 5 ∧ P.Monic)) := by
  intro S₅₁ Q₁₃
  have h3 : ¬ 3 ∣ N := sixth_power_free_three_not_dvd ho hN hfree
  have hfour := (three_free_sixthPowerFree_forces_147_largeSources ho hN hq hq4 he hev h3 hfree).1
  refine ⟨?_, ?_, ?_⟩
  · intro p hp d hd hlen r hr hnd hdvd
    obtain ⟨_, hr_mem, hpner, _, _, hord, _, hmod, hZMod_r, hZMod_p⟩ :=
      odd_perfect_component_cyclotomic_dual_splitting ho hN hp hd hlen hr hnd hdvd
    have hr53 : 53 ≤ r := sixth_power_free_min_prime_ge_53 ho hN hfree hr_mem
    exact ⟨hr_mem, hr53, hpner, hmod, hord, hZMod_r.1, hZMod_p.1, hZMod_p.2.2⟩
  · intro p hp r hr hrsig
    have hp_sq := (Finset.mem_filter.mp hp).1
    obtain ⟨hp_mem, _, hp_exp⟩ := Finset.mem_filter.mp hp_sq
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
    rw [sigma_one_sq_eq hp_prime] at hrsig
    have hr_odd : Odd r := by
      apply hr.odd_of_ne_two
      rintro rfl
      have hmod2 : (p ^ 2 + p + 1) % 2 = 1 := by
        have hp2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
        have h1 : p ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hp2]
        omega
      have hdvd2 : (p ^ 2 + p + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hrsig
      omega
    have hr_dvd_N : r ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hp_prime (Nat.ordProj_dvd N p)
        ((hp_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)) hr hr_odd
      rw [← sigma_one_apply, hp_exp, sigma_one_sq_eq hp_prime]
      exact hrsig
    have hr_mem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hr_dvd_N, hN.2.ne'⟩
    have hr53 : 53 ≤ r := sixth_power_free_min_prime_ge_53 ho hN hfree hr_mem
    have hr_ne3 : r ≠ 3 := by omega
    have hnd3 : ¬ r ∣ 3 := fun hd3 => hr_ne3 (by have := Nat.le_of_dvd (by decide) hd3; omega)
    have hdvd3 : (r : ℤ) ∣ eval (p : ℤ) (cyclotomic 3 ℤ) := by
      rw [eval_cyclotomic_three_int]
      exact_mod_cast hrsig
    obtain ⟨hpner, _, _, hord, _, hmod, ⟨_, hcard_r, hmem_r⟩, ⟨hcard_p, hmul_p, _, hmem_p⟩⟩ :=
      cyclotomic_dual_splitting_of_dvd_eval_cyclotomic hp_prime hr (by decide) hnd3 hdvd3
    have htot3 : Nat.totient 3 = 2 := by decide
    rw [htot3] at hcard_r
    exact ⟨hr_mem, hr53, hr_ne3, hpner, hmod, hord, ⟨hcard_r, hmem_r⟩, ⟨hcard_p, hmul_p, hmem_p⟩⟩
  · intro p hp r hr hrsig
    have hp_lg := (Finset.mem_filter.mp hp).1
    have hp_mem := (Finset.mem_filter.mp hp_lg).1
    have hp_exp : N.factorization p = 4 := hfour p hp_lg
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hp_odd : Odd p := ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp_mem)
    rw [sigma_one_four_eq hp_prime] at hrsig
    have hr_odd : Odd r := by
      apply hr.odd_of_ne_two
      rintro rfl
      have hmod2 : (p ^ 4 + p ^ 3 + p ^ 2 + p + 1) % 2 = 1 := by
        have hp2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
        have h1 : p ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hp2]
        have h3 : p ^ 3 % 2 = 1 := by simp [Nat.pow_mod, hp2]
        have h4 : p ^ 4 % 2 = 1 := by simp [Nat.pow_mod, hp2]
        omega
      have hdvd2 : (p ^ 4 + p ^ 3 + p ^ 2 + p + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hrsig
      omega
    have hr_dvd_N : r ∣ N := by
      apply dvd_perfect_of_exact_prime_pow hN hp_prime (Nat.ordProj_dvd N p)
        ((hp_prime.pow_dvd_iff_le_factorization hN.2.ne').not.mpr (by omega)) hr hr_odd
      rw [← sigma_one_apply, hp_exp, sigma_one_four_eq hp_prime]
      exact hrsig
    have hr_mem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hr_dvd_N, hN.2.ne'⟩
    have hr53 : 53 ≤ r := sixth_power_free_min_prime_ge_53 ho hN hfree hr_mem
    have hr_ne5 : r ≠ 5 := by omega
    have hnd5 : ¬ r ∣ 5 := fun hd5 => hr_ne5 (by have := Nat.le_of_dvd (by decide) hd5; omega)
    have hdvd5 : (r : ℤ) ∣ eval (p : ℤ) (cyclotomic 5 ℤ) := by
      rw [eval_cyclotomic_five_int]
      exact_mod_cast hrsig
    obtain ⟨hpner, _, _, hord, _, hmod, ⟨_, hcard_r, hmem_r⟩, ⟨hcard_p, hmul_p, _, hmem_p⟩⟩ :=
      cyclotomic_dual_splitting_of_dvd_eval_cyclotomic hp_prime hr (by decide) hnd5 hdvd5
    have htot5 : Nat.totient 5 = 4 := by decide
    rw [htot5] at hcard_r
    exact ⟨hr_mem, hr53, hr_ne5, hpner, hmod, hord, ⟨hcard_r, hmem_r⟩, ⟨hcard_p, hmul_p, hmem_p⟩⟩

end OddPerfect
