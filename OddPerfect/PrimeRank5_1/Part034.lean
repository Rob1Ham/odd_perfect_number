module

public import OddPerfect.PrimeRank5_1.Part033
import Mathlib.Tactic.NormNum.Prime

public section

set_option maxRecDepth 16000

namespace OddPerfect.SpoofBox

theorem rank5_1_792 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,421,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 8 rank5_1_768 rank5_1_791

theorem rank5_1_793 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,423,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 431 423 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,431,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_794 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 421 rank5_1_792 rank5_1_793

theorem rank5_1_795 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,351,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 353 351 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,353,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 1 .exponent 5 rank5_1_767 rank5_1_794

theorem rank5_1_796 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,143,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 3 139 143 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,0⟩, ⟨false,19,19,4,0⟩, ⟨false,127,139,2,0⟩, ⟨false,263,523,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 4 .base 349 rank5_1_766 rank5_1_795

theorem rank5_1_797 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,5,5⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,349,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 1 7 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_798 : PrimeCovered (#v[⟨false,3,3,8,8⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 13 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_799 : PrimeCovered (#v[⟨false,3,3,10,10⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_missing _ 0 23 (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rank5_1_800 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,149,2,0⟩, ⟨false,263,265,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 263 265 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,149,2,0⟩, ⟨false,263,263,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_801 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,149,2,0⟩, ⟨false,267,269,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 269 267 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,149,2,0⟩, ⟨false,269,269,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_802 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,149,2,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 265 rank5_1_800 rank5_1_801

theorem rank5_1_803 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,151,151,2,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_804 : PrimeCovered (#v[⟨false,3,3,12,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 149 rank5_1_802 rank5_1_803

theorem rank5_1_805 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,263,269,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 0 .exponent 10 rank5_1_799 rank5_1_804

theorem rank5_1_806 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,271,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_807 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,151,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 269 rank5_1_805 rank5_1_806

theorem rank5_1_808 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,153,157,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 157 153 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,157,157,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_809 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,263,277,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 151 rank5_1_807 rank5_1_808

theorem rank5_1_810 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,279,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 281 279 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,281,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_811 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,157,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 4 .base 277 rank5_1_809 rank5_1_810

theorem rank5_1_812 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,159,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 3 163 159 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,163,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

theorem rank5_1_813 : PrimeCovered (#v[⟨false,3,3,10,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5) := by
  exact primeCovered_split _ 3 .base 157 rank5_1_811 rank5_1_812

theorem rank5_1_814 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,299,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_upper _ 4 293 299 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,263,293,2,0⟩] : Vector Slot 5)
  exact primeCovered_split _ 0 .exponent 8 rank5_1_798 rank5_1_813

theorem rank5_1_815 : PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,301,349,2,0⟩] : Vector Slot 5) := by
  apply covered_prime_lower _ 4 307 301 7 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change PrimeCovered (#v[⟨false,3,3,8,0⟩, ⟨true,5,5,9,0⟩, ⟨false,19,19,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,307,349,2,0⟩] : Vector Slot 5)
  exact primeCovered_reject _ (by decide +kernel)

end OddPerfect.SpoofBox
