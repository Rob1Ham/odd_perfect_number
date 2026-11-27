module

public import OddPerfect.HarmonicRange101.Part007
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf3685_0 : PrimeBank := .leaf [2, 3, 7, 13, 19, 23, 31, 43, 67, 83, 103, 127, 139, 163, 167, 229]
theorem leaf3685_0_valid : leaf3685_0.Certified := by
  simp only [leaf3685_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf3685_1 : PrimeBank := .leaf [241, 277, 283, 307, 331, 337, 367, 479, 499, 829, 883, 1579, 1663, 1693, 1949, 2131]
theorem leaf3685_1_valid : leaf3685_1.Certified := by
  simp only [leaf3685_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 263] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 487] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 71] }]), by simp⟩

@[expose] def leaf3685_2 : PrimeBank := .leaf [2251, 2287, 2293, 2311, 2503, 3259, 3373, 3433, 4729, 5281, 5851, 7297, 7351, 8923, 9199, 10099]
theorem leaf3685_2_valid : leaf3685_2.Certified := by
  simp only [leaf3685_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 191] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 281] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 197] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1487] }, .lucas { root := 5, primeFactors := [2, 743] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 73] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by simp⟩

@[expose] def leaf3685_3 : PrimeBank := .leaf [11701, 11909, 13339, 15091, 16141, 19441, 19489, 20611, 23743, 29947, 30367, 43237, 48823, 57163, 91801, 99713]
theorem leaf3685_3_valid : leaf3685_3.Certified := by
  simp only [leaf3685_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 229] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 503] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 269] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 229] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 241] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 79, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1361] }, .lucas { root := 3, primeFactors := [2, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 41] }]), by simp⟩

@[expose] def leaf3685_4 : PrimeBank := .leaf [102913, 113989, 119089, 120391, 135283, 169681, 177013, 186037, 227977, 229759, 239851, 244753, 295237, 347131, 356263, 394699]
theorem leaf3685_4_valid : leaf3685_4.Certified := by
  simp only [leaf3685_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 23, 59] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 827] }]), by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 4013] }, .lucas { root := 2, primeFactors := [2, 17, 59] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 101] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 149] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 419] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 23, 59] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 149, 257] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 41] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5099] }, .lucas { root := 2, primeFactors := [2, 2549] }, .lucas { root := 2, primeFactors := [2, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 139] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 19, 29] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59377] }, .lucas { root := 5, primeFactors := [2, 3, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 157, 419] }]), by simp⟩

@[expose] def leaf3685_5 : PrimeBank := .leaf [663763, 740533, 800281, 1141081, 1235389, 1976383, 2447923, 2695411, 4586797, 4873051, 5089519, 5247019, 5390821, 5471551, 5684257, 15066043]
theorem leaf3685_5_valid : leaf3685_5.Certified := by
  simp only [leaf3685_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 89, 113] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 47, 101] }]), by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 37, 257] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 191] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 59, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 109, 197] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67, 149] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 103, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 31, 1303] }, .lucas { root := 6, primeFactors := [2, 3, 7, 31] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 661] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67, 149] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 647, 3881] }, .lucas { root := 13, primeFactors := [2, 5, 97] }]), by simp⟩

@[expose] def leaf3685_6 : PrimeBank := .leaf [15916111, 17284807]
theorem leaf3685_6_valid : leaf3685_6.Certified := by
  simp only [leaf3685_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 19, 3989] }, .lucas { root := 2, primeFactors := [2, 997] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 11, 4157] }, .lucas { root := 2, primeFactors := [2, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]), by simp⟩

@[expose] def pool3685 : PrimeBank := (.branch 11701 (.branch 241 leaf3685_0 (.branch 2251 leaf3685_1 leaf3685_2)) (.branch 663763 (.branch 102913 leaf3685_3 leaf3685_4) (.branch 15916111 leaf3685_5 leaf3685_6)))
theorem pool3685_valid : pool3685.Certified := ⟨⟨leaf3685_0_valid,⟨leaf3685_1_valid,leaf3685_2_valid⟩⟩,⟨⟨leaf3685_3_valid,leaf3685_4_valid⟩,⟨leaf3685_5_valid,leaf3685_6_valid⟩⟩⟩

theorem covered3685 : Range 3685 3709 :=
  scan_sound pool3685 pool3685_valid 5 3685 [5, 3, 7, 0, 3, 5, 0, 3, 0, 7, 3, 11] [[(2,(.split 15091 []))], [(2,(.split 239851 []))], [(2,(.split 307 [(2,(.split 3433 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3709 : Range 3709 3733 :=
  scan_sound pool3685 pool3685_valid 5 3709 [0, 3, 47, 5, 3, 0, 61, 3, 5, 0, 3, 7] [[(2,(.split 4586797 [(1,(.split 99713 []))]))], [(2,(.split 1976383 []))], [(2,(.split 356263 []))]]
    (by decide) (by decide +kernel)

theorem covered3733 : Range 3733 3757 :=
  scan_sound pool3685 pool3685_valid 5 3733 [0, 3, 37, 0, 3, 19, 5, 3, 23, 11, 3, 5] [[(2,(.split 663763 []))], [(2,(.split 2311 [(2,(.raise [(883,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered3757 : Range 3757 3781 :=
  scan_sound pool3685 pool3685_valid 6 3757 [13, 3, 0, 53, 3, 0, 0, 3, 7, 5, 3, 0] [[(2,(.split 7297 [(1,(.split 277 [(1,(.split 139 []))]))]))], [(2,(.split 9199 []))], [(2,(.split 2287 [(2,(.split 91801 []))]))], [(2,(.split 2503 []))]]
    (by decide) (by decide +kernel)

theorem covered3781 : Range 3781 3805 :=
  scan_sound pool3685 pool3685_valid 6 3781 [19, 3, 5, 7, 3, 17, 0, 3, 0, 29, 3, 0] [[(2,(.split 2251 [(2,(.raise [(2131,1)]))]))], [(2,(.split 1579 [(2,(.raise [(7,1)]))]))], [(2,(.split 295237 [(1,(.split 3433 [(1,(.raise [(43,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered3805 : Range 3805 3829 :=
  scan_sound pool3685 pool3685_valid 6 3805 [5, 3, 13, 37, 3, 5, 11, 3, 0, 0, 3, 43] [[(2,(.split 394699 []))], [(2,(.split 4873051 []))]]
    (by decide) (by decide +kernel)

theorem covered3829 : Range 3829 3853 :=
  scan_sound pool3685 pool3685_valid 6 3829 [7, 3, 0, 5, 3, 11, 23, 3, 5, 0, 3, 0] [[(2,(.split 48823 []))], [(2,(.split 8923 []))], [(2,(.split 1141081 [(1,(.split 1693 [(1,(.split 337 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered3853 : Range 3853 3877 :=
  scan_sound pool3685 pool3685_valid 6 3853 [0, 3, 7, 17, 3, 0, 5, 3, 53, 7, 3, 5] [[(2,(.split 30367 []))], [(2,(.split 347131 []))]]
    (by decide) (by decide +kernel)

theorem covered3877 : Range 3877 3901 :=
  scan_sound pool3685 pool3685_valid 6 3877 [0, 3, 0, 11, 3, 13, 0, 3, 17, 5, 3, 7] [[(2,(.split 5281 [(1,(.split 139 [(2,(.raise [(499,1)]))]))]))], [(2,(.split 15066043 []))], [(2,(.split 102913 [(1,(.split 7351 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3901 : Range 3901 3925 :=
  scan_sound pool3685 pool3685_valid 6 3901 [47, 3, 5, 0, 3, 0, 7, 3, 0, 0, 3, 0] [[(2,(.split 5089519 []))], [(2,(.split 13339 []))], [(2,(.split 283 [(2,(.raise [(367,1), (127,1)]))]))], [(2,(.split 119089 [(1,(.split 11909 [(1,(.split 43 []))]))]))], [(2,(.split 229759 []))]]
    (by decide) (by decide +kernel)

theorem covered3925 : Range 3925 3949 :=
  scan_sound pool3685 pool3685_valid 6 3925 [5, 3, 0, 0, 3, 5, 31, 3, 7, 0, 3, 0] [[(2,(.split 169681 [(1,(.split 2293 [(1,(.raise [(31,1), (7,1)]))]))]))], [(2,(.split 23743 []))], [(2,(.split 740533 [(1,(.split 479 []))]))], [(2,(.split 10099 []))]]
    (by decide) (by decide +kernel)

theorem covered3949 : Range 3949 3973 :=
  scan_sound pool3685 pool3685_valid 6 3949 [11, 3, 59, 5, 3, 37, 17, 3, 5, 0, 3, 11] [[(2,(.split 5247019 []))]]
    (by decide) (by decide +kernel)

theorem covered3973 : Range 3973 3997 :=
  scan_sound pool3685 pool3685_valid 6 3973 [29, 3, 41, 23, 3, 7, 5, 3, 0, 13, 3, 5] [[(2,(.split 15916111 []))]]
    (by decide) (by decide +kernel)

theorem covered3997 : Range 3997 4021 :=
  scan_sound pool3685 pool3685_valid 6 3997 [7, 3, 0, 0, 3, 0, 19, 3, 0, 5, 3, 0] [[(2,(.split 120391 []))], [(2,(.split 331 [(2,(.split 16141 []))]))], [(2,(.split 1235389 [(1,(.split 13 [(3,(.raise [(43,1)]))]))]))], [(2,(.split 177013 [(1,(.split 67 []))]))], [(2,(.split 19489 [(1,(.split 1949 [(1,(.split 829 [(1,(.raise [(83,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered4021 : Range 4021 4045 :=
  scan_sound pool3685 pool3685_valid 7 4021 [0, 3, 5, 0, 3, 29, 37, 3, 11, 7, 3, 13] [[(2,(.split 5390821 [(1,(.raise [(2695411,1)]))]))], [(2,(.split 3373 [(1,(.split 241 [(1,(.split 229 [(1,(.split 23 []))])), (2,(.split 19441 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered4045 : Range 4045 4069 :=
  scan_sound pool3685 pool3685_valid 7 4045 [5, 3, 0, 0, 3, 5, 0, 3, 31, 17, 3, 7] [[(2,(.split 244753 [(1,(.split 67 []))]))], [(2,(.split 5471551 []))], [(2,(.split 11701 [(1,(.raise [(5851,1), (67,1), (7,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered4069 : Range 4069 4093 :=
  scan_sound pool3685 pool3685_valid 7 4069 [13, 3, 0, 5, 3, 0, 7, 3, 5, 61, 3, 0] [[(2,(.split 139 [(2,(.raise [(499,1), (103,1)]))]))], [(2,(.split 227977 [(1,(.split 113989 []))]))], [(2,(.split 29947 []))]]
    (by decide) (by decide +kernel)

theorem covered4093 : Range 4093 4117 :=
  scan_sound pool3685 pool3685_valid 7 4093 [0, 3, 17, 0, 3, 11, 5, 3, 7, 0, 3, 5] [[(2,(.split 20611 []))], [(2,(.split 800281 [(1,(.raise [(57163,1)]))]))], [(2,(.split 3259 []))]]
    (by decide) (by decide +kernel)

theorem covered4117 : Range 4117 4141 :=
  scan_sound pool3685 pool3685_valid 7 4117 [23, 3, 13, 7, 3, 0, 0, 3, 0, 5, 3, 0] [[(2,(.split 139 [(2,(.split 499 []))]))], [(2,(.split 5684257 [(1,(.split 4729 [(1,(.raise [(43,1)]))]))]))], [(2,(.split 163 [(2,(.raise [(67,1), (19,1), (7,1)]))]))], [(2,(.split 2447923 []))]]
    (by decide) (by decide +kernel)

theorem covered4141 : Range 4141 4165 :=
  scan_sound pool3685 pool3685_valid 7 4141 [41, 3, 5, 11, 3, 7, 0, 3, 0, 0, 3, 23] [[(2,(.split 43237 [(1,(.split 1663 []))]))], [(2,(.split 17284807 []))], [(2,(.split 186037 [(1,(.split 167 []))]))]]
    (by decide) (by decide +kernel)

theorem covered4165 : Range 4165 4189 :=
  scan_sound pool3685 pool3685_valid 7 4165 [5, 3, 11, 43, 3, 5, 0, 3, 37, 47, 3, 53] [[(2,(.split 135283 []))]]
    (by decide) (by decide +kernel)

theorem covered4189 : Range 4189 4197 :=
  scan_sound pool3685 pool3685_valid 7 4189 [59, 3, 7, 5] []
    (by decide) (by decide +kernel)

theorem segment3685 : Range 3685 4197 := (range_join (range_join (range_join (range_join covered3685 covered3709) (range_join covered3733 (range_join covered3757 covered3781))) (range_join (range_join covered3805 (range_join covered3829 covered3853)) (range_join covered3877 (range_join covered3901 covered3925)))) (range_join (range_join (range_join covered3949 covered3973) (range_join covered3997 (range_join covered4021 covered4045))) (range_join (range_join covered4069 (range_join covered4093 covered4117)) (range_join covered4141 (range_join covered4165 covered4189)))))

theorem through4197 : Range 101 4197 := (range_join through3685 segment3685)

end OddPerfect.HarmonicChain.HarmonicRange101
