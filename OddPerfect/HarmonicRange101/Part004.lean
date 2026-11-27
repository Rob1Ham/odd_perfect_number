module

public import OddPerfect.HarmonicRange101.Part003
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf1637_0 : PrimeBank := .leaf [2, 3, 7, 19, 23, 31, 43, 47, 59, 61, 67, 79, 83, 103, 139, 151]
theorem leaf1637_0_valid : leaf1637_0.Certified := by
  simp only [leaf1637_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf1637_1 : PrimeBank := .leaf [167, 211, 223, 239, 271, 277, 307, 331, 367, 409, 421, 433, 463, 487, 601, 631]
theorem leaf1637_1_valid : leaf1637_1.Certified := by
  simp only [leaf1637_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf1637_2 : PrimeBank := .leaf [907, 937, 1201, 1279, 1291, 1399, 1553, 1607, 1619, 1873, 1951, 2083, 2239, 2383, 2389, 2467]
theorem leaf1637_2_valid : leaf1637_2.Certified := by
  simp only [leaf1637_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 233] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 97] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 73] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 809] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 347] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 373] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by simp⟩

@[expose] def leaf1637_3 : PrimeBank := .leaf [2531, 2557, 2767, 2803, 3019, 3121, 3187, 3331, 3541, 3607, 4099, 4129, 4933, 7411, 7759, 7951]
theorem leaf1637_3_valid : leaf1637_3.Certified := by
  simp only [leaf1637_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 461] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 467] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 59] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 601] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 683] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 431] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53] }]), by simp⟩

@[expose] def leaf1637_4 : PrimeBank := .leaf [8761, 12497, 12583, 14731, 14821, 15263, 15541, 15607, 15901, 15913, 16069, 16453, 16651, 17239, 19867, 31081]
theorem leaf1637_4_valid : leaf1637_4.Certified := by
  simp only [leaf1637_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 73] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 71] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 233] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 491] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 587] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 37] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 103] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 457] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 43] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 37] }]), by simp⟩

@[expose] def leaf1637_5 : PrimeBank := .leaf [32611, 35617, 38971, 39733, 40507, 48907, 57787, 59221, 68743, 71437, 81013, 91577, 95857, 111949, 145417, 152959]
theorem leaf1637_5_valid : leaf1637_5.Certified := by
  simp only [leaf1637_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 433] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 157] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9631] }, .lucas { root := 3, primeFactors := [2, 3, 5, 107] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 67] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5953] }, .lucas { root := 7, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 43, 157] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11447] }, .lucas { root := 5, primeFactors := [2, 59, 97] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 1997] }, .lucas { root := 2, primeFactors := [2, 499] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 491] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 73, 83] }]), by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 13, 37, 53] }]), by simp⟩

@[expose] def leaf1637_6 : PrimeBank := .leaf [154543, 200029, 284587, 305917, 352771, 456451, 464539, 570001, 577531, 611833, 636919, 686479, 915769, 929077, 990151, 1024921]
theorem leaf1637_6_valid : leaf1637_6.Certified := by
  simp only [leaf1637_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 599] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 79, 211] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47431] }, .lucas { root := 12, primeFactors := [2, 3, 5, 17, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 37, 53] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 179] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 139, 557] }]), by primality (cert := .witnesses [.lucas { root := 28, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 37, 53] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 19, 37, 151] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 677] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 23, 79] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 139, 557] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 23, 41] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 13, 73] }]), by simp⟩

@[expose] def leaf1637_7 : PrimeBank := .leaf [1155061, 1177507, 1324681, 1372957, 1706629, 2922391, 3247921, 3281533, 3413257, 3730693, 3894703, 4534771, 5684257]
theorem leaf1637_7_valid : leaf1637_7.Certified := by
  simp only [leaf1637_7,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 19, 313] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 19, 83] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 677] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 1847] }, .lucas { root := 5, primeFactors := [2, 13, 71] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 19, 1709] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 347] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 151, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 1847] }, .lucas { root := 5, primeFactors := [2, 13, 71] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 23, 1931] }, .lucas { root := 2, primeFactors := [2, 5, 193] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 47, 1973] }, .lucas { root := 2, primeFactors := [2, 17, 29] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 71, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 43] }]), by simp⟩

@[expose] def pool1637 : PrimeBank := (.branch 8761 (.branch 907 (.branch 167 leaf1637_0 leaf1637_1) (.branch 2531 leaf1637_2 leaf1637_3)) (.branch 154543 (.branch 32611 leaf1637_4 leaf1637_5) (.branch 1155061 leaf1637_6 leaf1637_7)))
theorem pool1637_valid : pool1637.Certified := ⟨⟨⟨leaf1637_0_valid,leaf1637_1_valid⟩,⟨leaf1637_2_valid,leaf1637_3_valid⟩⟩,⟨⟨leaf1637_4_valid,leaf1637_5_valid⟩,⟨leaf1637_6_valid,leaf1637_7_valid⟩⟩⟩

theorem covered1637 : Range 1637 1661 :=
  scan_sound pool1637 pool1637_valid 5 1637 [0, 11, 3, 31, 5, 3, 17, 13, 3, 5, 0, 3] [[(2,(.split 1291 [(2,(.raise [(907,1)]))]))], [(2,(.split 915769 [(1,(.split 91577 [(1,(.raise [(15263,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered1661 : Range 1661 1685 :=
  scan_sound pool1637 pool1637_valid 6 1661 [11, 0, 3, 0, 0, 3, 7, 5, 3, 23, 41, 3] [[(2,(.split 421 [(1,(.split 211 [(2,(.split 31 []))])), (2,(.split 59221 []))]))], [(2,(.split 16453 [(1,(.split 433 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))]))], [(2,(.split 929077 [(1,(.split 464539 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1685 : Range 1685 1709 :=
  scan_sound pool1637 pool1637_valid 6 1685 [5, 7, 3, 19, 0, 3, 0, 0, 3, 13, 5, 3] [[(2,(.split 487 [(2,(.split 151 []))]))], [(2,(.split 12583 []))], [(2,(.split 2389 [(1,(.split 239 [(2,(.raise [(3019,1)]))])), (2,(.raise [(2803,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1709 : Range 1709 1733 :=
  scan_sound pool1637 pool1637_valid 6 1709 [0, 29, 3, 5, 17, 3, 0, 0, 3, 11, 7, 3] [[(2,(.split 2922391 []))], [(2,(.split 2557 [(1,(.split 1279 [])), (2,(.split 19 []))]))], [(2,(.split 990151 []))]]
    (by decide) (by decide +kernel)

theorem covered1733 : Range 1733 1757 :=
  scan_sound pool1637 pool1637_valid 6 1733 [0, 5, 3, 37, 0, 3, 5, 0, 3, 17, 0, 3] [[(2,(.split 8761 [(1,(.split 7 []))]))], [(2,(.split 32611 []))], [(2,(.split 145417 [(1,(.split 47 [(2,(.split 61 [(1,(.raise [(31,1)]))]))]))]))], [(2,(.split 1024921 [(1,(.split 271 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1757 : Range 1757 1781 :=
  scan_sound pool1637 pool1637_valid 6 1757 [7, 0, 3, 41, 5, 3, 29, 7, 3, 5, 0, 3] [[(2,(.split 7759 [(2,(.raise [(7,1)]))]))], [(2,(.split 81013 [(1,(.split 40507 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1781 : Range 1781 1805 :=
  scan_sound pool1637 pool1637_valid 6 1781 [13, 0, 3, 0, 0, 3, 11, 5, 3, 7, 0, 3] [[(2,(.split 1279 [(2,(.raise [(2383,1)]))]))], [(2,(.split 456451 []))], [(2,(.split 1399 [(2,(.raise [(3607,1)]))]))], [(2,(.split 154543 []))]]
    (by decide) (by decide +kernel)

theorem covered1805 : Range 1805 1829 :=
  scan_sound pool1637 pool1637_valid 6 1805 [5, 13, 3, 0, 7, 3, 23, 17, 3, 0, 5, 3] [[(2,(.split 3281533 [(1,(.split 331 []))]))], [(2,(.split 223 [(2,(.raise [(16651,1), (31,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1829 : Range 1829 1853 :=
  scan_sound pool1637 pool1637_valid 6 1829 [31, 0, 3, 5, 11, 3, 7, 19, 3, 0, 43, 3] [[(2,(.split 1201 [(1,(.split 601 [(1,(.split 7 [])), (2,(.raise [(19,1)]))])), (2,(.raise [(68743,1)]))]))], [(2,(.split 3413257 [(1,(.split 1706629 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1853 : Range 1853 1877 :=
  scan_sound pool1637 pool1637_valid 6 1853 [17, 5, 3, 11, 0, 3, 5, 0, 3, 0, 0, 3] [[(2,(.split 1155061 [(1,(.raise [(577531,1)]))]))], [(2,(.split 3331 [(2,(.raise [(284587,1)]))]))], [(2,(.split 3187 [(2,(.raise [(15607,1)]))]))], [(2,(.split 463 [(2,(.split 19 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1877 : Range 1877 1901 :=
  scan_sound pool1637 pool1637_valid 6 1877 [0, 0, 3, 7, 5, 3, 0, 31, 3, 5, 7, 3] [[(2,(.split 57787 []))], [(2,(.split 1177507 []))], [(2,(.split 48907 []))]]
    (by decide) (by decide +kernel)

theorem covered1901 : Range 1901 1925 :=
  scan_sound pool1637 pool1637_valid 6 1901 [0, 11, 3, 0, 23, 3, 0, 5, 3, 19, 17, 3] [[(2,(.split 39733 [(1,(.split 19867 []))]))], [(2,(.split 14731 []))], [(2,(.split 211 [(2,(.split 67 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1925 : Range 1925 1949 :=
  scan_sound pool1637 pool1637_valid 6 1925 [5, 41, 3, 0, 0, 3, 13, 7, 3, 29, 5, 3] [[(2,(.split 3730693 [(1,(.raise [(2531,1), (67,1)]))]))], [(2,(.split 95857 [(1,(.split 167 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1949 : Range 1949 1973 :=
  scan_sound pool1637 pool1637_valid 6 1949 [0, 0, 3, 5, 19, 3, 37, 13, 3, 7, 11, 3] [[(2,(.split 200029 [(1,(.split 83 [(2,(.raise [(367,1)]))]))]))], [(2,(.split 16069 [(1,(.split 1607 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1973 : Range 1973 1997 :=
  scan_sound pool1637 pool1637_valid 6 1973 [0, 5, 3, 0, 7, 3, 5, 0, 3, 11, 0, 3] [[(2,(.split 3894703 []))], [(2,(.split 4129 [(1,(.split 59 [(2,(.split 3541 []))])), (2,(.split 5684257 []))]))], [(2,(.split 1873 [(1,(.split 937 [(1,(.split 67 [(2,(.raise [(31,1)]))]))])), (2,(.raise [(463,1)]))]))], [(2,(.split 1324681 [(1,(.split 12497 [(1,(.raise [(2083,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered1997 : Range 1997 2021 :=
  scan_sound pool1637 pool1637_valid 6 1997 [0, 0, 3, 0, 5, 3, 7, 0, 3, 5, 0, 3] [[(2,(.split 570001 [(1,(.raise [(2767,1), (103,1)]))]))], [(2,(.split 3121 [(1,(.split 223 [(2,(.raise [(16651,1)]))])), (2,(.split 3247921 []))]))], [(2,(.split 38971 []))], [(2,(.split 14821 [(1,(.split 7411 []))]))], [(2,(.split 4099 [(2,(.raise [(331,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2021 : Range 2021 2045 :=
  scan_sound pool1637 pool1637_valid 6 2021 [43, 7, 3, 0, 0, 3, 19, 5, 3, 0, 13, 3] [[(2,(.split 1951 [(2,(.raise [(79,1)]))]))], [(2,(.split 1372957 [(1,(.raise [(686479,1)]))]))], [(2,(.split 67 [(2,(.split 7 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2045 : Range 2045 2069 :=
  scan_sound pool1637 pool1637_valid 6 2045 [5, 23, 3, 7, 0, 3, 11, 29, 3, 0, 5, 3] [[(2,(.split 1279 [(2,(.raise [(2383,1)]))]))], [(2,(.split 17239 []))]]
    (by decide) (by decide +kernel)

theorem covered2069 : Range 2069 2093 :=
  scan_sound pool1637 pool1637_valid 6 2069 [0, 19, 3, 5, 31, 3, 0, 0, 3, 0, 0, 3] [[(2,(.split 611833 [(1,(.split 305917 [(1,(.raise [(152959,1)]))]))]))], [(2,(.split 4099 [(2,(.raise [(151,1)]))]))], [(2,(.split 15901 [(1,(.split 7951 []))]))], [(2,(.split 71437 [(1,(.split 1553 [(1,(.split 23 []))]))]))], [(2,(.split 111949 [(1,(.split 2239 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2093 : Range 2093 2117 :=
  scan_sound pool1637 pool1637_valid 6 2093 [7, 5, 3, 0, 11, 3, 5, 7, 3, 0, 0, 3] [[(2,(.split 15913 [(1,(.split 277 [(1,(.split 139 []))]))]))], [(2,(.split 636919 []))], [(2,(.split 43 [(2,(.split 631 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2117 : Range 2117 2141 :=
  scan_sound pool1637 pool1637_valid 6 2117 [29, 13, 3, 11, 5, 3, 0, 0, 3, 5, 0, 3] [[(2,(.split 4534771 []))], [(2,(.split 307 [(2,(.split 4933 [(1,(.raise [(2467,1)]))]))]))], [(2,(.split 31081 [(1,(.split 15541 [(1,(.split 409 [(1,(.raise [(19,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2141 : Range 2141 2149 :=
  scan_sound pool1637 pool1637_valid 6 2141 [0, 0, 3, 19] [[(2,(.split 352771 []))], [(2,(.split 35617 [(1,(.split 1619 []))]))]]
    (by decide) (by decide +kernel)

theorem segment1637 : Range 1637 2149 := (range_join (range_join (range_join (range_join covered1637 covered1661) (range_join covered1685 (range_join covered1709 covered1733))) (range_join (range_join covered1757 (range_join covered1781 covered1805)) (range_join covered1829 (range_join covered1853 covered1877)))) (range_join (range_join (range_join covered1901 covered1925) (range_join covered1949 (range_join covered1973 covered1997))) (range_join (range_join covered2021 (range_join covered2045 covered2069)) (range_join covered2093 (range_join covered2117 covered2141)))))

theorem through2149 : Range 101 2149 := (range_join through1637 segment1637)

end OddPerfect.HarmonicChain.HarmonicRange101
