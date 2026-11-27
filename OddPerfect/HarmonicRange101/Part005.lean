module

public import OddPerfect.HarmonicRange101.Part004
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf2149_0 : PrimeBank := .leaf [2, 3, 7, 11, 19, 31, 37, 43, 47, 53, 67, 79, 97, 103, 127, 139]
theorem leaf2149_0_valid : leaf2149_0.Certified := by
  simp only [leaf2149_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf2149_1 : PrimeBank := .leaf [151, 157, 163, 167, 193, 199, 223, 227, 233, 241, 271, 283, 307, 331, 367, 379]
theorem leaf2149_1_valid : leaf2149_1.Certified := by
  simp only [leaf2149_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf2149_2 : PrimeBank := .leaf [433, 463, 499, 571, 631, 661, 757, 787, 881, 883, 1093, 1109, 1759, 1783, 1831, 1993]
theorem leaf2149_2_valid : leaf2149_2.Certified := by
  simp only [leaf2149_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 277] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 293] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 61] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83] }]), by simp⟩

@[expose] def leaf2149_3 : PrimeBank := .leaf [1999, 2113, 2269, 2437, 2689, 2749, 2803, 3169, 3571, 3607, 3673, 3769, 3919, 5233, 5381, 5419]
theorem leaf2149_3_valid : leaf2149_3.Certified := by
  simp only [leaf2149_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 229] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 467] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 601] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 653] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 269] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by simp⟩

@[expose] def leaf2149_4 : PrimeBank := .leaf [5483, 6271, 6653, 7699, 7759, 8719, 9199, 10733, 11437, 11617, 11833, 12541, 13297, 14713, 18251, 18397]
theorem leaf2149_4_valid : leaf2149_4.Certified := by
  simp only [leaf2149_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2741] }, .lucas { root := 2, primeFactors := [2, 5, 137] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1663] }, .lucas { root := 3, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 431] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 73] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2683] }, .lucas { root := 2, primeFactors := [2, 3, 149] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 953] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 73] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 73] }]), by simp⟩

@[expose] def leaf2149_5 : PrimeBank := .leaf [21493, 21799, 23071, 24571, 24697, 39877, 43597, 44959, 49393, 54829, 65827, 66721, 70423, 88969, 89917, 91801]
theorem leaf2149_5_valid : leaf2149_5.Certified := by
  simp only [leaf2149_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 173] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 769] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3323] }, .lucas { root := 2, primeFactors := [2, 11, 151] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 173] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59, 127] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 53] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 139] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 97] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 337] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 127] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 17] }]), by simp⟩

@[expose] def leaf2149_6 : PrimeBank := .leaf [111127, 119797, 128599, 145861, 150211, 161527, 179833, 182509, 182953, 189463, 198047, 226201, 235003, 241393, 260191, 269167]
theorem leaf2149_6_valid : leaf2149_6.Certified := by
  simp only [leaf2149_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 18521] }, .lucas { root := 3, primeFactors := [2, 5, 463] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 149] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 21433] }, .lucas { root := 5, primeFactors := [2, 3, 19, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 26921] }, .lucas { root := 13, primeFactors := [2, 5, 673] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 59, 127] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 67, 227] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 347] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 99023] }, .lucas { root := 5, primeFactors := [2, 7, 11, 643] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 53, 739] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47, 107] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 113, 397] }]), by simp⟩

@[expose] def leaf2149_7 : PrimeBank := .leaf [323053, 365017, 376891, 415381, 1008901, 1618471, 1980469, 2149687, 2619871, 5168803, 5333791, 5473261, 5815333]
theorem leaf2149_7_valid : leaf2149_7.Certified := by
  simp only [leaf2149_7,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 26921] }, .lucas { root := 13, primeFactors := [2, 5, 673] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 227] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 739] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 23, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 367] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29, 271] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 11, 47] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 17, 467] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 379, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 11, 2309] }, .lucas { root := 2, primeFactors := [2, 577] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67, 2411] }, .lucas { root := 6, primeFactors := [2, 5, 241] }]), by simp⟩

@[expose] def pool2149 : PrimeBank := (.branch 5483 (.branch 433 (.branch 151 leaf2149_0 leaf2149_1) (.branch 1999 leaf2149_2 leaf2149_3)) (.branch 111127 (.branch 21493 leaf2149_4 leaf2149_5) (.branch 323053 leaf2149_6 leaf2149_7)))
theorem pool2149_valid : pool2149.Certified := ⟨⟨⟨leaf2149_0_valid,leaf2149_1_valid⟩,⟨leaf2149_2_valid,leaf2149_3_valid⟩⟩,⟨⟨leaf2149_4_valid,leaf2149_5_valid⟩,⟨leaf2149_6_valid,leaf2149_7_valid⟩⟩⟩

theorem covered2149 : Range 2149 2173 :=
  scan_sound pool2149 pool2149_valid 6 2149 [7, 3, 0, 5, 3, 17, 0, 3, 5, 11, 3, 13] [[(2,(.split 2749 [(1,(.split 241 [(1,(.split 11 [])), (2,(.raise [(11,1)]))])), (2,(.raise [(3919,1)]))]))], [(2,(.split 119797 [(1,(.split 199 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2173 : Range 2173 2197 :=
  scan_sound pool2149 pool2149_valid 6 2173 [41, 3, 7, 0, 3, 37, 5, 3, 11, 7, 3, 5] [[(2,(.split 226201 [(1,(.split 6653 [(1,(.split 1109 [(1,(.raise [(7,1)]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2197 : Range 2197 2221 :=
  scan_sound pool2149 pool2149_valid 6 2197 [13, 3, 31, 0, 3, 0, 47, 3, 0, 5, 3, 7] [[(2,(.split 1618471 []))], [(2,(.split 3607 [(2,(.raise [(223,1)]))]))], [(2,(.split 376891 []))]]
    (by decide) (by decide +kernel)

theorem covered2221 : Range 2221 2245 :=
  scan_sound pool2149 pool2149_valid 6 2221 [0, 3, 5, 17, 3, 23, 7, 3, 0, 0, 3, 0] [[(2,(.split 235003 []))], [(2,(.split 23071 []))], [(2,(.split 128599 []))], [(2,(.split 757 [(1,(.split 379 [(2,(.raise [(787,1)]))])), (2,(.split 14713 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2245 : Range 2245 2269 :=
  scan_sound pool2149 pool2149_valid 6 2245 [5, 3, 13, 0, 3, 5, 37, 3, 7, 31, 3, 0] [[(2,(.split 241393 [(1,(.split 881 [(1,(.split 7 []))]))]))], [(2,(.split 1759 [(2,(.raise [(7759,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2269 : Range 2269 2293 :=
  scan_sound pool2149 pool2149_valid 6 2269 [0, 3, 0, 5, 3, 43, 0, 3, 5, 0, 3, 29] [[(2,(.split 7699 []))], [(2,(.split 5168803 []))], [(2,(.split 8719 []))], [(2,(.split 91801 [(1,(.split 19 [(2,(.split 127 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2293 : Range 2293 2317 :=
  scan_sound pool2149 pool2149_valid 6 2293 [0, 3, 0, 11, 3, 7, 5, 3, 0, 0, 3, 5] [[(2,(.split 463 [(2,(.split 3769 [(1,(.raise [(19,1)]))]))]))], [(2,(.split 151 [(2,(.split 2689 [(1,(.split 1093 []))]))]))], [(2,(.split 5333791 []))], [(2,(.split 883 [(2,(.raise [(260191,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2317 : Range 2317 2341 :=
  scan_sound pool2149 pool2149_valid 6 2317 [7, 3, 11, 23, 3, 13, 17, 3, 0, 5, 3, 0] [[(2,(.split 111127 []))], [(2,(.split 5473261 [(1,(.split 1999 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2341 : Range 2341 2365 :=
  scan_sound pool2149 pool2149_valid 8 2341 [0, 3, 5, 0, 3, 0, 13, 3, 0, 7, 3, 17] [[(2,(.split 49393 [(1,(.split 24697 [(1,(.split 233 [(1,(.split 53 [(1,(.split 37 [(1,(.raise [(19,1)]))]))]))]))]))]))], [(2,(.split 661 [(1,(.split 331 [(2,(.split 5233 []))])), (2,(.split 145861 []))]))], [(2,(.split 2437 [(1,(.split 2269 [(1,(.split 227 []))])), (2,(.split 1980469 []))]))], [(2,(.split 150211 []))]]
    (by decide) (by decide +kernel)

theorem covered2365 : Range 2365 2389 :=
  scan_sound pool2149 pool2149_valid 8 2365 [5, 3, 23, 0, 3, 5, 0, 3, 0, 0, 3, 7] [[(2,(.split 43597 [(1,(.split 21799 []))]))], [(2,(.split 269167 []))], [(2,(.split 182953 [(1,(.split 5381 [(1,(.split 31 []))]))]))], [(2,(.split 151 [(2,(.split 12541 [(1,(.raise [(6271,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2389 : Range 2389 2413 :=
  scan_sound pool2149 pool2149_valid 8 2389 [0, 3, 0, 5, 3, 0, 7, 3, 5, 29, 3, 0] [[(2,(.split 2803 [(2,(.raise [(2619871,1)]))]))], [(2,(.split 571 [(2,(.raise [(151,1), (127,1)]))]))], [(2,(.split 13297 [(1,(.split 433 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))]))], [(2,(.split 5815333 [(1,(.split 415381 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2413 : Range 2413 2437 :=
  scan_sound pool2149 pool2149_valid 8 2413 [19, 3, 0, 41, 3, 0, 5, 3, 7, 11, 3, 5] [[(2,(.split 11437 [(1,(.split 43 [(2,(.raise [(631,1)]))]))]))], [(2,(.split 189463 []))]]
    (by decide) (by decide +kernel)

theorem covered2437 : Range 2437 2461 :=
  scan_sound pool2149 pool2149_valid 8 2437 [0, 3, 0, 7, 3, 0, 31, 3, 11, 5, 3, 0] [[(2,(.split 1980469 [(1,(.raise [(198047,1)]))]))], [(2,(.split 88969 [(1,(.split 67 [(2,(.raise [(7,3)]))]))]))], [(2,(.split 65827 []))], [(2,(.split 139 [(2,(.split 499 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2461 : Range 2461 2485 :=
  scan_sound pool2149 pool2149_valid 8 2461 [23, 3, 5, 0, 3, 7, 0, 3, 0, 37, 3, 13] [[(2,(.split 271 [(2,(.raise [(24571,1)]))]))], [(2,(.split 307 [(2,(.split 43 []))]))], [(2,(.split 323053 [(1,(.raise [(161527,1), (19,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2485 : Range 2485 2509 :=
  scan_sound pool2149 pool2149_valid 8 2485 [5, 3, 19, 47, 3, 5, 11, 3, 41, 0, 3, 23] [[(2,(.split 1831 [(2,(.raise [(163,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered2509 : Range 2509 2533 :=
  scan_sound pool2149 pool2149_valid 8 2509 [13, 3, 7, 5, 3, 11, 0, 3, 5, 7, 3, 0] [[(2,(.split 3673 [(1,(.split 167 [(2,(.raise [(11,1)]))])), (2,(.split 1993 []))]))], [(2,(.split 70423 []))]]
    (by decide) (by decide +kernel)

theorem covered2533 : Range 2533 2557 :=
  scan_sound pool2149 pool2149_valid 8 2533 [17, 3, 43, 0, 3, 0, 5, 3, 0, 0, 3, 5] [[(2,(.split 2149687 []))], [(2,(.split 21493 [(1,(.split 43 [(2,(.raise [(631,1)]))]))]))], [(2,(.split 39877 [(1,(.split 163 []))]))], [(2,(.split 79 [(2,(.split 2113 [(1,(.raise [(151,1), (43,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2557 : Range 2557 2581 :=
  scan_sound pool2149 pool2149_valid 8 2557 [0, 3, 13, 11, 3, 17, 7, 3, 31, 5, 3, 0] [[(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))]))], [(2,(.split 179833 [(1,(.split 89917 [(1,(.raise [(44959,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2581 : Range 2581 2605 :=
  scan_sound pool2149 pool2149_valid 8 2581 [29, 3, 5, 13, 3, 0, 0, 3, 7, 23, 3, 19] [[(2,(.split 283 [(2,(.raise [(367,1), (19,1)]))]))], [(2,(.split 11617 [(1,(.split 193 [(1,(.split 157 [(1,(.split 79 []))])), (2,(.raise [(1783,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2605 : Range 2605 2629 :=
  scan_sound pool2149 pool2149_valid 8 2605 [5, 3, 0, 7, 3, 5, 0, 3, 0, 43, 3, 37] [[(2,(.split 31 [(2,(.split 331 []))]))], [(2,(.split 11833 [(1,(.split 193 [(1,(.split 97 [(2,(.split 3169 []))])), (2,(.raise [(1783,1)]))]))]))], [(2,(.split 66721 [(1,(.split 103 [(2,(.raise [(3571,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered2629 : Range 2629 2653 :=
  scan_sound pool2149 pool2149_valid 8 2629 [11, 3, 0, 5, 3, 7, 19, 3, 5, 0, 3, 11] [[(2,(.split 365017 [(1,(.split 182509 [(1,(.raise [(18251,1)]))]))]))], [(2,(.split 18397 [(1,(.split 9199 []))]))]]
    (by decide) (by decide +kernel)

theorem covered2653 : Range 2653 2661 :=
  scan_sound pool2149 pool2149_valid 8 2653 [7, 3, 0, 0] [[(2,(.split 1008901 [(1,(.split 10733 [(1,(.raise [(47,1)]))]))]))], [(2,(.split 54829 [(1,(.split 5483 []))]))]]
    (by decide) (by decide +kernel)

theorem segment2149 : Range 2149 2661 := (range_join (range_join (range_join (range_join covered2149 covered2173) (range_join covered2197 (range_join covered2221 covered2245))) (range_join (range_join covered2269 (range_join covered2293 covered2317)) (range_join covered2341 (range_join covered2365 covered2389)))) (range_join (range_join (range_join covered2413 covered2437) (range_join covered2461 (range_join covered2485 covered2509))) (range_join (range_join covered2533 (range_join covered2557 covered2581)) (range_join covered2605 (range_join covered2629 covered2653)))))

theorem through2661 : Range 101 2661 := (range_join through2149 segment2149)

end OddPerfect.HarmonicChain.HarmonicRange101
