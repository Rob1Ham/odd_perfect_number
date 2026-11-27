module

public import OddPerfect.HarmonicRange101.Part012
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf6245_0 : PrimeBank := .leaf [2, 3, 7, 11, 13, 19, 23, 31, 37, 43, 47, 67, 79, 83, 97, 109]
theorem leaf6245_0_valid : leaf6245_0.Certified := by
  simp only [leaf6245_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf6245_1 : PrimeBank := .leaf [131, 191, 199, 211, 223, 307, 331, 439, 487, 521, 547, 631, 643, 907, 1093, 1117]
theorem leaf6245_1_valid : leaf6245_1.Certified := by
  simp only [leaf6245_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }]), by simp⟩

@[expose] def leaf6245_2 : PrimeBank := .leaf [1327, 1373, 1423, 2203, 2239, 2707, 2719, 3019, 3169, 4813, 5407, 5413, 6121, 9907, 12241, 12547]
theorem leaf6245_2_valid : leaf6245_2.Certified := by
  simp only [leaf6245_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 373] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 401] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 127] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 41] }]), by simp⟩

@[expose] def leaf6245_3 : PrimeBank := .leaf [12637, 13267, 13729, 13859, 14533, 15349, 16651, 16979, 17419, 17713, 22643, 24481, 24979, 25423, 28657, 50587]
theorem leaf6245_3_valid : leaf6245_3.Certified := by
  simp only [leaf6245_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 67] }]), by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 173] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 653] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2903] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11321] }, .lucas { root := 3, primeFactors := [2, 5, 283] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 181] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 223] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 8431] }, .lucas { root := 3, primeFactors := [2, 3, 5, 281] }]), by simp⟩

@[expose] def leaf6245_4 : PrimeBank := .leaf [51691, 55609, 59467, 66457, 72727, 76231, 80251, 109819, 111217, 114781, 118297, 149077, 152461, 169789, 208231, 304897]
theorem leaf6245_4_valid : leaf6245_4.Certified := by
  simp only [leaf6245_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 1723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 331] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 71] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 107] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6101] }, .lucas { root := 2, primeFactors := [2, 5, 61] }]), by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 331] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1913] }, .lucas { root := 3, primeFactors := [2, 239] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 31, 53] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 41, 101] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 11] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 14149] }, .lucas { root := 6, primeFactors := [2, 3, 131] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 631] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]), by simp⟩

@[expose] def leaf6245_5 : PrimeBank := .leaf [554017, 1018177, 1041577, 1351813, 1951007, 5690719, 6075709, 6744781, 13010419, 13489561, 13642669, 14003281, 14871907, 21776701, 22575841, 40825711]
theorem leaf6245_5_valid : leaf6245_5.Certified := by
  simp only [leaf6245_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 199] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5303] }, .lucas { root := 5, primeFactors := [2, 11, 241] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43399] }, .lucas { root := 13, primeFactors := [2, 3, 2411] }, .lucas { root := 6, primeFactors := [2, 5, 241] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 149, 6547] }, .lucas { root := 2, primeFactors := [2, 3, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 41, 701] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 53, 233] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 53, 101] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 347, 2083] }, .lucas { root := 2, primeFactors := [2, 3, 347] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 53, 101] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 41, 79] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 2161] }, .lucas { root := 23, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 53, 131] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 6599] }, .lucas { root := 13, primeFactors := [2, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 6719] }, .lucas { root := 11, primeFactors := [2, 3359] }, .lucas { root := 11, primeFactors := [2, 23, 73] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 71, 6389] }, .lucas { root := 2, primeFactors := [2, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]), by simp⟩

@[expose] def leaf6245_6 : PrimeBank := .leaf [42922153, 43158331, 43553401, 44269063, 45151681]
theorem leaf6245_6_valid : leaf6245_6.Certified := by
  simp only [leaf6245_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13, 6551] }, .lucas { root := 17, primeFactors := [2, 5, 131] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 73, 6569] }, .lucas { root := 3, primeFactors := [2, 821] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 6599] }, .lucas { root := 13, primeFactors := [2, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1109, 6653] }, .lucas { root := 2, primeFactors := [2, 277] }, .lucas { root := 2, primeFactors := [2, 1663] }, .lucas { root := 3, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 61, primeFactors := [2, 3, 5, 7, 6719] }, .lucas { root := 11, primeFactors := [2, 3359] }, .lucas { root := 11, primeFactors := [2, 23, 73] }]), by simp⟩

@[expose] def pool6245 : PrimeBank := (.branch 12637 (.branch 131 leaf6245_0 (.branch 1327 leaf6245_1 leaf6245_2)) (.branch 554017 (.branch 51691 leaf6245_3 leaf6245_4) (.branch 42922153 leaf6245_5 leaf6245_6)))
theorem pool6245_valid : pool6245.Certified := ⟨⟨leaf6245_0_valid,⟨leaf6245_1_valid,leaf6245_2_valid⟩⟩,⟨⟨leaf6245_3_valid,leaf6245_4_valid⟩,⟨leaf6245_5_valid,leaf6245_6_valid⟩⟩⟩

theorem covered6245 : Range 6245 6269 :=
  scan_sound pool6245 pool6245_valid 5 6245 [5, 0, 3, 7, 13, 3, 0, 11, 3, 0, 5, 3] [[(2,(.split 13010419 []))], [(2,(.split 118297 [(1,(.split 331 []))]))], [(2,(.split 28657 [(1,(.split 37 [(2,(.raise [(67,1), (23,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered6269 : Range 6269 6293 :=
  scan_sound pool6245 pool6245_valid 5 6269 [0, 0, 3, 5, 0, 3, 11, 61, 3, 0, 19, 3] [[(2,(.split 97 [(1,(.split 7 [])), (2,(.split 3169 [(1,(.raise [(7,1)]))]))]))], [(2,(.split 304897 [(1,(.raise [(13859,1)]))]))], [(2,(.split 3019 []))], [(2,(.split 1327 []))]]
    (by decide) (by decide +kernel)

theorem covered6293 : Range 6293 6317 :=
  scan_sound pool6245 pool6245_valid 6 6293 [7, 5, 3, 0, 0, 3, 5, 7, 3, 0, 59, 3] [[(2,(.split 24481 [(1,(.split 12241 [(1,(.split 6121 []))]))]))], [(2,(.split 1018177 [(1,(.raise [(72727,1)]))]))], [(2,(.split 5690719 []))]]
    (by decide) (by decide +kernel)

theorem covered6317 : Range 6317 6341 :=
  scan_sound pool6245 pool6245_valid 6 6317 [0, 71, 3, 0, 5, 3, 0, 13, 3, 5, 0, 3] [[(2,(.split 439 [(2,(.raise [(67,1)]))]))], [(2,(.split 2203 []))], [(2,(.split 12547 []))], [(2,(.split 51691 []))]]
    (by decide) (by decide +kernel)

theorem covered6341 : Range 6341 6365 :=
  scan_sound pool6245 pool6245_valid 6 6341 [17, 0, 3, 11, 7, 3, 0, 5, 3, 0, 0, 3] [[(2,(.split 169789 [(1,(.raise [(16979,1), (79,1)]))]))], [(2,(.split 631 [(2,(.raise [(307,1)]))]))], [(2,(.split 554017 [(1,(.raise [(631,1), (439,1)]))]))], [(2,(.split 13489561 [(1,(.split 6744781 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6365 : Range 6365 6389 :=
  scan_sound pool6245 pool6245_valid 7 6365 [5, 0, 3, 23, 0, 3, 7, 0, 3, 13, 5, 3] [[(2,(.split 17713 [(1,(.split 521 [(1,(.split 109 [(1,(.split 11 []))]))]))]))], [(2,(.split 1041577 [(1,(.raise [(22643,1)]))]))], [(2,(.split 149077 [(1,(.split 131 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6389 : Range 6389 6413 :=
  scan_sound pool6245 pool6245_valid 7 6389 [0, 7, 3, 5, 0, 3, 37, 19, 3, 43, 13, 3] [[(2,(.component 40825711 2 [(40825711,1)]))], [(2,(.split 13642669 [(1,(.raise [(80251,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6413 : Range 6413 6437 :=
  scan_sound pool6245 pool6245_valid 7 6413 [11, 5, 3, 7, 0, 3, 5, 0, 3, 59, 7, 3] [[(2,(.split 2239 []))], [(2,(.split 223 [(2,(.raise [(16651,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6437 : Range 6437 6461 :=
  scan_sound pool6245 pool6245_valid 7 6437 [41, 47, 3, 17, 5, 3, 0, 0, 3, 5, 11, 3] [[(2,(.split 5407 []))], [(2,(.split 152461 [(1,(.raise [(76231,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6461 : Range 6461 6485 :=
  scan_sound pool6245 pool6245_valid 7 6461 [7, 23, 3, 29, 0, 3, 0, 5, 3, 11, 0, 3] [[(2,(.split 208231 []))], [(2,(.split 1351813 [(1,(.raise [(47,1), (31,1)]))]))], [(2,(.split 14003281 [(1,(.split 114781 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6485 : Range 6485 6509 :=
  scan_sound pool6245 pool6245_valid 7 6485 [5, 13, 3, 0, 43, 3, 73, 67, 3, 7, 5, 3] [[(2,(.split 24979 []))]]
    (by decide) (by decide +kernel)

theorem covered6509 : Range 6509 6533 :=
  scan_sound pool6245 pool6245_valid 7 6509 [23, 17, 3, 5, 7, 3, 0, 11, 3, 61, 0, 3] [[(2,(.split 6075709 [(1,(.raise [(191,1)]))]))], [(2,(.split 25423 []))]]
    (by decide) (by decide +kernel)

theorem covered6533 : Range 6533 6557 :=
  scan_sound pool6245 pool6245_valid 7 6533 [47, 5, 3, 13, 31, 3, 5, 0, 3, 0, 0, 3] [[(2,(.split 15349 [(1,(.split 307 []))]))], [(2,(.split 42922153 [(1,(.raise [(1951007,1)]))]))], [(2,(.split 50587 []))]]
    (by decide) (by decide +kernel)

theorem covered6557 : Range 6557 6581 :=
  scan_sound pool6245 pool6245_valid 7 6557 [79, 7, 3, 0, 5, 3, 0, 0, 3, 5, 0, 3] [[(2,(.split 487 [(2,(.split 12637 []))]))], [(2,(.component 43158331 2 [(43158331,1)]))], [(2,(.split 9907 []))], [(2,(.split 66457 [(1,(.split 47 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6581 : Range 6581 6605 :=
  scan_sound pool6245 pool6245_valid 7 6581 [0, 29, 3, 7, 11, 3, 19, 5, 3, 0, 7, 3] [[(2,(.split 1117 [(1,(.split 43 [(2,(.raise [(631,1)]))])), (2,(.raise [(59467,1)]))]))], [(2,(.split 43553401 [(1,(.split 21776701 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6605 : Range 6605 6629 :=
  scan_sound pool6245 pool6245_valid 7 6605 [5, 0, 3, 11, 17, 3, 13, 0, 3, 37, 5, 3] [[(2,(.split 643 [(2,(.raise [(1423,1)]))]))], [(2,(.split 109819 []))]]
    (by decide) (by decide +kernel)

theorem covered6629 : Range 6629 6653 :=
  scan_sound pool6245 pool6245_valid 7 6629 [7, 19, 3, 5, 0, 3, 29, 7, 3, 17, 61, 3] [[(2,(.split 5413 [(1,(.split 2707 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6653 : Range 6653 6677 :=
  scan_sound pool6245 pool6245_valid 7 6653 [0, 5, 3, 0, 0, 3, 5, 59, 3, 7, 0, 3] [[(2,(.component 44269063 2 [(44269063,1)]))], [(2,(.split 199 [(2,(.raise [(13267,1)]))]))], [(2,(.split 111217 [(1,(.split 55609 []))]))], [(2,(.split 199 [(2,(.raise [(13267,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6677 : Range 6677 6701 :=
  scan_sound pool6245 pool6245_valid 7 6677 [11, 0, 3, 41, 5, 3, 0, 0, 3, 5, 37, 3] [[(2,(.split 14871907 []))], [(2,(.split 17419 []))], [(2,(.split 14533 [(1,(.split 79 [(2,(.split 13 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered6701 : Range 6701 6725 :=
  scan_sound pool6245 pool6245_valid 7 6701 [0, 0, 3, 19, 0, 3, 7, 5, 3, 0, 11, 3] [[(2,(.split 4813 [(1,(.raise [(83,1), (43,1), (31,1), (7,1)]))]))], [(2,(.split 2719 []))], [(2,(.split 13729 [(1,(.split 1373 [(1,(.split 1093 [(1,(.raise [(547,1)]))]))]))]))], [(2,(.split 45151681 [(1,(.split 22575841 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6725 : Range 6725 6749 :=
  scan_sound pool6245 pool6245_valid 7 6725 [5, 7, 3, 53, 0, 3, 0, 23, 3, 11, 5, 3] [[(2,(.split 907 [(2,(.raise [(19,1)]))]))], [(2,(.split 211 [(2,(.raise [(67,1), (31,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6749 : Range 6749 6757 :=
  scan_sound pool6245 pool6245_valid 7 6749 [17, 43, 3, 5] []
    (by decide) (by decide +kernel)

theorem segment6245 : Range 6245 6757 := (range_join (range_join (range_join (range_join covered6245 covered6269) (range_join covered6293 (range_join covered6317 covered6341))) (range_join (range_join covered6365 (range_join covered6389 covered6413)) (range_join covered6437 (range_join covered6461 covered6485)))) (range_join (range_join (range_join covered6509 covered6533) (range_join covered6557 (range_join covered6581 covered6605))) (range_join (range_join covered6629 (range_join covered6653 covered6677)) (range_join covered6701 (range_join covered6725 covered6749)))))

theorem through6757 : Range 101 6757 := (range_join through6245 segment6245)

end OddPerfect.HarmonicChain.HarmonicRange101
