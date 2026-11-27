module

public import OddPerfect.HarmonicRange10001.Part034
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange10001

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf149265_0 : PrimeBank := .leaf [2, 3, 7, 19, 31, 43, 79, 103, 139, 151, 499, 547, 571, 631, 751, 787]
theorem leaf149265_0_valid : leaf149265_0.Certified := by
  simp only [leaf149265_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf149265_1 : PrimeBank := .leaf [1327, 1627, 1663, 1699, 2239, 2371, 3271, 3391, 10987, 15331, 15583, 16927, 23311, 35839, 43573, 62683]
theorem leaf149265_1_valid : leaf149265_1.Certified := by
  simp only [leaf149265_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 271] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 373] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 113] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 73] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 53] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 37] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 181] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3631] }, .lucas { root := 15, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 337] }]), by simp⟩

@[expose] def leaf149265_2 : PrimeBank := .leaf [136777, 155047, 219727, 307147, 382567, 412639, 573871, 992863, 1200607, 1883857, 2803573, 3499843, 4058797, 5388013, 5485429, 5760913]
theorem leaf149265_2_valid : leaf149265_2.Certified := by
  simp only [leaf149265_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 41, 139] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 25841] }, .lucas { root := 3, primeFactors := [2, 5, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 313] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 71, 103] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 63761] }, .lucas { root := 3, primeFactors := [2, 5, 797] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 97, 709] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 37, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 4243] }, .lucas { root := 2, primeFactors := [2, 3, 7, 101] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 18191] }, .lucas { root := 29, primeFactors := [2, 5, 17, 107] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 3019] }, .lucas { root := 2, primeFactors := [2, 3, 503] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 509] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 347] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 211, 229] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 7127] }, .lucas { root := 5, primeFactors := [2, 7, 509] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 3907] }, .lucas { root := 2, primeFactors := [2, 3, 7, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 257, 467] }]), by simp⟩

@[expose] def leaf149265_3 : PrimeBank := .leaf [9141961, 15586591, 27514441, 37665079, 82300591, 115490899, 122128429, 169158271, 204756127, 246816127, 456905893, 522289981, 1066142251, 1175125387, 1177580359, 1720664791]
theorem leaf149265_3_valid : leaf149265_3.Certified := by
  simp only [leaf149265_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 29, 37, 71] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 519553] }, .lucas { root := 5, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 23, 3323] }, .lucas { root := 2, primeFactors := [2, 11, 151] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 570683] }, .lucas { root := 2, primeFactors := [2, 7, 40763] }, .lucas { root := 2, primeFactors := [2, 89, 229] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 61, 263] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 6416161] }, .lucas { root := 13, primeFactors := [2, 3, 5, 13367] }, .lucas { root := 5, primeFactors := [2, 41, 163] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 19, 43, 12457] }, .lucas { root := 10, primeFactors := [2, 3, 173] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1579, 3571] }, .lucas { root := 3, primeFactors := [2, 3, 263] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 521, 3853] }, .lucas { root := 2, primeFactors := [2, 3, 107] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 61, 74929] }, .lucas { root := 17, primeFactors := [2, 3, 7, 223] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 38075491] }, .lucas { root := 3, primeFactors := [2, 3, 5, 423061] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 641] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17, 23, 41, 181] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 19, 163] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2543, 77017] }, .lucas { root := 5, primeFactors := [2, 31, 41] }, .lucas { root := 7, primeFactors := [2, 3, 3209] }, .lucas { root := 3, primeFactors := [2, 401] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 2844397] }, .lucas { root := 2, primeFactors := [2, 3, 8779] }, .lucas { root := 11, primeFactors := [2, 3, 7, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 59, 74779] }, .lucas { root := 2, primeFactors := [2, 3, 11, 103] }]), by simp⟩

@[expose] def leaf149265_4 : PrimeBank := .leaf [1727851231, 7428919219, 7455217051, 7482759919, 22314832543, 22323796333, 22356080881, 22418923171, 22431502213, 22490850931]
theorem leaf149265_4_valid : leaf149265_4.Certified := by
  simp only [leaf149265_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 61, 2141] }, .lucas { root := 2, primeFactors := [2, 5, 107] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 139, 179, 7109] }, .lucas { root := 2, primeFactors := [2, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 191, 997] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 24971, 49943] }, .lucas { root := 2, primeFactors := [2, 5, 11, 227] }, .lucas { root := 5, primeFactors := [2, 24971] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 43, 193, 149381] }, .lucas { root := 3, primeFactors := [2, 5, 7, 11, 97] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 12451, 149411] }, .lucas { root := 3, primeFactors := [2, 3, 5, 83] }, .lucas { root := 2, primeFactors := [2, 5, 67, 223] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 89, 149519] }, .lucas { root := 13, primeFactors := [2, 74759] }, .lucas { root := 11, primeFactors := [2, 37379] }, .lucas { root := 2, primeFactors := [2, 11, 1699] }, .lucas { root := 3, primeFactors := [2, 3, 283] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 23, 31, 149729] }, .lucas { root := 3, primeFactors := [2, 4679] }, .lucas { root := 11, primeFactors := [2, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 1783, 149771] }, .lucas { root := 10, primeFactors := [2, 3, 11] }, .lucas { root := 6, primeFactors := [2, 5, 17, 881] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 4999, 149969] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }, .lucas { root := 3, primeFactors := [2, 7, 13, 103] }]), by simp⟩

@[expose] def pool149265 : PrimeBank := (.branch 136777 (.branch 1327 leaf149265_0 leaf149265_1) (.branch 9141961 leaf149265_2 (.branch 1727851231 leaf149265_3 leaf149265_4)))
theorem pool149265_valid : pool149265.Certified := ⟨⟨leaf149265_0_valid,leaf149265_1_valid⟩,⟨leaf149265_2_valid,⟨leaf149265_3_valid,leaf149265_4_valid⟩⟩⟩

theorem covered149265 : Range 149265 149361 :=
  scan_sound pool149265 pool149265_valid 4 149265 [3, 61, 0, 3, 113, 5, 3, 13, 11, 3, 5, 0, 3, 337, 23, 3, 0, 173, 3, 7, 5, 3, 0, 17, 3, 5, 7, 3, 19, 0, 3, 31, 59, 3, 0, 5, 3, 23, 0, 3, 5, 11, 3, 0, 233, 3, 13, 7] [[(2,(.split 136777 []))], [(2,(.raise [(7428919219,1)]))], [(2,(.raise [(115490899,1)]))], [(2,(.raise [(382567,1)]))], [(2,(.raise [(23311,1)]))], [(2,(.split 5760913 []))], [(2,(.split 43573 []))], [(2,(.raise [(1663,1), (19,1)]))]]
    (by decide) (by decide +kernel)

theorem covered149361 : Range 149361 149457 :=
  scan_sound pool149265 pool149265_valid 4 149361 [3, 41, 5, 3, 11, 0, 3, 5, 0, 3, 0, 13, 3, 7, 31, 3, 0, 5, 3, 0, 7, 3, 5, 53, 3, 0, 11, 3, 0, 0, 3, 0, 5, 3, 7, 23, 3, 5, 29, 3, 0, 7, 3, 17, 199, 3, 103, 5] [[(2,(.raise [(547,1), (151,1)]))], [(2,(.split 2803573 []))], [(2,(.raise [(22314832543,1)]))], [(2,(.raise [(204756127,1)]))], [(2,(.split 5485429 []))], [(2,(.split 22323796333 []))], [(2,(.split 1883857 []))], [(2,(.split 1627 []))], [(2,(.raise [(1175125387,1)]))], [(2,(.raise [(62683,1)]))]]
    (by decide) (by decide +kernel)

theorem covered149457 : Range 149457 149553 :=
  scan_sound pool149265 pool149265_valid 4 149457 [3, 0, 13, 3, 5, 137, 3, 7, 19, 3, 23, 11, 3, 83, 5, 3, 0, 0, 3, 5, 0, 3, 11, 0, 3, 47, 307, 3, 7, 5, 3, 0, 0, 3, 5, 7, 3, 0, 0, 3, 229, 13, 3, 0, 5, 3, 17, 0] [[(2,(.raise [(10987,1)]))], [(2,(.raise [(573871,1)]))], [(2,(.raise [(307147,1)]))], [(2,(.split 122128429 []))], [(2,(.raise [(631,1), (19,1)]))], [(2,(.split 22356080881 []))], [(2,(.raise [(751,1), (139,1)]))], [(2,(.raise [(412639,1)]))], [(2,(.raise [(992863,1)]))], [(2,(.raise [(16927,1)]))], [(2,(.raise [(7455217051,1)]))]]
    (by decide) (by decide +kernel)

theorem covered149553 : Range 149553 149649 :=
  scan_sound pool149265 pool149265_valid 4 149553 [3, 5, 347, 3, 0, 0, 3, 11, 7, 3, 373, 5, 3, 0, 101, 3, 5, 19, 3, 13, 227, 3, 7, 211, 3, 0, 5, 3, 41, 7, 3, 5, 13, 3, 157, 0, 3, 0, 0, 3, 11, 5, 3, 7, 151, 3, 5, 263] [[(2,(.raise [(1720664791,1)]))], [(2,(.split 27514441 []))], [(2,(.raise [(1177580359,1)]))], [(2,(.raise [(1327,1), (43,1)]))], [(2,(.split 3271 []))], [(2,(.split 456905893 []))], [(2,(.raise [(1066142251,1)]))]]
    (by decide) (by decide +kernel)

theorem covered149649 : Range 149649 149745 :=
  scan_sound pool149265 pool149265_valid 4 149649 [3, 17, 7, 3, 109, 103, 3, 19, 5, 3, 13, 97, 3, 5, 11, 3, 7, 43, 3, 181, 0, 3, 107, 5, 3, 11, 19, 3, 5, 23, 3, 0, 0, 3, 0, 17, 3, 7, 5, 3, 0, 0, 3, 5, 7, 3, 137, 11] [[(2,(.split 9141961 []))], [(2,(.raise [(571,1), (7,1)]))], [(2,(.raise [(1200607,1)]))], [(2,(.raise [(2239,1)]))], [(2,(.raise [(22418923171,1)]))], [(2,(.split 5388013 []))]]
    (by decide) (by decide +kernel)

theorem covered149745 : Range 149745 149841 :=
  scan_sound pool149265 pool149265_valid 4 149745 [3, 13, 0, 3, 17, 5, 3, 0, 31, 3, 5, 0, 3, 0, 13, 3, 19, 7, 3, 101, 5, 3, 47, 0, 3, 5, 163, 3, 59, 0, 3, 7, 11, 3, 37, 5, 3, 233, 7, 3, 5, 0, 3, 11, 269, 3, 0, 0] [[(2,(.raise [(155047,1)]))], [(2,(.raise [(3391,1)]))], [(2,(.raise [(35839,1)]))], [(2,(.split 22431502213 []))], [(2,(.raise [(3499843,1)]))], [(2,(.split 4058797 []))], [(2,(.raise [(7482759919,1)]))], [(2,(.raise [(2371,1)]))], [(2,(.raise [(499,1), (79,1)]))]]
    (by decide) (by decide +kernel)

theorem covered149841 : Range 149841 149937 :=
  scan_sound pool149265 pool149265_valid 4 149841 [3, 29, 5, 3, 7, 13, 3, 5, 277, 3, 0, 7, 3, 0, 73, 3, 0, 5, 3, 67, 71, 3, 5, 37, 3, 7, 0, 3, 11, 0, 3, 13, 5, 3, 0, 0, 3, 5, 197, 3, 0, 17, 3, 313, 13, 3, 7, 5] [[(2,(.split 522289981 []))], [(2,(.raise [(246816127,1)]))], [(2,(.raise [(1727851231,1)]))], [(2,(.raise [(82300591,1)]))], [(2,(.raise [(15583,1)]))], [(2,(.raise [(1699,1), (787,1)]))], [(2,(.raise [(219727,1)]))], [(2,(.raise [(103,1), (31,1)]))]]
    (by decide) (by decide +kernel)

theorem covered149937 : Range 149937 150001 :=
  scan_sound pool149265 pool149265_valid 4 149937 [3, 0, 11, 3, 5, 7, 3, 113, 0, 3, 17, 29, 3, 11, 5, 3, 0, 0, 3, 5, 47, 3, 13, 23, 3, 127, 7, 3, 0, 5, 3, 61] [[(2,(.raise [(15331,1)]))], [(2,(.raise [(37665079,1)]))], [(2,(.raise [(22490850931,1)]))], [(2,(.raise [(15586591,1)]))], [(2,(.raise [(169158271,1)]))]]
    (by decide) (by decide +kernel)

theorem segment149265 : Range 149265 150001 := (range_join (range_join (range_join covered149265 covered149361) (range_join covered149457 covered149553)) (range_join (range_join covered149649 covered149745) (range_join covered149841 covered149937)))

theorem through150001 : Range 10001 150001 := (range_join through149265 segment149265)

end OddPerfect.HarmonicChain.HarmonicRange10001
