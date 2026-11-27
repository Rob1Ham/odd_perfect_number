module

public import OddPerfect.HarmonicRange101.Part002
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf1125_0 : PrimeBank := .leaf [2, 3, 7, 11, 19, 23, 31, 43, 67, 79, 103, 109, 127, 139, 151, 157]
theorem leaf1125_0_valid : leaf1125_0.Certified := by
  simp only [leaf1125_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf1125_1 : PrimeBank := .leaf [163, 167, 181, 223, 233, 271, 283, 311, 313, 331, 367, 379, 463, 487, 631, 751]
theorem leaf1125_1_valid : leaf1125_1.Certified := by
  simp only [leaf1125_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf1125_2 : PrimeBank := .leaf [787, 797, 823, 827, 907, 937, 1051, 1117, 1627, 1693, 1699, 1993, 2143, 2293, 2383, 2389]
theorem leaf1125_2_valid : leaf1125_2.Certified := by
  simp only [leaf1125_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 271] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 283] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 191] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199] }]), by simp⟩

@[expose] def leaf1125_3 : PrimeBank := .leaf [2707, 2719, 3253, 3571, 3607, 3673, 3769, 4051, 5419, 5683, 6079, 6271, 6991, 7129, 7867, 8167]
theorem leaf1125_3_valid : leaf1125_3.Certified := by
  simp only [leaf1125_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 271] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 601] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 157] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 947] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 1013] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 233] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 23] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1361] }, .lucas { root := 3, primeFactors := [2, 5, 17] }]), by simp⟩

@[expose] def leaf1125_4 : PrimeBank := .leaf [8269, 9631, 10267, 11299, 15733, 16333, 19429, 20533, 22039, 24571, 26839, 28057, 29429, 38923, 39217, 41149]
theorem leaf1125_4_valid : leaf1125_4.Certified := by
  simp only [leaf1125_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 107] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 269] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1361] }, .lucas { root := 3, primeFactors := [2, 5, 17] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1619] }, .lucas { root := 2, primeFactors := [2, 809] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 59] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 3673] }, .lucas { root := 5, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 71] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 167] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 1051] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 499] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 127] }]), by simp⟩

@[expose] def leaf1125_5 : PrimeBank := .leaf [48247, 55147, 59467, 65353, 68743, 70123, 78787, 80167, 96493, 112207, 118801, 125539, 141907, 142591, 158047, 158071]
theorem leaf1125_5_valid : leaf1125_5.Certified := by
  simp only [leaf1125_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 17, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 101] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 53] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 389] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 67] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 29, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 431] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 18701] }, .lucas { root := 2, primeFactors := [2, 5, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 353] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 97] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 53, 71] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 479] }]), by simp⟩

@[expose] def leaf1125_6 : PrimeBank := .leaf [187963, 201451, 215953, 283813, 313549, 331579, 368551, 374683, 698419, 733591, 863497, 1018879, 1216021, 1253737, 1353733, 1395943]
theorem leaf1125_6_valid : leaf1125_6.Certified := by
  simp only [leaf1125_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31327] }, .lucas { root := 6, primeFactors := [2, 3, 23, 227] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 79] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 409] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 353] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 29, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 109] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 811] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 241] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 179] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 97, 1163] }, .lucas { root := 5, primeFactors := [2, 7, 83] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 197, 1181] }, .lucas { root := 7, primeFactors := [2, 5, 59] }]), by simp⟩

@[expose] def leaf1125_7 : PrimeBank := .leaf [1424443, 1482307, 1886503, 2037757, 2212657, 2432041, 2465227, 2507473, 16293691]
theorem leaf1125_7_valid : leaf1125_7.Certified := by
  simp only [leaf1125_7,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 199, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 29, 1217] }, .lucas { root := 3, primeFactors := [2, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 229, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 17, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 31, 1487] }, .lucas { root := 5, primeFactors := [2, 743] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151, 907] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 37, 233] }]), by simp⟩

@[expose] def pool1125 : PrimeBank := (.branch 8269 (.branch 787 (.branch 163 leaf1125_0 leaf1125_1) (.branch 2707 leaf1125_2 leaf1125_3)) (.branch 187963 (.branch 48247 leaf1125_4 leaf1125_5) (.branch 1424443 leaf1125_6 leaf1125_7)))
theorem pool1125_valid : pool1125.Certified := ⟨⟨⟨leaf1125_0_valid,leaf1125_1_valid⟩,⟨leaf1125_2_valid,leaf1125_3_valid⟩⟩,⟨⟨leaf1125_4_valid,leaf1125_5_valid⟩,⟨leaf1125_6_valid,leaf1125_7_valid⟩⟩⟩

theorem covered1125 : Range 1125 1149 :=
  scan_sound pool1125 pool1125_valid 5 1125 [3, 7, 0, 3, 11, 5, 3, 17, 7, 3, 5, 31] [[(2,(.split 79 [(2,(.split 7 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1149 : Range 1149 1173 :=
  scan_sound pool1125 pool1125_valid 7 1149 [3, 0, 0, 3, 13, 19, 3, 0, 5, 3, 7, 0] [[(2,(.split 3673 [(1,(.split 167 [(2,(.split 28057 []))])), (2,(.split 1993 []))]))], [(2,(.split 313 [(1,(.split 157 [(1,(.split 79 [(2,(.split 43 []))])), (2,(.split 8269 [(1,(.raise [(827,1)]))]))])), (2,(.split 181 [(2,(.raise [(139,1)]))])), (3,(.split 157 []))]))], [(2,(.split 1353733 [(1,(.split 29429 [(1,(.split 23 []))]))]))], [(2,(.split 65353 [(1,(.split 797 [(1,(.split 19 [(2,(.split 127 []))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered1173 : Range 1173 1197 :=
  scan_sound pool1125 pool1125_valid 7 1173 [3, 5, 11, 3, 0, 7, 3, 0, 29, 3, 0, 5] [[(2,(.split 1395943 []))], [(2,(.split 201451 []))], [(2,(.split 1424443 []))]]
    (by decide) (by decide +kernel)

theorem covered1197 : Range 1197 1221 :=
  scan_sound pool1125 pool1125_valid 7 1197 [3, 11, 0, 3, 5, 17, 3, 7, 0, 3, 0, 23] [[(2,(.split 68743 []))], [(2,(.split 70123 []))], [(2,(.split 1482307 []))]]
    (by decide) (by decide +kernel)

theorem covered1221 : Range 1221 1245 :=
  scan_sound pool1125 pool1125_valid 7 1221 [3, 0, 5, 3, 0, 0, 3, 5, 0, 3, 17, 11] [[(2,(.split 78787 []))], [(2,(.split 215953 [(1,(.split 5683 []))]))], [(2,(.split 1051 [(2,(.raise [(368551,1)]))]))], [(2,(.split 1117 [(1,(.split 43 [(2,(.split 631 []))])), (2,(.raise [(59467,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1245 : Range 1245 1269 :=
  scan_sound pool1125 pool1125_valid 7 1245 [3, 29, 0, 3, 7, 5, 3, 0, 13, 3, 5, 7] [[(2,(.split 7129 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.raise [(112207,1)]))]))], [(2,(.split 1693 [(1,(.split 937 [(1,(.split 67 [(2,(.raise [(31,1)]))])), (2,(.raise [(7,1)]))])), (2,(.raise [(487,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1269 : Range 1269 1293 :=
  scan_sound pool1125 pool1125_valid 7 1269 [3, 31, 19, 3, 0, 0, 3, 0, 5, 3, 0, 0] [[(2,(.split 125539 []))], [(2,(.split 2383 [(2,(.split 151 []))]))], [(2,(.split 43 [(2,(.split 631 []))]))], [(2,(.split 127 [(2,(.split 5419 []))]))], [(2,(.split 907 [(2,(.split 39217 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1293 : Range 1293 1317 :=
  scan_sound pool1125 pool1125_valid 7 1293 [3, 5, 0, 3, 0, 0, 3, 0, 7, 3, 13, 5] [[(2,(.split 80167 []))], [(2,(.split 1699 [(2,(.split 2389 []))]))], [(2,(.split 2293 [(1,(.split 31 [(2,(.split 331 []))])), (2,(.raise [(463,1)]))]))], [(2,(.split 55147 []))]]
    (by decide) (by decide +kernel)

theorem covered1317 : Range 1317 1341 :=
  scan_sound pool1125 pool1125_valid 7 1317 [3, 0, 0, 3, 5, 0, 3, 11, 31, 3, 7, 13] [[(2,(.split 22039 []))], [(2,(.split 15733 [(1,(.split 7867 []))]))], [(2,(.split 2707 [(2,(.raise [(187963,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1341 : Range 1341 1365 :=
  scan_sound pool1125 pool1125_valid 7 1341 [3, 17, 5, 3, 19, 7, 3, 5, 23, 3, 0, 29] [[(2,(.split 142591 []))]]
    (by decide) (by decide +kernel)

theorem covered1365 : Range 1365 1389 :=
  scan_sound pool1125 pool1125_valid 7 1365 [3, 0, 37, 3, 0, 5, 3, 7, 0, 3, 5, 19] [[(2,(.split 463 [(2,(.split 3769 [(1,(.raise [(19,1)]))]))]))], [(2,(.split 1886503 []))], [(2,(.split 6991 [(2,(.raise [(16293691,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1389 : Range 1389 1413 :=
  scan_sound pool1125 pool1125_valid 7 1389 [3, 13, 7, 3, 11, 0, 3, 23, 5, 3, 0, 17] [[(2,(.split 3607 [(2,(.raise [(223,1)]))]))], [(2,(.split 283813 [(1,(.split 141907 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1413 : Range 1413 1437 :=
  scan_sound pool1125 pool1125_valid 7 1413 [3, 5, 13, 3, 7, 0, 3, 0, 0, 3, 0, 5] [[(2,(.split 96493 [(1,(.split 48247 []))]))], [(2,(.split 2037757 [(1,(.raise [(1018879,1)]))]))], [(2,(.split 907 [(2,(.raise [(751,1), (7,1)]))]))], [(2,(.split 158071 []))]]
    (by decide) (by decide +kernel)

theorem covered1437 : Range 1437 1461 :=
  scan_sound pool1125 pool1125_valid 7 1437 [3, 0, 11, 3, 5, 0, 3, 0, 0, 3, 31, 0] [[(2,(.split 3253 [(1,(.split 1627 [])), (2,(.raise [(4051,1)]))]))], [(2,(.split 698419 []))], [(2,(.split 31 [(2,(.split 331 [(2,(.raise [(19,1)]))]))]))], [(2,(.split 2719 [(2,(.raise [(2465227,1)]))]))], [(2,(.split 283 [(2,(.split 367 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1461 : Range 1461 1485 :=
  scan_sound pool1125 pool1125_valid 7 1461 [3, 7, 5, 3, 13, 0, 3, 5, 7, 3, 0, 0] [[(2,(.split 823 [(2,(.raise [(751,1), (43,1)]))]))], [(2,(.split 313549 [(1,(.split 6271 []))]))], [(2,(.split 733591 []))]]
    (by decide) (by decide +kernel)

theorem covered1485 : Range 1485 1509 :=
  scan_sound pool1125 pool1125_valid 7 1485 [3, 0, 0, 3, 0, 5, 3, 0, 19, 3, 5, 11] [[(2,(.split 2212657 [(1,(.raise [(158047,1), (7,1)]))]))], [(2,(.split 38923 []))], [(2,(.split 31 [(2,(.split 331 [(2,(.raise [(19,1)]))]))]))], [(2,(.split 11299 []))]]
    (by decide) (by decide +kernel)

theorem covered1509 : Range 1509 1533 :=
  scan_sound pool1125 pool1125_valid 7 1509 [3, 0, 17, 3, 37, 7, 3, 0, 5, 3, 11, 0] [[(2,(.split 67 [(2,(.split 43 [(2,(.raise [(631,1)]))]))]))], [(2,(.split 331579 []))], [(2,(.split 41149 [(1,(.split 823 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1533 : Range 1533 1557 :=
  scan_sound pool1125 pool1125_valid 7 1533 [3, 5, 29, 3, 23, 0, 3, 7, 0, 3, 0, 5] [[(2,(.split 127 [(2,(.split 5419 []))]))], [(2,(.split 16333 [(1,(.split 8167 []))]))], [(2,(.split 6079 [(2,(.raise [(2143,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered1557 : Range 1557 1581 :=
  scan_sound pool1125 pool1125_valid 7 1557 [3, 0, 7, 3, 5, 0, 3, 0, 11, 3, 19, 0] [[(2,(.split 2432041 [(1,(.split 1216021 []))]))], [(2,(.split 379 [(2,(.split 787 []))]))], [(2,(.split 163 [(2,(.raise [(139,1), (67,1), (19,1)]))]))], [(2,(.split 118801 [(1,(.split 311 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1581 : Range 1581 1605 :=
  scan_sound pool1125 pool1125_valid 7 1581 [3, 0, 5, 3, 7, 37, 3, 5, 0, 3, 0, 7] [[(2,(.split 2507473 [(1,(.split 1253737 []))]))], [(2,(.split 271 [(2,(.raise [(24571,1), (43,1)]))]))], [(2,(.split 103 [(2,(.split 3571 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1605 : Range 1605 1629 :=
  scan_sound pool1125 pool1125_valid 7 1605 [3, 0, 0, 3, 0, 5, 3, 0, 0, 3, 5, 0] [[(2,(.split 19429 [(1,(.split 67 [(2,(.raise [(31,1), (19,1)]))]))]))], [(2,(.split 863497 [(1,(.split 233 [(1,(.split 109 [(1,(.split 11 []))]))]))]))], [(2,(.split 26839 []))], [(2,(.split 374683 []))], [(2,(.split 9631 [(2,(.raise [(151,1)]))]))], [(2,(.split 20533 [(1,(.split 10267 []))]))]]
    (by decide) (by decide +kernel)

theorem covered1629 : Range 1629 1637 :=
  scan_sound pool1125 pool1125_valid 7 1629 [3, 7, 23, 3] []
    (by decide) (by decide +kernel)

theorem segment1125 : Range 1125 1637 := (range_join (range_join (range_join (range_join covered1125 covered1149) (range_join covered1173 (range_join covered1197 covered1221))) (range_join (range_join covered1245 (range_join covered1269 covered1293)) (range_join covered1317 (range_join covered1341 covered1365)))) (range_join (range_join (range_join covered1389 covered1413) (range_join covered1437 (range_join covered1461 covered1485))) (range_join (range_join covered1509 (range_join covered1533 covered1557)) (range_join covered1581 (range_join covered1605 covered1629)))))

theorem through1637 : Range 101 1637 := (range_join through1125 segment1125)

end OddPerfect.HarmonicChain.HarmonicRange101
