module

public import OddPerfect.HarmonicRange101.Part018
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf9317_0 : PrimeBank := .leaf [2, 3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 79, 103, 151, 163, 167]
theorem leaf9317_0_valid : leaf9317_0.Certified := by
  simp only [leaf9317_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf9317_1 : PrimeBank := .leaf [179, 307, 311, 331, 401, 439, 491, 499, 811, 883, 1039, 1093, 1231, 1609, 1627, 1637]
theorem leaf9317_1_valid : leaf9317_1.Certified := by
  simp only [leaf9317_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 173] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 67] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 271] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 409] }]), by simp⟩

@[expose] def leaf9317_2 : PrimeBank := .leaf [1873, 2617, 3571, 3607, 3677, 6841, 7603, 7669, 10243, 10723, 10891, 13999, 14827, 22717, 47111, 47977]
theorem leaf9317_2_valid : leaf9317_2.Certified := by
  simp only [leaf9317_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 601] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 919] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 181] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 569] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1787] }, .lucas { root := 2, primeFactors := [2, 19, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 353] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 631] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 673] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 1999] }, .lucas { root := 3, primeFactors := [2, 3, 37] }]), by simp⟩

@[expose] def leaf9317_3 : PrimeBank := .leaf [51199, 51907, 51991, 65323, 67801, 104743, 204781, 237571, 316957, 324637, 345637, 393859, 649273, 650869, 668821, 691129]
theorem leaf9317_3_valid : leaf9317_3.Certified := by
  simp only [leaf9317_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 7, 23, 53] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 41, 211] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 191] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 113] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 3413] }, .lucas { root := 2, primeFactors := [2, 853] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7919] }, .lucas { root := 7, primeFactors := [2, 37, 107] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 61, 433] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 13, 2081] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9601] }, .lucas { root := 13, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 21881] }, .lucas { root := 3, primeFactors := [2, 5, 547] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 2081] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 73, 743] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 71, 157] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 29, 331] }]), by simp⟩

@[expose] def leaf9317_4 : PrimeBank := .leaf [817123, 1018981, 1549351, 2116327, 2238487, 2373649, 2429257, 3212777, 4200013, 4237663, 4400923, 4428433, 7123981, 29701387, 30384919, 30844927]
theorem leaf9317_4_valid : leaf9317_4.Certified := by
  simp only [leaf9317_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 8011] }, .lucas { root := 14, primeFactors := [2, 3, 5, 89] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 37] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 313] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 9533] }, .lucas { root := 2, primeFactors := [2, 2383] }, .lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 349, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 49451] }, .lucas { root := 10, primeFactors := [2, 5, 23, 43] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 127, 797] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 103, 557] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 149] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 449] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 229, 3203] }, .lucas { root := 2, primeFactors := [2, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 67] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 3209] }, .lucas { root := 3, primeFactors := [2, 401] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 43, 1061] }, .lucas { root := 2, primeFactors := [2, 5, 53] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 229, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]), by simp⟩

@[expose] def leaf9317_5 : PrimeBank := .leaf [32127769, 86927653, 90658963, 90887623, 93886411, 94468681, 94935793, 95052751, 96108613]
theorem leaf9317_5_valid : leaf9317_5.Certified := by
  simp only [leaf9317_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 409, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 37, 9323] }, .lucas { root := 2, primeFactors := [2, 59, 79] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 23, 9521] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 227, 9533] }, .lucas { root := 2, primeFactors := [2, 2383] }, .lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 19, 9689] }, .lucas { root := 3, primeFactors := [2, 7, 173] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 9719] }, .lucas { root := 17, primeFactors := [2, 43, 113] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 29, 9743] }, .lucas { root := 5, primeFactors := [2, 4871] }, .lucas { root := 11, primeFactors := [2, 5, 487] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 9749] }, .lucas { root := 2, primeFactors := [2, 2437] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19, 43, 9803] }, .lucas { root := 2, primeFactors := [2, 13, 29] }]), by simp⟩

@[expose] def pool9317 : PrimeBank := (.branch 51199 (.branch 179 leaf9317_0 (.branch 1873 leaf9317_1 leaf9317_2)) (.branch 817123 leaf9317_3 (.branch 32127769 leaf9317_4 leaf9317_5)))
theorem pool9317_valid : pool9317.Certified := ⟨⟨leaf9317_0_valid,⟨leaf9317_1_valid,leaf9317_2_valid⟩⟩,⟨leaf9317_3_valid,⟨leaf9317_4_valid,leaf9317_5_valid⟩⟩⟩

theorem covered9317 : Range 9317 9341 :=
  scan_sound pool9317 pool9317_valid 5 9317 [7, 0, 3, 0, 5, 3, 19, 7, 3, 5, 0, 3] [[(2,(.split 67801 [(1,(.split 167 []))]))], [(2,(.split 86927653 [(1,(.raise [(11,1)]))]))], [(2,(.split 51991 []))]]
    (by decide) (by decide +kernel)

theorem covered9341 : Range 9341 9365 :=
  scan_sound pool9317 pool9317_valid 5 9341 [0, 0, 3, 13, 0, 3, 47, 5, 3, 7, 11, 3] [[(2,(.split 499 [(2,(.raise [(7,1)]))]))], [(2,(.split 2238487 []))], [(2,(.split 163 [(2,(.raise [(67,1), (19,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9365 : Range 9365 9389 :=
  scan_sound pool9317 pool9317_valid 5 9365 [5, 17, 3, 0, 7, 3, 0, 83, 3, 11, 5, 3] [[(2,(.split 2373649 [(1,(.split 1637 [(1,(.raise [(7,1)]))]))]))], [(2,(.split 22717 [(1,(.raise [(307,1), (79,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9389 : Range 9389 9413 :=
  scan_sound pool9317 pool9317_valid 5 9389 [41, 0, 3, 5, 0, 3, 7, 0, 3, 23, 97, 3] [[(2,(.split 4200013 [(1,(.raise [(491,1)]))]))], [(2,(.split 1549351 []))], [(2,(.split 2617 [(1,(.split 1609 [(1,(.raise [(23,1), (11,1), (7,3)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered9413 : Range 9413 9437 :=
  scan_sound pool9317 pool9317_valid 5 9413 [0, 5, 3, 0, 0, 3, 5, 11, 3, 0, 0, 3] [[(2,(.split 237571 []))], [(2,(.split 103 [(2,(.raise [(3571,1)]))]))], [(2,(.split 3607 []))], [(2,(.split 668821 [(1,(.raise [(43,1), (19,1)]))]))], [(2,(.split 4237663 []))]]
    (by decide) (by decide +kernel)

theorem covered9437 : Range 9437 9461 :=
  scan_sound pool9317 pool9317_valid 5 9437 [0, 0, 3, 7, 5, 3, 11, 13, 3, 5, 7, 3] [[(2,(.split 817123 []))], [(2,(.split 29701387 []))]]
    (by decide) (by decide +kernel)

theorem covered9461 : Range 9461 9485 :=
  scan_sound pool9317 pool9317_valid 5 9461 [0, 0, 3, 0, 17, 3, 0, 5, 3, 0, 19, 3] [[(2,(.split 345637 [(1,(.split 3677 [(1,(.raise [(47,1)]))]))]))], [(2,(.split 65323 []))], [(2,(.split 10723 []))], [(2,(.split 51907 []))], [(2,(.split 47977 [(1,(.split 1873 [(1,(.raise [(23,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered9485 : Range 9485 9509 :=
  scan_sound pool9317 pool9317_valid 5 9485 [5, 53, 3, 0, 11, 3, 0, 7, 3, 13, 5, 3] [[(2,(.split 1039 []))], [(2,(.split 1627 []))]]
    (by decide) (by decide +kernel)

theorem covered9509 : Range 9509 9533 :=
  scan_sound pool9317 pool9317_valid 5 9509 [37, 0, 3, 5, 31, 3, 0, 89, 3, 7, 13, 3] [[(2,(.split 51199 []))], [(2,(.component 90658963 2 [(90658963,1)]))]]
    (by decide) (by decide +kernel)

theorem covered9533 : Range 9533 9557 :=
  scan_sound pool9317 pool9317_valid 5 9533 [0, 5, 3, 0, 7, 3, 5, 0, 3, 0, 41, 3] [[(2,(.component 90887623 2 [(90887623,1)]))], [(2,(.split 2116327 []))], [(2,(.split 30384919 []))], [(2,(.split 104743 []))]]
    (by decide) (by decide +kernel)

theorem covered9557 : Range 9557 9581 :=
  scan_sound pool9317 pool9317_valid 5 9557 [19, 11, 3, 73, 5, 3, 7, 17, 3, 5, 61, 3] []
    (by decide) (by decide +kernel)

theorem covered9581 : Range 9581 9605 :=
  scan_sound pool9317 pool9317_valid 5 9581 [11, 7, 3, 0, 43, 3, 53, 5, 3, 29, 0, 3] [[(2,(.split 691129 [(1,(.raise [(103,1), (19,1)]))]))], [(2,(.split 811 [(2,(.raise [(31,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9605 : Range 9605 9629 :=
  scan_sound pool9317 pool9317_valid 5 9605 [5, 13, 3, 7, 0, 3, 59, 0, 3, 0, 5, 3] [[(2,(.split 4400923 []))], [(2,(.split 30844927 []))], [(2,(.split 7123981 [(1,(.raise [(43,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9629 : Range 9629 9653 :=
  scan_sound pool9317 pool9317_valid 5 9629 [0, 0, 3, 5, 23, 3, 31, 0, 3, 11, 0, 3] [[(2,(.split 1018981 [(1,(.raise [(883,1)]))]))], [(2,(.split 204781 [(1,(.split 151 []))]))], [(2,(.split 4428433 [(1,(.raise [(47111,1)]))]))], [(2,(.split 6841 [(1,(.split 311 []))]))]]
    (by decide) (by decide +kernel)

theorem covered9653 : Range 9653 9677 :=
  scan_sound pool9317 pool9317_valid 5 9653 [7, 5, 3, 13, 0, 3, 5, 7, 3, 19, 17, 3] [[(2,(.split 393859 []))]]
    (by decide) (by decide +kernel)

theorem covered9677 : Range 9677 9701 :=
  scan_sound pool9317 pool9317_valid 5 9677 [0, 0, 3, 23, 5, 3, 0, 11, 3, 5, 0, 3] [[(2,(.split 67 [(2,(.split 31 [(2,(.raise [(331,1)]))]))]))], [(2,(.split 10243 []))], [(2,(.component 93886411 2 [(93886411,1)]))], [(2,(.split 7603 []))]]
    (by decide) (by decide +kernel)

theorem covered9701 : Range 9701 9725 :=
  scan_sound pool9317 pool9317_valid 5 9701 [89, 31, 3, 17, 7, 3, 11, 5, 3, 0, 0, 3] [[(2,(.split 94468681 [(1,(.raise [(179,1)]))]))], [(2,(.split 1231 []))]]
    (by decide) (by decide +kernel)

theorem covered9725 : Range 9725 9749 :=
  scan_sound pool9317 pool9317_valid 5 9725 [5, 71, 3, 37, 0, 3, 7, 0, 3, 0, 5, 3] [[(2,(.split 2429257 [(1,(.split 401 [(1,(.raise [(67,1)]))]))]))], [(2,(.split 7669 [(1,(.raise [(59,1), (31,1), (19,1), (7,1)]))]))], [(2,(.split 94935793 [(1,(.split 1093 []))]))]]
    (by decide) (by decide +kernel)

theorem covered9749 : Range 9749 9773 :=
  scan_sound pool9317 pool9317_valid 5 9749 [0, 7, 3, 5, 11, 3, 43, 13, 3, 0, 0, 3] [[(2,(.component 95052751 2 [(95052751,1)]))], [(2,(.split 316957 [(1,(.raise [(439,1), (43,1)]))]))], [(2,(.split 649273 [(1,(.split 324637 []))]))]]
    (by decide) (by decide +kernel)

theorem covered9773 : Range 9773 9797 :=
  scan_sound pool9317 pool9317_valid 5 9773 [29, 5, 3, 7, 0, 3, 5, 0, 3, 0, 7, 3] [[(2,(.split 650869 [(1,(.split 11 []))]))], [(2,(.split 13999 []))], [(2,(.split 10891 []))]]
    (by decide) (by decide +kernel)

theorem covered9797 : Range 9797 9821 :=
  scan_sound pool9317 pool9317_valid 5 9797 [97, 41, 3, 0, 5, 3, 17, 0, 3, 5, 0, 3] [[(2,(.split 96108613 [(1,(.raise [(14827,1)]))]))], [(2,(.split 67 [(2,(.raise [(31,1), (19,1), (7,3)]))]))], [(2,(.split 32127769 [(1,(.split 3212777 []))]))]]
    (by decide) (by decide +kernel)

theorem covered9821 : Range 9821 9829 :=
  scan_sound pool9317 pool9317_valid 5 9821 [7, 11, 3, 31] []
    (by decide) (by decide +kernel)

theorem segment9317 : Range 9317 9829 := (range_join (range_join (range_join (range_join covered9317 covered9341) (range_join covered9365 (range_join covered9389 covered9413))) (range_join (range_join covered9437 (range_join covered9461 covered9485)) (range_join covered9509 (range_join covered9533 covered9557)))) (range_join (range_join (range_join covered9581 covered9605) (range_join covered9629 (range_join covered9653 covered9677))) (range_join (range_join covered9701 (range_join covered9725 covered9749)) (range_join covered9773 (range_join covered9797 covered9821)))))

theorem through9829 : Range 101 9829 := (range_join through9317 segment9317)

end OddPerfect.HarmonicChain.HarmonicRange101
