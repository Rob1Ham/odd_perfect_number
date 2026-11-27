module

public import OddPerfect.HarmonicRange101.Part006
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf3173_0 : PrimeBank := .leaf [2, 3, 7, 11, 19, 31, 43, 47, 59, 67, 79, 127, 139, 151, 163, 223]
theorem leaf3173_0_valid : leaf3173_0.Certified := by
  simp only [leaf3173_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf3173_1 : PrimeBank := .leaf [331, 379, 431, 439, 491, 499, 601, 619, 631, 683, 787, 853, 877, 919, 997, 1039]
theorem leaf3173_1_valid : leaf3173_1.Certified := by
  simp only [leaf3173_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 173] }]), by simp⟩

@[expose] def leaf3173_2 : PrimeBank := .leaf [1459, 1483, 1733, 1753, 1993, 2221, 2347, 2467, 2683, 3049, 3571, 3691, 3931, 4007, 4051, 4441]
theorem leaf3173_2_valid : leaf3173_2.Certified := by
  simp only [leaf3173_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 433] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 73] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 149] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 131] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 2003] }, .lucas { root := 5, primeFactors := [2, 7, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]), by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 37] }]), by simp⟩

@[expose] def leaf3173_3 : PrimeBank := .leaf [5419, 5647, 6301, 6733, 9067, 11941, 15607, 16651, 17851, 18133, 23561, 23743, 24197, 29671, 30169, 38917]
theorem leaf3173_3_valid : leaf3173_3.Certified := by
  simp only [leaf3173_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 941] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 199] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 263] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 23, 43] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 419] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 47] }]), by simp⟩

@[expose] def leaf3173_4 : PrimeBank := .leaf [41941, 51673, 52981, 56911, 59779, 65551, 70201, 74149, 91387, 114547, 129769, 136237, 166457, 225289, 254827, 259537]
theorem leaf3173_4_valid : leaf3173_4.Certified := by
  simp only [leaf3173_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 233] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2153] }, .lucas { root := 3, primeFactors := [2, 269] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 883] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 271] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 23] }]), by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 167] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5077] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5407] }, .lucas { root := 3, primeFactors := [2, 3, 17, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11353] }, .lucas { root := 7, primeFactors := [2, 3, 11, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 20807] }, .lucas { root := 5, primeFactors := [2, 101, 103] }]), by primality (cert := .witnesses [.lucas { root := 43, primeFactors := [2, 3, 7, 149] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 5407] }, .lucas { root := 3, primeFactors := [2, 3, 17, 53] }]), by simp⟩

@[expose] def leaf3173_5 : PrimeBank := .leaf [284587, 340387, 398477, 492967, 509653, 532333, 554117, 587173, 630067, 704839, 791827, 1324681, 1555243, 1583653, 1623859, 1664569]
theorem leaf3173_5_valid : leaf3173_5.Certified := by
  simp only [leaf3173_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47431] }, .lucas { root := 12, primeFactors := [2, 3, 5, 17, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 56731] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 79, 97] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 179] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 53] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 23, 317] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 167, 293] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 173, 607] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 79, 1487] }, .lucas { root := 5, primeFactors := [2, 743] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 1109] }, .lucas { root := 2, primeFactors := [2, 277] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 19, 83] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 127, 157] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 1109] }, .lucas { root := 2, primeFactors := [2, 277] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 241, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 61, 379] }]), by simp⟩

@[expose] def leaf3173_6 : PrimeBank := .leaf [1844749, 1932001, 3834091, 3984769, 4194919, 4352461, 5471551, 5805529, 10378063, 10572253, 11611057, 11899051, 12190573, 12655807, 13479913]
theorem leaf3173_6_valid : leaf3173_6.Certified := by
  simp only [leaf3173_6,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 29, 31] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 29, 113] }]), by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 1153] }, .lucas { root := 5, primeFactors := [2, 3] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 197] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 43, 241] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 71, 3407] }, .lucas { root := 5, primeFactors := [2, 13, 131] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 271, 3251] }, .lucas { root := 6, primeFactors := [2, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71, 3407] }, .lucas { root := 5, primeFactors := [2, 13, 131] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 3449] }, .lucas { root := 3, primeFactors := [2, 431] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 97, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 593, 3557] }, .lucas { root := 2, primeFactors := [2, 7, 127] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 3671] }, .lucas { root := 13, primeFactors := [2, 5, 367] }]), by simp⟩

@[expose] def pool3173 : PrimeBank := (.branch 5419 (.branch 331 leaf3173_0 (.branch 1459 leaf3173_1 leaf3173_2)) (.branch 284587 (.branch 41941 leaf3173_3 leaf3173_4) (.branch 1844749 leaf3173_5 leaf3173_6)))
theorem pool3173_valid : pool3173.Certified := ⟨⟨leaf3173_0_valid,⟨leaf3173_1_valid,leaf3173_2_valid⟩⟩,⟨⟨leaf3173_3_valid,leaf3173_4_valid⟩,⟨leaf3173_5_valid,leaf3173_6_valid⟩⟩⟩

theorem covered3173 : Range 3173 3197 :=
  scan_sound pool3173 pool3173_valid 5 3173 [19, 5, 3, 11, 0, 3, 5, 0, 3, 0, 31, 3] [[(2,(.split 259537 [(1,(.split 129769 [(1,(.raise [(683,1)]))]))]))], [(2,(.split 15607 []))], [(2,(.split 11941 [(1,(.split 853 [(2,(.raise [(5647,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered3197 : Range 3197 3221 :=
  scan_sound pool3173 pool3173_valid 5 3197 [23, 7, 3, 0, 5, 3, 0, 13, 3, 5, 0, 3] [[(2,(.split 151 [(2,(.split 7 []))]))], [(2,(.split 56911 []))], [(2,(.split 492967 []))]]
    (by decide) (by decide +kernel)

theorem covered3221 : Range 3221 3245 :=
  scan_sound pool3173 pool3173_valid 5 3221 [0, 11, 3, 7, 0, 3, 53, 5, 3, 41, 7, 3] [[(2,(.split 10378063 []))], [(2,(.split 31 [(2,(.split 331 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3245 : Range 3245 3269 :=
  scan_sound pool3173 pool3173_valid 6 3245 [5, 17, 3, 0, 0, 3, 0, 0, 3, 13, 5, 3] [[(2,(.split 10572253 [(1,(.split 79 []))]))], [(2,(.split 4051 [(2,(.raise [(5471551,1)]))]))], [(2,(.split 1459 [(2,(.raise [(1039,1)]))]))], [(2,(.split 38917 [(1,(.split 11 [(2,(.split 19 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered3269 : Range 3269 3293 :=
  scan_sound pool3173 pool3173_valid 6 3269 [7, 0, 3, 5, 29, 3, 17, 7, 3, 19, 11, 3] [[(2,(.split 509653 [(1,(.raise [(254827,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered3293 : Range 3293 3317 :=
  scan_sound pool3173 pool3173_valid 6 3293 [37, 5, 3, 0, 0, 3, 5, 0, 3, 7, 0, 3] [[(2,(.split 1555243 []))], [(2,(.split 74149 [(1,(.split 1483 []))]))], [(2,(.split 59779 []))], [(2,(.split 3931 [(2,(.raise [(23743,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered3317 : Range 3317 3341 :=
  scan_sound pool3173 pool3173_valid 6 3317 [31, 0, 3, 0, 5, 3, 0, 0, 3, 5, 47, 3] [[(2,(.split 2683 [(2,(.raise [(2467,1)]))]))], [(2,(.split 6301 [(1,(.split 1753 [(1,(.split 877 [(1,(.raise [(439,1)]))]))]))]))], [(2,(.split 1583653 [(1,(.raise [(791827,1)]))]))], [(2,(.split 284587 []))]]
    (by decide) (by decide +kernel)

theorem covered3341 : Range 3341 3365 :=
  scan_sound pool3173 pool3173_valid 6 3341 [13, 0, 3, 0, 17, 3, 7, 5, 3, 0, 0, 3] [[(2,(.split 532333 [(1,(.split 24197 [(1,(.raise [(11,1), (7,1)]))]))]))], [(2,(.split 619 [(2,(.raise [(43,1), (19,1)]))]))], [(2,(.split 379 [(2,(.raise [(787,1)]))]))], [(2,(.split 17851 []))]]
    (by decide) (by decide +kernel)

theorem covered3365 : Range 3365 3389 :=
  scan_sound pool3173 pool3173_valid 6 3365 [5, 7, 3, 0, 0, 3, 11, 31, 3, 17, 5, 3] [[(2,(.split 1623859 []))], [(2,(.split 79 [(2,(.split 43 [(2,(.raise [(631,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered3389 : Range 3389 3413 :=
  scan_sound pool3173 pool3173_valid 6 3389 [0, 0, 3, 5, 43, 3, 19, 41, 3, 0, 7, 3] [[(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))]))], [(2,(.split 3834091 []))], [(2,(.split 11611057 [(1,(.split 5805529 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3413 : Range 3413 3437 :=
  scan_sound pool3173 pool3173_valid 6 3413 [0, 5, 3, 13, 11, 3, 5, 23, 3, 47, 0, 3] [[(2,(.split 1664569 [(1,(.split 166457 []))]))], [(2,(.split 91387 []))]]
    (by decide) (by decide +kernel)

theorem covered3437 : Range 3437 3461 :=
  scan_sound pool3173 pool3173_valid 6 3437 [7, 19, 3, 11, 5, 3, 0, 7, 3, 5, 0, 3] [[(2,(.split 11899051 []))], [(2,(.split 3984769 [(1,(.split 398477 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3461 : Range 3461 3485 :=
  scan_sound pool3173 pool3173_valid 6 3461 [0, 0, 3, 0, 0, 3, 23, 5, 3, 7, 59, 3] [[(2,(.split 619 [(2,(.split 6733 []))]))], [(2,(.split 65551 []))], [(2,(.split 3571 []))], [(2,(.split 30169 [(1,(.split 431 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3485 : Range 3485 3509 :=
  scan_sound pool3173 pool3173_valid 6 3485 [5, 11, 3, 0, 7, 3, 13, 0, 3, 31, 5, 3] [[(2,(.split 12190573 [(1,(.split 554117 []))]))], [(2,(.split 51673 [(1,(.raise [(3691,1), (79,1), (7,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered3509 : Range 3509 3533 :=
  scan_sound pool3173 pool3173_valid 6 3509 [11, 0, 3, 5, 0, 3, 7, 13, 3, 0, 0, 3] [[(2,(.split 587173 [(1,(.split 41941 [(1,(.raise [(67,1)]))]))]))], [(2,(.split 29671 []))], [(2,(.split 787 [(2,(.raise [(163,1)]))]))], [(2,(.split 18133 [(1,(.split 9067 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3533 : Range 3533 3557 :=
  scan_sound pool3173 pool3173_valid 6 3533 [0, 5, 3, 0, 0, 3, 5, 0, 3, 53, 11, 3] [[(2,(.split 114547 []))], [(2,(.split 4441 [(1,(.split 2221 [(1,(.split 31 []))]))]))], [(2,(.split 19 [(2,(.split 127 [(2,(.raise [(5419,1)]))]))]))], [(2,(.split 4194919 []))]]
    (by decide) (by decide +kernel)

theorem covered3557 : Range 3557 3581 :=
  scan_sound pool3173 pool3173_valid 6 3557 [0, 0, 3, 7, 5, 3, 43, 0, 3, 5, 7, 3] [[(2,(.split 12655807 []))], [(2,(.split 136237 [(1,(.split 4007 []))]))], [(2,(.split 139 [(2,(.split 499 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3581 : Range 3581 3605 :=
  scan_sound pool3173 pool3173_valid 6 3581 [0, 0, 3, 17, 37, 3, 0, 5, 3, 59, 13, 3] [[(2,(.split 3049 [(1,(.split 601 [(1,(.split 43 []))]))]))], [(2,(.split 225289 [(1,(.split 1733 [(1,(.split 19 []))]))]))], [(2,(.split 1844749 [(1,(.split 47 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3605 : Range 3605 3629 :=
  scan_sound pool3173 pool3173_valid 6 3605 [5, 0, 3, 23, 0, 3, 0, 7, 3, 0, 5, 3] [[(2,(.split 223 [(2,(.raise [(16651,1)]))]))], [(2,(.split 4352461 [(1,(.split 70201 []))]))], [(2,(.split 52981 [(1,(.split 59 [(2,(.raise [(19,1)]))]))]))], [(2,(.split 919 [(2,(.raise [(163,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered3629 : Range 3629 3653 :=
  scan_sound pool3173 pool3173_valid 6 3629 [19, 0, 3, 5, 0, 3, 11, 0, 3, 7, 41, 3] [[(2,(.split 2347 [(2,(.raise [(7,1)]))]))], [(2,(.split 630067 []))], [(2,(.split 340387 []))]]
    (by decide) (by decide +kernel)

theorem covered3653 : Range 3653 3677 :=
  scan_sound pool3173 pool3173_valid 6 3653 [13, 5, 3, 0, 7, 3, 5, 19, 3, 0, 0, 3] [[(2,(.split 704839 []))], [(2,(.split 13479913 [(1,(.raise [(491,1), (7,1)]))]))], [(2,(.split 1993 [(1,(.split 997 [(1,(.split 499 []))])), (2,(.split 1324681 []))]))]]
    (by decide) (by decide +kernel)

theorem covered3677 : Range 3677 3685 :=
  scan_sound pool3173 pool3173_valid 6 3677 [0, 13, 3, 29] [[(2,(.split 1932001 [(1,(.split 23561 [(1,(.raise [(11,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem segment3173 : Range 3173 3685 := (range_join (range_join (range_join (range_join covered3173 covered3197) (range_join covered3221 (range_join covered3245 covered3269))) (range_join (range_join covered3293 (range_join covered3317 covered3341)) (range_join covered3365 (range_join covered3389 covered3413)))) (range_join (range_join (range_join covered3437 covered3461) (range_join covered3485 (range_join covered3509 covered3533))) (range_join (range_join covered3557 (range_join covered3581 covered3605)) (range_join covered3629 (range_join covered3653 covered3677)))))

theorem through3685 : Range 101 3685 := (range_join through3173 segment3173)

end OddPerfect.HarmonicChain.HarmonicRange101
