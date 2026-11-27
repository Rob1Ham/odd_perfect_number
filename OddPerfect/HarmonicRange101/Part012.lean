module

public import OddPerfect.HarmonicRange101.Part011
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf5733_0 : PrimeBank := .leaf [2, 3, 5, 7, 13, 19, 31, 43, 61, 67, 79, 103, 127, 139, 151, 191]
theorem leaf5733_0_valid : leaf5733_0.Certified := by
  simp only [leaf5733_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf5733_1 : PrimeBank := .leaf [211, 239, 271, 283, 331, 359, 367, 389, 409, 499, 523, 541, 607, 653, 811, 1213]
theorem leaf5733_1_valid : leaf5733_1.Certified := by
  simp only [leaf5733_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101] }]), by simp⟩

@[expose] def leaf5733_2 : PrimeBank := .leaf [1861, 2011, 2143, 2383, 2659, 3187, 3373, 3571, 3847, 3889, 4021, 5419, 5569, 6373, 6529, 6733]
theorem leaf5733_2_valid : leaf5733_2.Certified := by
  simp only [leaf5733_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 67] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 397] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 443] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 281] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 641] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by simp⟩

@[expose] def leaf5733_3 : PrimeBank := .leaf [7027, 7129, 10099, 12547, 13711, 13963, 14251, 21499, 23747, 24571, 24847, 33937, 38671, 42571, 75253, 76511]
theorem leaf5733_3_valid : leaf5733_3.Certified := by
  simp only [leaf5733_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 41] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 457] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 179] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3583] }, .lucas { root := 3, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 383] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 101] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 101] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 6271] }, .lucas { root := 11, primeFactors := [2, 3, 5, 11, 19] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]), by simp⟩

@[expose] def leaf5733_4 : PrimeBank := .leaf [79669, 80221, 81619, 113749, 118873, 124231, 160441, 171559, 211039, 227497, 237157, 303019, 422077, 964339, 1016089, 1567567]
theorem leaf5733_4_valid : leaf5733_4.Certified := by
  simp only [leaf5733_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 2213] }, .lucas { root := 2, primeFactors := [2, 7, 79] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 191] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 61, 223] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9479] }, .lucas { root := 7, primeFactors := [2, 7, 677] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 127] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41, 101] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 191] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 353] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 9479] }, .lucas { root := 7, primeFactors := [2, 7, 677] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19763] }, .lucas { root := 2, primeFactors := [2, 41, 241] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 50503] }, .lucas { root := 5, primeFactors := [2, 3, 19, 443] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 160723] }, .lucas { root := 2, primeFactors := [2, 3, 8929] }, .lucas { root := 11, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 42337] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 13, 29] }]), by simp⟩

@[expose] def leaf5733_5 : PrimeBank := .leaf [1739233, 1760467, 1830181, 1837273, 1856719, 1902007, 1928677, 5193553, 11366587, 11413351, 11695951, 12490921, 34427557, 36572257, 38112103]
theorem leaf5733_5_valid : leaf5733_5.Certified := by
  simp only [leaf5733_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 61] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 12757] }, .lucas { root := 2, primeFactors := [2, 3, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]), by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 47, 59] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 61, 89] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 105667] }, .lucas { root := 3, primeFactors := [2, 3, 11, 1601] }, .lucas { root := 3, primeFactors := [2, 5] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 160723] }, .lucas { root := 2, primeFactors := [2, 3, 8929] }, .lucas { root := 11, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 29, 41] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 59, 139] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 47, 79] }]), by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 13, 17, 157] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 163, 5867] }, .lucas { root := 5, primeFactors := [2, 7, 419] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 6047] }, .lucas { root := 5, primeFactors := [2, 3023] }, .lucas { root := 5, primeFactors := [2, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 6173] }, .lucas { root := 2, primeFactors := [2, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }]), by simp⟩

@[expose] def pool5733 : PrimeBank := (.branch 7027 (.branch 211 leaf5733_0 (.branch 1861 leaf5733_1 leaf5733_2)) (.branch 79669 leaf5733_3 (.branch 1739233 leaf5733_4 leaf5733_5)))
theorem pool5733_valid : pool5733.Certified := ⟨⟨leaf5733_0_valid,⟨leaf5733_1_valid,leaf5733_2_valid⟩⟩,⟨leaf5733_3_valid,⟨leaf5733_4_valid,leaf5733_5_valid⟩⟩⟩

theorem covered5733 : Range 5733 5757 :=
  scan_sound pool5733 pool5733_valid 5 5733 [3, 5, 0, 3, 0, 0, 3, 7, 0, 3, 11, 5] [[(2,(.split 1567567 []))], [(2,(.split 237157 [(1,(.split 139 []))]))], [(2,(.split 79 [(2,(.split 43 []))]))], [(2,(.split 6373 [(1,(.split 3187 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5757 : Range 5757 5781 :=
  scan_sound pool5733 pool5733_valid 8 5757 [3, 13, 7, 3, 5, 73, 3, 29, 23, 3, 53, 0] [[(2,(.split 3889 [(1,(.split 409 [(1,(.split 389 [(1,(.split 5 [(3,(.split 13 []))]))]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered5781 : Range 5781 5805 :=
  scan_sound pool5733 pool5733_valid 8 5781 [3, 0, 5, 3, 7, 0, 3, 5, 11, 3, 0, 7] [[(2,(.split 1760467 []))], [(2,(.split 67 [(2,(.split 7 []))]))], [(2,(.split 3847 []))]]
    (by decide) (by decide +kernel)

theorem covered5805 : Range 5805 5829 :=
  scan_sound pool5733 pool5733_valid 8 5805 [3, 0, 37, 3, 0, 5, 3, 11, 0, 3, 5, 0] [[(2,(.split 811 [(2,(.raise [(31,1)]))]))], [(2,(.split 523 [(2,(.raise [(7027,1)]))]))], [(2,(.split 541 [(1,(.split 271 [(2,(.raise [(24571,1)]))])), (2,(.raise [(13963,1)]))]))], [(2,(.split 2011 []))]]
    (by decide) (by decide +kernel)

theorem covered5829 : Range 5829 5853 :=
  scan_sound pool5733 pool5733_valid 8 5829 [3, 7, 19, 3, 13, 0, 3, 0, 5, 3, 0, 0] [[(2,(.split 11366587 []))], [(2,(.split 38671 []))], [(2,(.split 14251 []))], [(2,(.split 11413351 []))]]
    (by decide) (by decide +kernel)

theorem covered5853 : Range 5853 5877 :=
  scan_sound pool5733 pool5733_valid 8 5853 [3, 5, 0, 3, 0, 11, 3, 0, 0, 3, 7, 5] [[(2,(.split 33937 [(1,(.split 239 []))]))], [(2,(.split 127 [(2,(.raise [(5419,1)]))]))], [(2,(.split 34427557 [(1,(.split 5569 []))]))], [(2,(.split 2383 []))]]
    (by decide) (by decide +kernel)

theorem covered5877 : Range 5877 5901 :=
  scan_sound pool5733 pool5733_valid 8 5877 [3, 0, 0, 3, 5, 7, 3, 43, 71, 3, 0, 17] [[(2,(.split 7129 [(1,(.split 31 [(2,(.raise [(331,1)]))]))]))], [(2,(.split 118873 [(1,(.split 1213 [(1,(.raise [(607,1)]))]))]))], [(2,(.split 42571 []))]]
    (by decide) (by decide +kernel)

theorem covered5901 : Range 5901 5925 :=
  scan_sound pool5733 pool5733_valid 8 5901 [3, 0, 5, 3, 19, 23, 3, 5, 61, 3, 31, 0] [[(2,(.split 81619 []))], [(2,(.split 11695951 []))]]
    (by decide) (by decide +kernel)

theorem covered5925 : Range 5925 5949 :=
  scan_sound pool5733 pool5733_valid 8 5925 [3, 0, 7, 3, 17, 5, 3, 0, 13, 3, 5, 19] [[(2,(.split 103 [(2,(.raise [(3571,1)]))]))], [(2,(.split 1856719 []))]]
    (by decide) (by decide +kernel)

theorem covered5949 : Range 5949 5973 :=
  scan_sound pool5733 pool5733_valid 8 5949 [3, 11, 0, 3, 7, 59, 3, 67, 5, 3, 47, 7] [[(2,(.split 75253 [(1,(.split 191 []))]))]]
    (by decide) (by decide +kernel)

theorem covered5973 : Range 5973 5997 :=
  scan_sound pool5733 pool5733_valid 8 5973 [3, 5, 43, 3, 0, 31, 3, 0, 53, 3, 13, 5] [[(2,(.split 160441 [(1,(.split 80221 []))]))], [(2,(.split 283 [(2,(.raise [(367,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered5997 : Range 5997 6021 :=
  scan_sound pool5733 pool5733_valid 8 5997 [3, 7, 17, 3, 5, 0, 3, 0, 7, 3, 11, 13] [[(2,(.split 79669 [(1,(.split 151 []))]))], [(2,(.split 1902007 []))]]
    (by decide) (by decide +kernel)

theorem covered6021 : Range 6021 6045 :=
  scan_sound pool5733 pool5733_valid 8 6021 [3, 19, 5, 3, 0, 37, 3, 5, 0, 3, 7, 0] [[(2,(.split 5193553 [(1,(.raise [(211,1), (31,1)]))]))], [(2,(.split 6529 [(1,(.split 1861 [(1,(.split 653 [(1,(.raise [(19,1)]))]))]))]))], [(2,(.split 1739233 [(1,(.raise [(124231,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6045 : Range 6045 6069 :=
  scan_sound pool5733 pool5733_valid 8 6045 [3, 0, 23, 3, 0, 5, 3, 73, 11, 3, 5, 0] [[(2,(.split 36572257 [(1,(.raise [(76511,1)]))]))], [(2,(.split 1928677 [(1,(.raise [(964339,1)]))]))], [(2,(.split 67 [(2,(.split 31 [(2,(.raise [(331,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered6069 : Range 6069 6093 :=
  scan_sound pool5733 pool5733_valid 8 6069 [3, 13, 0, 3, 59, 0, 3, 7, 5, 3, 0, 0] [[(2,(.split 139 [(2,(.raise [(499,1), (7,1)]))]))], [(2,(.split 2143 []))], [(2,(.split 227497 [(1,(.split 113749 []))]))], [(2,(.split 3373 [(1,(.split 19 [(2,(.raise [(127,1), (7,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered6093 : Range 6093 6117 :=
  scan_sound pool5733 pool5733_valid 8 6093 [3, 5, 7, 3, 0, 17, 3, 31, 41, 3, 0, 5] [[(2,(.split 171559 []))], [(2,(.split 6733 [(1,(.split 13 [(2,(.split 61 [])), (3,(.split 7 []))]))]))]]
    (by decide) (by decide +kernel)

theorem covered6117 : Range 6117 6141 :=
  scan_sound pool5733 pool5733_valid 8 6117 [3, 29, 0, 3, 5, 11, 3, 0, 0, 3, 17, 7] [[(2,(.split 12490921 [(1,(.raise [(23747,1)]))]))], [(2,(.split 1016089 [(1,(.raise [(139,1), (43,1)]))]))], [(2,(.split 211 [(2,(.raise [(103,1), (31,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6141 : Range 6141 6165 :=
  scan_sound pool5733 pool5733_valid 8 6141 [3, 0, 5, 3, 11, 0, 3, 5, 47, 3, 61, 0] [[(2,(.split 24847 []))], [(2,(.split 10099 []))], [(2,(.split 21499 []))]]
    (by decide) (by decide +kernel)

theorem covered6165 : Range 6165 6189 :=
  scan_sound pool5733 pool5733_valid 8 6165 [3, 7, 31, 3, 0, 5, 3, 37, 7, 3, 5, 23] [[(2,(.component 38112103 2 [(38112103,1)]))]]
    (by decide) (by decide +kernel)

theorem covered6189 : Range 6189 6213 :=
  scan_sound pool5733 pool5733_valid 8 6189 [3, 41, 11, 3, 0, 0, 3, 0, 5, 3, 7, 0] [[(2,(.split 422077 [(1,(.raise [(211039,1)]))]))], [(2,(.split 1830181 [(1,(.raise [(359,1), (7,1)]))]))], [(2,(.split 303019 []))], [(2,(.split 1837273 [(1,(.raise [(13711,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered6213 : Range 6213 6237 :=
  scan_sound pool5733 pool5733_valid 8 6213 [3, 5, 0, 3, 0, 7, 3, 13, 0, 3, 23, 5] [[(2,(.split 12547 []))], [(2,(.split 2659 []))], [(2,(.split 4021 [(1,(.split 2011 []))]))]]
    (by decide) (by decide +kernel)

theorem covered6237 : Range 6237 6245 :=
  scan_sound pool5733 pool5733_valid 8 6237 [3, 17, 79, 3] []
    (by decide) (by decide +kernel)

theorem segment5733 : Range 5733 6245 := (range_join (range_join (range_join (range_join covered5733 covered5757) (range_join covered5781 (range_join covered5805 covered5829))) (range_join (range_join covered5853 (range_join covered5877 covered5901)) (range_join covered5925 (range_join covered5949 covered5973)))) (range_join (range_join (range_join covered5997 covered6021) (range_join covered6045 (range_join covered6069 covered6093))) (range_join (range_join covered6117 (range_join covered6141 covered6165)) (range_join covered6189 (range_join covered6213 covered6237)))))

theorem through6245 : Range 101 6245 := (range_join through5733 segment5733)

end OddPerfect.HarmonicChain.HarmonicRange101
