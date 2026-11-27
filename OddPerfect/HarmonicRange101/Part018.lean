module

public import OddPerfect.HarmonicRange101.Part017
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.HarmonicChain.HarmonicRange101

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] def leaf8805_0 : PrimeBank := .leaf [2, 3, 7, 11, 19, 31, 37, 43, 47, 67, 79, 103, 167, 223, 283, 367]
theorem leaf8805_0_valid : leaf8805_0.Certified := by
  simp only [leaf8805_0,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

@[expose] def leaf8805_1 : PrimeBank := .leaf [491, 499, 523, 547, 631, 769, 823, 997, 1049, 1327, 1423, 1669, 2179, 3463, 3559, 3919]
theorem leaf8805_1_valid : leaf8805_1.Certified := by
  simp only [leaf8805_1,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 131] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 139] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 577] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 593] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 653] }]), by simp⟩

@[expose] def leaf8805_2 : PrimeBank := .leaf [4111, 4327, 4759, 4909, 4987, 5791, 7027, 7069, 7237, 8287, 9817, 10163, 12979, 14029, 14143, 16573]
theorem leaf8805_2_valid : leaf8805_2.Certified := by
  simp only [leaf8805_2,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 137] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 103] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 61] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 409] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 277] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 193] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 409] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5081] }, .lucas { root := 3, primeFactors := [2, 5, 127] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 103] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 167] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2357] }, .lucas { root := 2, primeFactors := [2, 19, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]), by simp⟩

@[expose] def leaf8805_3 : PrimeBank := .leaf [16651, 20641, 22567, 27397, 70207, 88741, 101149, 102253, 164431, 177481, 181277, 182659, 191449, 203617, 246769, 309391]
theorem leaf8805_3_valid : leaf8805_3.Certified := by
  simp only [leaf8805_3,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3761] }, .lucas { root := 3, primeFactors := [2, 5, 47] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 761] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11701] }, .lucas { root := 6, primeFactors := [2, 3, 5, 13] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 8429] }, .lucas { root := 2, primeFactors := [2, 7, 43] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 8521] }, .lucas { root := 13, primeFactors := [2, 3, 5, 71] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17, 29] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 45319] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 4349] }, .lucas { root := 2, primeFactors := [2, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2659] }, .lucas { root := 2, primeFactors := [2, 3, 443] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 101] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 53, 97] }]), by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 10313] }, .lucas { root := 3, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]), by simp⟩

@[expose] def leaf8805_4 : PrimeBank := .leaf [339151, 349183, 373447, 380917, 537331, 890011, 1032049, 1287217, 1461601, 2574433, 3796951, 3988093, 4458127, 5746567, 6024127, 6456391]
theorem leaf8805_4_valid : leaf8805_4.Certified := by
  simp only [leaf8805_4,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 19] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 1021] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 20747] }, .lucas { root := 5, primeFactors := [2, 11, 23, 41] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3527] }, .lucas { root := 5, primeFactors := [2, 41, 43] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17911] }, .lucas { root := 3, primeFactors := [2, 3, 5, 199] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 11, 29, 31] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 2389] }, .lucas { root := 2, primeFactors := [2, 3, 199] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 1277] }, .lucas { root := 2, primeFactors := [2, 11, 29] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 29] }]), by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 7, 1277] }, .lucas { root := 2, primeFactors := [2, 11, 29] }]), by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 17, 1489] }, .lucas { root := 14, primeFactors := [2, 3, 31] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 109, 3049] }, .lucas { root := 11, primeFactors := [2, 3, 127] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 349, 2129] }, .lucas { root := 3, primeFactors := [2, 7, 19] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 61, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 227, 4423] }, .lucas { root := 3, primeFactors := [2, 3, 11, 67] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 19, 47, 241] }]), by simp⟩

@[expose] def leaf8805_5 : PrimeBank := .leaf [6669541, 11493133, 12116413, 12338449, 13182391, 26364781, 26542951, 27297817, 27953269, 28210267, 38786029, 77572057, 80344333, 82074541]
theorem leaf8805_5_valid : leaf8805_5.Certified := by
  simp only [leaf8805_5,PrimeBank.Certified,List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 179] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 61, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 31, 47] }]), by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 19, 83, 163] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 19, 593] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 19, 593] }]), by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 17, 1487] }, .lucas { root := 5, primeFactors := [2, 743] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 29, 431] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 43, 71, 109] }]), by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 73, 3067] }, .lucas { root := 2, primeFactors := [2, 3, 7, 73] }]), by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]), by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83, 8963] }, .lucas { root := 2, primeFactors := [2, 4481] }, .lucas { root := 3, primeFactors := [2, 5, 7] }]), by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 151, 9059] }, .lucas { root := 2, primeFactors := [2, 7, 647] }]), by simp⟩

@[expose] def pool8805 : PrimeBank := (.branch 16651 (.branch 491 leaf8805_0 (.branch 4111 leaf8805_1 leaf8805_2)) (.branch 339151 leaf8805_3 (.branch 6669541 leaf8805_4 leaf8805_5)))
theorem pool8805_valid : pool8805.Certified := ⟨⟨leaf8805_0_valid,⟨leaf8805_1_valid,leaf8805_2_valid⟩⟩,⟨leaf8805_3_valid,⟨leaf8805_4_valid,leaf8805_5_valid⟩⟩⟩

theorem covered8805 : Range 8805 8829 :=
  scan_sound pool8805 pool8805_valid 5 8805 [3, 0, 23, 3, 7, 5, 3, 0, 0, 3, 5, 7] [[(2,(.split 77572057 [(1,(.split 38786029 []))]))], [(2,(.split 101149 [(1,(.split 769 [(1,(.raise [(11,1)]))]))]))], [(2,(.split 14029 [(1,(.split 43 [(2,(.raise [(631,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered8829 : Range 8829 8853 :=
  scan_sound pool8805 pool8805_valid 5 8829 [3, 0, 11, 3, 0, 0, 3, 37, 5, 3, 0, 53] [[(2,(.split 182659 []))], [(2,(.split 4987 []))], [(2,(.split 2179 []))], [(2,(.split 6024127 []))]]
    (by decide) (by decide +kernel)

theorem covered8853 : Range 8853 8877 :=
  scan_sound pool8805 pool8805_valid 5 8853 [3, 5, 17, 3, 0, 0, 3, 0, 7, 3, 19, 5] [[(2,(.split 9817 [(1,(.split 4909 [(1,(.raise [(491,1)]))]))]))], [(2,(.split 70207 []))], [(2,(.split 102253 [(1,(.split 43 []))]))]]
    (by decide) (by decide +kernel)

theorem covered8877 : Range 8877 8901 :=
  scan_sound pool8805 pool8805_valid 5 8877 [3, 13, 83, 3, 5, 0, 3, 17, 0, 3, 7, 11] [[(2,(.split 537331 []))], [(2,(.split 26364781 [(1,(.raise [(13182391,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered8901 : Range 8901 8925 :=
  scan_sound pool8805 pool8805_valid 5 8901 [3, 29, 5, 3, 59, 7, 3, 5, 37, 3, 11, 0] [[(2,(.split 26542951 []))]]
    (by decide) (by decide +kernel)

theorem covered8925 : Range 8925 8949 :=
  scan_sound pool8805 pool8805_valid 5 8925 [3, 79, 0, 3, 0, 5, 3, 7, 0, 3, 5, 23] [[(2,(.split 3796951 []))], [(2,(.split 2574433 [(1,(.split 1287217 []))]))], [(2,(.split 1327 []))]]
    (by decide) (by decide +kernel)

theorem covered8949 : Range 8949 8973 :=
  scan_sound pool8805 pool8805_valid 5 8949 [3, 0, 7, 3, 13, 17, 3, 0, 5, 3, 0, 0] [[(2,(.split 523 [(2,(.raise [(7027,1)]))]))], [(2,(.split 80344333 [(1,(.raise [(5791,1)]))]))], [(2,(.split 11493133 [(1,(.raise [(5746567,1)]))]))], [(2,(.split 14143 []))]]
    (by decide) (by decide +kernel)

theorem covered8973 : Range 8973 8997 :=
  scan_sound pool8805 pool8805_valid 5 8973 [3, 5, 47, 3, 7, 13, 3, 11, 89, 3, 17, 5] []
    (by decide) (by decide +kernel)

theorem covered8997 : Range 8997 9021 :=
  scan_sound pool8805 pool8805_valid 5 8997 [3, 0, 0, 3, 5, 0, 3, 0, 0, 3, 71, 29] [[(2,(.split 890011 []))], [(2,(.split 37 [(2,(.split 67 [(2,(.raise [(31,1)]))])), (3,(.split 19 []))]))], [(2,(.split 3919 []))], [(2,(.split 283 [(2,(.raise [(367,1)]))]))], [(2,(.split 203617 [(1,(.split 1669 [(1,(.raise [(167,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered9021 : Range 9021 9045 :=
  scan_sound pool8805 pool8805_valid 5 9021 [3, 7, 5, 3, 0, 11, 3, 5, 7, 3, 0, 0] [[(2,(.split 1032049 [(1,(.split 20641 []))]))], [(2,(.split 191449 [(1,(.split 547 []))]))], [(2,(.split 373447 []))]]
    (by decide) (by decide +kernel)

theorem covered9045 : Range 9045 9069 :=
  scan_sound pool8805 pool8805_valid 5 9045 [3, 83, 0, 3, 11, 5, 3, 0, 13, 3, 5, 0] [[(2,(.split 27297817 [(1,(.raise [(10163,1)]))]))], [(2,(.split 82074541 [(1,(.raise [(339151,1)]))]))], [(2,(.split 7237 [(1,(.split 47 [(2,(.raise [(11,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered9069 : Range 9069 9093 :=
  scan_sound pool8805 pool8805_valid 5 9069 [3, 47, 43, 3, 29, 7, 3, 31, 5, 3, 61, 0] [[(2,(.split 367 [(2,(.raise [(3463,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9093 : Range 9093 9117 :=
  scan_sound pool8805 pool8805_valid 5 9093 [3, 5, 11, 3, 19, 0, 3, 7, 0, 3, 13, 5] [[(2,(.split 223 [(2,(.raise [(16651,1)]))]))], [(2,(.split 7069 [(1,(.split 43 [(2,(.raise [(631,1)]))]))]))]]
    (by decide) (by decide +kernel)

theorem covered9117 : Range 9117 9141 :=
  scan_sound pool8805 pool8805_valid 5 9117 [3, 11, 7, 3, 5, 0, 3, 23, 0, 3, 0, 13] [[(2,(.split 1461601 [(1,(.split 997 [(1,(.raise [(499,1)]))]))]))], [(2,(.split 380917 [(1,(.split 283 []))]))], [(2,(.split 12979 []))]]
    (by decide) (by decide +kernel)

theorem covered9141 : Range 9141 9165 :=
  scan_sound pool8805 pool8805_valid 5 9141 [3, 41, 5, 3, 7, 0, 3, 5, 0, 3, 0, 7] [[(2,(.split 3988093 [(1,(.split 181277 []))]))], [(2,(.split 27953269 [(1,(.raise [(164431,1)]))]))], [(2,(.split 6456391 []))]]
    (by decide) (by decide +kernel)

theorem covered9165 : Range 9165 9189 :=
  scan_sound pool8805 pool8805_valid 5 9165 [3, 89, 53, 3, 0, 5, 3, 67, 0, 3, 5, 0] [[(2,(.split 349183 []))], [(2,(.split 1423 []))], [(2,(.split 27397 [(1,(.raise [(103,1), (79,1), (19,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9189 : Range 9189 9213 :=
  scan_sound pool8805 pool8805_valid 5 9189 [3, 7, 29, 3, 17, 0, 3, 0, 5, 3, 0, 61] [[(2,(.split 28210267 []))], [(2,(.split 4458127 []))], [(2,(.split 12116413 [(1,(.raise [(4759,1)]))]))]]
    (by decide) (by decide +kernel)

theorem covered9213 : Range 9213 9237 :=
  scan_sound pool8805 pool8805_valid 5 9213 [3, 5, 13, 3, 0, 23, 3, 0, 11, 3, 7, 5] [[(2,(.split 16573 [(1,(.raise [(8287,1), (7,1)]))]))], [(2,(.split 823 []))]]
    (by decide) (by decide +kernel)

theorem covered9237 : Range 9237 9261 :=
  scan_sound pool8805 pool8805_valid 5 9237 [3, 0, 0, 3, 5, 7, 3, 11, 19, 3, 0, 47] [[(2,(.split 177481 [(1,(.split 88741 []))]))], [(2,(.split 3559 []))], [(2,(.split 309391 []))]]
    (by decide) (by decide +kernel)

theorem covered9261 : Range 9261 9285 :=
  scan_sound pool8805 pool8805_valid 5 9261 [3, 59, 5, 3, 13, 73, 3, 5, 0, 3, 0, 0] [[(2,(.split 4111 []))], [(2,(.split 4327 []))], [(2,(.split 22567 []))]]
    (by decide) (by decide +kernel)

theorem covered9285 : Range 9285 9309 :=
  scan_sound pool8805 pool8805_valid 5 9285 [3, 37, 7, 3, 0, 5, 3, 17, 71, 3, 5, 41] [[(2,(.split 12338449 [(1,(.split 246769 []))]))]]
    (by decide) (by decide +kernel)

theorem covered9309 : Range 9309 9317 :=
  scan_sound pool8805 pool8805_valid 5 9309 [3, 0, 67, 3] [[(2,(.split 6669541 [(1,(.split 1049 []))]))]]
    (by decide) (by decide +kernel)

theorem segment8805 : Range 8805 9317 := (range_join (range_join (range_join (range_join covered8805 covered8829) (range_join covered8853 (range_join covered8877 covered8901))) (range_join (range_join covered8925 (range_join covered8949 covered8973)) (range_join covered8997 (range_join covered9021 covered9045)))) (range_join (range_join (range_join covered9069 covered9093) (range_join covered9117 (range_join covered9141 covered9165))) (range_join (range_join covered9189 (range_join covered9213 covered9237)) (range_join covered9261 (range_join covered9285 covered9309)))))

theorem through9317 : Range 101 9317 := (range_join through8805 segment8805)

end OddPerfect.HarmonicChain.HarmonicRange101
