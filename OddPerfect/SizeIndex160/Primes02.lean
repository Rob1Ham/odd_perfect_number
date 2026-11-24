module

public import OddPerfect.SizeIndex160.Primes01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.Size160

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf31 : PrimeBank := .leaf [77951, 78049, 79631, 84437, 84463, 84871, 86353, 86561, 89591, 89599, 90793, 91411, 93739, 93811, 95239, 95479]

theorem bankLeaf31_valid : bankLeaf31.Certified := by
  simp only [bankLeaf31, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7963] }, .lucas { root := 5, primeFactors := [2, 3, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 19, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 2011] }, .lucas { root := 3, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 109, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 53, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 15913] }, .lucas { root := 5, primeFactors := [2, 3, 13, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf32 : PrimeBank := .leaf [96493, 96911, 98561, 100621, 101051, 102673, 102913, 104179, 104281, 105337, 107719, 108541, 109537, 110563, 111919, 114769]

theorem bankLeaf32_valid : bankLeaf32.Certified := by
  simp only [bankLeaf32, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 18, primeFactors := [2, 3, 5, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 43, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 97, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 18427] }, .lucas { root := 2, primeFactors := [2, 3, 37, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 797] }]), by simp⟩

@[expose] noncomputable def bankLeaf33 : PrimeBank := .leaf [115327, 119321, 120157, 121001, 121267, 121921, 122167, 122921, 124249, 124633, 125683, 125731, 127189, 127709, 128341, 130423]

theorem bankLeaf33_valid : bankLeaf33.Certified := by
  simp only [bankLeaf33, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6737] }, .lucas { root := 3, primeFactors := [2, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 617] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 31, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 20947] }, .lucas { root := 3, primeFactors := [2, 3, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3533] }, .lucas { root := 2, primeFactors := [2, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 4561] }, .lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 21737] }, .lucas { root := 6, primeFactors := [2, 11, 13, 19] }]), by simp⟩

@[expose] noncomputable def bankLeaf34 : PrimeBank := .leaf [130447, 132607, 135281, 136417, 140731, 140813, 141623, 142231, 144751, 144941, 144967, 145381, 146033, 147029, 148513, 148663]

theorem bankLeaf34_valid : bankLeaf34.Certified := by
  simp only [bankLeaf34, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7247] }, .lucas { root := 5, primeFactors := [2, 3623] }, .lucas { root := 5, primeFactors := [2, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 53, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 19, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 4691] }, .lucas { root := 2, primeFactors := [2, 5, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 47, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7247] }, .lucas { root := 5, primeFactors := [2, 3623] }, .lucas { root := 5, primeFactors := [2, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2423] }, .lucas { root := 5, primeFactors := [2, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 9127] }, .lucas { root := 3, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 59, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf35 : PrimeBank := .leaf [151201, 152407, 153817, 155371, 161773, 162709, 163417, 163729, 165211, 166703, 169111, 172153, 176089, 176419, 178987, 179743]

theorem bankLeaf35_valid : bankLeaf35.Certified := by
  simp only [bankLeaf35, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 8467] }, .lucas { root := 2, primeFactors := [2, 3, 17, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 5179] }, .lucas { root := 2, primeFactors := [2, 3, 863] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 17, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 5507] }, .lucas { root := 2, primeFactors := [2, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 4903] }, .lucas { root := 3, primeFactors := [2, 3, 19, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 1879] }, .lucas { root := 6, primeFactors := [2, 3, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 11, 23, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 1297] }, .lucas { root := 10, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf36 : PrimeBank := .leaf [182713, 185167, 188011, 188137, 190097, 190261, 190793, 192343, 197101, 197887, 201499, 202183, 207469, 213337, 213881, 215143]

theorem bankLeaf36_valid : bankLeaf36.Certified := by
  simp only [bankLeaf36, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 23, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 2089] }, .lucas { root := 7, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 3407] }, .lucas { root := 5, primeFactors := [2, 13, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 32057] }, .lucas { root := 3, primeFactors := [2, 4007] }, .lucas { root := 5, primeFactors := [2, 2003] }, .lucas { root := 5, primeFactors := [2, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 43, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 43, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 2963] }, .lucas { root := 2, primeFactors := [2, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 5347] }, .lucas { root := 3, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf37 : PrimeBank := .leaf [217081, 222991, 225751, 226741, 230257, 241229, 249541, 250361, 253639, 260191, 264769, 269117, 280561, 283831, 286541, 286981]

theorem bankLeaf37_valid : bankLeaf37.Certified := by
  simp only [bankLeaf37, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7433] }, .lucas { root := 3, primeFactors := [2, 929] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 3779] }, .lucas { root := 2, primeFactors := [2, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 4639] }, .lucas { root := 3, primeFactors := [2, 3, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 4159] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 3541] }, .lucas { root := 7, primeFactors := [2, 3, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 9461] }, .lucas { root := 3, primeFactors := [2, 5, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 14327] }, .lucas { root := 5, primeFactors := [2, 13, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 4783] }, .lucas { root := 6, primeFactors := [2, 3, 797] }]), by simp⟩

@[expose] noncomputable def bankLeaf38 : PrimeBank := .leaf [292631, 293147, 293459, 297841, 301681, 306517, 309091, 311827, 316037, 318457, 321077, 332191, 337901, 340583, 351023, 352909]

theorem bankLeaf38_valid : bankLeaf38.Certified := by
  simp only [bankLeaf38, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 2251] }, .lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 20939] }, .lucas { root := 2, primeFactors := [2, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13339] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 17, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 41, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 10303] }, .lucas { root := 3, primeFactors := [2, 3, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 51971] }, .lucas { root := 2, primeFactors := [2, 5, 5197] }, .lucas { root := 7, primeFactors := [2, 3, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11287] }, .lucas { root := 3, primeFactors := [2, 3, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 4423] }, .lucas { root := 3, primeFactors := [2, 3, 11, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11467] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 3691] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 113, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 25073] }, .lucas { root := 3, primeFactors := [2, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9803] }, .lucas { root := 2, primeFactors := [2, 13, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf39 : PrimeBank := .leaf [356693, 360541, 360637, 360851, 363889, 377011, 384481, 386641, 389651, 398581, 399403, 401173, 414313, 415669, 424903, 427451]

theorem bankLeaf39_valid : bankLeaf39.Certified := by
  simp only [bankLeaf39, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 12739] }, .lucas { root := 2, primeFactors := [2, 3, 11, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 2003] }, .lucas { root := 5, primeFactors := [2, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 59, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7793] }, .lucas { root := 3, primeFactors := [2, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 22189] }, .lucas { root := 2, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 61, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 47, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 3079] }, .lucas { root := 6, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 83, 103] }]), by simp⟩

@[expose] noncomputable def bankLeaf40 : PrimeBank := .leaf [429227, 434977, 438833, 443227, 464941, 467431, 471161, 475483, 477209, 479971, 481153, 492103, 499159, 500153, 504011, 509221]

theorem bankLeaf40_valid : bankLeaf40.Certified := by
  simp only [bankLeaf40, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23, 31, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 27427] }, .lucas { root := 5, primeFactors := [2, 3, 7, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 61, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 15581] }, .lucas { root := 2, primeFactors := [2, 5, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11779] }, .lucas { root := 2, primeFactors := [2, 3, 13, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11321] }, .lucas { root := 3, primeFactors := [2, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 59651] }, .lucas { root := 2, primeFactors := [2, 5, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 5333] }, .lucas { root := 2, primeFactors := [2, 31, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 13, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 2521] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 101, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 3877] }, .lucas { root := 2, primeFactors := [2, 3, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 23, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf41 : PrimeBank := .leaf [522061, 529411, 531589, 538651, 541141, 545473, 548557, 558253, 558421, 562477, 567661, 593951, 612067, 613213, 617341, 620461]

theorem bankLeaf41_valid : bankLeaf41.Certified := by
  simp only [bankLeaf41, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 11, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 2521] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 1429] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 2689] }, .lucas { root := 19, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 2467] }, .lucas { root := 2, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 9461] }, .lucas { root := 3, primeFactors := [2, 5, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 1697] }, .lucas { root := 3, primeFactors := [2, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 137, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 10289] }, .lucas { root := 3, primeFactors := [2, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 383] }]), by simp⟩

@[expose] noncomputable def bankLeaf42 : PrimeBank := .leaf [621301, 622513, 635471, 638767, 649793, 650869, 653641, 688453, 699157, 715753, 728953, 732541, 740989, 751411, 752449, 765181]

theorem bankLeaf42_valid : bankLeaf42.Certified := by
  simp only [bankLeaf42, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 53, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 3943] }, .lucas { root := 3, primeFactors := [2, 3, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 73, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 103, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19421] }, .lucas { root := 3, primeFactors := [2, 5, 971] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 9941] }, .lucas { root := 2, primeFactors := [2, 5, 7, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 4339] }, .lucas { root := 10, primeFactors := [2, 3, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2287] }, .lucas { root := 19, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 3919] }, .lucas { root := 3, primeFactors := [2, 3, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 13, 109] }]), by simp⟩

@[expose] noncomputable def bankLeaf43 : PrimeBank := .leaf [782671, 785299, 785947, 794191, 797161, 800281, 801337, 822761, 827131, 830833, 837313, 861001, 863497, 877543, 895087, 897707]

theorem bankLeaf43_valid : bankLeaf43.Certified := by
  simp only [bankLeaf43, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 3727] }, .lucas { root := 3, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 7699] }, .lucas { root := 3, primeFactors := [2, 3, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 18713] }, .lucas { root := 3, primeFactors := [2, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 173, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 67, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 79, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 19, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 23, 6359] }, .lucas { root := 13, primeFactors := [2, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 49727] }, .lucas { root := 5, primeFactors := [2, 23, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 448853] }, .lucas { root := 2, primeFactors := [2, 112213] }, .lucas { root := 2, primeFactors := [2, 3, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]), by simp⟩

@[expose] noncomputable def bankLeaf44 : PrimeBank := .leaf [925669, 926659, 962543, 973001, 990151, 1007161, 1032851, 1034879, 1037681, 1049821, 1058821, 1077301, 1090927, 1097113, 1145371, 1147021]

theorem bankLeaf44_valid : bankLeaf44.Certified := by
  simp only [bankLeaf44, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2857] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 51481] }, .lucas { root := 17, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 7, 197, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 53, primeFactors := [2, 3, 5, 7, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 13, 53, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 17, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17497] }, .lucas { root := 5, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 2521] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 60607] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 2689] }, .lucas { root := 19, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 73, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 2731] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf45 : PrimeBank := .leaf [1159843, 1166323, 1222567, 1242217, 1244357, 1246591, 1248001, 1249121, 1250413, 1276657, 1282399, 1289513, 1315747, 1332979, 1347919, 1351093]

theorem bankLeaf45_valid : bankLeaf45.Certified := by
  simp only [bankLeaf45, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 83, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 6703] }, .lucas { root := 5, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 203761] }, .lucas { root := 11, primeFactors := [2, 3, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 113, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 37, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 79, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 26597] }, .lucas { root := 2, primeFactors := [2, 61, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 41, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 7, 23027] }, .lucas { root := 2, primeFactors := [2, 29, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 222163] }, .lucas { root := 2, primeFactors := [2, 3, 61, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 1571] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 37, 179] }]), by simp⟩

@[expose] noncomputable def bankLeaf46 : PrimeBank := .leaf [1371511, 1372537, 1376461, 1380277, 1445371, 1477807, 1491491, 1517297, 1528399, 1557433, 1578961, 1584941, 1599181, 1644691, 1667353, 1674289]

theorem bankLeaf46_valid : bankLeaf46.Certified := by
  simp only [bankLeaf46, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 2549] }, .lucas { root := 2, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 23, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 48179] }, .lucas { root := 6, primeFactors := [2, 13, 17, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 22391] }, .lucas { root := 13, primeFactors := [2, 5, 2239] }, .lucas { root := 3, primeFactors := [2, 3, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 37, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 19, 41, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 97, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11321] }, .lucas { root := 3, primeFactors := [2, 5, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 2423] }, .lucas { root := 5, primeFactors := [2, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 73, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 69473] }, .lucas { root := 3, primeFactors := [2, 13, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 11, 151] }]), by simp⟩

@[expose] noncomputable def bankLeaf47 : PrimeBank := .leaf [1682207, 1692283, 1692337, 1803647, 1805911, 1806113, 1814599, 1866461, 1866871, 1867147, 1876403, 1886503, 1888171, 1895599, 1909811, 1950391]

theorem bankLeaf47_valid : bankLeaf47.Certified := by
  simp only [bankLeaf47, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 841103] }, .lucas { root := 5, primeFactors := [2, 420551] }, .lucas { root := 17, primeFactors := [2, 5, 13, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 17, 47, 353] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 35257] }, .lucas { root := 7, primeFactors := [2, 3, 13, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 69371] }, .lucas { root := 2, primeFactors := [2, 5, 7, 991] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 3541] }, .lucas { root := 7, primeFactors := [2, 3, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 100811] }, .lucas { root := 2, primeFactors := [2, 5, 17, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 93323] }, .lucas { root := 2, primeFactors := [2, 29, 1609] }, .lucas { root := 7, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20743] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 43, 7237] }, .lucas { root := 2, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 19, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 229, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 62939] }, .lucas { root := 2, primeFactors := [2, 31469] }, .lucas { root := 2, primeFactors := [2, 7867] }, .lucas { root := 3, primeFactors := [2, 3, 19, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 53, 1987] }, .lucas { root := 2, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 27283] }, .lucas { root := 5, primeFactors := [2, 3, 4547] }, .lucas { root := 2, primeFactors := [2, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf48 : PrimeBank := .leaf [1956611, 1963111, 1964041, 1977917, 1983851, 2064077, 2117131, 2126431, 2164387, 2167621, 2172539, 2180921, 2212009, 2261827, 2289401, 2311333]

theorem bankLeaf48_valid : bankLeaf48.Certified := by
  simp only [bankLeaf48, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 23, 47, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 65437] }, .lucas { root := 6, primeFactors := [2, 3, 7, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 13, 1259] }, .lucas { root := 2, primeFactors := [2, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 29, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 3607] }, .lucas { root := 5, primeFactors := [2, 3, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 10531] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 70571] }, .lucas { root := 2, primeFactors := [2, 5, 7057] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 23627] }, .lucas { root := 2, primeFactors := [2, 11813] }, .lucas { root := 2, primeFactors := [2, 2953] }, .lucas { root := 13, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 29, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 113, 9613] }, .lucas { root := 2, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 37, 47, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 29, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11447] }, .lucas { root := 5, primeFactors := [2, 59, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 192611] }, .lucas { root := 18, primeFactors := [2, 5, 11, 17, 103] }]), by simp⟩

@[expose] noncomputable def bankLeaf49 : PrimeBank := .leaf [2374591, 2409829, 2426789, 2468269, 2537551, 2538097, 2608387, 2661961, 2692801, 2746609, 2775389, 2780923, 2860237, 2884621, 2941691, 3156161]

theorem bankLeaf49_valid : bankLeaf49.Certified := by
  simp only [bankLeaf49, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 79153] }, .lucas { root := 10, primeFactors := [2, 3, 17, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 409, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 59, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 23, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 5639] }, .lucas { root := 7, primeFactors := [2, 2819] }, .lucas { root := 2, primeFactors := [2, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 19, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 39521] }, .lucas { root := 3, primeFactors := [2, 5, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 3169] }, .lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 57221] }, .lucas { root := 2, primeFactors := [2, 5, 2861] }, .lucas { root := 2, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 9011] }, .lucas { root := 2, primeFactors := [2, 5, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 269, 1723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 79451] }, .lucas { root := 6, primeFactors := [2, 5, 7, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 131, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 294169] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]), by simp⟩

@[expose] noncomputable def bankLeaf50 : PrimeBank := .leaf [3206171, 3348577, 3409261, 3556843, 3563501, 3641611, 3658159, 3679789, 3981071, 4010597, 4015513, 4017023, 4060339, 4091671, 4100539, 4107029]

theorem bankLeaf50_valid : bankLeaf50.Certified := by
  simp only [bankLeaf50, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 29147] }, .lucas { root := 2, primeFactors := [2, 13, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 56821] }, .lucas { root := 6, primeFactors := [2, 3, 5, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 34871] }, .lucas { root := 7, primeFactors := [2, 5, 11, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7127] }, .lucas { root := 5, primeFactors := [2, 7, 509] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17341] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 29033] }, .lucas { root := 3, primeFactors := [2, 19, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 71, 617] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 19, 23, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 113, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 43, 1297] }, .lucas { root := 10, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29, 69259] }, .lucas { root := 2, primeFactors := [2, 3, 7, 17, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 35617] }, .lucas { root := 11, primeFactors := [2, 3, 7, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 4133] }, .lucas { root := 2, primeFactors := [2, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 52571] }, .lucas { root := 2, primeFactors := [2, 5, 7, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1026757] }, .lucas { root := 2, primeFactors := [2, 3, 3169] }, .lucas { root := 7, primeFactors := [2, 3, 11] }]), by simp⟩

end OddPerfect.IndexComponent.Size160
