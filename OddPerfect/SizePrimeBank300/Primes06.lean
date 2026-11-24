module

public import OddPerfect.SizePrimeBank300.Primes05
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf107 : PrimeBank := .leaf [7616881, 7731517, 7738781, 7794023, 7795811, 7834583, 7857781, 7908811, 7926241, 7998827, 8024927, 8045221, 8111291, 8136281, 8242697, 8252681]

theorem bankLeaf107_valid : bankLeaf107.Certified := by
  simp only [bankLeaf107, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 71, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 29, 1709] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 167, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1013, 3847] }, .lucas { root := 5, primeFactors := [2, 3, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 131, 541] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 53, 353] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 33053] }, .lucas { root := 2, primeFactors := [2, 8263] }, .lucas { root := 3, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 6299] }, .lucas { root := 2, primeFactors := [2, 47, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 134087] }, .lucas { root := 5, primeFactors := [2, 67043] }, .lucas { root := 2, primeFactors := [2, 33521] }, .lucas { root := 6, primeFactors := [2, 5, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 19, 3881] }, .lucas { root := 13, primeFactors := [2, 5, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 107, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 193, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]), by simp⟩

@[expose] noncomputable def bankLeaf108 : PrimeBank := .leaf [8267393, 8344043, 8368123, 8369947, 8381161, 8401397, 8454841, 8460677, 8484181, 8490763, 8515321, 8566849, 8576317, 8599579, 8617627, 8627893]

theorem bankLeaf108_valid : bankLeaf108.Certified := by
  simp only [bankLeaf108, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 9227] }, .lucas { root := 2, primeFactors := [2, 7, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 35059] }, .lucas { root := 10, primeFactors := [2, 3, 5843] }, .lucas { root := 2, primeFactors := [2, 23, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 28463] }, .lucas { root := 5, primeFactors := [2, 7, 19, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 11923] }, .lucas { root := 5, primeFactors := [2, 3, 1987] }, .lucas { root := 2, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 31, 751] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 302167] }, .lucas { root := 5, primeFactors := [2, 3, 16787] }, .lucas { root := 2, primeFactors := [2, 7, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 141403] }, .lucas { root := 3, primeFactors := [2, 3, 23567] }, .lucas { root := 5, primeFactors := [2, 11783] }, .lucas { root := 5, primeFactors := [2, 43, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 79, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 6451] }, .lucas { root := 3, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 107, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 34033] }, .lucas { root := 7, primeFactors := [2, 3, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 110251] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 11677] }, .lucas { root := 2, primeFactors := [2, 3, 7, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 7901] }, .lucas { root := 2, primeFactors := [2, 5, 79] }]), by simp⟩

@[expose] noncomputable def bankLeaf109 : PrimeBank := .leaf [8682437, 8845231, 8932457, 8933917, 8935049, 8970971, 9034453, 9105457, 9151031, 9170881, 9183799, 9227497, 9254689, 9327281, 9382501, 9466799]

theorem bankLeaf109_valid : bankLeaf109.Certified := by
  simp only [bankLeaf109, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 310087] }, .lucas { root := 7, primeFactors := [2, 3, 7, 23, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31, 9511] }, .lucas { root := 3, primeFactors := [2, 3, 5, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 85889] }, .lucas { root := 3, primeFactors := [2, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 744493] }, .lucas { root := 2, primeFactors := [2, 3, 7, 8863] }, .lucas { root := 3, primeFactors := [2, 3, 7, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 41, 27241] }, .lucas { root := 17, primeFactors := [2, 3, 5, 227] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 35851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 189697] }, .lucas { root := 5, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 130729] }, .lucas { root := 29, primeFactors := [2, 3, 13, 419] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 3019] }, .lucas { root := 2, primeFactors := [2, 3, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 384479] }, .lucas { root := 7, primeFactors := [2, 192239] }, .lucas { root := 11, primeFactors := [2, 277, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 149, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 31, 3761] }, .lucas { root := 3, primeFactors := [2, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf110 : PrimeBank := .leaf [9600433, 9780821, 9843907, 9901391, 9946789, 10050613, 10065821, 10067741, 10114393, 10165373, 10196539, 10275301, 10366691, 10378063, 10541359, 10561409]

theorem bankLeaf110_valid : bankLeaf110.Certified := by
  simp only [bankLeaf110, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 200009] }, .lucas { root := 3, primeFactors := [2, 23, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 19, 3677] }, .lucas { root := 2, primeFactors := [2, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 523, 3137] }, .lucas { root := 3, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 103, 9613] }, .lucas { root := 2, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 828899] }, .lucas { root := 2, primeFactors := [2, 7, 59207] }, .lucas { root := 5, primeFactors := [2, 7, 4229] }, .lucas { root := 2, primeFactors := [2, 7, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 5857] }, .lucas { root := 7, primeFactors := [2, 3, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 26489] }, .lucas { root := 3, primeFactors := [2, 7, 11, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 29611] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 421433] }, .lucas { root := 3, primeFactors := [2, 11, 4789] }, .lucas { root := 2, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 43, 8443] }, .lucas { root := 2, primeFactors := [2, 3, 7, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1036669] }, .lucas { root := 2, primeFactors := [2, 3, 86389] }, .lucas { root := 2, primeFactors := [2, 3, 23, 313] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 271, 2161] }, .lucas { root := 23, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 577] }]), by simp⟩

@[expose] noncomputable def bankLeaf111 : PrimeBank := .leaf [10688807, 10723561, 10828777, 10835701, 10857851, 10908731, 11172199, 11235533, 11373751, 11382361, 11445877, 11509789, 11552213, 11556431, 11721781, 11725981]

theorem bankLeaf111_valid : bankLeaf111.Certified := by
  simp only [bankLeaf111, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 34, primeFactors := [2, 3, 5, 89363] }, .lucas { root := 5, primeFactors := [2, 7, 13, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 43, 1499] }, .lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 17, 89, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1862033] }, .lucas { root := 3, primeFactors := [2, 29, 4013] }, .lucas { root := 2, primeFactors := [2, 17, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 36479] }, .lucas { root := 7, primeFactors := [2, 13, 23, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 8623] }, .lucas { root := 3, primeFactors := [2, 3, 479] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 959149] }, .lucas { root := 14, primeFactors := [2, 3, 83, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 31, 13309] }, .lucas { root := 6, primeFactors := [2, 3, 1109] }, .lucas { root := 2, primeFactors := [2, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 5, 17, 67979] }, .lucas { root := 2, primeFactors := [2, 41, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 27919] }, .lucas { root := 3, primeFactors := [2, 3, 11, 47] }]), by simp⟩

@[expose] noncomputable def bankLeaf112 : PrimeBank := .leaf [11731409, 11794063, 11896771, 11929039, 12040843, 12188089, 12207031, 12349039, 12395041, 12533041, 12535769, 12570541, 12648613, 12833941, 12865927, 12881171]

theorem bankLeaf112_valid : bankLeaf112.Certified := by
  simp only [bankLeaf112, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 56401] }, .lucas { root := 13, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 280811] }, .lucas { root := 2, primeFactors := [2, 5, 28081] }, .lucas { root := 19, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 23327] }, .lucas { root := 5, primeFactors := [2, 107, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 61, 2963] }, .lucas { root := 2, primeFactors := [2, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 11, 1399] }, .lucas { root := 13, primeFactors := [2, 3, 233] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 17, 67, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 113, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53, 59, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 62003] }, .lucas { root := 2, primeFactors := [2, 29, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1288117] }, .lucas { root := 11, primeFactors := [2, 3, 11927] }, .lucas { root := 5, primeFactors := [2, 67, 89] }]), by simp⟩

@[expose] noncomputable def bankLeaf113 : PrimeBank := .leaf [13004671, 13049611, 13097927, 13109357, 13342393, 13351537, 13475851, 13493071, 13573249, 13630919, 13693571, 13794607, 13840121, 14061661, 14073559, 14092193]

theorem bankLeaf113_valid : bankLeaf113.Certified := by
  simp only [bankLeaf113, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 61927] }, .lucas { root := 3, primeFactors := [2, 3, 10321] }, .lucas { root := 7, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 62141] }, .lucas { root := 2, primeFactors := [2, 5, 13, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 263, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 23, 97, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 23, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 8429] }, .lucas { root := 2, primeFactors := [2, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 89839] }, .lucas { root := 7, primeFactors := [2, 3, 7, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 8819] }, .lucas { root := 2, primeFactors := [2, 4409] }, .lucas { root := 3, primeFactors := [2, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 13, 2719] }, .lucas { root := 3, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 7, 139091] }, .lucas { root := 2, primeFactors := [2, 5, 7, 1987] }, .lucas { root := 2, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 11317] }, .lucas { root := 2, primeFactors := [2, 3, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 109481] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 49429] }, .lucas { root := 2, primeFactors := [2, 3, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 234361] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf114 : PrimeBank := .leaf [14252401, 14321189, 14373901, 14374663, 14597959, 14613541, 14723179, 14737117, 14794651, 14833963, 15221321, 15251867, 15302827, 15317513, 15326501, 15631591]

theorem bankLeaf114_valid : bankLeaf114.Certified := by
  simp only [bankLeaf114, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 37, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 59, 8669] }, .lucas { root := 2, primeFactors := [2, 11, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 15971] }, .lucas { root := 2, primeFactors := [2, 5, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 14327] }, .lucas { root := 5, primeFactors := [2, 13, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 1499, 1637] }, .lucas { root := 2, primeFactors := [2, 7, 107] }, .lucas { root := 2, primeFactors := [2, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 769, 1597] }, .lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 13, 17, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 380533] }, .lucas { root := 2, primeFactors := [2, 3, 19, 1669] }, .lucas { root := 2, primeFactors := [2, 3, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 11, 61, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 273527] }, .lucas { root := 5, primeFactors := [2, 11, 12433] }, .lucas { root := 13, primeFactors := [2, 3, 7, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 30, primeFactors := [2, 3, 5, 13, 149, 269] }]), by simp⟩

@[expose] noncomputable def bankLeaf115 : PrimeBank := .leaf [15637651, 15852481, 16075303, 16127389, 16141189, 16244999, 16256839, 16267271, 16441151, 16585171, 16630193, 16668401, 17069453, 17174221, 17263699, 17299603]

theorem bankLeaf115_valid : bankLeaf115.Certified := by
  simp only [bankLeaf115, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 53, 281] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 359, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 447983] }, .lucas { root := 5, primeFactors := [2, 19, 11789] }, .lucas { root := 2, primeFactors := [2, 7, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 97, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 11, 37, 2851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 37, 43, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 449, 3623] }, .lucas { root := 5, primeFactors := [2, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 78977] }, .lucas { root := 3, primeFactors := [2, 617] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1039387] }, .lucas { root := 2, primeFactors := [2, 3, 211, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 5953] }, .lucas { root := 7, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 43, 99241] }, .lucas { root := 11, primeFactors := [2, 3, 5, 827] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 103, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2877283] }, .lucas { root := 2, primeFactors := [2, 3, 17761] }, .lucas { root := 19, primeFactors := [2, 3, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 11047] }, .lucas { root := 3, primeFactors := [2, 3, 7, 263] }]), by simp⟩

@[expose] noncomputable def bankLeaf116 : PrimeBank := .leaf [17423267, 17534591, 17559739, 17884211, 17996831, 18074731, 18137543, 18160339, 18198601, 18267551, 18376499, 18404653, 18414499, 18432461, 18480001, 18919391]

theorem bankLeaf116_valid : bankLeaf116.Certified := by
  simp only [bankLeaf116, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 19, 3853] }, .lucas { root := 2, primeFactors := [2, 3, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 1753459] }, .lucas { root := 2, primeFactors := [2, 3, 7, 83, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 43, 463] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 61, 163, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 643, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 31, 292541] }, .lucas { root := 2, primeFactors := [2, 5, 14627] }, .lucas { root := 2, primeFactors := [2, 71, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 432389] }, .lucas { root := 2, primeFactors := [2, 11, 31, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 19, 41, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 179, 7333] }, .lucas { root := 6, primeFactors := [2, 3, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 219103] }, .lucas { root := 6, primeFactors := [2, 3, 13, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3069083] }, .lucas { root := 2, primeFactors := [2, 43, 127, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 47, 19609] }, .lucas { root := 13, primeFactors := [2, 3, 19, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 38611] }, .lucas { root := 3, primeFactors := [2, 3, 5, 11, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf117 : PrimeBank := .leaf [18982297, 19087279, 19218301, 19295839, 19322789, 19405739, 19506889, 19587401, 19981303, 20143639, 20241187, 20305777, 20381027, 20437301, 20505409, 20515909]

theorem bankLeaf117_valid : bankLeaf117.Certified := by
  simp only [bankLeaf117, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 87881] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 29, 15671] }, .lucas { root := 13, primeFactors := [2, 5, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1071991] }, .lucas { root := 3, primeFactors := [2, 3, 5, 43, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 97, 49801] }, .lucas { root := 13, primeFactors := [2, 3, 5, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 17, 53, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 17, 15937] }, .lucas { root := 7, primeFactors := [2, 3, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 11, 302747] }, .lucas { root := 6, primeFactors := [2, 19, 31, 257] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 19, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 37, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf118 : PrimeBank := .leaf [20933761, 21075451, 21275323, 21520451, 21567673, 21631691, 21728981, 22199431, 22205857, 22260629, 22406023, 22431271, 22608881, 22812947, 22822493, 22867937]

theorem bankLeaf118_valid : bankLeaf118.Certified := by
  simp only [bankLeaf118, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 10903] }, .lucas { root := 3, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 53, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 6703] }, .lucas { root := 5, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 61487] }, .lucas { root := 5, primeFactors := [2, 71, 433] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 257, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 11939] }, .lucas { root := 2, primeFactors := [2, 47, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 67271] }, .lucas { root := 14, primeFactors := [2, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 89, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 19, 22531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 751] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 263, 2843] }, .lucas { root := 2, primeFactors := [2, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 5, 7, 47, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 17, 51613] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 74099] }, .lucas { root := 2, primeFactors := [2, 37049] }, .lucas { root := 6, primeFactors := [2, 11, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13, 7853] }, .lucas { root := 2, primeFactors := [2, 13, 151] }]), by simp⟩

@[expose] noncomputable def bankLeaf119 : PrimeBank := .leaf [22926121, 22996651, 23083783, 23159681, 23408353, 23451457, 23469599, 23594437, 23615827, 23655641, 23795861, 24756481, 24969491, 25294999, 25384507, 25426091]

theorem bankLeaf119_valid : bankLeaf119.Certified := by
  simp only [bankLeaf119, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 103981] }, .lucas { root := 6, primeFactors := [2, 3, 5, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 17449] }, .lucas { root := 14, primeFactors := [2, 3, 727] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 19, 719, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 71, 181] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 591391] }, .lucas { root := 3, primeFactors := [2, 3, 5, 6571] }, .lucas { root := 3, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 9833] }, .lucas { root := 3, primeFactors := [2, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 23, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 4215833] }, .lucas { root := 3, primeFactors := [2, 53, 61, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 2542609] }, .lucas { root := 19, primeFactors := [2, 3, 17657] }, .lucas { root := 3, primeFactors := [2, 2207] }, .lucas { root := 5, primeFactors := [2, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf120 : PrimeBank := .leaf [25524791, 25902229, 25953493, 25979311, 26010319, 26099221, 26131453, 26456251, 26610109, 26644367, 27763969, 28015921, 28674229, 28841317, 28878847, 28952731]

theorem bankLeaf120_valid : bankLeaf120.Certified := by
  simp only [bankLeaf120, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17839] }, .lucas { root := 6, primeFactors := [2, 3, 991] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 29, 41, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 43, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 467, 4663] }, .lucas { root := 3, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 16673] }, .lucas { root := 3, primeFactors := [2, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 37, 51437] }, .lucas { root := 2, primeFactors := [2, 7, 11, 167] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 217229] }, .lucas { root := 2, primeFactors := [2, 11, 4937] }, .lucas { root := 3, primeFactors := [2, 617] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 19, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 11093] }, .lucas { root := 2, primeFactors := [2, 47, 59] }]), by simp⟩

@[expose] noncomputable def bankLeaf121 : PrimeBank := .leaf [29037121, 29279959, 29482223, 29718701, 29763857, 29845969, 29866451, 30048643, 30068491, 30300731, 30687997, 30885607, 31012561, 31029319, 31114073, 31438357]

theorem bankLeaf121_valid : bankLeaf121.Certified := by
  simp only [bankLeaf121, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 7, 29, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4879993] }, .lucas { root := 7, primeFactors := [2, 3, 13, 15641] }, .lucas { root := 3, primeFactors := [2, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 3907] }, .lucas { root := 2, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 11, 27017] }, .lucas { root := 5, primeFactors := [2, 11, 307] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 373, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 128413] }, .lucas { root := 2, primeFactors := [2, 3, 29, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 53, 18911] }, .lucas { root := 14, primeFactors := [2, 5, 31, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 311, 9743] }, .lucas { root := 5, primeFactors := [2, 4871] }, .lucas { root := 11, primeFactors := [2, 5, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2557333] }, .lucas { root := 5, primeFactors := [2, 3, 877] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1715867] }, .lucas { root := 2, primeFactors := [2, 313, 2741] }, .lucas { root := 2, primeFactors := [2, 5, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 131, 2699] }, .lucas { root := 2, primeFactors := [2, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 461, 5683] }, .lucas { root := 2, primeFactors := [2, 3, 947] }]), by simp⟩

@[expose] noncomputable def bankLeaf122 : PrimeBank := .leaf [32009891, 32292739, 32668561, 33034273, 33048947, 33136801, 33319243, 33425173, 33453179, 33728111, 33999967, 34199239, 34210243, 34702823, 34714793, 35047559]

theorem bankLeaf122_valid : bankLeaf122.Certified := by
  simp only [bankLeaf122, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1794041] }, .lucas { root := 3, primeFactors := [2, 5, 44851] }, .lucas { root := 10, primeFactors := [2, 3, 5, 13, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 101, 3407] }, .lucas { root := 5, primeFactors := [2, 13, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 61, 38699] }, .lucas { root := 2, primeFactors := [2, 11, 1759] }, .lucas { root := 6, primeFactors := [2, 3, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 13807] }, .lucas { root := 5, primeFactors := [2, 3, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 56093] }, .lucas { root := 2, primeFactors := [2, 37, 379] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 17, 23, 3889] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13, 401, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 11, 13, 17, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 225343] }, .lucas { root := 3, primeFactors := [2, 3, 13, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 31, 19997] }, .lucas { root := 2, primeFactors := [2, 4999] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 14813] }, .lucas { root := 2, primeFactors := [2, 7, 23] }]), by simp⟩

@[expose] noncomputable def bankLeaf123 : PrimeBank := .leaf [35142721, 35941459, 36065947, 36314543, 36565673, 36855109, 37369771, 37514419, 37680901, 38272603, 38533987, 38647753, 38748851, 38786029, 38903141, 39628009]

theorem bankLeaf123_valid : bankLeaf123.Certified := by
  simp only [bankLeaf123, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 28, primeFactors := [2, 3, 5, 36607] }, .lucas { root := 3, primeFactors := [2, 3, 6101] }, .lucas { root := 2, primeFactors := [2, 5, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 858713] }, .lucas { root := 3, primeFactors := [2, 107339] }, .lucas { root := 6, primeFactors := [2, 7, 11, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 271, 6091] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 31963] }, .lucas { root := 2, primeFactors := [2, 3, 7, 761] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 53, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 113, 55331] }, .lucas { root := 2, primeFactors := [2, 5, 11, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 43, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 6378767] }, .lucas { root := 5, primeFactors := [2, 3189383] }, .lucas { root := 5, primeFactors := [2, 7, 409, 557] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 13, 11261] }, .lucas { root := 2, primeFactors := [2, 5, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 110711] }, .lucas { root := 17, primeFactors := [2, 5, 11071] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 31, 3691] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 26209] }, .lucas { root := 11, primeFactors := [2, 3, 7, 13] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
