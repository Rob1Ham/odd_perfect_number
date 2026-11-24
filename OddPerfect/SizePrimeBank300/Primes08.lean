module

public import OddPerfect.SizePrimeBank300.Primes07
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf140 : PrimeBank := .leaf [246793303, 248875867, 249470743, 250088941, 250590853, 250801819, 253154329, 254322041, 257051021, 257057869, 258357403, 258785941, 259858993, 262209281, 262878787, 265837681]

theorem bankLeaf140_valid : bankLeaf140.Certified := by
  simp only [bankLeaf140, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 71, 563] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 1389383] }, .lucas { root := 5, primeFactors := [2, 701, 991] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19, 79309] }, .lucas { root := 2, primeFactors := [2, 3, 2203] }, .lucas { root := 5, primeFactors := [2, 3, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 23, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 269, 47779] }, .lucas { root := 3, primeFactors := [2, 3, 7963] }, .lucas { root := 5, primeFactors := [2, 3, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 21421489] }, .lucas { root := 13, primeFactors := [2, 3, 11, 29, 1399] }, .lucas { root := 13, primeFactors := [2, 3, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 47, 16073] }, .lucas { root := 3, primeFactors := [2, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 616157] }, .lucas { root := 2, primeFactors := [2, 31, 4969] }, .lucas { root := 11, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 146317] }, .lucas { root := 2, primeFactors := [2, 3, 89, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 859081] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7159] }, .lucas { root := 3, primeFactors := [2, 3, 1193] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf141 : PrimeBank := .leaf [266112779, 267270691, 268088311, 271895803, 276763169, 277158841, 278218153, 279131659, 280257881, 284733023, 284758421, 284841523, 295225751, 297903607, 301471069, 302313163]

theorem bankLeaf141_valid : bankLeaf141.Certified := by
  simp only [bankLeaf141, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 47, 211, 13417] }, .lucas { root := 5, primeFactors := [2, 3, 13, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1051, 43117] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }, .lucas { root := 2, primeFactors := [2, 3, 3593] }, .lucas { root := 3, primeFactors := [2, 449] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 329951] }, .lucas { root := 19, primeFactors := [2, 5, 6599] }, .lucas { root := 13, primeFactors := [2, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 347, 10313] }, .lucas { root := 3, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 2905439] }, .lucas { root := 11, primeFactors := [2, 383, 3793] }, .lucas { root := 5, primeFactors := [2, 3, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 67, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 25122589] }, .lucas { root := 2, primeFactors := [2, 3, 67, 31247] }, .lucas { root := 5, primeFactors := [2, 17, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 37, 499, 2729] }, .lucas { root := 3, primeFactors := [2, 11, 31] }]), by simp⟩

@[expose] noncomputable def bankLeaf142 : PrimeBank := .leaf [303529829, 304213471, 304410611, 305175781, 306758461, 307977209, 310897033, 312410911, 315242227, 316950847, 317931301, 320373271, 320694229, 323352761, 329422297, 329984299]

theorem bankLeaf142_valid : bankLeaf142.Certified := by
  simp only [bankLeaf142, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 71, 152681] }, .lucas { root := 3, primeFactors := [2, 5, 11, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 17, 211, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 223, 19501] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 977, 5233] }, .lucas { root := 10, primeFactors := [2, 3, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 263, 1901] }, .lucas { root := 2, primeFactors := [2, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 167, 2689] }, .lucas { root := 19, primeFactors := [2, 3, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 15359] }, .lucas { root := 11, primeFactors := [2, 7, 1097] }, .lucas { root := 3, primeFactors := [2, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 72647] }, .lucas { root := 5, primeFactors := [2, 7, 5189] }, .lucas { root := 2, primeFactors := [2, 1297] }, .lucas { root := 10, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 989797] }, .lucas { root := 2, primeFactors := [2, 3, 82483] }, .lucas { root := 2, primeFactors := [2, 3, 59, 233] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2618923] }, .lucas { root := 2, primeFactors := [2, 3, 19, 22973] }, .lucas { root := 2, primeFactors := [2, 5743] }, .lucas { root := 10, primeFactors := [2, 3, 11, 29] }]), by simp⟩

@[expose] noncomputable def bankLeaf143 : PrimeBank := .leaf [336095857, 337708039, 338841859, 343965353, 352536911, 353461951, 362764543, 367735663, 367792309, 369023021, 370385167, 376939231, 378361939, 379687663, 389916367, 392376151]

theorem bankLeaf143_valid : bankLeaf143.Certified := by
  simp only [bankLeaf143, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2333999] }, .lucas { root := 13, primeFactors := [2, 17, 19, 3613] }, .lucas { root := 2, primeFactors := [2, 3, 7, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 19, 29, 6029] }, .lucas { root := 2, primeFactors := [2, 11, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 137, 18461] }, .lucas { root := 2, primeFactors := [2, 5, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 11, 1549, 2069] }, .lucas { root := 2, primeFactors := [2, 3, 43] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 157, 5003] }, .lucas { root := 2, primeFactors := [2, 41, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 31, 53, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 2918537] }, .lucas { root := 3, primeFactors := [2, 97, 3761] }, .lucas { root := 3, primeFactors := [2, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 31, 101, 251] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 61730861] }, .lucas { root := 2, primeFactors := [2, 5, 223, 13841] }, .lucas { root := 6, primeFactors := [2, 5, 173] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47, 28547] }, .lucas { root := 2, primeFactors := [2, 7, 2039] }, .lucas { root := 7, primeFactors := [2, 1019] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19, 488617] }, .lucas { root := 5, primeFactors := [2, 3, 20359] }, .lucas { root := 11, primeFactors := [2, 3, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 41, 139] }]), by simp⟩

@[expose] noncomputable def bankLeaf144 : PrimeBank := .leaf [393452473, 396045497, 399451777, 399929489, 404573891, 405307681, 405313411, 412450637, 414810691, 416255023, 419460841, 420149893, 427884607, 428810647, 434312371, 438417391]

theorem bankLeaf144_valid : bankLeaf144.Certified := by
  simp only [bankLeaf144, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 2341979] }, .lucas { root := 2, primeFactors := [2, 19, 61631] }, .lucas { root := 11, primeFactors := [2, 5, 6163] }, .lucas { root := 3, primeFactors := [2, 3, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 642931] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29, 739] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 83, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 17, 29, 7243] }, .lucas { root := 2, primeFactors := [2, 3, 17, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 825661] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 43, 73, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 929, 14543] }, .lucas { root := 5, primeFactors := [2, 11, 661] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23125279] }, .lucas { root := 3, primeFactors := [2, 3, 11, 53, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 911, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 2339, 14969] }, .lucas { root := 2, primeFactors := [2, 7, 167] }, .lucas { root := 3, primeFactors := [2, 1871] }, .lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 29, 157, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 4825693] }, .lucas { root := 6, primeFactors := [2, 3, 134047] }, .lucas { root := 6, primeFactors := [2, 3, 11, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 14613913] }, .lucas { root := 10, primeFactors := [2, 3, 29, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]), by simp⟩

@[expose] noncomputable def bankLeaf145 : PrimeBank := .leaf [451473481, 466344409, 475800499, 477869921, 478880543, 480960559, 486315301, 501178511, 518332453, 518386877, 521402591, 522541321, 527135461, 527532101, 534239119, 534697747]

theorem bankLeaf145_valid : bankLeaf145.Certified := by
  simp only [bankLeaf145, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 418031] }, .lucas { root := 11, primeFactors := [2, 5, 17, 2459] }, .lucas { root := 2, primeFactors := [2, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 953, 27737] }, .lucas { root := 3, primeFactors := [2, 3467] }, .lucas { root := 2, primeFactors := [2, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 37, 18517] }, .lucas { root := 6, primeFactors := [2, 3, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1229, 1319] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 7, 23, 311291] }, .lucas { root := 2, primeFactors := [2, 5, 7, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 1061, 3701] }, .lucas { root := 2, primeFactors := [2, 5, 53] }, .lucas { root := 2, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 47, 8039] }, .lucas { root := 11, primeFactors := [2, 4019] }, .lucas { root := 2, primeFactors := [2, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 109, 478351] }, .lucas { root := 3, primeFactors := [2, 3, 5, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 7, 622073] }, .lucas { root := 3, primeFactors := [2, 11, 7069] }, .lucas { root := 2, primeFactors := [2, 3, 19, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 310313] }, .lucas { root := 3, primeFactors := [2, 79, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 347, 4073] }, .lucas { root := 3, primeFactors := [2, 509] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 8101481] }, .lucas { root := 3, primeFactors := [2, 5, 337, 601] }]), by simp⟩

@[expose] noncomputable def bankLeaf146 : PrimeBank := .leaf [536701327, 545392189, 549568273, 552006661, 554317681, 557437421, 557828389, 560286943, 562036049, 573663131, 575709019, 577515739, 584398351, 585604027, 588744487, 596514349]

theorem bankLeaf146_valid : bankLeaf146.Certified := by
  simp only [bankLeaf146, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 31, 412213] }, .lucas { root := 5, primeFactors := [2, 3, 34351] }, .lucas { root := 3, primeFactors := [2, 3, 5, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 19, 173, 419] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 329951] }, .lucas { root := 19, primeFactors := [2, 5, 6599] }, .lucas { root := 13, primeFactors := [2, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 29, 961099] }, .lucas { root := 3, primeFactors := [2, 3, 160183] }, .lucas { root := 3, primeFactors := [2, 3, 11, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 1191941] }, .lucas { root := 2, primeFactors := [2, 5, 61, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 93381157] }, .lucas { root := 2, primeFactors := [2, 3, 11, 235811] }, .lucas { root := 2, primeFactors := [2, 5, 23581] }, .lucas { root := 6, primeFactors := [2, 3, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 17, 295187] }, .lucas { root := 5, primeFactors := [2, 37, 3989] }, .lucas { root := 2, primeFactors := [2, 997] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 3374489] }, .lucas { root := 3, primeFactors := [2, 13, 71, 457] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 95951503] }, .lucas { root := 5, primeFactors := [2, 3, 17, 313567] }, .lucas { root := 5, primeFactors := [2, 3, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 1979, 2861] }, .lucas { root := 2, primeFactors := [2, 23, 43] }, .lucas { root := 2, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 37, 35099] }, .lucas { root := 2, primeFactors := [2, 7, 23, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 61, 109, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 29, 102533] }, .lucas { root := 2, primeFactors := [2, 25633] }, .lucas { root := 5, primeFactors := [2, 3, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf147 : PrimeBank := .leaf [599437081, 599737009, 604842197, 612415423, 612928711, 623089081, 628652797, 633530171, 642661823, 652271327, 656276671, 680963417, 684842713, 692888543, 695370101, 696451621]

theorem bankLeaf147_valid : bankLeaf147.Certified := by
  simp only [bankLeaf147, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 11, 19, 31, 257] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 277, 122827] }, .lucas { root := 5, primeFactors := [2, 3, 11, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 263, 6581] }, .lucas { root := 14, primeFactors := [2, 5, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 167, 313699] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 13, 23, 30269] }, .lucas { root := 3, primeFactors := [2, 7, 23, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 193, 151357] }, .lucas { root := 2, primeFactors := [2, 3, 12613] }, .lucas { root := 2, primeFactors := [2, 3, 1051] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 293, 159013] }, .lucas { root := 6, primeFactors := [2, 3, 7, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 29, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 12160061] }, .lucas { root := 2, primeFactors := [2, 5, 11, 31, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 18233909] }, .lucas { root := 2, primeFactors := [2, 7, 11, 53, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 151, 46051] }, .lucas { root := 3, primeFactors := [2, 3, 5, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11607527] }, .lucas { root := 5, primeFactors := [2, 7, 101, 8209] }, .lucas { root := 7, primeFactors := [2, 3, 19] }]), by simp⟩

@[expose] noncomputable def bankLeaf148 : PrimeBank := .leaf [699906607, 700047031, 708196039, 709140083, 710955781, 712782407, 716452609, 716930839, 723397193, 744660883, 759273457, 762566461, 768091447, 776311381, 786645889, 796625303]

theorem bankLeaf148_valid : bankLeaf148.Certified := by
  simp only [bankLeaf148, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 421, 1721] }, .lucas { root := 3, primeFactors := [2, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 37, 607, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 199, 254537] }, .lucas { root := 3, primeFactors := [2, 31817] }, .lucas { root := 3, primeFactors := [2, 41, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53, 179, 1249] }, .lucas { root := 7, primeFactors := [2, 3, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 50913029] }, .lucas { root := 2, primeFactors := [2, 17, 109, 6869] }, .lucas { root := 2, primeFactors := [2, 17, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 37, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 19, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 108553] }, .lucas { root := 5, primeFactors := [2, 3, 4523] }, .lucas { root := 5, primeFactors := [2, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 73, 4261] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 15818197] }, .lucas { root := 2, primeFactors := [2, 3, 1318183] }, .lucas { root := 3, primeFactors := [2, 3, 19, 31, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 79, 160879] }, .lucas { root := 3, primeFactors := [2, 3, 26813] }, .lucas { root := 2, primeFactors := [2, 6703] }, .lucas { root := 5, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1901, 22447] }, .lucas { root := 2, primeFactors := [2, 5, 19] }, .lucas { root := 3, primeFactors := [2, 3, 29, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 59, 5623] }, .lucas { root := 5, primeFactors := [2, 3, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 311, 941] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 29, 661, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]), by simp⟩

@[expose] noncomputable def bankLeaf149 : PrimeBank := .leaf [809292571, 817018003, 817170061, 822628111, 826632619, 826729801, 828561571, 829621381, 831794981, 834019001, 834669361, 848697683, 849840193, 853390763, 861235321, 877398919]

theorem bankLeaf149_valid : bankLeaf149.Certified := by
  simp only [bankLeaf149, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 677, 39847] }, .lucas { root := 5, primeFactors := [2, 3, 29, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 53, 97, 109] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 27420937] }, .lucas { root := 7, primeFactors := [2, 3, 1142539] }, .lucas { root := 2, primeFactors := [2, 3, 109, 1747] }, .lucas { root := 2, primeFactors := [2, 3, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 83, 1277] }, .lucas { root := 2, primeFactors := [2, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2689, 10271] }, .lucas { root := 19, primeFactors := [2, 3, 7] }, .lucas { root := 7, primeFactors := [2, 5, 13, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 59, 131, 5381] }, .lucas { root := 3, primeFactors := [2, 5, 269] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 18401] }, .lucas { root := 3, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 60621263] }, .lucas { root := 5, primeFactors := [2, 13, 2331587] }, .lucas { root := 2, primeFactors := [2, 139, 8387] }, .lucas { root := 2, primeFactors := [2, 7, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 569, 2593] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 43, 101, 3061] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf150 : PrimeBank := .leaf [903518491, 911193301, 916224583, 917087137, 938710207, 942060617, 947220577, 947239753, 955921051, 989955251, 1001523179, 1002091357, 1015015789, 1021193837, 1024823381, 1037358851]

theorem bankLeaf150_valid : bankLeaf150.Certified := by
  simp only [bankLeaf150, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 29, 148361] }, .lucas { root := 3, primeFactors := [2, 5, 3709] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 67, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 1678067] }, .lucas { root := 2, primeFactors := [2, 13, 233, 277] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 16822511] }, .lucas { root := 19, primeFactors := [2, 5, 1682251] }, .lucas { root := 3, primeFactors := [2, 3, 5, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 9866881] }, .lucas { root := 7, primeFactors := [2, 3, 5, 571] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 373, 1523] }, .lucas { root := 2, primeFactors := [2, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1277, 22079] }, .lucas { root := 2, primeFactors := [2, 11, 29] }, .lucas { root := 7, primeFactors := [2, 7, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 19, 23, 44939] }, .lucas { root := 2, primeFactors := [2, 22469] }, .lucas { root := 2, primeFactors := [2, 41, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf151 : PrimeBank := .leaf [1065192899, 1069395493, 1079852201, 1087954603, 1092087791, 1094522287, 1100739151, 1112084671, 1114998887, 1117871311, 1119494113, 1128748349, 1139535451, 1144863931, 1158061627, 1176597091]

theorem bankLeaf151_valid : bankLeaf151.Certified := by
  simp only [bankLeaf151, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 6916837] }, .lucas { root := 5, primeFactors := [2, 3, 19, 23, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 8101481] }, .lucas { root := 3, primeFactors := [2, 5, 337, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 251, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 1126247] }, .lucas { root := 5, primeFactors := [2, 11, 51193] }, .lucas { root := 5, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 53, 2060543] }, .lucas { root := 5, primeFactors := [2, 11, 229, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 1275667] }, .lucas { root := 5, primeFactors := [2, 3, 7, 4339] }, .lucas { root := 10, primeFactors := [2, 3, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 223, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 37069489] }, .lucas { root := 22, primeFactors := [2, 3, 28603] }, .lucas { root := 2, primeFactors := [2, 3, 7, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 31, 137, 149, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 37262377] }, .lucas { root := 5, primeFactors := [2, 3, 167, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 359, 2953] }, .lucas { root := 13, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 3100957] }, .lucas { root := 2, primeFactors := [2, 3, 258413] }, .lucas { root := 2, primeFactors := [2, 7, 11, 839] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 778819] }, .lucas { root := 2, primeFactors := [2, 3, 129803] }, .lucas { root := 2, primeFactors := [2, 64901] }, .lucas { root := 2, primeFactors := [2, 5, 11, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41, 71, 499] }]), by simp⟩

@[expose] noncomputable def bankLeaf152 : PrimeBank := .leaf [1205235307, 1205476469, 1209166601, 1220002291, 1226758987, 1277623381, 1281388837, 1299754273, 1303315891, 1308017119, 1346733637, 1350760001, 1353753013, 1362395539, 1377020431, 1383576521]

theorem bankLeaf152_valid : bankLeaf152.Certified := by
  simp only [bankLeaf152, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 137, 157, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 43052731] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 439, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 29, 163, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 347579] }, .lucas { root := 2, primeFactors := [2, 7, 11, 37, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 251, 3121] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 1935793] }, .lucas { root := 5, primeFactors := [2, 3, 4481] }, .lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 1173433] }, .lucas { root := 5, primeFactors := [2, 3, 13, 3761] }, .lucas { root := 3, primeFactors := [2, 5, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 479, 90697] }, .lucas { root := 5, primeFactors := [2, 3, 3779] }, .lucas { root := 2, primeFactors := [2, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 1151, 5119] }, .lucas { root := 17, primeFactors := [2, 5, 23] }, .lucas { root := 3, primeFactors := [2, 3, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 112227803] }, .lucas { root := 2, primeFactors := [2, 811, 69191] }, .lucas { root := 11, primeFactors := [2, 5, 11, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 33769] }, .lucas { root := 11, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 89, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 23557] }, .lucas { root := 5, primeFactors := [2, 3, 13, 151] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 37, 113, 8273] }, .lucas { root := 3, primeFactors := [2, 11, 47] }]), by simp⟩

@[expose] noncomputable def bankLeaf153 : PrimeBank := .leaf [1396830683, 1399045519, 1399927283, 1405482289, 1446260951, 1472381413, 1478526139, 1493913401, 1501489387, 1512597319, 1514770111, 1567696597, 1570630777, 1577431459, 1577535103, 1579264051]

theorem bankLeaf153_valid : bankLeaf153.Certified := by
  simp only [bankLeaf153, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 23, 259949] }, .lucas { root := 2, primeFactors := [2, 13, 4999] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 5081, 10597] }, .lucas { root := 3, primeFactors := [2, 5, 127] }, .lucas { root := 5, primeFactors := [2, 3, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 7, 19, 4493] }, .lucas { root := 2, primeFactors := [2, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 229, 126311] }, .lucas { root := 23, primeFactors := [2, 5, 17, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 113, 1085827] }, .lucas { root := 2, primeFactors := [2, 3, 7, 103, 251] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 6203, 21061] }, .lucas { root := 2, primeFactors := [2, 7, 443] }, .lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 457643] }, .lucas { root := 2, primeFactors := [2, 41, 5581] }, .lucas { root := 6, primeFactors := [2, 3, 5, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 22699] }, .lucas { root := 12, primeFactors := [2, 3, 13, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf154 : PrimeBank := .leaf [1580015219, 1588537271, 1590315431, 1626784531, 1642640371, 1644512641, 1647035419, 1648480921, 1657268111, 1663002277, 1670214331, 1686024841, 1699421291, 1727870509, 1738389269, 1740100459]

theorem bankLeaf154_valid : bankLeaf154.Certified := by
  simp only [bankLeaf154, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 5, 10093, 15739] }, .lucas { root := 2, primeFactors := [2, 3, 29] }, .lucas { root := 2, primeFactors := [2, 3, 43, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 14457413] }, .lucas { root := 2, primeFactors := [2, 17, 107, 1987] }, .lucas { root := 2, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 7746593] }, .lucas { root := 3, primeFactors := [2, 7, 34583] }, .lucas { root := 5, primeFactors := [2, 17291] }, .lucas { root := 6, primeFactors := [2, 5, 7, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 193, 40529] }, .lucas { root := 3, primeFactors := [2, 17, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 43, 19919] }, .lucas { root := 7, primeFactors := [2, 23, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1367, 28687] }, .lucas { root := 5, primeFactors := [2, 683] }, .lucas { root := 6, primeFactors := [2, 3, 7, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 3319, 4139] }, .lucas { root := 6, primeFactors := [2, 3, 7, 79] }, .lucas { root := 2, primeFactors := [2, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 37, 59, 89, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 83, 128437] }, .lucas { root := 5, primeFactors := [2, 3, 7, 11, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 687331] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 43, 193, 1693] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 127, 191161] }, .lucas { root := 28, primeFactors := [2, 3, 5, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 19, 42437] }, .lucas { root := 2, primeFactors := [2, 103] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
