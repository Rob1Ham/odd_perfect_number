module

public import OddPerfect.SizePrimeBank300.Primes12
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf208 : PrimeBank := .leaf [15798461357509, 15933784794583, 16165035796957, 16176671303467, 16841848456579, 17342847747419, 17579386575067, 17748600316039, 17813680786663, 17993349570499, 18046347790267, 18132200719277, 18871143464293, 19063784705143, 19467484639261, 19731582134141]

theorem bankLeaf208_valid : bankLeaf208.Certified := by
  simp only [bankLeaf208, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 71773805381] }, .lucas { root := 2, primeFactors := [2, 5, 44773, 80153] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13, 41] }, .lucas { root := 3, primeFactors := [2, 43, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13901, 96905713] }, .lucas { root := 2, primeFactors := [2, 5, 139] }, .lucas { root := 5, primeFactors := [2, 3, 17, 118757] }, .lucas { root := 2, primeFactors := [2, 11, 2699] }, .lucas { root := 2, primeFactors := [2, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 12739, 11139071] }, .lucas { root := 2, primeFactors := [2, 3, 11, 193] }, .lucas { root := 11, primeFactors := [2, 5, 73, 15259] }, .lucas { root := 2, primeFactors := [2, 3, 2543] }, .lucas { root := 5, primeFactors := [2, 31, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 19, 211, 1009, 40819] }, .lucas { root := 3, primeFactors := [2, 3, 6803] }, .lucas { root := 2, primeFactors := [2, 19, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 17, 510083757277] }, .lucas { root := 2, primeFactors := [2, 3, 431, 98624083] }, .lucas { root := 3, primeFactors := [2, 3, 31, 530237] }, .lucas { root := 2, primeFactors := [2, 7, 29, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2929897762511] }, .lucas { root := 11, primeFactors := [2, 5, 401473, 729787] }, .lucas { root := 5, primeFactors := [2, 3, 17, 41] }, .lucas { root := 2, primeFactors := [2, 3, 121631] }, .lucas { root := 22, primeFactors := [2, 5, 12163] }, .lucas { root := 5, primeFactors := [2, 3, 2027] }, .lucas { root := 2, primeFactors := [2, 1013] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 53, 3295168477] }, .lucas { root := 2, primeFactors := [2, 3, 337, 814829] }, .lucas { root := 2, primeFactors := [2, 7, 29101] }, .lucas { root := 2, primeFactors := [2, 3, 5, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13723, 218530321] }, .lucas { root := 2, primeFactors := [2, 3, 2287] }, .lucas { root := 19, primeFactors := [2, 3, 127] }, .lucas { root := 41, primeFactors := [2, 3, 5, 523, 1741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23, 331, 9029, 9421] }, .lucas { root := 2, primeFactors := [2, 37, 61] }, .lucas { root := 2, primeFactors := [2, 3, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 41, 67, 163, 26407] }, .lucas { root := 5, primeFactors := [2, 3, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 41, 83, 933675419] }, .lucas { root := 2, primeFactors := [2, 13, 67, 71, 7549] }, .lucas { root := 2, primeFactors := [2, 3, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 23, 31, 233, 279007] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 2749, 358886543] }, .lucas { root := 6, primeFactors := [2, 3, 229] }, .lucas { root := 7, primeFactors := [2, 7, 29, 73, 12109] }, .lucas { root := 6, primeFactors := [2, 3, 1009] }]), by simp⟩

@[expose] noncomputable def bankLeaf209 : PrimeBank := .leaf [20343393309397, 20851336893943, 21293987317453, 21350651564197, 21414089265143, 21642230062111, 21856159267171, 22010861183683, 22125996444329, 22242194743981, 22730307345587, 22980733022201, 23039948849747, 23223849323621, 23565541864751, 24024775850869]

theorem bankLeaf209_valid : bankLeaf209.Certified := by
  simp only [bankLeaf209, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 283, 457, 13108093] }, .lucas { root := 5, primeFactors := [2, 3, 487, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 31, 127, 8291, 18121] }, .lucas { root := 2, primeFactors := [2, 5, 829] }, .lucas { root := 23, primeFactors := [2, 3, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 967, 4621, 14747] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 11] }, .lucas { root := 2, primeFactors := [2, 73, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 103058238391] }, .lucas { root := 11, primeFactors := [2, 3, 5, 19, 151, 773, 1549] }, .lucas { root := 2, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 728538642239] }, .lucas { root := 7, primeFactors := [2, 11, 37, 241, 3713737] }, .lucas { root := 5, primeFactors := [2, 3, 13, 11903] }, .lucas { root := 5, primeFactors := [2, 11, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 524068123421] }, .lucas { root := 2, primeFactors := [2, 5, 26203406171] }, .lucas { root := 2, primeFactors := [2, 5, 29, 53, 1704841] }, .lucas { root := 7, primeFactors := [2, 3, 5, 14207] }, .lucas { root := 5, primeFactors := [2, 7103] }, .lucas { root := 5, primeFactors := [2, 53, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 370703245733] }, .lucas { root := 2, primeFactors := [2, 92675811433] }, .lucas { root := 5, primeFactors := [2, 3, 3861492143] }, .lucas { root := 5, primeFactors := [2, 1930746071] }, .lucas { root := 7, primeFactors := [2, 5, 11, 911, 19267] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 761, 14934498913] }, .lucas { root := 5, primeFactors := [2, 3, 17, 47, 64901] }, .lucas { root := 2, primeFactors := [2, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 114903665111] }, .lucas { root := 7, primeFactors := [2, 5, 13, 3853, 229399] }, .lucas { root := 2, primeFactors := [2, 3, 107] }, .lucas { root := 7, primeFactors := [2, 3, 13, 17, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11519974424873] }, .lucas { root := 3, primeFactors := [2, 61, 139, 557, 304903] }, .lucas { root := 3, primeFactors := [2, 3, 13, 1303] }, .lucas { root := 6, primeFactors := [2, 3, 7, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 49121, 1918979] }, .lucas { root := 3, primeFactors := [2, 5, 307] }, .lucas { root := 2, primeFactors := [2, 959489] }, .lucas { root := 3, primeFactors := [2, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 154004973403] }, .lucas { root := 2, primeFactors := [2, 3, 7, 3666785081] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17, 367, 2099] }, .lucas { root := 2, primeFactors := [2, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]), by simp⟩

@[expose] noncomputable def bankLeaf210 : PrimeBank := .leaf [24837228904511, 25317725864513, 25322743716601, 26078086201549, 26185818869971, 27121758120683, 27647957545189, 27815217672493, 28552914124561, 30861871474787, 31479823396757, 31949284516627, 31964044249933, 32238400926181, 32528030679467, 32615913256463]

theorem bankLeaf210_valid : bankLeaf210.Certified := by
  simp only [bankLeaf210, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 131, 1723610611] }, .lucas { root := 2, primeFactors := [2, 3, 5, 1193, 5351] }, .lucas { root := 3, primeFactors := [2, 149] }, .lucas { root := 11, primeFactors := [2, 5, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 17, 2243, 100621] }, .lucas { root := 2, primeFactors := [2, 19, 59] }, .lucas { root := 18, primeFactors := [2, 3, 5, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1088777, 1995977] }, .lucas { root := 3, primeFactors := [2, 13, 19, 29] }, .lucas { root := 3, primeFactors := [2, 249497] }, .lucas { root := 5, primeFactors := [2, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 872860628999] }, .lucas { root := 7, primeFactors := [2, 401, 1088354899] }, .lucas { root := 2, primeFactors := [2, 3, 60464161] }, .lucas { root := 11, primeFactors := [2, 3, 5, 199, 211] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19, 11971, 3397003] }, .lucas { root := 10, primeFactors := [2, 3, 5, 7, 19] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29, 2789] }, .lucas { root := 2, primeFactors := [2, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 167, 2467, 13751] }, .lucas { root := 2, primeFactors := [2, 3, 137] }, .lucas { root := 11, primeFactors := [2, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 3889, 360712867] }, .lucas { root := 11, primeFactors := [2, 3] }, .lucas { root := 2, primeFactors := [2, 3, 479, 125509] }, .lucas { root := 2, primeFactors := [2, 3, 10459] }, .lucas { root := 2, primeFactors := [2, 3, 7, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 401, 32609, 407219] }, .lucas { root := 3, primeFactors := [2, 1019] }, .lucas { root := 2, primeFactors := [2, 7, 17, 29, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 59, 227, 257, 4219] }, .lucas { root := 2, primeFactors := [2, 3, 19, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 858313506749] }, .lucas { root := 2, primeFactors := [2, 19, 233, 48470381] }, .lucas { root := 10, primeFactors := [2, 5, 7, 346217] }, .lucas { root := 3, primeFactors := [2, 13, 3329] }, .lucas { root := 3, primeFactors := [2, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf211 : PrimeBank := .leaf [33038978287897, 34047782581661, 34276926782411, 35595178037371, 35909757982597, 36016625156983, 36094178999551, 36441801894643, 36825984292217, 37470919266199, 38160408950501, 38806310567851, 38934969278521, 41284013010997, 41292578210753, 41325067365823]

theorem bankLeaf211_valid : bankLeaf211.Certified := by
  simp only [bankLeaf211, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 277, 236655337] }, .lucas { root := 5, primeFactors := [2, 3, 19, 518981] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 203669, 8358607] }, .lucas { root := 2, primeFactors := [2, 59, 863] }, .lucas { root := 3, primeFactors := [2, 3, 154789] }, .lucas { root := 2, primeFactors := [2, 3, 12899] }, .lucas { root := 2, primeFactors := [2, 6449] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 13, 17, 15509921621] }, .lucas { root := 2, primeFactors := [2, 5, 775496081] }, .lucas { root := 3, primeFactors := [2, 5, 71, 136531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 103, 11069, 16519] }, .lucas { root := 2, primeFactors := [2, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }, .lucas { root := 3, primeFactors := [2, 3, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 241, 12416928763] }, .lucas { root := 2, primeFactors := [2, 3, 7, 677, 436693] }, .lucas { root := 2, primeFactors := [2, 3, 151, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 6002770859497] }, .lucas { root := 7, primeFactors := [2, 3, 271, 34182787] }, .lucas { root := 3, primeFactors := [2, 3, 11, 19, 27259] }, .lucas { root := 2, primeFactors := [2, 3, 7, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 4910772653] }, .lucas { root := 2, primeFactors := [2, 29, 71, 596257] }, .lucas { root := 5, primeFactors := [2, 3, 6211] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 21027451889] }, .lucas { root := 3, primeFactors := [2, 1314215743] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1759, 17789] }, .lucas { root := 6, primeFactors := [2, 3, 293] }, .lucas { root := 2, primeFactors := [2, 4447] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 17, 73, 757, 39341] }, .lucas { root := 2, primeFactors := [2, 5, 7, 281] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 23, 2550183931] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 37, 15629] }, .lucas { root := 2, primeFactors := [2, 3907] }, .lucas { root := 2, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 161923, 1575397] }, .lucas { root := 2, primeFactors := [2, 3, 26987] }, .lucas { root := 2, primeFactors := [2, 103, 131] }, .lucas { root := 2, primeFactors := [2, 3, 29, 503] }]), by simp⟩

@[expose] noncomputable def bankLeaf212 : PrimeBank := .leaf [41413832311099, 41865594655627, 41983564756831, 43489493991451, 43780498807753, 44353590379237, 45198750015791, 45692145853819, 47079202116283, 47285614651747, 47700750211981, 48032559288281, 48401662036451, 48439681604861, 48603603235441, 48645437568001]

theorem bankLeaf212_valid : bankLeaf212.Certified := by
  simp only [bankLeaf212, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 530946568091] }, .lucas { root := 2, primeFactors := [2, 5, 53094656809] }, .lucas { root := 11, primeFactors := [2, 3, 1667, 442367] }, .lucas { root := 2, primeFactors := [2, 7, 17] }, .lucas { root := 5, primeFactors := [2, 29, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 35117, 3153901] }, .lucas { root := 2, primeFactors := [2, 8779] }, .lucas { root := 11, primeFactors := [2, 3, 7, 11, 19] }, .lucas { root := 2, primeFactors := [2, 3, 5, 10513] }, .lucas { root := 7, primeFactors := [2, 3, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 13, 31, 61, 3931307] }, .lucas { root := 2, primeFactors := [2, 557, 3529] }, .lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 43, 2020141141] }, .lucas { root := 6, primeFactors := [2, 3, 5, 1759, 19141] }, .lucas { root := 6, primeFactors := [2, 3, 293] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 109, 594903031] }, .lucas { root := 6, primeFactors := [2, 3, 5, 41, 433, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 383, 240841637] }, .lucas { root := 2, primeFactors := [2, 7, 29, 179, 1657] }, .lucas { root := 11, primeFactors := [2, 3, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 313, 331, 1009, 10723] }, .lucas { root := 2, primeFactors := [2, 3, 1787] }, .lucas { root := 2, primeFactors := [2, 19, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 149, 5479, 210131] }, .lucas { root := 3, primeFactors := [2, 3, 11, 83] }, .lucas { root := 6, primeFactors := [2, 5, 21013] }, .lucas { root := 2, primeFactors := [2, 3, 17, 103] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17, 120430813] }, .lucas { root := 5, primeFactors := [2, 3, 10035901] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 59] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf213 : PrimeBank := .leaf [49918102555193, 50368445538589, 51193000249429, 51206126365213, 52230452374901, 52669702089469, 52812493022953, 52852004066809, 53221069258177, 53454996722401, 55747762232143, 56186222638043, 56468006409121, 56824611309311, 57335739644437, 59376284620771]

theorem bankLeaf213_valid : bankLeaf213.Certified := by
  simp only [bankLeaf213, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 6239762819399] }, .lucas { root := 7, primeFactors := [2, 19, 23, 7139316727] }, .lucas { root := 3, primeFactors := [2, 3, 132209569] }, .lucas { root := 11, primeFactors := [2, 3, 467, 983] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 281, 13327, 21977] }, .lucas { root := 3, primeFactors := [2, 3, 2221] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }, .lucas { root := 3, primeFactors := [2, 41, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 522304523749] }, .lucas { root := 2, primeFactors := [2, 3, 7, 39227, 52837] }, .lucas { root := 2, primeFactors := [2, 11, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }, .lucas { root := 2, primeFactors := [2, 3, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3877, 377365819] }, .lucas { root := 2, primeFactors := [2, 3, 17, 19] }, .lucas { root := 3, primeFactors := [2, 3, 139, 331, 1367] }, .lucas { root := 5, primeFactors := [2, 683] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 23, 179, 19810963] }, .lucas { root := 5, primeFactors := [2, 3, 67, 16427] }, .lucas { root := 2, primeFactors := [2, 43, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 61, 122814829] }, .lucas { root := 14, primeFactors := [2, 3, 3411523] }, .lucas { root := 2, primeFactors := [2, 3, 189529] }, .lucas { root := 22, primeFactors := [2, 3, 53, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 13, 59, 311, 13339] }, .lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 5, 13, 953, 458669879] }, .lucas { root := 13, primeFactors := [2, 457, 501827] }, .lucas { root := 2, primeFactors := [2, 13, 19301] }, .lucas { root := 2, primeFactors := [2, 5, 193] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf214 : PrimeBank := .leaf [61543768014103, 62316423268709, 62434548604903, 62911130477521, 66007803837179, 67123837929583, 67412764337119, 68633947703159, 69710210289691, 70150423768699, 70331254588753, 71316922984999, 71869647051217, 72777851643949, 73603473319847, 74584300382201]

theorem bankLeaf214_valid : bankLeaf214.Certified := by
  simp only [bankLeaf214, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 29, 2243, 14335501] }, .lucas { root := 2, primeFactors := [2, 19, 59] }, .lucas { root := 2, primeFactors := [2, 3, 5, 19, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2225586545311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 74186218177] }, .lucas { root := 13, primeFactors := [2, 3, 7, 55198079] }, .lucas { root := 17, primeFactors := [2, 13, 19, 29, 3853] }, .lucas { root := 2, primeFactors := [2, 3, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 16493, 630919669] }, .lucas { root := 2, primeFactors := [2, 7, 19, 31] }, .lucas { root := 2, primeFactors := [2, 3, 52576639] }, .lucas { root := 6, primeFactors := [2, 3, 8762773] }, .lucas { root := 2, primeFactors := [2, 3, 61, 11971] }, .lucas { root := 10, primeFactors := [2, 3, 5, 7, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 4714843131227] }, .lucas { root := 2, primeFactors := [2, 751, 3139043363] }, .lucas { root := 2, primeFactors := [2, 7, 13, 73, 191, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 59, 727, 4139983] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11, 29, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 73, 153910420861] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 83, 541, 8161] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 23, 439, 3398729707] }, .lucas { root := 2, primeFactors := [2, 3, 47, 148793] }, .lucas { root := 3, primeFactors := [2, 7, 2657] }, .lucas { root := 3, primeFactors := [2, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 23, 37, 41, 526049] }, .lucas { root := 3, primeFactors := [2, 17, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1465234470599] }, .lucas { root := 7, primeFactors := [2, 4231, 173154629] }, .lucas { root := 3, primeFactors := [2, 3, 5, 47] }, .lucas { root := 2, primeFactors := [2, 43288657] }, .lucas { root := 5, primeFactors := [2, 3, 541, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 125639, 567493] }, .lucas { root := 13, primeFactors := [2, 62819] }, .lucas { root := 2, primeFactors := [2, 7, 641] }, .lucas { root := 7, primeFactors := [2, 3, 19, 131] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 19, 1213, 121661] }, .lucas { root := 2, primeFactors := [2, 3, 101] }, .lucas { root := 2, primeFactors := [2, 5, 7, 11, 79] }]), by simp⟩

@[expose] noncomputable def bankLeaf215 : PrimeBank := .leaf [76682225834119, 77230798373051, 77395372480441, 77454079403707, 77581941314431, 78069955458259, 79236309623407, 80888727900887, 82753268919751, 83031235923439, 83446718075641, 85584439140289, 91011850411981, 91551857004271, 99207834129529, 99995282631947]

theorem bankLeaf215_valid : bankLeaf215.Certified := by
  simp only [bankLeaf215, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 4260123657451] }, .lucas { root := 2, primeFactors := [2, 3, 5, 53, 809, 220793] }, .lucas { root := 3, primeFactors := [2, 11, 13, 193] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 61, 3527, 20393] }, .lucas { root := 5, primeFactors := [2, 41, 43] }, .lucas { root := 3, primeFactors := [2, 2549] }, .lucas { root := 2, primeFactors := [2, 7, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 29, 12739235027] }, .lucas { root := 2, primeFactors := [2, 7, 19, 47891861] }, .lucas { root := 2, primeFactors := [2, 5, 53, 45181] }, .lucas { root := 2, primeFactors := [2, 3, 5, 251] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 827, 1228355651] }, .lucas { root := 2, primeFactors := [2, 5, 24567113] }, .lucas { root := 3, primeFactors := [2, 37, 82997] }, .lucas { root := 2, primeFactors := [2, 20749] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 24, primeFactors := [2, 3, 5, 11, 13, 257197417] }, .lucas { root := 15, primeFactors := [2, 3, 7, 1530937] }, .lucas { root := 10, primeFactors := [2, 3, 11, 1933] }, .lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 19, 72931, 302629] }, .lucas { root := 10, primeFactors := [2, 3, 5, 11, 13, 17] }, .lucas { root := 2, primeFactors := [2, 3, 25219] }, .lucas { root := 2, primeFactors := [2, 3, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 68687, 3374677] }, .lucas { root := 5, primeFactors := [2, 61, 563] }, .lucas { root := 5, primeFactors := [2, 3, 31247] }, .lucas { root := 5, primeFactors := [2, 17, 919] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 1516864173533] }, .lucas { root := 2, primeFactors := [2, 31, 863, 14174711] }, .lucas { root := 13, primeFactors := [2, 5, 11, 128861] }, .lucas { root := 3, primeFactors := [2, 5, 17, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 151, 193, 2685017] }, .lucas { root := 3, primeFactors := [2, 37, 47, 193] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf216 : PrimeBank := .leaf [101153235616801, 101797501228817, 102704422012531, 105647694227671, 106442138516353, 107331526897849, 114118662694961, 115512048133057, 116235975405131, 116446518124847, 117925236645991, 118912328583511, 118936780586461, 121012813720289, 127992782604139, 130281033796141]

theorem bankLeaf216_valid : bankLeaf216.Certified := by
  simp only [bankLeaf216, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 17, 22619, 109609] }, .lucas { root := 2, primeFactors := [2, 43, 263] }, .lucas { root := 14, primeFactors := [2, 3, 4567] }, .lucas { root := 3, primeFactors := [2, 3, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11933, 533172197] }, .lucas { root := 2, primeFactors := [2, 19, 157] }, .lucas { root := 2, primeFactors := [2, 10429, 12781] }, .lucas { root := 7, primeFactors := [2, 3, 11, 79] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 13, 313, 841356779] }, .lucas { root := 2, primeFactors := [2, 420678389] }, .lucas { root := 2, primeFactors := [2, 13, 47, 172127] }, .lucas { root := 5, primeFactors := [2, 89, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 503084258227] }, .lucas { root := 2, primeFactors := [2, 3, 11, 19, 263, 508471] }, .lucas { root := 15, primeFactors := [2, 3, 5, 17, 997] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 61, 122814829] }, .lucas { root := 14, primeFactors := [2, 3, 3411523] }, .lucas { root := 2, primeFactors := [2, 3, 189529] }, .lucas { root := 22, primeFactors := [2, 3, 53, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 11, 33811, 49811] }, .lucas { root := 15, primeFactors := [2, 3, 5, 7, 23] }, .lucas { root := 6, primeFactors := [2, 5, 17, 293] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 73, 677, 5437, 14629] }, .lucas { root := 5, primeFactors := [2, 3, 151] }, .lucas { root := 2, primeFactors := [2, 3, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 11, 31, 47, 89, 56711] }, .lucas { root := 7, primeFactors := [2, 5, 53, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 97, 12653, 538367] }, .lucas { root := 2, primeFactors := [2, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }, .lucas { root := 5, primeFactors := [2, 269183] }, .lucas { root := 5, primeFactors := [2, 134591] }, .lucas { root := 13, primeFactors := [2, 5, 43, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 540235775537] }, .lucas { root := 3, primeFactors := [2, 80669, 418559] }, .lucas { root := 2, primeFactors := [2, 7, 43, 67] }, .lucas { root := 7, primeFactors := [2, 7, 4271] }, .lucas { root := 7, primeFactors := [2, 5, 7, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2171350563269] }, .lucas { root := 2, primeFactors := [2, 5393, 100655969] }, .lucas { root := 3, primeFactors := [2, 337] }, .lucas { root := 3, primeFactors := [2, 7, 197, 2281] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19] }]), by simp⟩

@[expose] noncomputable def bankLeaf217 : PrimeBank := .leaf [134633676459019, 137476732909837, 138161295607249, 138167925546667, 140084304076289, 140300847537397, 141177405182927, 143872038649231, 147912020646589, 150019243780639, 153348667863557, 154702548132607, 154790744960881, 155054846734201, 155062027558931, 160006125892973]

theorem bankLeaf217_valid : bankLeaf217.Certified := by
  simp only [bankLeaf217, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 325343, 570001] }, .lucas { root := 5, primeFactors := [2, 162671] }, .lucas { root := 11, primeFactors := [2, 5, 16267] }, .lucas { root := 3, primeFactors := [2, 3, 2711] }, .lucas { root := 7, primeFactors := [2, 5, 271] }, .lucas { root := 28, primeFactors := [2, 3, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 479, 307259] }, .lucas { root := 2, primeFactors := [2, 7, 17, 1291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 23, 37, 41, 526049] }, .lucas { root := 3, primeFactors := [2, 17, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 71, 163, 293, 2973881] }, .lucas { root := 6, primeFactors := [2, 5, 7, 13, 19, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 73, 1061, 61917997] }, .lucas { root := 2, primeFactors := [2, 5, 53] }, .lucas { root := 6, primeFactors := [2, 3, 7, 737119] }, .lucas { root := 3, primeFactors := [2, 3, 31, 1321] }, .lucas { root := 13, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 15973, 23384161] }, .lucas { root := 7, primeFactors := [2, 3, 11] }, .lucas { root := 23, primeFactors := [2, 3, 5, 5413] }, .lucas { root := 5, primeFactors := [2, 3, 11, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 10663, 14210851] }, .lucas { root := 3, primeFactors := [2, 3, 1777] }, .lucas { root := 5, primeFactors := [2, 3, 37] }, .lucas { root := 2, primeFactors := [2, 3, 5, 211, 449] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 47, primeFactors := [2, 3, 5, 7, 61, 3527, 20393] }, .lucas { root := 5, primeFactors := [2, 41, 43] }, .lucas { root := 3, primeFactors := [2, 2549] }, .lucas { root := 2, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 23, 12503, 42793] }, .lucas { root := 5, primeFactors := [2, 7, 19, 47] }, .lucas { root := 5, primeFactors := [2, 3, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf218 : PrimeBank := .leaf [163065499816327, 164771988343271, 164853258892057, 166062471846877, 169299992707751, 170034833900341, 172110179118949, 172676809976347, 173087234930041, 178809055095947, 179972425963171, 180173340581797, 181345750520141, 182793085014437, 184254857174911, 185247563104753]

theorem bankLeaf218_valid : bankLeaf218.Certified := by
  simp only [bankLeaf218, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 21937, 1238892433] }, .lucas { root := 7, primeFactors := [2, 3, 457] }, .lucas { root := 5, primeFactors := [2, 3, 31, 61, 13649] }, .lucas { root := 3, primeFactors := [2, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 11, 213989595251] }, .lucas { root := 2, primeFactors := [2, 5, 17, 50350493] }, .lucas { root := 3, primeFactors := [2, 79, 159337] }, .lucas { root := 5, primeFactors := [2, 3, 2213] }, .lucas { root := 2, primeFactors := [2, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 2221, 3779, 38971] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }, .lucas { root := 2, primeFactors := [2, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }, .lucas { root := 2, primeFactors := [2, 3, 5, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 19, 72931, 302629] }, .lucas { root := 10, primeFactors := [2, 3, 5, 11, 13, 17] }, .lucas { root := 2, primeFactors := [2, 3, 25219] }, .lucas { root := 2, primeFactors := [2, 3, 467] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 41, 1033, 22303921] }, .lucas { root := 5, primeFactors := [2, 3, 43] }, .lucas { root := 7, primeFactors := [2, 3, 5, 199, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 181, 449, 4271, 5903] }, .lucas { root := 7, primeFactors := [2, 5, 7, 61] }, .lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 683, 31991, 33773] }, .lucas { root := 7, primeFactors := [2, 5, 7, 457] }, .lucas { root := 2, primeFactors := [2, 8443] }, .lucas { root := 2, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 67, 4231, 221227] }, .lucas { root := 3, primeFactors := [2, 3, 5, 47] }, .lucas { root := 2, primeFactors := [2, 3, 36871] }, .lucas { root := 15, primeFactors := [2, 3, 5, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 277, 31477, 40529] }, .lucas { root := 6, primeFactors := [2, 3, 43, 61] }, .lucas { root := 3, primeFactors := [2, 17, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 33749, 3118523] }, .lucas { root := 2, primeFactors := [2, 11, 13, 59] }, .lucas { root := 2, primeFactors := [2, 11, 229, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 227, 22047643243] }, .lucas { root := 2, primeFactors := [2, 3, 2477, 494497] }, .lucas { root := 2, primeFactors := [2, 619] }, .lucas { root := 15, primeFactors := [2, 3, 17, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 29, 12347, 9817411] }, .lucas { root := 2, primeFactors := [2, 6173] }, .lucas { root := 2, primeFactors := [2, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }, .lucas { root := 7, primeFactors := [2, 3, 5, 327247] }, .lucas { root := 3, primeFactors := [2, 3, 54541] }, .lucas { root := 2, primeFactors := [2, 3, 5, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 317, 997, 19433153] }, .lucas { root := 3, primeFactors := [2, 303643] }, .lucas { root := 2, primeFactors := [2, 3, 5623] }, .lucas { root := 5, primeFactors := [2, 3, 937] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf219 : PrimeBank := .leaf [186139085244311, 187051793464801, 187673266740451, 189396382956961, 191615024926373, 192091292916307, 195006165968459, 197340338942587, 198041655652411, 199592183280697, 201858430533847, 203011532805331, 204120268280977, 216207774081289, 219900698580377, 221112832862321]

theorem bankLeaf219_valid : bankLeaf219.Certified := by
  simp only [bankLeaf219, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 479, 6661, 530359] }, .lucas { root := 6, primeFactors := [2, 3, 5, 37] }, .lucas { root := 3, primeFactors := [2, 3, 37, 2389] }, .lucas { root := 2, primeFactors := [2, 3, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 17, 15436373] }, .lucas { root := 2, primeFactors := [2, 7, 11251] }, .lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 154183, 8114741] }, .lucas { root := 3, primeFactors := [2, 3, 7, 3671] }, .lucas { root := 13, primeFactors := [2, 5, 367] }, .lucas { root := 2, primeFactors := [2, 5, 151, 2687] }, .lucas { root := 5, primeFactors := [2, 17, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5023, 9536881591] }, .lucas { root := 3, primeFactors := [2, 3, 31] }, .lucas { root := 6, primeFactors := [2, 3, 5, 557, 190243] }, .lucas { root := 2, primeFactors := [2, 3, 13, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 113, 68399, 591739] }, .lucas { root := 7, primeFactors := [2, 11, 3109] }, .lucas { root := 6, primeFactors := [2, 3, 7, 37] }, .lucas { root := 2, primeFactors := [2, 3, 7, 73, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 67, 111943838099] }, .lucas { root := 2, primeFactors := [2, 14851, 3768899] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11] }, .lucas { root := 2, primeFactors := [2, 7, 29, 9283] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 73, 191, 37442759] }, .lucas { root := 7, primeFactors := [2, 23, 41, 19853] }, .lucas { root := 2, primeFactors := [2, 7, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 6601388521747] }, .lucas { root := 2, primeFactors := [2, 3, 2179, 5197, 97157] }, .lucas { root := 7, primeFactors := [2, 3, 11] }, .lucas { root := 7, primeFactors := [2, 3, 433] }, .lucas { root := 2, primeFactors := [2, 107, 227] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 4139, 1027423433] }, .lucas { root := 2, primeFactors := [2, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }, .lucas { root := 5, primeFactors := [2, 7, 23, 797689] }, .lucas { root := 11, primeFactors := [2, 3, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 11, 179, 3881, 130987] }, .lucas { root := 13, primeFactors := [2, 5, 97] }, .lucas { root := 5, primeFactors := [2, 3, 19, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 9029, 276760613] }, .lucas { root := 2, primeFactors := [2, 37, 61] }, .lucas { root := 2, primeFactors := [2, 17, 19, 214211] }, .lucas { root := 2, primeFactors := [2, 5, 31, 691] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
