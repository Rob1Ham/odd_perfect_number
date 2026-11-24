module

public import OddPerfect.SizePrimeBank300.Primes11
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf195 : PrimeBank := .leaf [1348929011257, 1350244511299, 1385051186569, 1385484666361, 1394813567261, 1407376241059, 1409655816661, 1446219454153, 1476372844561, 1511140989109, 1528366755967, 1535874355681, 1542487131851, 1552757273887, 1553418542761, 1559802835441]

theorem bankLeaf195_valid : bankLeaf195.Certified := by
  simp only [bankLeaf195, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 179, 2207, 8369] }, .lucas { root := 5, primeFactors := [2, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }, .lucas { root := 3, primeFactors := [2, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 31, 27813713] }, .lucas { root := 3, primeFactors := [2, 1738357] }, .lucas { root := 2, primeFactors := [2, 3, 31, 4673] }, .lucas { root := 3, primeFactors := [2, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 7, 19, 53, 430897] }, .lucas { root := 10, primeFactors := [2, 3, 47, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 53, 227, 389, 2467] }, .lucas { root := 2, primeFactors := [2, 3, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31189, 7520687] }, .lucas { root := 13, primeFactors := [2, 3, 23, 113] }, .lucas { root := 5, primeFactors := [2, 29, 127, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 83, 241, 12907] }, .lucas { root := 2, primeFactors := [2, 3, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 173, 2531, 12511] }, .lucas { root := 2, primeFactors := [2, 5, 11, 23] }, .lucas { root := 3, primeFactors := [2, 3, 5, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 1319, 4663801] }, .lucas { root := 13, primeFactors := [2, 659] }, .lucas { root := 23, primeFactors := [2, 3, 5, 2591] }, .lucas { root := 7, primeFactors := [2, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 125928415759] }, .lucas { root := 3, primeFactors := [2, 3, 5689, 3689237] }, .lucas { root := 11, primeFactors := [2, 3, 79] }, .lucas { root := 2, primeFactors := [2, 922309] }, .lucas { root := 2, primeFactors := [2, 3, 151, 509] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 3067, 83054383] }, .lucas { root := 2, primeFactors := [2, 3, 7, 73] }, .lucas { root := 3, primeFactors := [2, 3, 13842397] }, .lucas { root := 5, primeFactors := [2, 3, 29, 13259] }, .lucas { root := 6, primeFactors := [2, 7, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 4457, 102559] }, .lucas { root := 3, primeFactors := [2, 557] }, .lucas { root := 3, primeFactors := [2, 3, 17093] }, .lucas { root := 2, primeFactors := [2, 4273] }, .lucas { root := 5, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 4407106091] }, .lucas { root := 2, primeFactors := [2, 5, 440710609] }, .lucas { root := 7, primeFactors := [2, 3, 13, 706267] }, .lucas { root := 3, primeFactors := [2, 3, 11, 29, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 18269, 118583] }, .lucas { root := 2, primeFactors := [2, 4567] }, .lucas { root := 3, primeFactors := [2, 3, 761] }, .lucas { root := 5, primeFactors := [2, 211, 281] }]), by simp⟩

@[expose] noncomputable def bankLeaf196 : PrimeBank := .leaf [1567624160569, 1567693701851, 1599246406441, 1610473313497, 1650922227287, 1653850268201, 1670048579431, 1690099754311, 1700044120501, 1755966521167, 1760756191423, 1765899395563, 1771353309631, 1780754182741, 1781434578409, 1812511449097]

theorem bankLeaf196_valid : bankLeaf196.Certified := by
  simp only [bankLeaf196, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47, 307, 4526833] }, .lucas { root := 5, primeFactors := [2, 3, 94309] }, .lucas { root := 6, primeFactors := [2, 3, 29, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 37, 53, 197, 277, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 1451, 3061579] }, .lucas { root := 2, primeFactors := [2, 5, 29] }, .lucas { root := 11, primeFactors := [2, 3, 13, 39251] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 131, 181, 2830039] }, .lucas { root := 3, primeFactors := [2, 3, 471673] }, .lucas { root := 13, primeFactors := [2, 3, 6551] }, .lucas { root := 17, primeFactors := [2, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 67, 857, 1493, 9629] }, .lucas { root := 2, primeFactors := [2, 373] }, .lucas { root := 2, primeFactors := [2, 29, 83] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 1707171469] }, .lucas { root := 2, primeFactors := [2, 3, 142264289] }, .lucas { root := 3, primeFactors := [2, 113, 39343] }, .lucas { root := 3, primeFactors := [2, 3, 79, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 47, 157, 13963] }, .lucas { root := 3, primeFactors := [2, 3, 13, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 2046581027] }, .lucas { root := 5, primeFactors := [2, 7, 59, 2477701] }, .lucas { root := 2, primeFactors := [2, 3, 5, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 257123, 1141319] }, .lucas { root := 2, primeFactors := [2, 59, 2179] }, .lucas { root := 7, primeFactors := [2, 3, 11] }, .lucas { root := 7, primeFactors := [2, 570659] }, .lucas { root := 2, primeFactors := [2, 11, 25939] }, .lucas { root := 3, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 259411, 1134557] }, .lucas { root := 2, primeFactors := [2, 3, 5, 8647] }, .lucas { root := 3, primeFactors := [2, 3, 11, 131] }, .lucas { root := 2, primeFactors := [2, 283639] }, .lucas { root := 6, primeFactors := [2, 3, 41, 1153] }, .lucas { root := 5, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 47, 1256278943] }, .lucas { root := 5, primeFactors := [2, 139, 4518989] }, .lucas { root := 2, primeFactors := [2, 1129747] }, .lucas { root := 2, primeFactors := [2, 3, 188291] }, .lucas { root := 2, primeFactors := [2, 5, 19, 991] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 1127183737] }, .lucas { root := 5, primeFactors := [2, 3, 7, 131, 51217] }, .lucas { root := 5, primeFactors := [2, 3, 11, 97] }]), by simp⟩

@[expose] noncomputable def bankLeaf197 : PrimeBank := .leaf [1824910918879, 1832934561331, 1861441475983, 1900421426047, 1923437047717, 1944241638571, 1957650063931, 1959224382721, 1991951243371, 1997660229043, 2005553791141, 2020300327691, 2033125998091, 2046284382253, 2049790620979, 2104305482273]

theorem bankLeaf197_valid : bankLeaf197.Certified := by
  simp only [bankLeaf197, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 619, 5194951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 59, 587] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 1097, 2864969] }, .lucas { root := 3, primeFactors := [2, 137] }, .lucas { root := 3, primeFactors := [2, 29, 53, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11, 17, 41, 402517] }, .lucas { root := 5, primeFactors := [2, 3, 3727] }, .lucas { root := 3, primeFactors := [2, 3, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 11, 15461051] }, .lucas { root := 2, primeFactors := [2, 5, 11, 28111] }, .lucas { root := 3, primeFactors := [2, 3, 5, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 379, 482627] }, .lucas { root := 2, primeFactors := [2, 241313] }, .lucas { root := 3, primeFactors := [2, 7541] }, .lucas { root := 2, primeFactors := [2, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 173, 1924528159] }, .lucas { root := 3, primeFactors := [2, 3, 7, 2633, 5801] }, .lucas { root := 3, primeFactors := [2, 7, 47] }, .lucas { root := 3, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 89, 2939, 7517] }, .lucas { root := 2, primeFactors := [2, 13, 113] }, .lucas { root := 2, primeFactors := [2, 1879] }, .lucas { root := 6, primeFactors := [2, 3, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 269317, 750157] }, .lucas { root := 2, primeFactors := [2, 3, 7481] }, .lucas { root := 6, primeFactors := [2, 5, 11, 17] }, .lucas { root := 2, primeFactors := [2, 3, 11, 5683] }, .lucas { root := 2, primeFactors := [2, 3, 947] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 98999, 156589] }, .lucas { root := 19, primeFactors := [2, 49499] }, .lucas { root := 2, primeFactors := [2, 24749] }, .lucas { root := 2, primeFactors := [2, 23, 269] }, .lucas { root := 2, primeFactors := [2, 3, 13049] }, .lucas { root := 3, primeFactors := [2, 7, 233] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 53, 177249451] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 29, 5821] }, .lucas { root := 6, primeFactors := [2, 3, 5, 97] }]), by simp⟩

@[expose] noncomputable def bankLeaf198 : PrimeBank := .leaf [2119910228171, 2128693124521, 2133300501401, 2158316902961, 2168798562241, 2190130430567, 2202194614231, 2246354414917, 2277499309493, 2277528080279, 2281485885577, 2283461629543, 2288137482121, 2307145143731, 2314462327501, 2317501006871]

theorem bankLeaf198_valid : bankLeaf198.Certified := by
  simp only [bankLeaf198, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7, 30284431831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 103, 179, 18251] }, .lucas { root := 2, primeFactors := [2, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 5913036457] }, .lucas { root := 7, primeFactors := [2, 3, 246376519] }, .lucas { root := 3, primeFactors := [2, 3, 29, 1415957] }, .lucas { root := 2, primeFactors := [2, 19, 31, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 10859, 982273] }, .lucas { root := 2, primeFactors := [2, 61, 89] }, .lucas { root := 5, primeFactors := [2, 3, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 19, 2441, 202921] }, .lucas { root := 6, primeFactors := [2, 5, 61] }, .lucas { root := 14, primeFactors := [2, 3, 5, 19, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 13841, 361481] }, .lucas { root := 6, primeFactors := [2, 5, 173] }, .lucas { root := 3, primeFactors := [2, 5, 7, 1291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 17, 71, 1019, 34381] }, .lucas { root := 6, primeFactors := [2, 3, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 31, 87870103] }, .lucas { root := 3, primeFactors := [2, 3, 14645017] }, .lucas { root := 10, primeFactors := [2, 3, 67801] }, .lucas { root := 11, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 4708459477] }, .lucas { root := 2, primeFactors := [2, 3, 7, 6228121] }, .lucas { root := 46, primeFactors := [2, 3, 5, 17, 43, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 113, 2730929] }, .lucas { root := 3, primeFactors := [2, 23, 41, 181] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf199 : PrimeBank := .leaf [2343895350169, 2387363771591, 2429110801861, 2443845485863, 2521087073569, 2549488493329, 2549755542947, 2623108622527, 2663272666141, 2668157220769, 2685198483619, 2704144073171, 2713299004769, 2767144311853, 2781059109643, 2884629032993]

theorem bankLeaf199_valid : bankLeaf199.Certified := by
  simp only [bankLeaf199, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 29, 233, 14453501] }, .lucas { root := 2, primeFactors := [2, 5, 137, 211] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 137, 15553277] }, .lucas { root := 2, primeFactors := [2, 683, 5693] }, .lucas { root := 2, primeFactors := [2, 1423] }, .lucas { root := 3, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 12342653969] }, .lucas { root := 3, primeFactors := [2, 31, 269, 92507] }, .lucas { root := 2, primeFactors := [2, 23, 2011] }, .lucas { root := 3, primeFactors := [2, 3, 5, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 19, 1913, 208759] }, .lucas { root := 3, primeFactors := [2, 239] }, .lucas { root := 3, primeFactors := [2, 3, 11, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 97, 179, 1823, 40277] }, .lucas { root := 5, primeFactors := [2, 911] }, .lucas { root := 2, primeFactors := [2, 10069] }, .lucas { root := 2, primeFactors := [2, 3, 839] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19, 41, 26724419] }, .lucas { root := 2, primeFactors := [2, 7, 31, 139, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 379, 421, 278191] }, .lucas { root := 3, primeFactors := [2, 3, 5, 11, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 2267, 943073] }, .lucas { root := 2, primeFactors := [2, 11, 103] }, .lucas { root := 3, primeFactors := [2, 13, 2267] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 97, 17137, 38461] }, .lucas { root := 5, primeFactors := [2, 3, 7, 17] }, .lucas { root := 13, primeFactors := [2, 3, 5, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 444539, 608303] }, .lucas { root := 2, primeFactors := [2, 222269] }, .lucas { root := 2, primeFactors := [2, 181, 307] }, .lucas { root := 5, primeFactors := [2, 304151] }, .lucas { root := 7, primeFactors := [2, 5, 7, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 107, 4597, 15671] }, .lucas { root := 5, primeFactors := [2, 3, 383] }, .lucas { root := 13, primeFactors := [2, 5, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 79, 153627821] }, .lucas { root := 3, primeFactors := [2, 5, 41, 43, 4357] }, .lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 31, 621521] }, .lucas { root := 3, primeFactors := [2, 5, 17, 457] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf200 : PrimeBank := .leaf [2885970942193, 2947776963163, 2956596702431, 2967043523209, 3033826866533, 3038776685491, 3064328247661, 3082032099281, 3091090109851, 3180314445761, 3195683246341, 3203890969243, 3327991890851, 3372531985651, 3375702307841, 3377651878597]

theorem bankLeaf200_valid : bankLeaf200.Certified := by
  simp only [bankLeaf200, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 4624953433] }, .lucas { root := 5, primeFactors := [2, 3, 11, 293, 59791] }, .lucas { root := 3, primeFactors := [2, 3, 5, 1993] }, .lucas { root := 5, primeFactors := [2, 3, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 491296160527] }, .lucas { root := 5, primeFactors := [2, 3, 81882693421] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 124064687] }, .lucas { root := 5, primeFactors := [2, 997, 62219] }, .lucas { root := 2, primeFactors := [2, 13, 2393] }, .lucas { root := 3, primeFactors := [2, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 42237095749] }, .lucas { root := 2, primeFactors := [2, 3, 17, 207044587] }, .lucas { root := 3, primeFactors := [2, 3, 7, 182579] }, .lucas { root := 2, primeFactors := [2, 11, 43, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 19, 79, 4334893] }, .lucas { root := 2, primeFactors := [2, 3, 361241] }, .lucas { root := 3, primeFactors := [2, 5, 11, 821] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 59, 163, 389, 2633] }, .lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 241, 4618693] }, .lucas { root := 2, primeFactors := [2, 3, 13, 71, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43, 9013, 131779] }, .lucas { root := 5, primeFactors := [2, 3, 751] }, .lucas { root := 2, primeFactors := [2, 3, 7321] }, .lucas { root := 7, primeFactors := [2, 3, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 17, 853, 1423, 1867] }, .lucas { root := 3, primeFactors := [2, 3, 79] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 361531007] }, .lucas { root := 5, primeFactors := [2, 71, 2545993] }, .lucas { root := 5, primeFactors := [2, 3, 3929] }, .lucas { root := 3, primeFactors := [2, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 23, 37, 11678593] }, .lucas { root := 15, primeFactors := [2, 3, 17, 1789] }, .lucas { root := 6, primeFactors := [2, 3, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 61, 647, 34603] }, .lucas { root := 2, primeFactors := [2, 3, 73, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 533981828207] }, .lucas { root := 5, primeFactors := [2, 266990914103] }, .lucas { root := 5, primeFactors := [2, 11, 12135950641] }, .lucas { root := 23, primeFactors := [2, 3, 5, 11, 569, 2693] }, .lucas { root := 2, primeFactors := [2, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 6863, 881669] }, .lucas { root := 5, primeFactors := [2, 47, 73] }, .lucas { root := 2, primeFactors := [2, 227, 971] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 79, 97, 887] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 281470989883] }, .lucas { root := 3, primeFactors := [2, 3, 43, 53, 20584393] }, .lucas { root := 5, primeFactors := [2, 3, 59, 14537] }, .lucas { root := 3, primeFactors := [2, 23, 79] }]), by simp⟩

@[expose] noncomputable def bankLeaf201 : PrimeBank := .leaf [3381863410579, 3442203582379, 3447899565839, 3467398618193, 3467554724111, 3478781116501, 3515044995197, 3565774117541, 3613045528091, 3660120919867, 3737657091169, 3740221981231, 3791139504307, 3867675755483, 3894564762019, 4031434050653]

theorem bankLeaf201_valid : bankLeaf201.Certified := by
  simp only [bankLeaf201, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 31, 137, 2267, 5417] }, .lucas { root := 2, primeFactors := [2, 11, 103] }, .lucas { root := 3, primeFactors := [2, 677] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 66293, 3269009] }, .lucas { root := 2, primeFactors := [2, 16573] }, .lucas { root := 2, primeFactors := [2, 3, 1381] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }, .lucas { root := 3, primeFactors := [2, 173, 1181] }, .lucas { root := 7, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 197, 761, 2312983] }, .lucas { root := 3, primeFactors := [2, 3, 7, 29, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 47, 83, 594511] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 19, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 125537321257] }, .lucas { root := 5, primeFactors := [2, 3, 5230721719] }, .lucas { root := 6, primeFactors := [2, 3, 103, 733, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 18401, 9689077] }, .lucas { root := 3, primeFactors := [2, 5, 23] }, .lucas { root := 2, primeFactors := [2, 3, 269141] }, .lucas { root := 2, primeFactors := [2, 5, 13457] }, .lucas { root := 3, primeFactors := [2, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 8205929663] }, .lucas { root := 5, primeFactors := [2, 7, 586137833] }, .lucas { root := 3, primeFactors := [2, 7, 17, 31, 19861] }, .lucas { root := 11, primeFactors := [2, 3, 5, 331] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 5647, 1824523] }, .lucas { root := 3, primeFactors := [2, 3, 941] }, .lucas { root := 2, primeFactors := [2, 3, 7, 43441] }, .lucas { root := 11, primeFactors := [2, 3, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 41, 31469, 41113] }, .lucas { root := 2, primeFactors := [2, 7867] }, .lucas { root := 3, primeFactors := [2, 3, 19, 23] }, .lucas { root := 5, primeFactors := [2, 3, 571] }]), by simp⟩

@[expose] noncomputable def bankLeaf202 : PrimeBank := .leaf [4052490063499, 4099581241957, 4143205906183, 4242586390571, 4287755796749, 4296301150081, 4310978424031, 4344740942669, 4361656956697, 4373689633189, 4420130701513, 4427882363263, 4454269239481, 4513076485163, 4534166740403, 4589566181929]

theorem bankLeaf202_valid : bankLeaf202.Certified := by
  simp only [bankLeaf202, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 32882586557] }, .lucas { root := 2, primeFactors := [2, 61, 134764699] }, .lucas { root := 2, primeFactors := [2, 3, 47, 223, 2143] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 31, 1949, 792793] }, .lucas { root := 2, primeFactors := [2, 487] }, .lucas { root := 10, primeFactors := [2, 3, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23, 6746492147] }, .lucas { root := 2, primeFactors := [2, 19, 383, 463549] }, .lucas { root := 2, primeFactors := [2, 3, 38629] }, .lucas { root := 2, primeFactors := [2, 3, 29, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 29, 107, 500579] }, .lucas { root := 2, primeFactors := [2, 13, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 977, 10082551] }, .lucas { root := 6, primeFactors := [2, 3, 5, 67217] }, .lucas { root := 3, primeFactors := [2, 4201] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 101, 1823486263] }, .lucas { root := 3, primeFactors := [2, 3, 13, 83, 281663] }, .lucas { root := 5, primeFactors := [2, 140831] }, .lucas { root := 11, primeFactors := [2, 5, 14083] }, .lucas { root := 3, primeFactors := [2, 3, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 163, 227, 19944877] }, .lucas { root := 2, primeFactors := [2, 3, 7, 17, 13967] }, .lucas { root := 5, primeFactors := [2, 6983] }, .lucas { root := 5, primeFactors := [2, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 7, 13, 23, 271, 12487] }, .lucas { root := 3, primeFactors := [2, 3, 2081] }, .lucas { root := 3, primeFactors := [2, 5, 13] }]), by simp⟩

@[expose] noncomputable def bankLeaf203 : PrimeBank := .leaf [4590514719337, 4635303278743, 4642673454589, 4680594500779, 4721592201421, 4721697244987, 4732145777657, 4803254465101, 5149146324851, 5211310507321, 5369801401451, 5567751651967, 5594292675731, 5666151340567, 5668573026559, 5695679040941]

theorem bankLeaf203_valid : bankLeaf203.Certified := by
  simp only [bankLeaf203, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 5813, 6390431] }, .lucas { root := 2, primeFactors := [2, 1453] }, .lucas { root := 2, primeFactors := [2, 3, 11] }, .lucas { root := 11, primeFactors := [2, 5, 639043] }, .lucas { root := 2, primeFactors := [2, 3, 73, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 30133, 2611529] }, .lucas { root := 5, primeFactors := [2, 3, 31] }, .lucas { root := 3, primeFactors := [2, 326441] }, .lucas { root := 3, primeFactors := [2, 5, 8161] }, .lucas { root := 7, primeFactors := [2, 3, 5, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 31, 43, 233, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 14321, 3032441] }, .lucas { root := 3, primeFactors := [2, 5, 179] }, .lucas { root := 3, primeFactors := [2, 5, 47, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 23, 4669392523] }, .lucas { root := 2, primeFactors := [2, 3, 778232087] }, .lucas { root := 10, primeFactors := [2, 17, 199, 115021] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 607, 31199227] }, .lucas { root := 3, primeFactors := [2, 3, 293, 17747] }, .lucas { root := 2, primeFactors := [2, 19, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 211, 233, 1034461] }, .lucas { root := 18, primeFactors := [2, 3, 5, 7, 821] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 2137, 3967, 4799] }, .lucas { root := 10, primeFactors := [2, 3, 89] }, .lucas { root := 6, primeFactors := [2, 3, 661] }, .lucas { root := 7, primeFactors := [2, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]), by simp⟩

@[expose] noncomputable def bankLeaf204 : PrimeBank := .leaf [5722211438623, 5738555624149, 5767237398301, 5863634991947, 5889307277311, 5937018283241, 5968930061879, 5986246439669, 6019485806281, 6341188605733, 6500993481529, 6545783871619, 6569400520481, 6607709210461, 7017607616783, 7160899293871]

theorem bankLeaf204_valid : bankLeaf204.Certified := by
  simp only [bankLeaf204, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 31, 37, 628477] }, .lucas { root := 2, primeFactors := [2, 3, 83, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 661, 241156313] }, .lucas { root := 3, primeFactors := [2, 521, 57859] }, .lucas { root := 2, primeFactors := [2, 3, 9643] }, .lucas { root := 2, primeFactors := [2, 3, 1607] }, .lucas { root := 5, primeFactors := [2, 11, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 47, 62379095659] }, .lucas { root := 2, primeFactors := [2, 3, 11, 21011, 44983] }, .lucas { root := 2, primeFactors := [2, 5, 11, 191] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 101, 7489, 17839] }, .lucas { root := 7, primeFactors := [2, 3, 13] }, .lucas { root := 6, primeFactors := [2, 3, 991] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 136051055447] }, .lucas { root := 5, primeFactors := [2, 35159, 1934797] }, .lucas { root := 11, primeFactors := [2, 17579] }, .lucas { root := 2, primeFactors := [2, 11, 17, 47] }, .lucas { root := 2, primeFactors := [2, 3, 161233] }, .lucas { root := 5, primeFactors := [2, 3, 3359] }, .lucas { root := 11, primeFactors := [2, 23, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 709, 1709, 41399] }, .lucas { root := 3, primeFactors := [2, 7, 61] }, .lucas { root := 7, primeFactors := [2, 7, 2957] }, .lucas { root := 2, primeFactors := [2, 739] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 2017, 87329761] }, .lucas { root := 5, primeFactors := [2, 3, 7] }, .lucas { root := 29, primeFactors := [2, 3, 5, 7, 47, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 13, 2976645367] }, .lucas { root := 3, primeFactors := [2, 3, 233, 709739] }, .lucas { root := 2, primeFactors := [2, 354869] }, .lucas { root := 2, primeFactors := [2, 79, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 47433216461] }, .lucas { root := 2, primeFactors := [2, 5, 7, 338808689] }, .lucas { root := 3, primeFactors := [2, 21175543] }, .lucas { root := 3, primeFactors := [2, 3, 31, 137, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 50461, 116239] }, .lucas { root := 7, primeFactors := [2, 3, 5, 29] }, .lucas { root := 6, primeFactors := [2, 3, 19373] }, .lucas { root := 2, primeFactors := [2, 29, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 29, 79, 257, 187043] }, .lucas { root := 2, primeFactors := [2, 41, 2281] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 127, 937, 286553] }, .lucas { root := 3, primeFactors := [2, 7, 17, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf205 : PrimeBank := .leaf [7320672187193, 7415508040487, 7766436390529, 7905387587089, 7909103848783, 8126903492887, 8157179360521, 8201186510791, 8503518281771, 8737481256739, 8836616628937, 8858956488251, 8908465760191, 8918947233611, 9040306524047, 9108709959749]

theorem bankLeaf205_valid : bankLeaf205.Certified := by
  simp only [bankLeaf205, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 19, 613, 123341] }, .lucas { root := 3, primeFactors := [2, 5, 7, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 40744549673] }, .lucas { root := 3, primeFactors := [2, 17, 31, 109, 88663] }, .lucas { root := 3, primeFactors := [2, 3, 7, 2111] }, .lucas { root := 7, primeFactors := [2, 5, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 20225094767] }, .lucas { root := 5, primeFactors := [2, 271, 337, 110729] }, .lucas { root := 3, primeFactors := [2, 13841] }, .lucas { root := 6, primeFactors := [2, 5, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 97, 1697892523] }, .lucas { root := 2, primeFactors := [2, 3, 23, 29, 424261] }, .lucas { root := 2, primeFactors := [2, 3, 5, 2357] }, .lucas { root := 2, primeFactors := [2, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 479, 2269, 1212847] }, .lucas { root := 2, primeFactors := [2, 3, 7] }, .lucas { root := 5, primeFactors := [2, 3, 19, 10639] }, .lucas { root := 6, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 643, 31440401] }, .lucas { root := 3, primeFactors := [2, 5, 83, 947] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 7, 13, 16061, 187043] }, .lucas { root := 12, primeFactors := [2, 5, 11, 73] }, .lucas { root := 2, primeFactors := [2, 41, 2281] }, .lucas { root := 7, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 67, 12691818331] }, .lucas { root := 10, primeFactors := [2, 3, 5, 423060611] }, .lucas { root := 6, primeFactors := [2, 5, 7, 89, 109] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 269, 50694253] }, .lucas { root := 5, primeFactors := [2, 3, 7, 603503] }, .lucas { root := 5, primeFactors := [2, 301751] }, .lucas { root := 13, primeFactors := [2, 5, 17, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 37507, 85889] }, .lucas { root := 17, primeFactors := [2, 3, 7, 19, 47] }, .lucas { root := 3, primeFactors := [2, 11, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 37, 131, 133223887] }, .lucas { root := 5, primeFactors := [2, 3, 1181, 2089] }, .lucas { root := 7, primeFactors := [2, 5, 59] }, .lucas { root := 7, primeFactors := [2, 3, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf206 : PrimeBank := .leaf [9177123452131, 9280684146823, 9438197072471, 9468940004449, 9726539312579, 10654978292191, 10805054366101, 10810256869463, 11124772385569, 11232875364041, 11709700117279, 11835246523601, 11940971871487, 12400411646533, 12467742253891, 12486437381123]

theorem bankLeaf206_valid : bankLeaf206.Certified := by
  simp only [bankLeaf206, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 47, 16831, 42967] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11, 17] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 31, 47, 797611] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 2417] }, .lucas { root := 3, primeFactors := [2, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 1459, 646894933] }, .lucas { root := 3, primeFactors := [2, 3] }, .lucas { root := 2, primeFactors := [2, 3, 53907911] }, .lucas { root := 7, primeFactors := [2, 5, 7, 770113] }, .lucas { root := 10, primeFactors := [2, 3, 7, 191] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 19, 111507269] }, .lucas { root := 2, primeFactors := [2, 61, 107, 4271] }, .lucas { root := 7, primeFactors := [2, 5, 7, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 71, 1632155573] }, .lucas { root := 2, primeFactors := [2, 408038893] }, .lucas { root := 2, primeFactors := [2, 3, 34003241] }, .lucas { root := 3, primeFactors := [2, 5, 850081] }, .lucas { root := 31, primeFactors := [2, 3, 5, 7, 11, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 8233, 237048061] }, .lucas { root := 10, primeFactors := [2, 3, 7] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41, 173, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 457, 64744237] }, .lucas { root := 2, primeFactors := [2, 3, 1798451] }, .lucas { root := 2, primeFactors := [2, 5, 35969] }, .lucas { root := 3, primeFactors := [2, 281] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11, 17, 317487707] }, .lucas { root := 2, primeFactors := [2, 158743853] }, .lucas { root := 2, primeFactors := [2, 6131, 6473] }, .lucas { root := 2, primeFactors := [2, 5, 613] }, .lucas { root := 3, primeFactors := [2, 809] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf207 : PrimeBank := .leaf [12704596693303, 13240442106403, 13307558221651, 13339102733461, 13462149171001, 13537641593297, 13688084491799, 14567641413739, 14818903179071, 14863108179151, 14957593125707, 15069283300651, 15167446089487, 15277058694481, 15511794835249, 15635923856983]

theorem bankLeaf207_valid : bankLeaf207.Certified := by
  simp only [bankLeaf207, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 19, 23, 210668867] }, .lucas { root := 2, primeFactors := [2, 105334433] }, .lucas { root := 5, primeFactors := [2, 7, 470243] }, .lucas { root := 2, primeFactors := [2, 191, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 101, 257, 12145033] }, .lucas { root := 5, primeFactors := [2, 3, 59, 953] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 107867, 341041] }, .lucas { root := 2, primeFactors := [2, 11, 4903] }, .lucas { root := 3, primeFactors := [2, 3, 19, 43] }, .lucas { root := 22, primeFactors := [2, 3, 5, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 17, 1181, 3691, 92357] }, .lucas { root := 7, primeFactors := [2, 5, 59] }, .lucas { root := 2, primeFactors := [2, 3, 5, 41] }, .lucas { root := 3, primeFactors := [2, 11, 2099] }, .lucas { root := 2, primeFactors := [2, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 367, 2755369] }, .lucas { root := 13, primeFactors := [2, 3, 7, 11, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 1481890317907] }, .lucas { root := 2, primeFactors := [2, 3, 23, 167, 64301411] }, .lucas { root := 2, primeFactors := [2, 5, 29, 221729] }, .lucas { root := 3, primeFactors := [2, 13, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 11, 4691, 13063] }, .lucas { root := 2, primeFactors := [2, 5, 7, 67] }, .lucas { root := 5, primeFactors := [2, 3, 7, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 22859, 4248971] }, .lucas { root := 2, primeFactors := [2, 11, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }, .lucas { root := 2, primeFactors := [2, 5, 11, 19, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 47, 151, 832679] }, .lucas { root := 7, primeFactors := [2, 7, 11, 5407] }, .lucas { root := 3, primeFactors := [2, 3, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 401, 6304009181] }, .lucas { root := 3, primeFactors := [2, 5, 7, 181, 193, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 11, 17, 5227, 65123] }, .lucas { root := 2, primeFactors := [2, 3, 13, 67] }, .lucas { root := 2, primeFactors := [2, 32561] }, .lucas { root := 6, primeFactors := [2, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 47, 763977287] }, .lucas { root := 5, primeFactors := [2, 313, 1220411] }, .lucas { root := 2, primeFactors := [2, 5, 122041] }, .lucas { root := 7, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 22567, 269179] }, .lucas { root := 3, primeFactors := [2, 3, 3761] }, .lucas { root := 3, primeFactors := [2, 5, 47] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13, 17, 29] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
