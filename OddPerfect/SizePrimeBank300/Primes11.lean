module

public import OddPerfect.SizePrimeBank300.Primes10
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf182 : PrimeBank := .leaf [121387119169, 123460400377, 124244862031, 124744666201, 125642407351, 126918638983, 128493601339, 129924628343, 129994124149, 131807445409, 132274505201, 132345512729, 133539253321, 134945578333, 135676061629, 136219001651]

theorem bankLeaf182_valid : bankLeaf182.Certified := by
  simp only [bankLeaf182, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 90317797] }, .lucas { root := 2, primeFactors := [2, 3, 271, 27773] }, .lucas { root := 2, primeFactors := [2, 53, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1714727783] }, .lucas { root := 5, primeFactors := [2, 97, 8838803] }, .lucas { root := 5, primeFactors := [2, 7, 269, 2347] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 7, 11, 2700101] }, .lucas { root := 2, primeFactors := [2, 5, 13, 31, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 190568527] }, .lucas { root := 3, primeFactors := [2, 3, 2437, 13033] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29] }, .lucas { root := 5, primeFactors := [2, 3, 181] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 379, 1361081] }, .lucas { root := 3, primeFactors := [2, 5, 7, 4861] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 23, 103, 193189] }, .lucas { root := 6, primeFactors := [2, 3, 17, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 71, 4657553] }, .lucas { root := 3, primeFactors := [2, 97, 3001] }, .lucas { root := 14, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 31, 339257] }, .lucas { root := 3, primeFactors := [2, 42407] }, .lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 73, 1385837] }, .lucas { root := 2, primeFactors := [2, 199, 1741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 17, 31, 311, 22871] }, .lucas { root := 7, primeFactors := [2, 5, 2287] }, .lucas { root := 19, primeFactors := [2, 3, 127] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf183 : PrimeBank := .leaf [136328481943, 139394845309, 140392204717, 142469884267, 143352274829, 143590301611, 147700651411, 148541590783, 151677497137, 152524929943, 152597832677, 152943249629, 154545688753, 171102215257, 172919530897, 174398409253]

theorem bankLeaf183_valid : bankLeaf183.Certified := by
  simp only [bankLeaf183, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 1091, 562871] }, .lucas { root := 2, primeFactors := [2, 5, 109] }, .lucas { root := 14, primeFactors := [2, 5, 7, 11, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11616237109] }, .lucas { root := 10, primeFactors := [2, 3, 7, 2293, 6701] }, .lucas { root := 2, primeFactors := [2, 3, 191] }, .lucas { root := 2, primeFactors := [2, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71, 164779583] }, .lucas { root := 5, primeFactors := [2, 11, 7489981] }, .lucas { root := 6, primeFactors := [2, 3, 5, 41611] }, .lucas { root := 2, primeFactors := [2, 3, 5, 19, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 701, 826171] }, .lucas { root := 10, primeFactors := [2, 3, 5, 27539] }, .lucas { root := 2, primeFactors := [2, 7, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 5119724101] }, .lucas { root := 6, primeFactors := [2, 3, 5, 23, 47, 15787] }, .lucas { root := 2, primeFactors := [2, 3, 877] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 43, 2935811] }, .lucas { root := 2, primeFactors := [2, 5, 173, 1697] }, .lucas { root := 3, primeFactors := [2, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 23, 89, 97, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 43, 2559229] }, .lucas { root := 6, primeFactors := [2, 3, 7, 30467] }, .lucas { root := 2, primeFactors := [2, 15233] }, .lucas { root := 3, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 1031066437] }, .lucas { root := 5, primeFactors := [2, 3, 85922203] }, .lucas { root := 2, primeFactors := [2, 3, 89, 160903] }, .lucas { root := 5, primeFactors := [2, 3, 7, 1277] }, .lucas { root := 2, primeFactors := [2, 11, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 577, 493873] }, .lucas { root := 5, primeFactors := [2, 3, 10289] }, .lucas { root := 3, primeFactors := [2, 643] }]), by simp⟩

@[expose] noncomputable def bankLeaf184 : PrimeBank := .leaf [174584317091, 175010608151, 176771523631, 179452162007, 181380545347, 181627957627, 182955964171, 184976953991, 187039475551, 189343400041, 190605173111, 193444878199, 198844055017, 200822829241, 201637702531, 204296477131]

theorem bankLeaf184_valid : bankLeaf184.Certified := by
  simp only [bankLeaf184, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 163, 5783, 18521] }, .lucas { root := 7, primeFactors := [2, 7, 59] }, .lucas { root := 3, primeFactors := [2, 5, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 7, 151, 739, 4481] }, .lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 61, 983, 7559] }, .lucas { root := 13, primeFactors := [2, 3779] }, .lucas { root := 2, primeFactors := [2, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 1447, 4769873] }, .lucas { root := 3, primeFactors := [2, 3, 241] }, .lucas { root := 3, primeFactors := [2, 241, 1237] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 13, 30199891] }, .lucas { root := 13, primeFactors := [2, 3, 5, 7, 31, 4639] }, .lucas { root := 3, primeFactors := [2, 3, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 16253, 45427] }, .lucas { root := 2, primeFactors := [2, 17, 239] }, .lucas { root := 3, primeFactors := [2, 3, 67, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 3659, 238103] }, .lucas { root := 2, primeFactors := [2, 31, 59] }, .lucas { root := 5, primeFactors := [2, 17, 47, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 59, 101, 557, 5573] }, .lucas { root := 2, primeFactors := [2, 7, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11, 67, 571, 45293] }, .lucas { root := 2, primeFactors := [2, 13, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 225460231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41, 183301] }, .lucas { root := 10, primeFactors := [2, 3, 5, 13, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 443, 18702413] }, .lucas { root := 2, primeFactors := [2, 4675603] }, .lucas { root := 2, primeFactors := [2, 3, 779267] }, .lucas { root := 2, primeFactors := [2, 19, 20507] }, .lucas { root := 2, primeFactors := [2, 10253] }, .lucas { root := 2, primeFactors := [2, 11, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 11, 127, 1197941] }, .lucas { root := 2, primeFactors := [2, 5, 89, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 83, 2453909] }, .lucas { root := 2, primeFactors := [2, 61, 89, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 8609, 29297] }, .lucas { root := 3, primeFactors := [2, 269] }, .lucas { root := 3, primeFactors := [2, 1831] }, .lucas { root := 3, primeFactors := [2, 3, 5, 61] }]), by simp⟩

@[expose] noncomputable def bankLeaf185 : PrimeBank := .leaf [205436217781, 207837725713, 217230976273, 219857721169, 222568976723, 232814414999, 233017007827, 235170205927, 237959523803, 239183225509, 239337374873, 239789806103, 246904049813, 247174661801, 249216868661, 249329489131]

theorem bankLeaf185_valid : bankLeaf185.Certified := by
  simp only [bankLeaf185, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 43, 857, 30971] }, .lucas { root := 2, primeFactors := [2, 5, 19, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 4525645339] }, .lucas { root := 3, primeFactors := [2, 3, 43, 109, 17881] }, .lucas { root := 7, primeFactors := [2, 3, 5, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 607, 7545913] }, .lucas { root := 5, primeFactors := [2, 3, 11, 101, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29137, 3819353] }, .lucas { root := 5, primeFactors := [2, 3, 607] }, .lucas { root := 3, primeFactors := [2, 281, 1699] }, .lucas { root := 3, primeFactors := [2, 3, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 491, 541, 39839] }, .lucas { root := 7, primeFactors := [2, 19919] }, .lucas { root := 7, primeFactors := [2, 23, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 109, 8285933] }, .lucas { root := 2, primeFactors := [2, 557, 3719] }, .lucas { root := 7, primeFactors := [2, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 1704131927] }, .lucas { root := 5, primeFactors := [2, 7, 19, 1279, 5009] }, .lucas { root := 3, primeFactors := [2, 3, 71] }, .lucas { root := 3, primeFactors := [2, 313] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 89, 4903, 45677] }, .lucas { root := 3, primeFactors := [2, 3, 19, 43] }, .lucas { root := 2, primeFactors := [2, 19, 601] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 7, 11, 109, 2897, 4931] }, .lucas { root := 3, primeFactors := [2, 181] }, .lucas { root := 6, primeFactors := [2, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 17, 241, 2152307] }, .lucas { root := 2, primeFactors := [2, 13, 82781] }, .lucas { root := 2, primeFactors := [2, 5, 4139] }, .lucas { root := 2, primeFactors := [2, 2069] }, .lucas { root := 2, primeFactors := [2, 11, 47] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 4787, 2603059] }, .lucas { root := 2, primeFactors := [2, 2393] }, .lucas { root := 3, primeFactors := [2, 13, 23] }, .lucas { root := 2, primeFactors := [2, 3, 467, 929] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2770327657] }, .lucas { root := 7, primeFactors := [2, 3, 1307, 3271] }, .lucas { root := 2, primeFactors := [2, 653] }, .lucas { root := 3, primeFactors := [2, 3, 5, 109] }]), by simp⟩

@[expose] noncomputable def bankLeaf186 : PrimeBank := .leaf [253514958703, 253541934287, 259926373051, 260670715787, 265170755671, 269267987071, 271082465131, 273625252091, 273818481499, 274427186197, 275036918797, 278014221827, 278658727003, 283564158181, 288351734399, 290770486991]

theorem bankLeaf186_valid : bankLeaf186.Certified := by
  simp only [bankLeaf186, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43, 982616119] }, .lucas { root := 12, primeFactors := [2, 3, 11, 1129, 13187] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 2, primeFactors := [2, 19, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 73, 1736588591] }, .lucas { root := 11, primeFactors := [2, 5, 11, 17, 227, 4091] }, .lucas { root := 2, primeFactors := [2, 5, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17, 719, 141769] }, .lucas { root := 14, primeFactors := [2, 3, 11, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 23, 435904207] }, .lucas { root := 5, primeFactors := [2, 3, 31, 2343571] }, .lucas { root := 2, primeFactors := [2, 3, 5, 191, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 23, 769, 499747] }, .lucas { root := 3, primeFactors := [2, 3, 13, 43, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 863, 1155607] }, .lucas { root := 3, primeFactors := [2, 3, 192601] }, .lucas { root := 7, primeFactors := [2, 3, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 1213, 7449367] }, .lucas { root := 2, primeFactors := [2, 3, 101] }, .lucas { root := 6, primeFactors := [2, 3, 17, 199, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 71, 241, 1599119] }, .lucas { root := 7, primeFactors := [2, 29, 79, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 15212137861] }, .lucas { root := 6, primeFactors := [2, 3, 5, 811, 104207] }, .lucas { root := 5, primeFactors := [2, 52103] }, .lucas { root := 5, primeFactors := [2, 109, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 15649, 1461367] }, .lucas { root := 11, primeFactors := [2, 3, 163] }, .lucas { root := 3, primeFactors := [2, 3, 19, 4273] }, .lucas { root := 5, primeFactors := [2, 3, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31439977] }, .lucas { root := 11, primeFactors := [2, 3, 1309999] }, .lucas { root := 3, primeFactors := [2, 3, 31, 7043] }, .lucas { root := 2, primeFactors := [2, 7, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 9137, 60133] }, .lucas { root := 3, primeFactors := [2, 571] }, .lucas { root := 6, primeFactors := [2, 3, 5011] }, .lucas { root := 2, primeFactors := [2, 3, 5, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 103, 1171, 3469] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }, .lucas { root := 2, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 29, 41, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 7, 13, 1584350189] }, .lucas { root := 2, primeFactors := [2, 19, 20846713] }, .lucas { root := 5, primeFactors := [2, 3, 868613] }, .lucas { root := 2, primeFactors := [2, 37, 5869] }, .lucas { root := 2, primeFactors := [2, 3, 163] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf187 : PrimeBank := .leaf [292717313533, 294730025479, 296107560877, 299749176169, 306487563493, 308378344871, 308890468603, 309047089313, 309160746071, 312885594317, 315188780447, 316089035473, 320996227397, 322099207841, 323602414939, 325837184863]

theorem bankLeaf187_valid : bankLeaf187.Certified := by
  simp only [bankLeaf187, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1161576641] }, .lucas { root := 6, primeFactors := [2, 5, 7, 61, 8501] }, .lucas { root := 7, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 7017381559] }, .lucas { root := 6, primeFactors := [2, 3, 11, 23, 1540927] }, .lucas { root := 3, primeFactors := [2, 3, 85607] }, .lucas { root := 5, primeFactors := [2, 23, 1861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2333, 10576781] }, .lucas { root := 2, primeFactors := [2, 11, 53] }, .lucas { root := 2, primeFactors := [2, 5, 23, 22993] }, .lucas { root := 5, primeFactors := [2, 3, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 13, 1319, 728381] }, .lucas { root := 13, primeFactors := [2, 659] }, .lucas { root := 2, primeFactors := [2, 5, 79, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 283, 8204507] }, .lucas { root := 2, primeFactors := [2, 17, 29, 53, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 29, 71, 659, 22727] }, .lucas { root := 5, primeFactors := [2, 11, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 248704081] }, .lucas { root := 11, primeFactors := [2, 3, 5, 1036267] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 742901657] }, .lucas { root := 3, primeFactors := [2, 7, 23, 576787] }, .lucas { root := 7, primeFactors := [2, 3, 7, 31, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 503, 739, 7561] }, .lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 3400930373] }, .lucas { root := 2, primeFactors := [2, 7, 43, 107, 26399] }, .lucas { root := 7, primeFactors := [2, 67, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 157594390223] }, .lucas { root := 5, primeFactors := [2, 29, 2717144659] }, .lucas { root := 2, primeFactors := [2, 3, 709, 212909] }, .lucas { root := 2, primeFactors := [2, 17, 31, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 109, 8630653] }, .lucas { root := 2, primeFactors := [2, 3, 101, 7121] }, .lucas { root := 3, primeFactors := [2, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 19, 61, 233, 22859] }, .lucas { root := 2, primeFactors := [2, 11, 1039] }, .lucas { root := 3, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 41, 49100489] }, .lucas { root := 3, primeFactors := [2, 17, 361033] }, .lucas { root := 5, primeFactors := [2, 3, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 1634355631] }, .lucas { root := 15, primeFactors := [2, 3, 5, 2017723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 6863] }, .lucas { root := 5, primeFactors := [2, 47, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13591, 570821] }, .lucas { root := 3, primeFactors := [2, 3, 5, 151] }, .lucas { root := 2, primeFactors := [2, 5, 28541] }, .lucas { root := 2, primeFactors := [2, 5, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }]), by simp⟩

@[expose] noncomputable def bankLeaf188 : PrimeBank := .leaf [327668647153, 329142823777, 332144352187, 332207361361, 335591796161, 338984002897, 358600679341, 372221190881, 372649725281, 373559364091, 374474805409, 386626708057, 386855506153, 388940209901, 391902413587, 400500370843]

theorem bankLeaf188_valid : bankLeaf188.Certified := by
  simp only [bankLeaf188, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 29, 113, 139, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 2913546949] }, .lucas { root := 10, primeFactors := [2, 3, 13, 18676583] }, .lucas { root := 5, primeFactors := [2, 19, 491489] }, .lucas { root := 3, primeFactors := [2, 15359] }, .lucas { root := 11, primeFactors := [2, 7, 1097] }, .lucas { root := 3, primeFactors := [2, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 41, 983, 26021] }, .lucas { root := 2, primeFactors := [2, 5, 1301] }, .lucas { root := 2, primeFactors := [2, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 11, 37, 71, 34913] }, .lucas { root := 3, primeFactors := [2, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 97, 5881, 10477] }, .lucas { root := 31, primeFactors := [2, 3, 5, 7] }, .lucas { root := 2, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 2729, 11071] }, .lucas { root := 3, primeFactors := [2, 11, 31] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 83, 181, 25117] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 118205431] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 389, 1447] }, .lucas { root := 3, primeFactors := [2, 3, 241] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 32143819] }, .lucas { root := 3, primeFactors := [2, 3, 7, 765329] }, .lucas { root := 3, primeFactors := [2, 31, 1543] }, .lucas { root := 5, primeFactors := [2, 3, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 53, 1949, 632323] }, .lucas { root := 2, primeFactors := [2, 487] }, .lucas { root := 2, primeFactors := [2, 3, 35129] }, .lucas { root := 3, primeFactors := [2, 4391] }, .lucas { root := 14, primeFactors := [2, 5, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 47, 401, 24767] }, .lucas { root := 5, primeFactors := [2, 7, 29, 61] }]), by simp⟩

@[expose] noncomputable def bankLeaf189 : PrimeBank := .leaf [414746743129, 426327378907, 428932133323, 441019876741, 442078452317, 445646455759, 448918291337, 450857606831, 460724037139, 463140612061, 463797723241, 465092326319, 469071595771, 470149013261, 470323176131, 471595255097]

theorem bankLeaf189_valid : bankLeaf189.Certified := by
  simp only [bankLeaf189, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 29, 43, 109, 127139] }, .lucas { root := 2, primeFactors := [2, 11, 5779] }, .lucas { root := 2, primeFactors := [2, 3, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 13, 761, 652937] }, .lucas { root := 3, primeFactors := [2, 17, 4801] }, .lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 11, 19, 29, 59, 28559] }, .lucas { root := 11, primeFactors := [2, 109, 131] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 31, 41, 59, 77569] }, .lucas { root := 13, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 239, 349, 42403] }, .lucas { root := 2, primeFactors := [2, 3, 37, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 38371, 1462427] }, .lucas { root := 10, primeFactors := [2, 3, 5, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }, .lucas { root := 2, primeFactors := [2, 7, 104459] }, .lucas { root := 2, primeFactors := [2, 29, 1801] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 277, 162764479] }, .lucas { root := 3, primeFactors := [2, 3, 47, 21377] }, .lucas { root := 3, primeFactors := [2, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 25595779841] }, .lucas { root := 3, primeFactors := [2, 5, 331, 60413] }, .lucas { root := 2, primeFactors := [2, 11, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 8693, 126851] }, .lucas { root := 2, primeFactors := [2, 41, 53] }, .lucas { root := 2, primeFactors := [2, 5, 43, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 59, 2857, 7643] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }, .lucas { root := 2, primeFactors := [2, 3821] }, .lucas { root := 3, primeFactors := [2, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 101, 2741, 839999] }, .lucas { root := 2, primeFactors := [2, 5, 137] }, .lucas { root := 17, primeFactors := [2, 419999] }, .lucas { root := 13, primeFactors := [2, 373, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 59, 547, 28499] }, .lucas { root := 2, primeFactors := [2, 14249] }, .lucas { root := 3, primeFactors := [2, 13, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29, 810601747] }, .lucas { root := 3, primeFactors := [2, 3, 71, 397, 4793] }, .lucas { root := 3, primeFactors := [2, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 197, 449, 619, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 397, 21212453] }, .lucas { root := 2, primeFactors := [2, 829, 6397] }, .lucas { root := 2, primeFactors := [2, 3, 13, 41] }]), by simp⟩

@[expose] noncomputable def bankLeaf190 : PrimeBank := .leaf [480771505499, 480831112093, 487880282891, 488965889519, 498223764019, 502128718657, 517996789291, 528515019661, 565564190431, 583826053231, 586297360433, 591221812231, 592057347953, 616949907001, 630133915661, 642370334407]

theorem bankLeaf190_valid : bankLeaf190.Certified := by
  simp only [bankLeaf190, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 40069259341] }, .lucas { root := 7, primeFactors := [2, 3, 5, 11, 101, 401, 1499] }, .lucas { root := 2, primeFactors := [2, 7, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 29, 4723, 1784977] }, .lucas { root := 2, primeFactors := [2, 3, 787] }, .lucas { root := 7, primeFactors := [2, 3, 41, 907] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2615253743] }, .lucas { root := 5, primeFactors := [2, 1307626871] }, .lucas { root := 13, primeFactors := [2, 5, 11, 11887517] }, .lucas { root := 2, primeFactors := [2, 2971879] }, .lucas { root := 6, primeFactors := [2, 3, 7, 13, 5443] }, .lucas { root := 2, primeFactors := [2, 3, 907] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17, 19, 24443] }, .lucas { root := 2, primeFactors := [2, 11, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 23, 3461, 13931] }, .lucas { root := 2, primeFactors := [2, 5, 173] }, .lucas { root := 2, primeFactors := [2, 5, 7, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 134063903] }, .lucas { root := 5, primeFactors := [2, 7, 31, 44129] }, .lucas { root := 3, primeFactors := [2, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 23, 149, 1542523] }, .lucas { root := 3, primeFactors := [2, 3, 317, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 17, 23, 227, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 101, 167, 1867949] }, .lucas { root := 2, primeFactors := [2, 29, 16103] }, .lucas { root := 5, primeFactors := [2, 83, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf191 : PrimeBank := .leaf [642681586231, 712373208973, 716002311341, 729230879101, 738389740637, 749154725101, 757905469663, 766390278611, 773206717141, 780413496727, 783834786271, 786631291189, 790579404481, 796057760833, 832342661863, 836488587007]

theorem bankLeaf191_valid : bankLeaf191.Certified := by
  simp only [bankLeaf191, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 1260159973] }, .lucas { root := 5, primeFactors := [2, 3, 23, 71, 107, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 44633, 70003] }, .lucas { root := 3, primeFactors := [2, 7, 797] }, .lucas { root := 2, primeFactors := [2, 3, 3889] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 37, 56915923] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29, 83, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2430769597] }, .lucas { root := 6, primeFactors := [2, 3, 202564133] }, .lucas { root := 2, primeFactors := [2, 50641033] }, .lucas { root := 10, primeFactors := [2, 3, 13, 23, 7057] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 193, 1437641] }, .lucas { root := 3, primeFactors := [2, 5, 127, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 17, 59, 11449069] }, .lucas { root := 2, primeFactors := [2, 3, 59, 103, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 1009, 6905039] }, .lucas { root := 7, primeFactors := [2, 7, 493217] }, .lucas { root := 3, primeFactors := [2, 15413] }, .lucas { root := 2, primeFactors := [2, 3853] }, .lucas { root := 2, primeFactors := [2, 3, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 13, 83, 40213] }, .lucas { root := 6, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 467, 16383539] }, .lucas { root := 2, primeFactors := [2, 1753, 4673] }, .lucas { root := 7, primeFactors := [2, 3, 73] }, .lucas { root := 3, primeFactors := [2, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53, 89, 205151] }, .lucas { root := 7, primeFactors := [2, 5, 11, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 83, 11057, 71429] }, .lucas { root := 3, primeFactors := [2, 691] }, .lucas { root := 2, primeFactors := [2, 7, 2551] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 4146134171] }, .lucas { root := 2, primeFactors := [2, 5, 997, 415861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 191467, 724531] }, .lucas { root := 2, primeFactors := [2, 3, 11, 967] }, .lucas { root := 10, primeFactors := [2, 3, 5, 24151] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 16937, 914597] }, .lucas { root := 3, primeFactors := [2, 29, 73] }, .lucas { root := 2, primeFactors := [2, 373, 613] }]), by simp⟩

@[expose] noncomputable def bankLeaf192 : PrimeBank := .leaf [836561914831, 840139875599, 852460489981, 858576981721, 871752897817, 883519833247, 884081512427, 890377091371, 900005345611, 900282886291, 902490190057, 916053560831, 918585913061, 933499535041, 934415109937, 949277008987]

theorem bankLeaf192_valid : bankLeaf192.Certified := by
  simp only [bankLeaf192, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 1303, 2039, 2693] }, .lucas { root := 6, primeFactors := [2, 3, 7, 31] }, .lucas { root := 7, primeFactors := [2, 1019] }, .lucas { root := 2, primeFactors := [2, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 397, 4815463] }, .lucas { root := 3, primeFactors := [2, 3, 59, 61, 223] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 29, 59, 36907469] }, .lucas { root := 2, primeFactors := [2, 13, 647, 1097] }, .lucas { root := 3, primeFactors := [2, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 439, 192611] }, .lucas { root := 18, primeFactors := [2, 5, 11, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 29, 147784129] }, .lucas { root := 7, primeFactors := [2, 3, 17, 19, 2383] }, .lucas { root := 5, primeFactors := [2, 3, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 9293, 1076417] }, .lucas { root := 2, primeFactors := [2, 23, 101] }, .lucas { root := 3, primeFactors := [2, 11, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 31, 634759] }, .lucas { root := 3, primeFactors := [2, 3, 67, 1579] }, .lucas { root := 3, primeFactors := [2, 3, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 463, 7549, 26209] }, .lucas { root := 2, primeFactors := [2, 3, 17, 37] }, .lucas { root := 11, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61, 4663, 161471] }, .lucas { root := 3, primeFactors := [2, 3, 7, 37] }, .lucas { root := 7, primeFactors := [2, 5, 67, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 107, 197, 15377] }, .lucas { root := 3, primeFactors := [2, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 37, 53, 127, 37369] }, .lucas { root := 7, primeFactors := [2, 3, 173] }]), by simp⟩

@[expose] noncomputable def bankLeaf193 : PrimeBank := .leaf [960720603511, 976278071191, 985996607929, 987900542491, 992636605033, 998125094891, 999808418797, 1037517185381, 1071419721181, 1076307159383, 1081646128183, 1081892014831, 1096259005867, 1112190585151, 1119131988031, 1122827308399]

theorem bankLeaf193_valid : bankLeaf193.Certified := by
  simp only [bankLeaf193, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 19, 31, 2861587] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 1747] }, .lucas { root := 2, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 151, 211, 269, 3797] }, .lucas { root := 2, primeFactors := [2, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 19, 23, 29, 71, 45659] }, .lucas { root := 2, primeFactors := [2, 37, 617] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 41513, 996311] }, .lucas { root := 3, primeFactors := [2, 5189] }, .lucas { root := 2, primeFactors := [2, 1297] }, .lucas { root := 10, primeFactors := [2, 3] }, .lucas { root := 7, primeFactors := [2, 5, 7, 43, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 1296266357] }, .lucas { root := 2, primeFactors := [2, 7, 11, 4208657] }, .lucas { root := 3, primeFactors := [2, 17, 15473] }, .lucas { root := 3, primeFactors := [2, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 23, 743, 443227] }, .lucas { root := 3, primeFactors := [2, 3, 7, 61, 173] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 439, 40676527] }, .lucas { root := 6, primeFactors := [2, 3, 11, 31, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 17, 37, 61, 79, 1951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 647, 5501, 50651] }, .lucas { root := 2, primeFactors := [2, 5, 11] }, .lucas { root := 2, primeFactors := [2, 5, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 11, 1092820217] }, .lucas { root := 3, primeFactors := [2, 136602527] }, .lucas { root := 5, primeFactors := [2, 487, 140249] }, .lucas { root := 3, primeFactors := [2, 47, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 9616307069] }, .lucas { root := 2, primeFactors := [2, 53, 45359939] }, .lucas { root := 2, primeFactors := [2, 13, 67, 2003] }, .lucas { root := 5, primeFactors := [2, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 31, 109, 2194319] }, .lucas { root := 7, primeFactors := [2, 7, 22391] }, .lucas { root := 13, primeFactors := [2, 5, 2239] }, .lucas { root := 3, primeFactors := [2, 3, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 592133327] }, .lucas { root := 5, primeFactors := [2, 71, 4169953] }, .lucas { root := 11, primeFactors := [2, 3, 14479] }, .lucas { root := 3, primeFactors := [2, 3, 19, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 23, 43, 63073099] }, .lucas { root := 2, primeFactors := [2, 3, 11, 461, 691] }]), by simp⟩

@[expose] noncomputable def bankLeaf194 : PrimeBank := .leaf [1125114715117, 1132827484651, 1170911630593, 1197173348741, 1221324894479, 1226812764101, 1227285212611, 1229576892433, 1273880539247, 1274564409623, 1277255785249, 1298015636963, 1315984880461, 1319008032883, 1335495402823, 1344698476591]

theorem bankLeaf194_valid : bankLeaf194.Certified := by
  simp only [bankLeaf194, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 409, 474619] }, .lucas { root := 2, primeFactors := [2, 3, 79103] }, .lucas { root := 5, primeFactors := [2, 39551] }, .lucas { root := 7, primeFactors := [2, 5, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 41, 6857, 26863] }, .lucas { root := 3, primeFactors := [2, 857] }, .lucas { root := 5, primeFactors := [2, 3, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 46200743] }, .lucas { root := 5, primeFactors := [2, 7, 19, 173687] }, .lucas { root := 5, primeFactors := [2, 86843] }, .lucas { root := 2, primeFactors := [2, 7, 6203] }, .lucas { root := 2, primeFactors := [2, 7, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 211, 313, 523, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 13, 239, 196544077] }, .lucas { root := 2, primeFactors := [2, 3, 16378673] }, .lucas { root := 3, primeFactors := [2, 113, 9059] }, .lucas { root := 2, primeFactors := [2, 7, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 159326333] }, .lucas { root := 2, primeFactors := [2, 11, 233, 15541] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 89, 331, 1388693] }, .lucas { root := 2, primeFactors := [2, 347173] }, .lucas { root := 2, primeFactors := [2, 3, 7, 4133] }, .lucas { root := 2, primeFactors := [2, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 17, 229, 134287] }, .lucas { root := 5, primeFactors := [2, 3, 22381] }, .lucas { root := 10, primeFactors := [2, 3, 5, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 23, 71, 6101, 9133] }, .lucas { root := 2, primeFactors := [2, 5, 61] }, .lucas { root := 6, primeFactors := [2, 3, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 102451, 888623] }, .lucas { root := 3, primeFactors := [2, 3, 5, 683] }, .lucas { root := 5, primeFactors := [2, 7, 63473] }, .lucas { root := 3, primeFactors := [2, 3967] }, .lucas { root := 6, primeFactors := [2, 3, 661] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 41, 36056227] }, .lucas { root := 3, primeFactors := [2, 3, 23, 227, 1151] }, .lucas { root := 17, primeFactors := [2, 5, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 83, 2477, 286981] }, .lucas { root := 2, primeFactors := [2, 619] }, .lucas { root := 6, primeFactors := [2, 3, 5, 4783] }, .lucas { root := 6, primeFactors := [2, 3, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67, 173, 809, 2339] }, .lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 3631, 217003] }, .lucas { root := 15, primeFactors := [2, 3, 5, 11] }, .lucas { root := 3, primeFactors := [2, 3, 59, 613] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 37, 173062867] }, .lucas { root := 2, primeFactors := [2, 3, 103, 280037] }, .lucas { root := 2, primeFactors := [2, 70009] }, .lucas { root := 19, primeFactors := [2, 3, 2917] }, .lucas { root := 5, primeFactors := [2, 3] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
