module

public import OddPerfect.SizePrimeBank300.Primes08
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf155 : PrimeBank := .leaf [1767059981, 1795966537, 1806482129, 1830824353, 1831394497, 1877102911, 1887117139, 1890771811, 1895333441, 1902450961, 1942157131, 1947157841, 1986459091, 1999981393, 2018659771, 2046537721]

theorem bankLeaf155_valid : bankLeaf155.Certified := by
  simp only [bankLeaf155, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 822329] }, .lucas { root := 3, primeFactors := [2, 13, 7907] }, .lucas { root := 2, primeFactors := [2, 59, 67] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 283, 3209] }, .lucas { root := 3, primeFactors := [2, 401] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 23, 5303] }, .lucas { root := 5, primeFactors := [2, 11, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 971, 107971] }, .lucas { root := 3, primeFactors := [2, 3, 5, 59, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 11, 13, 61, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 17, 47, 3307] }, .lucas { root := 2, primeFactors := [2, 3, 19, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 24339473] }, .lucas { root := 3, primeFactors := [2, 1521217] }, .lucas { root := 5, primeFactors := [2, 3, 19, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 11, 859939] }, .lucas { root := 2, primeFactors := [2, 3, 331, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71, 586849] }, .lucas { root := 11, primeFactors := [2, 3, 6113] }, .lucas { root := 3, primeFactors := [2, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 331, 67763] }, .lucas { root := 2, primeFactors := [2, 17, 1993] }, .lucas { root := 5, primeFactors := [2, 3, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 59, 96353] }, .lucas { root := 3, primeFactors := [2, 3011] }, .lucas { root := 2, primeFactors := [2, 5, 7, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf156 : PrimeBank := .leaf [2048215633, 2052890293, 2124921121, 2129902711, 2157751381, 2235195191, 2238236249, 2271543691, 2276387233, 2300865181, 2316843833, 2333282713, 2343435803, 2366169307, 2373879229, 2395275511]

theorem bankLeaf156_valid : bankLeaf156.Certified := by
  simp only [bankLeaf156, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 31, 47, 29287] }, .lucas { root := 5, primeFactors := [2, 3, 1627] }, .lucas { root := 3, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 171074191] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 29, 4013] }, .lucas { root := 2, primeFactors := [2, 17, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 17, 37201] }, .lucas { root := 7, primeFactors := [2, 3, 5, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 1240087] }, .lucas { root := 3, primeFactors := [2, 3, 41, 71] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 5824471] }, .lucas { root := 11, primeFactors := [2, 3, 5, 194149] }, .lucas { root := 2, primeFactors := [2, 3, 5393] }, .lucas { root := 3, primeFactors := [2, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 71, 47711] }, .lucas { root := 11, primeFactors := [2, 5, 13, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 38347753] }, .lucas { root := 5, primeFactors := [2, 3, 1597823] }, .lucas { root := 5, primeFactors := [2, 798911] }, .lucas { root := 11, primeFactors := [2, 5, 7, 101, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 109, 421, 6311] }, .lucas { root := 7, primeFactors := [2, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 97220113] }, .lucas { root := 5, primeFactors := [2, 3, 11, 19, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 673, 1741037] }, .lucas { root := 2, primeFactors := [2, 11, 39569] }, .lucas { root := 3, primeFactors := [2, 2473] }, .lucas { root := 5, primeFactors := [2, 3, 103] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 421, 3533] }, .lucas { root := 2, primeFactors := [2, 883] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf157 : PrimeBank := .leaf [2396970181, 2401104071, 2401511401, 2402910859, 2426723729, 2445609913, 2452859971, 2485642321, 2508541843, 2513706667, 2561074343, 2579964631, 2612510473, 2630809123, 2745256771, 2767631689]

theorem bankLeaf157_valid : bankLeaf157.Certified := by
  simp only [bankLeaf157, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 227, 5333] }, .lucas { root := 2, primeFactors := [2, 31, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 31, 103, 139, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 523, 2551] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 400485143] }, .lucas { root := 5, primeFactors := [2, 200242571] }, .lucas { root := 2, primeFactors := [2, 5, 11, 1820387] }, .lucas { root := 2, primeFactors := [2, 59, 15427] }, .lucas { root := 2, primeFactors := [2, 3, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 13, 7417] }, .lucas { root := 5, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 101900413] }, .lucas { root := 2, primeFactors := [2, 3, 2830567] }, .lucas { root := 3, primeFactors := [2, 3, 283, 1667] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 47, 1307] }, .lucas { root := 2, primeFactors := [2, 653] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 233, 94441] }, .lucas { root := 11, primeFactors := [2, 3, 5, 787] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 17, 37, 61, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 71, 167, 7253] }, .lucas { root := 2, primeFactors := [2, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13, 29, 26249] }, .lucas { root := 3, primeFactors := [2, 17, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 157, 146989] }, .lucas { root := 2, primeFactors := [2, 3, 1361] }, .lucas { root := 3, primeFactors := [2, 5, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf158 : PrimeBank := .leaf [2773167361, 2787959227, 2813416783, 2826807791, 2857757261, 2889382663, 2889765031, 2897011417, 2898485987, 2906068351, 2940027031, 2948165497, 2999246191, 3037086319, 3099719989, 3109622749]

theorem bankLeaf158_valid : bankLeaf158.Certified := by
  simp only [bankLeaf158, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 4091, 8737] }, .lucas { root := 2, primeFactors := [2, 5, 409] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 877, 322327] }, .lucas { root := 5, primeFactors := [2, 3, 47, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 142887863] }, .lucas { root := 5, primeFactors := [2, 13, 5495687] }, .lucas { root := 5, primeFactors := [2, 7, 392549] }, .lucas { root := 2, primeFactors := [2, 13, 7549] }, .lucas { root := 2, primeFactors := [2, 3, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 53, 163, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 29, 89, 37321] }, .lucas { root := 23, primeFactors := [2, 3, 5, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13, 83, 111871] }, .lucas { root := 7, primeFactors := [2, 3, 5, 11, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 19, 1619, 4283] }, .lucas { root := 2, primeFactors := [2, 809] }, .lucas { root := 2, primeFactors := [2, 2141] }, .lucas { root := 2, primeFactors := [2, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19373789] }, .lucas { root := 2, primeFactors := [2, 7, 691921] }, .lucas { root := 21, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 37, 263, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 457, 89599] }, .lucas { root := 3, primeFactors := [2, 3, 109, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 383, 261031] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7, 11, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 37, 1954367] }, .lucas { root := 5, primeFactors := [2, 977183] }, .lucas { root := 5, primeFactors := [2, 31, 15761] }, .lucas { root := 3, primeFactors := [2, 5, 197] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf159 : PrimeBank := .leaf [3133157107, 3148618279, 3158528101, 3198884209, 3234361159, 3249191191, 3259149331, 3276580189, 3308013439, 3321954973, 3325881113, 3335124931, 3359318491, 3401266261, 3408217147, 3483038983]

theorem bankLeaf159_valid : bankLeaf159.Certified := by
  simp only [bankLeaf159, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 40366901] }, .lucas { root := 2, primeFactors := [2, 5, 7, 57667] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 29, 43, 4111] }, .lucas { root := 12, primeFactors := [2, 3, 5, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 8556511] }, .lucas { root := 3, primeFactors := [2, 3, 5, 223, 1279] }, .lucas { root := 3, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 1777, 8707] }, .lucas { root := 5, primeFactors := [2, 3, 37] }, .lucas { root := 5, primeFactors := [2, 3, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 108638311] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11, 329207] }, .lucas { root := 5, primeFactors := [2, 241, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 101, 127, 3041] }, .lucas { root := 3, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 179, 193, 15959] }, .lucas { root := 11, primeFactors := [2, 79, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 41, 18913] }, .lucas { root := 7, primeFactors := [2, 3, 197] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 111170831] }, .lucas { root := 7, primeFactors := [2, 5, 11117083] }, .lucas { root := 14, primeFactors := [2, 3, 17, 108991] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 17, 199603] }, .lucas { root := 3, primeFactors := [2, 3, 13, 853] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 8098253] }, .lucas { root := 2, primeFactors := [2, 587, 3449] }, .lucas { root := 3, primeFactors := [2, 431] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 189345397] }, .lucas { root := 5, primeFactors := [2, 3, 31, 59, 8627] }, .lucas { root := 2, primeFactors := [2, 19, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 2008673] }, .lucas { root := 3, primeFactors := [2, 41, 1531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17] }]), by simp⟩

@[expose] noncomputable def bankLeaf160 : PrimeBank := .leaf [3499901929, 3501822143, 3523057633, 3564746191, 3622746821, 3706509671, 3727678613, 3927085741, 3965456029, 3968312611, 4106087021, 4216187737, 4281922861, 4305505681, 4338835663, 4356227321]

theorem bankLeaf160_valid : bankLeaf160.Certified := by
  simp only [bankLeaf160, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 17, 37, 109, 709] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 392669] }, .lucas { root := 2, primeFactors := [2, 89, 1103] }, .lucas { root := 5, primeFactors := [2, 19, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1163, 34057] }, .lucas { root := 5, primeFactors := [2, 7, 83] }, .lucas { root := 5, primeFactors := [2, 3, 11, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 133131379] }, .lucas { root := 3, primeFactors := [2, 3, 22188563] }, .lucas { root := 2, primeFactors := [2, 11, 1008571] }, .lucas { root := 3, primeFactors := [2, 3, 5, 33619] }, .lucas { root := 2, primeFactors := [2, 3, 13, 431] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 2777, 6263] }, .lucas { root := 3, primeFactors := [2, 347] }, .lucas { root := 5, primeFactors := [2, 31, 101] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 31, 53, 17851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 31, 53, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 2273, 31397] }, .lucas { root := 3, primeFactors := [2, 71] }, .lucas { root := 2, primeFactors := [2, 47, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 7, 17, 31, 1621] }, .lucas { root := 2, primeFactors := [2, 3, 5] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 97, 1122739] }, .lucas { root := 2, primeFactors := [2, 3, 187123] }, .lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]), by simp⟩

@[expose] noncomputable def bankLeaf161 : PrimeBank := .leaf [4360138339, 4363627871, 4404022699, 4416852373, 4440731591, 4454783383, 4486665151, 4507976059, 4511462359, 4665427471, 4672993939, 4802611441, 4929674461, 4933442879, 4992178363, 5126569771]

theorem bankLeaf161_valid : bankLeaf161.Certified := by
  simp only [bankLeaf161, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 43, 16899761] }, .lucas { root := 3, primeFactors := [2, 5, 211247] }, .lucas { root := 5, primeFactors := [2, 7, 79, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7, 379, 23497] }, .lucas { root := 5, primeFactors := [2, 3, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 734003783] }, .lucas { root := 5, primeFactors := [2, 19, 19315889] }, .lucas { root := 3, primeFactors := [2, 167, 7229] }, .lucas { root := 2, primeFactors := [2, 13, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 23, 179, 25763] }, .lucas { root := 5, primeFactors := [2, 11, 1171] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 43, 107, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 271, 2772433] }, .lucas { root := 5, primeFactors := [2, 3, 13, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 1013, 57097] }, .lucas { root := 7, primeFactors := [2, 3, 13, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 17, 10267] }, .lucas { root := 2, primeFactors := [2, 3, 29, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 61, 79, 5573] }, .lucas { root := 2, primeFactors := [2, 7, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 82161241] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7, 89, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 37, 732617] }, .lucas { root := 3, primeFactors := [2, 91577] }, .lucas { root := 3, primeFactors := [2, 11447] }, .lucas { root := 5, primeFactors := [2, 59, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 12379, 67213] }, .lucas { root := 2, primeFactors := [2, 3, 2063] }, .lucas { root := 5, primeFactors := [2, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }, .lucas { root := 2, primeFactors := [2, 3, 1867] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 24412237] }, .lucas { root := 6, primeFactors := [2, 3, 103, 19751] }, .lucas { root := 7, primeFactors := [2, 5, 79] }]), by simp⟩

@[expose] noncomputable def bankLeaf162 : PrimeBank := .leaf [5141996917, 5196805069, 5203368103, 5253388687, 5264187869, 5274951023, 5297786297, 5319047759, 5350412887, 5434413581, 5459407361, 5469144841, 5489122519, 5490513541, 5554122337, 5556696991]

theorem bankLeaf162_valid : bankLeaf162.Certified := by
  simp only [bankLeaf162, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 1721, 35569] }, .lucas { root := 3, primeFactors := [2, 5, 43] }, .lucas { root := 11, primeFactors := [2, 3, 13, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 10061, 86197] }, .lucas { root := 3, primeFactors := [2, 5, 503] }, .lucas { root := 2, primeFactors := [2, 3, 11, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 13, 29, 37, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1316046967] }, .lucas { root := 7, primeFactors := [2, 3, 13, 16872397] }, .lucas { root := 2, primeFactors := [2, 3, 1406033] }, .lucas { root := 3, primeFactors := [2, 87877] }, .lucas { root := 2, primeFactors := [2, 3, 2441] }, .lucas { root := 6, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 11, 41, 5848061] }, .lucas { root := 2, primeFactors := [2, 5, 269, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 53, 109, 613] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 251, 39041] }, .lucas { root := 3, primeFactors := [2, 5, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 271720679] }, .lucas { root := 17, primeFactors := [2, 3163, 42953] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }, .lucas { root := 3, primeFactors := [2, 7, 13, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 193871] }, .lucas { root := 13, primeFactors := [2, 5, 19387] }, .lucas { root := 2, primeFactors := [2, 3, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 5064023] }, .lucas { root := 5, primeFactors := [2, 233, 10867] }, .lucas { root := 2, primeFactors := [2, 3, 1811] }, .lucas { root := 6, primeFactors := [2, 5, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 9240947] }, .lucas { root := 2, primeFactors := [2, 11, 13, 79, 409] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 2755021] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17, 37, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 13, 31, 459611] }, .lucas { root := 6, primeFactors := [2, 5, 19, 41, 59] }]), by simp⟩

@[expose] noncomputable def bankLeaf163 : PrimeBank := .leaf [5608387541, 5732075647, 5815511341, 5828898601, 5846533159, 5878200649, 5927871379, 5969148541, 6056018503, 6061190089, 6149624869, 6159328577, 6199228913, 6228362269, 6250747829, 6256017851]

theorem bankLeaf163_valid : bankLeaf163.Certified := by
  simp only [bankLeaf163, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 41, 23831] }, .lucas { root := 11, primeFactors := [2, 5, 2383] }, .lucas { root := 5, primeFactors := [2, 3, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 31, 9433] }, .lucas { root := 5, primeFactors := [2, 3, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 31, 41, 76259] }, .lucas { root := 2, primeFactors := [2, 7, 13, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 37, 12503] }, .lucas { root := 5, primeFactors := [2, 7, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4447, 219119] }, .lucas { root := 3, primeFactors := [2, 3, 13, 19] }, .lucas { root := 17, primeFactors := [2, 89, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 244925027] }, .lucas { root := 2, primeFactors := [2, 122462513] }, .lucas { root := 3, primeFactors := [2, 157, 48751] }, .lucas { root := 3, primeFactors := [2, 3, 5, 13] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 99485809] }, .lucas { root := 13, primeFactors := [2, 3, 101, 20521] }, .lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5897, 171161] }, .lucas { root := 3, primeFactors := [2, 11, 67] }, .lucas { root := 6, primeFactors := [2, 5, 11, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 2161, 116867] }, .lucas { root := 23, primeFactors := [2, 3, 5] }, .lucas { root := 2, primeFactors := [2, 71, 823] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 181, 314591] }, .lucas { root := 7, primeFactors := [2, 5, 163, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 96239509] }, .lucas { root := 6, primeFactors := [2, 3, 8019959] }, .lucas { root := 17, primeFactors := [2, 83, 48313] }, .lucas { root := 5, primeFactors := [2, 3, 11, 61] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 107, 1123427] }, .lucas { root := 2, primeFactors := [2, 561713] }, .lucas { root := 3, primeFactors := [2, 35107] }, .lucas { root := 2, primeFactors := [2, 3, 5851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 227, 32423] }, .lucas { root := 5, primeFactors := [2, 13, 29, 43] }]), by simp⟩

@[expose] noncomputable def bankLeaf164 : PrimeBank := .leaf [6305373793, 6367921363, 6419358349, 6458686391, 6553160377, 6653904277, 6915876949, 7215061951, 7293259993, 7348177253, 7352086561, 7563524537, 7580566663, 7678895047, 7685542369, 7742682019]

theorem bankLeaf164_valid : bankLeaf164.Certified := by
  simp only [bankLeaf164, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 373, 110321] }, .lucas { root := 6, primeFactors := [2, 5, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 5, 13, 89, 101, 5527] }, .lucas { root := 5, primeFactors := [2, 3, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 101, 127, 3041] }, .lucas { root := 3, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 554492023] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1091, 12101] }, .lucas { root := 2, primeFactors := [2, 5, 109] }, .lucas { root := 3, primeFactors := [2, 5, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 16033471] }, .lucas { root := 15, primeFactors := [2, 3, 5, 659, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1153, 263561] }, .lucas { root := 5, primeFactors := [2, 3] }, .lucas { root := 3, primeFactors := [2, 5, 11, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 2113, 66877] }, .lucas { root := 5, primeFactors := [2, 3, 11] }, .lucas { root := 5, primeFactors := [2, 3, 5573] }, .lucas { root := 2, primeFactors := [2, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 17, 9901] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 67, 1109243] }, .lucas { root := 2, primeFactors := [2, 31, 17891] }, .lucas { root := 2, primeFactors := [2, 5, 1789] }, .lucas { root := 6, primeFactors := [2, 3, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 23, 2791, 19937] }, .lucas { root := 6, primeFactors := [2, 3, 5, 31] }, .lucas { root := 3, primeFactors := [2, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 7, 23, 83, 1997] }, .lucas { root := 2, primeFactors := [2, 499] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf165 : PrimeBank := .leaf [7801857533, 8007671311, 8056011857, 8090422789, 8209197757, 8220344521, 8331612343, 8443703269, 8575358941, 8590324811, 8602968151, 8824793797, 8922316471, 8923733659, 9023174851, 9196436593]

theorem bankLeaf165_valid : bankLeaf165.Certified := by
  simp only [bankLeaf165, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 16390457] }, .lucas { root := 3, primeFactors := [2, 61, 33587] }, .lucas { root := 6, primeFactors := [2, 7, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 127, 2101751] }, .lucas { root := 11, primeFactors := [2, 5, 7, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 26500039] }, .lucas { root := 6, primeFactors := [2, 3, 4416673] }, .lucas { root := 15, primeFactors := [2, 3, 13, 3539] }, .lucas { root := 2, primeFactors := [2, 29, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 96314557] }, .lucas { root := 2, primeFactors := [2, 3, 13, 617401] }, .lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 228033271] }, .lucas { root := 6, primeFactors := [2, 3, 5, 23, 110161] }, .lucas { root := 22, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 53, 709, 1823] }, .lucas { root := 5, primeFactors := [2, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1388602057] }, .lucas { root := 7, primeFactors := [2, 3, 57858419] }, .lucas { root := 2, primeFactors := [2, 28929209] }, .lucas { root := 3, primeFactors := [2, 7, 11, 6709] }, .lucas { root := 2, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 13, 53, 4421] }, .lucas { root := 3, primeFactors := [2, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 761, 62603] }, .lucas { root := 2, primeFactors := [2, 113, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 20233, 42457] }, .lucas { root := 5, primeFactors := [2, 3, 281] }, .lucas { root := 11, primeFactors := [2, 3, 29, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 17, 53551] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 5647, 52667] }, .lucas { root := 3, primeFactors := [2, 3, 941] }, .lucas { root := 2, primeFactors := [2, 17, 1549] }, .lucas { root := 2, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23607761] }, .lucas { root := 3, primeFactors := [2, 5, 11, 139, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 23, 83, 31511] }, .lucas { root := 7, primeFactors := [2, 5, 23, 137] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf166 : PrimeBank := .leaf [9352230341, 9370586851, 9383676751, 9471036101, 9551122621, 9597637019, 9985717993, 10057295749, 10177286401, 10214657137, 10455371551, 10460439263, 10487680421, 10564674611, 10695665473, 10721967961]

theorem bankLeaf166_valid : bankLeaf166.Certified := by
  simp only [bankLeaf166, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 101, 4629817] }, .lucas { root := 10, primeFactors := [2, 3, 64303] }, .lucas { root := 6, primeFactors := [2, 3, 7, 1531] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1381, 68581] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }, .lucas { root := 6, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 12245029] }, .lucas { root := 2, primeFactors := [2, 3, 1020419] }, .lucas { root := 2, primeFactors := [2, 7, 23, 3169] }, .lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 208644283] }, .lucas { root := 20, primeFactors := [2, 3, 7, 11, 19, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 2837, 8627] }, .lucas { root := 2, primeFactors := [2, 709] }, .lucas { root := 2, primeFactors := [2, 19, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 22651567] }, .lucas { root := 3, primeFactors := [2, 3, 7, 539323] }, .lucas { root := 2, primeFactors := [2, 3, 7, 12841] }, .lucas { root := 21, primeFactors := [2, 3, 5, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 151, 469769] }, .lucas { root := 3, primeFactors := [2, 13, 4517] }, .lucas { root := 2, primeFactors := [2, 1129] }, .lucas { root := 11, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 31, 57653] }, .lucas { root := 2, primeFactors := [2, 7, 29, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 163, 352607] }, .lucas { root := 5, primeFactors := [2, 176303] }, .lucas { root := 15, primeFactors := [2, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 19, 101, 103, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 73, 2067451] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 23, 353161] }, .lucas { root := 22, primeFactors := [2, 3, 5, 109] }]), by simp⟩

@[expose] noncomputable def bankLeaf167 : PrimeBank := .leaf [10822630597, 11018941331, 11242578713, 11300690413, 11461748923, 11466709231, 11549197141, 11616639863, 11738616277, 11910033901, 11967024851, 12081356831, 12091081603, 12117963973, 12244884163, 12246841879]

theorem bankLeaf167_valid : bankLeaf167.Certified := by
  simp only [bankLeaf167, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 28537097] }, .lucas { root := 3, primeFactors := [2, 7, 509591] }, .lucas { root := 11, primeFactors := [2, 5, 131, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 151, 227, 1429] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 382223641] }, .lucas { root := 17, primeFactors := [2, 3, 5, 3185197] }, .lucas { root := 2, primeFactors := [2, 3, 7, 5417] }, .lucas { root := 3, primeFactors := [2, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 43, 53, 73, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 14657, 20857] }, .lucas { root := 3, primeFactors := [2, 229] }, .lucas { root := 10, primeFactors := [2, 3, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 67, 14600269] }, .lucas { root := 2, primeFactors := [2, 3, 47, 8629] }, .lucas { root := 6, primeFactors := [2, 3, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 67, 263, 751] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 47, 457, 1013] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2015180267] }, .lucas { root := 2, primeFactors := [2, 11, 199, 460297] }, .lucas { root := 7, primeFactors := [2, 3, 2131] }, .lucas { root := 2, primeFactors := [2, 3, 5, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1009830331] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11220337] }, .lucas { root := 11, primeFactors := [2, 3, 19, 1367] }, .lucas { root := 5, primeFactors := [2, 683] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 291544861] }, .lucas { root := 6, primeFactors := [2, 3, 5, 4859081] }, .lucas { root := 3, primeFactors := [2, 5, 331, 367] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf168 : PrimeBank := .leaf [12346432697, 12533290309, 12821654851, 12877987183, 12926572181, 12936304421, 12982873237, 13189649827, 13483794013, 13517349613, 13608804697, 13751549137, 13818703441, 13878036481, 13971969971, 14027349673]

theorem bankLeaf168_valid : bankLeaf168.Certified := by
  simp only [bankLeaf168, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11, 4521389] }, .lucas { root := 2, primeFactors := [2, 17, 66491] }, .lucas { root := 2, primeFactors := [2, 5, 61, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 107, 491, 1627] }, .lucas { root := 3, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 379, 131701] }, .lucas { root := 6, primeFactors := [2, 3, 5, 439] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 37307107] }, .lucas { root := 2, primeFactors := [2, 3, 2072617] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 223, 347, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 103, 841259] }, .lucas { root := 2, primeFactors := [2, 11, 38239] }, .lucas { root := 13, primeFactors := [2, 3, 6373] }, .lucas { root := 2, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 8463187] }, .lucas { root := 2, primeFactors := [2, 3, 29, 31, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 19, 59, 6553] }, .lucas { root := 10, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 223, 258197] }, .lucas { root := 2, primeFactors := [2, 17, 3797] }, .lucas { root := 2, primeFactors := [2, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 7, 11, 5867] }, .lucas { root := 5, primeFactors := [2, 7, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 37, 5394583] }, .lucas { root := 3, primeFactors := [2, 3, 299699] }, .lucas { root := 2, primeFactors := [2, 7, 21407] }, .lucas { root := 5, primeFactors := [2, 7, 11, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 17, 61, 26839] }, .lucas { root := 3, primeFactors := [2, 3, 7, 71] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
