module

public import OddPerfect.SizePrimeBank300.Primes13
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.IndexComponent.SizePrimeBank300

set_option maxRecDepth 20000
set_option maxHeartbeats 0

@[expose] noncomputable def bankLeaf220 : PrimeBank := .leaf [223957037756467, 230464097482937, 230706970592411, 232521698460221, 232619462237557, 234644065482067, 234784582614581, 234895531489741, 236032642533997, 237899493854161, 238441665492001, 239390727985399, 242281924709761, 247544928465283, 248531574771551, 248554705490239]

theorem bankLeaf220_valid : bankLeaf220.Certified := by
  simp only [bankLeaf220, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 2069, 5003, 171713] }, .lucas { root := 2, primeFactors := [2, 11, 47] }, .lucas { root := 2, primeFactors := [2, 41, 61] }, .lucas { root := 3, primeFactors := [2, 2683] }, .lucas { root := 2, primeFactors := [2, 3, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 31, 419, 2011, 47951] }, .lucas { root := 3, primeFactors := [2, 3, 5, 67] }, .lucas { root := 7, primeFactors := [2, 5, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 43, 73, 565361263] }, .lucas { root := 3, primeFactors := [2, 3, 163, 64231] }, .lucas { root := 12, primeFactors := [2, 3, 5, 2141] }, .lucas { root := 2, primeFactors := [2, 5, 107] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 141221, 15251867] }, .lucas { root := 2, primeFactors := [2, 5, 23, 307] }, .lucas { root := 2, primeFactors := [2, 7, 487, 2237] }, .lucas { root := 2, primeFactors := [2, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11831, 16693, 198017] }, .lucas { root := 7, primeFactors := [2, 5, 7, 13] }, .lucas { root := 2, primeFactors := [2, 3, 13, 107] }, .lucas { root := 6, primeFactors := [2, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 12517, 27611, 33967] }, .lucas { root := 6, primeFactors := [2, 3, 7, 149] }, .lucas { root := 2, primeFactors := [2, 5, 11, 251] }, .lucas { root := 3, primeFactors := [2, 3, 17, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 19, 16673, 268789] }, .lucas { root := 3, primeFactors := [2, 521] }, .lucas { root := 2, primeFactors := [2, 3, 13, 1723] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 193, 11439343] }, .lucas { root := 3, primeFactors := [2, 3, 635519] }, .lucas { root := 11, primeFactors := [2, 13, 24443] }, .lucas { root := 2, primeFactors := [2, 11, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 79, 97, 2671, 177211] }, .lucas { root := 7, primeFactors := [2, 3, 5, 89] }, .lucas { root := 10, primeFactors := [2, 3, 5, 11, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 7369, 48787] }, .lucas { root := 7, primeFactors := [2, 3, 307] }, .lucas { root := 2, primeFactors := [2, 3, 47, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 83, 15559, 217333] }, .lucas { root := 3, primeFactors := [2, 3, 2593] }, .lucas { root := 7, primeFactors := [2, 3] }, .lucas { root := 2, primeFactors := [2, 3, 6037] }, .lucas { root := 5, primeFactors := [2, 3, 503] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 7, 710090213633] }, .lucas { root := 3, primeFactors := [2, 103, 139, 193741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 3229] }, .lucas { root := 6, primeFactors := [2, 3, 269] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf221 : PrimeBank := .leaf [253067024871751, 258381756584713, 262349354591659, 269282504108399, 272509811686691, 275434440766579, 281362890397573, 282097794109643, 285996443195311, 288197171658101, 288389032776263, 288848538414427, 291944018133683, 292502835310001, 292938126094387, 294211030224641]

theorem bankLeaf221_valid : bankLeaf221.Certified := by
  simp only [bankLeaf221, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 83, 2275609073] }, .lucas { root := 3, primeFactors := [2, 11, 71, 182107] }, .lucas { root := 2, primeFactors := [2, 3, 67, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 41, 251, 24847063] }, .lucas { root := 5, primeFactors := [2, 3, 4141177] }, .lucas { root := 5, primeFactors := [2, 3, 13, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 17, 211, 35117, 97171] }, .lucas { root := 2, primeFactors := [2, 8779] }, .lucas { root := 11, primeFactors := [2, 3, 7, 11, 19] }, .lucas { root := 10, primeFactors := [2, 3, 5, 41, 79] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2483641, 6161081] }, .lucas { root := 7, primeFactors := [2, 3, 5, 6899] }, .lucas { root := 2, primeFactors := [2, 3449] }, .lucas { root := 3, primeFactors := [2, 431] }, .lucas { root := 3, primeFactors := [2, 5, 154027] }, .lucas { root := 2, primeFactors := [2, 3, 43, 199] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 160841, 17918141] }, .lucas { root := 3, primeFactors := [2, 5, 4021] }, .lucas { root := 2, primeFactors := [2, 3, 5, 67] }, .lucas { root := 2, primeFactors := [2, 5, 19, 61, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 29, 167, 2706709147] }, .lucas { root := 3, primeFactors := [2, 3, 97, 109, 42667] }, .lucas { root := 7, primeFactors := [2, 3, 13, 547] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 48141423069071] }, .lucas { root := 17, primeFactors := [2, 5, 61, 78920365687] }, .lucas { root := 3, primeFactors := [2, 3, 13153394281] }, .lucas { root := 17, primeFactors := [2, 3, 5, 13, 29, 167, 1741] }, .lucas { root := 2, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 113, 44544403133] }, .lucas { root := 2, primeFactors := [2, 11136100783] }, .lucas { root := 5, primeFactors := [2, 3, 1856016797] }, .lucas { root := 2, primeFactors := [2, 881, 526679] }, .lucas { root := 23, primeFactors := [2, 71, 3709] }, .lucas { root := 2, primeFactors := [2, 3, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 4178611933] }, .lucas { root := 2, primeFactors := [2, 3, 11, 31656151] }, .lucas { root := 3, primeFactors := [2, 3, 5, 131, 179] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 2311, 99460133] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }, .lucas { root := 2, primeFactors := [2, 17, 313, 4673] }, .lucas { root := 3, primeFactors := [2, 73] }]), by simp⟩

@[expose] noncomputable def bankLeaf222 : PrimeBank := .leaf [295127290051981, 297003021451861, 297337950655117, 298201259281183, 303236760454211, 303567967057423, 304018940824561, 307940520066469, 308599047587209, 312076885622591, 320592990263761, 320683080755221, 327550613699641, 332142098321281, 338220607644037, 343632680481721]

theorem bankLeaf222_valid : bankLeaf222.Certified := by
  simp only [bankLeaf222, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 347, 14175182039] }, .lucas { root := 7, primeFactors := [2, 16333, 433943] }, .lucas { root := 2, primeFactors := [2, 3, 1361] }, .lucas { root := 3, primeFactors := [2, 5, 17] }, .lucas { root := 5, primeFactors := [2, 17, 12763] }, .lucas { root := 2, primeFactors := [2, 3, 709] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 83, 42647439853] }, .lucas { root := 2, primeFactors := [2, 3, 1184651107] }, .lucas { root := 2, primeFactors := [2, 3, 97, 617, 3299] }, .lucas { root := 2, primeFactors := [2, 17, 97] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 19, 23, 10883, 579641] }, .lucas { root := 2, primeFactors := [2, 5441] }, .lucas { root := 3, primeFactors := [2, 5, 17] }, .lucas { root := 6, primeFactors := [2, 5, 43, 337] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 19, 79448018593] }, .lucas { root := 7, primeFactors := [2, 3, 29, 984047] }, .lucas { root := 5, primeFactors := [2, 7, 70289] }, .lucas { root := 3, primeFactors := [2, 23, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 23, 431, 185302037] }, .lucas { root := 2, primeFactors := [2, 46325509] }, .lucas { root := 2, primeFactors := [2, 3, 73, 52883] }, .lucas { root := 2, primeFactors := [2, 137, 193] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17, 314395177211] }, .lucas { root := 2, primeFactors := [2, 5, 19, 31, 53377789] }, .lucas { root := 2, primeFactors := [2, 3, 4448149] }, .lucas { root := 6, primeFactors := [2, 3, 370679] }, .lucas { root := 7, primeFactors := [2, 7, 11, 29, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 547, 4990106851] }, .lucas { root := 3, primeFactors := [2, 3, 5, 29, 149, 7699] }, .lucas { root := 3, primeFactors := [2, 3, 1283] }, .lucas { root := 2, primeFactors := [2, 641] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 13306975093] }, .lucas { root := 5, primeFactors := [2, 3, 163, 2267719] }, .lucas { root := 21, primeFactors := [2, 3, 151, 2503] }, .lucas { root := 3, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 13, 19, 38036505583] }, .lucas { root := 3, primeFactors := [2, 3, 704379733] }, .lucas { root := 2, primeFactors := [2, 3, 7, 43, 191, 1021] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf223 : PrimeBank := .leaf [344461909346017, 347568611538691, 348243701878307, 348764834786503, 357516255917731, 358339387953089, 359137364064029, 361673794672711, 362204827770839, 363063988082203, 367091516400121, 383666297522203, 412116160123267, 420262176997681, 429593155185361, 439409519511359]

theorem bankLeaf223_valid : bankLeaf223.Certified := by
  simp only [bankLeaf223, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 11, 17, 61, 44936629] }, .lucas { root := 23, primeFactors := [2, 3, 11, 340429] }, .lucas { root := 2, primeFactors := [2, 3, 11, 2579] }, .lucas { root := 2, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 31, 61, 7083018791] }, .lucas { root := 7, primeFactors := [2, 5, 708301879] }, .lucas { root := 3, primeFactors := [2, 3, 37, 311, 10259] }, .lucas { root := 2, primeFactors := [2, 23, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 43, 5167, 261622157] }, .lucas { root := 6, primeFactors := [2, 3, 7, 41] }, .lucas { root := 2, primeFactors := [2, 65405539] }, .lucas { root := 2, primeFactors := [2, 3, 11, 330331] }, .lucas { root := 12, primeFactors := [2, 3, 5, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 37, 97, 2221, 2347] }, .lucas { root := 2, primeFactors := [2, 3, 5, 37] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 29, 193070790923] }, .lucas { root := 2, primeFactors := [2, 23, 4197191107] }, .lucas { root := 3, primeFactors := [2, 3, 433, 523, 3089] }, .lucas { root := 3, primeFactors := [2, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 11, 17, 25603, 1103111] }, .lucas { root := 2, primeFactors := [2, 3, 17, 251] }, .lucas { root := 7, primeFactors := [2, 5, 110311] }, .lucas { root := 6, primeFactors := [2, 3, 5, 3677] }, .lucas { root := 2, primeFactors := [2, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 13, 223633, 4146833] }, .lucas { root := 5, primeFactors := [2, 3, 1553] }, .lucas { root := 3, primeFactors := [2, 97] }, .lucas { root := 3, primeFactors := [2, 259177] }, .lucas { root := 5, primeFactors := [2, 3, 10799] }, .lucas { root := 19, primeFactors := [2, 5399] }, .lucas { root := 7, primeFactors := [2, 2699] }, .lucas { root := 2, primeFactors := [2, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 13, 197, 70715507179] }, .lucas { root := 3, primeFactors := [2, 3, 11785917863] }, .lucas { root := 5, primeFactors := [2, 17, 311, 1114613] }, .lucas { root := 2, primeFactors := [2, 67, 4159] }, .lucas { root := 3, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17, 457, 521, 1359053] }, .lucas { root := 2, primeFactors := [2, 47, 7229] }, .lucas { root := 2, primeFactors := [2, 13, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 68683, 14846449] }, .lucas { root := 2, primeFactors := [2, 3, 11447] }, .lucas { root := 5, primeFactors := [2, 59, 97] }, .lucas { root := 11, primeFactors := [2, 3, 19, 73, 223] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 311, 3499, 19587401] }, .lucas { root := 2, primeFactors := [2, 3, 11, 53] }, .lucas { root := 3, primeFactors := [2, 5, 7, 17, 823] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 881, 6211, 660659] }, .lucas { root := 2, primeFactors := [2, 3, 5, 23] }, .lucas { root := 2, primeFactors := [2, 330329] }, .lucas { root := 3, primeFactors := [2, 157, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 31, 56486851747] }, .lucas { root := 2, primeFactors := [2, 3, 13, 29, 4909, 5087] }, .lucas { root := 6, primeFactors := [2, 3, 409] }, .lucas { root := 5, primeFactors := [2, 2543] }, .lucas { root := 5, primeFactors := [2, 31, 41] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 11, 7691, 2596952279] }, .lucas { root := 2, primeFactors := [2, 5, 769] }, .lucas { root := 11, primeFactors := [2, 1298476139] }, .lucas { root := 2, primeFactors := [2, 349, 1860281] }, .lucas { root := 6, primeFactors := [2, 5, 46507] }, .lucas { root := 2, primeFactors := [2, 3, 23, 337] }]), by simp⟩

@[expose] noncomputable def bankLeaf224 : PrimeBank := .leaf [439552815560351, 443225178468643, 445455365264339, 457088476683403, 471533259687799, 475384700124973, 475686345674143, 481003352262457, 487247779146731, 492466462994279, 493295840179661, 493616224077391, 495841482334633, 496833428679257, 503310484468801, 514864412568431]

theorem bankLeaf224_valid : bankLeaf224.Certified := by
  simp only [bankLeaf224, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3000029, 24623383] }, .lucas { root := 2, primeFactors := [2, 23, 32609] }, .lucas { root := 3, primeFactors := [2, 1019] }, .lucas { root := 5, primeFactors := [2, 3, 7, 61, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1277, 37619, 176201] }, .lucas { root := 2, primeFactors := [2, 11, 29] }, .lucas { root := 2, primeFactors := [2, 7, 2687] }, .lucas { root := 5, primeFactors := [2, 17, 79] }, .lucas { root := 6, primeFactors := [2, 5, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 11, 954979, 1068751] }, .lucas { root := 3, primeFactors := [2, 3, 19, 8377] }, .lucas { root := 5, primeFactors := [2, 3, 349] }, .lucas { root := 3, primeFactors := [2, 3, 5, 19] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 887, 2141, 3665317] }, .lucas { root := 2, primeFactors := [2, 5, 107] }, .lucas { root := 2, primeFactors := [2, 3, 31, 59, 167] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 9013, 608523767] }, .lucas { root := 5, primeFactors := [2, 3, 751] }, .lucas { root := 5, primeFactors := [2, 73, 107, 38953] }, .lucas { root := 5, primeFactors := [2, 3, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 21859, 135021611] }, .lucas { root := 2, primeFactors := [2, 3, 3643] }, .lucas { root := 2, primeFactors := [2, 3, 607] }, .lucas { root := 2, primeFactors := [2, 5, 41, 329321] }, .lucas { root := 3, primeFactors := [2, 5, 8233] }, .lucas { root := 10, primeFactors := [2, 3, 7] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 38, primeFactors := [2, 3, 5, 17, 29, 875269] }, .lucas { root := 2, primeFactors := [2, 3, 41, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 17, 41, 79, 935046061] }, .lucas { root := 2, primeFactors := [2, 3, 5, 13, 379, 3163] }, .lucas { root := 3, primeFactors := [2, 3, 17, 31] }]), by simp⟩

@[expose] noncomputable def bankLeaf225 : PrimeBank := .leaf [520518327319589, 530468431681571, 539071637349799, 551178466726889, 551780297067913, 556126718788891, 557597259471113, 559016688150211, 566243024527183, 590385607384351, 596162293003363, 600803554877143, 607453794248251, 610391728348403, 613388130561469, 639334696481669]

theorem bankLeaf225_valid : bankLeaf225.Certified := by
  simp only [bankLeaf225, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 61, 443, 1319, 280837] }, .lucas { root := 13, primeFactors := [2, 659] }, .lucas { root := 2, primeFactors := [2, 3, 29, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 53046843168157] }, .lucas { root := 2, primeFactors := [2, 3, 23, 49037, 3919463] }, .lucas { root := 2, primeFactors := [2, 13, 23, 41] }, .lucas { root := 5, primeFactors := [2, 1959731] }, .lucas { root := 6, primeFactors := [2, 5, 195973] }, .lucas { root := 2, primeFactors := [2, 3, 7, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17, 16127, 15605347] }, .lucas { root := 5, primeFactors := [2, 11, 733] }, .lucas { root := 2, primeFactors := [2, 3, 19, 136889] }, .lucas { root := 3, primeFactors := [2, 71, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 13, 601, 1307, 87623] }, .lucas { root := 2, primeFactors := [2, 653] }, .lucas { root := 5, primeFactors := [2, 193, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 181, 263, 43906411] }, .lucas { root := 10, primeFactors := [2, 3, 5, 17, 28697] }, .lucas { root := 3, primeFactors := [2, 17, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 229, 8994447983] }, .lucas { root := 5, primeFactors := [2, 13, 4547, 76081] }, .lucas { root := 2, primeFactors := [2, 2273] }, .lucas { root := 3, primeFactors := [2, 71] }, .lucas { root := 7, primeFactors := [2, 3, 5, 317] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 59, 315828637373] }, .lucas { root := 2, primeFactors := [2, 29, 359, 7584013] }, .lucas { root := 6, primeFactors := [2, 3, 293, 719] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 157, 25261, 23795861] }, .lucas { root := 7, primeFactors := [2, 3, 5, 421] }, .lucas { root := 2, primeFactors := [2, 5, 11, 9833] }, .lucas { root := 3, primeFactors := [2, 1229] }, .lucas { root := 2, primeFactors := [2, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 71, 55435268299] }, .lucas { root := 3, primeFactors := [2, 3, 43, 10667, 20143] }, .lucas { root := 2, primeFactors := [2, 5333] }, .lucas { root := 2, primeFactors := [2, 31, 43] }, .lucas { root := 5, primeFactors := [2, 3, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 587, 271273, 623977] }, .lucas { root := 5, primeFactors := [2, 3, 89, 127] }, .lucas { root := 5, primeFactors := [2, 3, 25999] }, .lucas { root := 7, primeFactors := [2, 3, 7, 619] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17, 167, 285290029] }, .lucas { root := 2, primeFactors := [2, 3, 181, 43783] }, .lucas { root := 3, primeFactors := [2, 3, 7297] }, .lucas { root := 5, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 13, 37, 47, 175325459] }, .lucas { root := 6, primeFactors := [2, 7, 11, 23, 49499] }, .lucas { root := 2, primeFactors := [2, 24749] }, .lucas { root := 2, primeFactors := [2, 23, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5679519727421] }, .lucas { root := 13, primeFactors := [2, 5, 7, 11, 3687999823] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17, 34337] }, .lucas { root := 3, primeFactors := [2, 29, 37] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf226 : PrimeBank := .leaf [679078783976611, 680310719936857, 701981263105541, 714219756551929, 718247912206681, 727321051984843, 727642843683307, 739367693312861, 742915421345899, 745401181939717, 752471551093711, 800672808675011, 807813012557149, 829007553280001, 833039147209543, 835433438134111]

theorem bankLeaf226_valid : bankLeaf226.Certified := by
  simp only [bankLeaf226, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 37, 71, 937, 1296293] }, .lucas { root := 2, primeFactors := [2, 324073] }, .lucas { root := 5, primeFactors := [2, 3, 7, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 11, 860927, 1047467] }, .lucas { root := 5, primeFactors := [2, 11, 39133] }, .lucas { root := 5, primeFactors := [2, 3, 1087] }, .lucas { root := 3, primeFactors := [2, 3, 181] }, .lucas { root := 2, primeFactors := [2, 7, 23, 3253] }, .lucas { root := 2, primeFactors := [2, 3, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 43, 46398443941] }, .lucas { root := 6, primeFactors := [2, 3, 5, 43, 5994631] }, .lucas { root := 11, primeFactors := [2, 3, 5, 43, 1549] }, .lucas { root := 2, primeFactors := [2, 3, 43] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1553, 3457, 6885883] }, .lucas { root := 3, primeFactors := [2, 97] }, .lucas { root := 7, primeFactors := [2, 3] }, .lucas { root := 2, primeFactors := [2, 3, 382549] }, .lucas { root := 2, primeFactors := [2, 3, 71, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 53, 811, 6275939] }, .lucas { root := 2, primeFactors := [2, 101, 31069] }, .lucas { root := 2, primeFactors := [2, 3, 863] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 41, 52242863887] }, .lucas { root := 3, primeFactors := [2, 3, 2902381327] }, .lucas { root := 5, primeFactors := [2, 3, 13, 954103] }, .lucas { root := 5, primeFactors := [2, 3, 159017] }, .lucas { root := 3, primeFactors := [2, 11, 13, 139] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 29, 113, 1285952827] }, .lucas { root := 3, primeFactors := [2, 3, 179, 1197349] }, .lucas { root := 6, primeFactors := [2, 3, 113, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 43, 107, 6863, 163991] }, .lucas { root := 5, primeFactors := [2, 47, 73] }, .lucas { root := 7, primeFactors := [2, 5, 23, 31] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 73, 20900174299] }, .lucas { root := 3, primeFactors := [2, 3, 283, 2153, 5717] }, .lucas { root := 3, primeFactors := [2, 269] }, .lucas { root := 2, primeFactors := [2, 1429] }, .lucas { root := 6, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 43, 73, 77617, 114299] }, .lucas { root := 10, primeFactors := [2, 3, 7, 11] }, .lucas { root := 2, primeFactors := [2, 57149] }, .lucas { root := 2, primeFactors := [2, 7, 13, 157] }]), by simp⟩

@[expose] noncomputable def bankLeaf227 : PrimeBank := .leaf [839108393120143, 846503547981397, 860725245075571, 890196300145741, 893736880630277, 934388984224343, 950274111010589, 990643452963163, 1020392150510893, 1020646088677639, 1036950426156829, 1048870798357201, 1053085325072189, 1072619513920769, 1096741684364621, 1099298734488491]

theorem bankLeaf227_valid : bankLeaf227.Certified := by
  simp only [bankLeaf227, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 719, 3164877847] }, .lucas { root := 3, primeFactors := [2, 3, 13, 127, 11833] }, .lucas { root := 5, primeFactors := [2, 3, 17, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 2119515000347] }, .lucas { root := 2, primeFactors := [2, 23, 46076413051] }, .lucas { root := 3, primeFactors := [2, 3, 5, 102392029] }, .lucas { root := 2, primeFactors := [2, 3, 2844223] }, .lucas { root := 3, primeFactors := [2, 3, 474037] }, .lucas { root := 5, primeFactors := [2, 3, 39503] }, .lucas { root := 5, primeFactors := [2, 19751] }, .lucas { root := 7, primeFactors := [2, 5, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 53, 73823, 57106051] }, .lucas { root := 5, primeFactors := [2, 7, 5273] }, .lucas { root := 3, primeFactors := [2, 659] }, .lucas { root := 2, primeFactors := [2, 3, 5, 380707] }, .lucas { root := 2, primeFactors := [2, 3, 107, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 23, 151, 134521880827] }, .lucas { root := 5, primeFactors := [2, 3, 229, 97905299] }, .lucas { root := 2, primeFactors := [2, 163, 300323] }, .lucas { root := 2, primeFactors := [2, 11, 17, 73] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71, 2325454114937] }, .lucas { root := 3, primeFactors := [2, 185951, 1563217] }, .lucas { root := 17, primeFactors := [2, 5, 3719] }, .lucas { root := 7, primeFactors := [2, 11, 13] }, .lucas { root := 5, primeFactors := [2, 3, 29, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 22727, 120692993] }, .lucas { root := 5, primeFactors := [2, 11, 1033] }, .lucas { root := 5, primeFactors := [2, 3, 43] }, .lucas { root := 3, primeFactors := [2, 7, 47, 1433] }, .lucas { root := 3, primeFactors := [2, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 31, 41, 953, 1614233] }, .lucas { root := 3, primeFactors := [2, 23, 31, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 389, 222140194121] }, .lucas { root := 6, primeFactors := [2, 5, 13, 427192681] }, .lucas { root := 14, primeFactors := [2, 3, 5, 167, 21317] }, .lucas { root := 2, primeFactors := [2, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 41, primeFactors := [2, 3, 5, 7, 13, 8219, 1168639] }, .lucas { root := 2, primeFactors := [2, 7, 587] }, .lucas { root := 3, primeFactors := [2, 3, 31, 61, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 971, 14270222303] }, .lucas { root := 5, primeFactors := [2, 7, 521, 1956433] }, .lucas { root := 7, primeFactors := [2, 3, 40759] }, .lucas { root := 3, primeFactors := [2, 3, 6793] }, .lucas { root := 10, primeFactors := [2, 3, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 149, 1801, 1419427] }, .lucas { root := 11, primeFactors := [2, 3, 5] }, .lucas { root := 2, primeFactors := [2, 3, 78857] }, .lucas { root := 3, primeFactors := [2, 9857] }, .lucas { root := 5, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 1119124167719] }, .lucas { root := 19, primeFactors := [2, 29, 131, 147291941] }, .lucas { root := 3, primeFactors := [2, 5, 179, 41143] }, .lucas { root := 3, primeFactors := [2, 3, 6857] }, .lucas { root := 3, primeFactors := [2, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1181, 93082026629] }, .lucas { root := 7, primeFactors := [2, 5, 59] }, .lucas { root := 2, primeFactors := [2, 23, 229, 4418171] }, .lucas { root := 2, primeFactors := [2, 5, 37, 11941] }, .lucas { root := 10, primeFactors := [2, 3, 5, 199] }]), by simp⟩

@[expose] noncomputable def bankLeaf228 : PrimeBank := .leaf [1119754280001961, 1136796912795881, 1146504157422163, 1155775441150339, 1162191861700663, 1163018639068051, 1166355026258533, 1172635890975721, 1204468334955733, 1266189052768483, 1279548322755509, 1331399425301563, 1364743088602021, 1399194088311829, 1416258521793067, 1437263292796553]

theorem bankLeaf228_valid : bankLeaf228.Certified := by
  simp only [bankLeaf228, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 53, 164809, 356093] }, .lucas { root := 11, primeFactors := [2, 3, 7, 109] }, .lucas { root := 2, primeFactors := [2, 11, 8093] }, .lucas { root := 2, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 113, 35929105967] }, .lucas { root := 10, primeFactors := [2, 13, 23, 37, 71, 22871] }, .lucas { root := 7, primeFactors := [2, 5, 2287] }, .lucas { root := 19, primeFactors := [2, 3, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 1301, 20743, 91957] }, .lucas { root := 2, primeFactors := [2, 5, 13] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }, .lucas { root := 7, primeFactors := [2, 3, 79, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 1051, 183281865073] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7] }, .lucas { root := 10, primeFactors := [2, 3, 41, 93131029] }, .lucas { root := 6, primeFactors := [2, 3, 59, 163, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 14899895662829] }, .lucas { root := 2, primeFactors := [2, 11, 15233, 22230289] }, .lucas { root := 3, primeFactors := [2, 7, 17] }, .lucas { root := 23, primeFactors := [2, 3, 17, 1009] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 2778109, 3180589] }, .lucas { root := 2, primeFactors := [2, 3, 37, 6257] }, .lucas { root := 3, primeFactors := [2, 17, 23] }, .lucas { root := 7, primeFactors := [2, 3, 127, 2087] }, .lucas { root := 5, primeFactors := [2, 7, 149] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 19, 9801031271] }, .lucas { root := 13, primeFactors := [2, 5, 113, 167, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 31, 71, 103, 463, 105817] }, .lucas { root := 5, primeFactors := [2, 3, 4409] }, .lucas { root := 3, primeFactors := [2, 19, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 463, 251834789113] }, .lucas { root := 5, primeFactors := [2, 3, 20899, 502087] }, .lucas { root := 2, primeFactors := [2, 3, 43] }, .lucas { root := 3, primeFactors := [2, 3, 13, 41, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 43, 71, 757, 2084359] }, .lucas { root := 3, primeFactors := [2, 3, 37, 41, 229] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel), by simp⟩

@[expose] noncomputable def bankLeaf229 : PrimeBank := .leaf [1447553814182867, 1451303919735613, 1456785048372361, 1480439269830463, 1621781727656533, 1624699112891177, 1670658319616551, 1675411861177363, 1820210818824647, 1949751789915161, 1954904836276391, 1958423494433591, 1974702993887119, 1993800800670793, 2105339491746149, 2232385011981583]

theorem bankLeaf229_valid : bankLeaf229.Certified := by
  simp only [bankLeaf229, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 17, 41, 6144481481] }, .lucas { root := 6, primeFactors := [2, 5, 31, 103, 48109] }, .lucas { root := 2, primeFactors := [2, 3, 19, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 120941993311301] }, .lucas { root := 3, primeFactors := [2, 5, 7, 53, 42751, 76253] }, .lucas { root := 6, primeFactors := [2, 3, 5, 19] }, .lucas { root := 2, primeFactors := [2, 11, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 266671, 929057] }, .lucas { root := 6, primeFactors := [2, 3, 5, 2963] }, .lucas { root := 2, primeFactors := [2, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }, .lucas { root := 3, primeFactors := [2, 29033] }, .lucas { root := 3, primeFactors := [2, 19, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 157, 50696502631] }, .lucas { root := 3, primeFactors := [2, 3, 5, 107, 15793303] }, .lucas { root := 3, primeFactors := [2, 3, 7, 37, 10163] }, .lucas { root := 2, primeFactors := [2, 5081] }, .lucas { root := 3, primeFactors := [2, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 241919, 42973213] }, .lucas { root := 13, primeFactors := [2, 29, 43, 97] }, .lucas { root := 2, primeFactors := [2, 3, 17, 19, 11087] }, .lucas { root := 5, primeFactors := [2, 23, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 3881, 83077, 89983] }, .lucas { root := 13, primeFactors := [2, 5, 97] }, .lucas { root := 14, primeFactors := [2, 3, 7, 23, 43] }, .lucas { root := 3, primeFactors := [2, 3, 4999] }, .lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11, 43, 563, 3802193] }, .lucas { root := 3, primeFactors := [2, 71, 3347] }, .lucas { root := 2, primeFactors := [2, 7, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 17, 2371, 12852899] }, .lucas { root := 2, primeFactors := [2, 3, 5, 79] }, .lucas { root := 2, primeFactors := [2, 1409, 4561] }, .lucas { root := 3, primeFactors := [2, 11] }, .lucas { root := 11, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 53, 17171800177591] }, .lucas { root := 11, primeFactors := [2, 3, 5, 79, 113, 409, 17419] }, .lucas { root := 3, primeFactors := [2, 3, 2903] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 89, 997, 37889, 58147] }, .lucas { root := 3, primeFactors := [2, 37] }, .lucas { root := 3, primeFactors := [2, 3, 11, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 73, 2682771910183] }, .lucas { root := 6, primeFactors := [2, 3, 7, 13, 1637833889] }, .lucas { root := 3, primeFactors := [2, 41, 1248349] }, .lucas { root := 6, primeFactors := [2, 3, 23, 4523] }, .lucas { root := 5, primeFactors := [2, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 163, 79631, 2305091] }, .lucas { root := 13, primeFactors := [2, 5, 7963] }, .lucas { root := 5, primeFactors := [2, 3, 1327] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }, .lucas { root := 2, primeFactors := [2, 5, 353, 653] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 10741528019113] }, .lucas { root := 13, primeFactors := [2, 3, 11, 307, 132532919] }, .lucas { root := 7, primeFactors := [2, 7, 17, 556861] }, .lucas { root := 2, primeFactors := [2, 3, 5, 9281] }, .lucas { root := 3, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 109, 971, 7919, 443917] }, .lucas { root := 7, primeFactors := [2, 37, 107] }, .lucas { root := 7, primeFactors := [2, 3, 11, 19, 59] }]), by simp⟩

@[expose] noncomputable def bankLeaf230 : PrimeBank := .leaf [2238325969879561, 2240060022926953, 2249049650927341, 2256275128193893, 2268500435671871, 2332276869007711, 2339017532969207, 2356264653172291, 2406225921513077, 2511282478463599, 2542396357125397, 2544698614445093, 2563008738743291, 2639395353650659, 2703853428809791, 2742909003061789]

theorem bankLeaf230_valid : bankLeaf230.Certified := by
  simp only [bankLeaf230, PrimeBank.Certified, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 11, 1695701492333] }, .lucas { root := 3, primeFactors := [2, 47, 17669, 510481] }, .lucas { root := 2, primeFactors := [2, 7, 631] }, .lucas { root := 14, primeFactors := [2, 3, 5, 709] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 13831, 348572099] }, .lucas { root := 6, primeFactors := [2, 3, 5, 461] }, .lucas { root := 2, primeFactors := [2, 7, 307, 81101] }, .lucas { root := 2, primeFactors := [2, 5, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 31, 2339, 3128577743] }, .lucas { root := 2, primeFactors := [2, 7, 167] }, .lucas { root := 5, primeFactors := [2, 8641, 181031] }, .lucas { root := 17, primeFactors := [2, 3, 5] }, .lucas { root := 14, primeFactors := [2, 5, 43, 421] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 23, 163, 199, 1567598953] }, .lucas { root := 5, primeFactors := [2, 3, 19, 3437717] }, .lucas { root := 2, primeFactors := [2, 61, 73, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 509, 1049706041] }, .lucas { root := 3, primeFactors := [2, 5, 29, 904919] }, .lucas { root := 11, primeFactors := [2, 7, 109, 593] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 46273575413713] }, .lucas { root := 5, primeFactors := [2, 3, 17, 43, 59, 641, 34871] }, .lucas { root := 7, primeFactors := [2, 5, 11, 317] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 89, 1021147116551] }, .lucas { root := 7, primeFactors := [2, 5, 11, 1856631121] }, .lucas { root := 13, primeFactors := [2, 3, 5, 883, 8761] }, .lucas { root := 23, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 106321, 2410632649] }, .lucas { root := 13, primeFactors := [2, 3, 5, 443] }, .lucas { root := 7, primeFactors := [2, 3, 61, 548869] }, .lucas { root := 2, primeFactors := [2, 3, 53, 863] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 47, 859, 573467189] }, .lucas { root := 2, primeFactors := [2, 7, 17, 23, 1069] }, .lucas { root := 6, primeFactors := [2, 3, 89] }]),
    OddPerfect.IndexComponent.Size160.bank.prime_of_contains OddPerfect.IndexComponent.Size160.bank_valid (by decide +kernel),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 5569, 3731300711] }, .lucas { root := 13, primeFactors := [2, 3, 29] }, .lucas { root := 13, primeFactors := [2, 5, 139, 2684389] }, .lucas { root := 2, primeFactors := [2, 3, 7, 31957] }, .lucas { root := 2, primeFactors := [2, 3, 2663] }, .lucas { root := 5, primeFactors := [2, 11] }]), by simp⟩

end OddPerfect.IndexComponent.SizePrimeBank300
