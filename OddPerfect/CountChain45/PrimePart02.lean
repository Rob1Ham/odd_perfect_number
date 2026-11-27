module

public import OddPerfect.CountChain45.PrimePart01
import Mathlib.Tactic.Primality

public section

namespace OddPerfect.FactorBudget.Count45

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] noncomputable def primes32 : List ℕ := [11059, 12343, 12547, 13003, 13399, 14401, 14813, 15919, 16339, 17137, 17579, 18457, 19603, 20359, 24379, 24919, 26731, 26893, 28211, 29023, 31723, 35671, 37871, 38677]

theorem primes32_valid : ∀ p ∈ primes32, p.Prime := by
  simp only [primes32, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 19, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 379] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 389] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 17, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 4153] }, .lucas { root := 5, primeFactors := [2, 3, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 29, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 293] }]), by simp⟩

@[expose] noncomputable def primes33 : List ℕ := [42701, 44531, 51487, 52267, 52807, 54869, 56701, 58217, 59023, 62047, 63601, 64661, 70981, 79399, 89659, 92723, 95479, 95857, 99241, 110557, 115571, 117911, 119953, 125731]

theorem primes33_valid : ∀ p ∈ primes33, p.Prime := by
  simp only [primes33, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 8581] }, .lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 281] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 29, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1093] }, .lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 53, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 37, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 15913] }, .lucas { root := 5, primeFactors := [2, 3, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 1997] }, .lucas { root := 2, primeFactors := [2, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 827] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 37, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 13, 907] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 127] }]), by simp⟩

@[expose] noncomputable def primes34 : List ℕ := [132947, 147083, 160967, 227267, 261581, 347509, 407741, 427001, 429211, 456451, 464941, 503947, 672127, 808627, 830279, 863497, 889453, 1097113, 1395943, 1867147, 2088139, 2123369, 2380141, 2415733]

theorem primes34_valid : ∀ p ∈ primes34, p.Prime := by
  simp only [primes34, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 6043] }, .lucas { root := 5, primeFactors := [2, 3, 19, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 5657] }, .lucas { root := 3, primeFactors := [2, 7, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 41, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 8741] }, .lucas { root := 2, primeFactors := [2, 5, 19, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 29, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 29, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 27997] }, .lucas { root := 5, primeFactors := [2, 3, 2333] }, .lucas { root := 2, primeFactors := [2, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 1231] }, .lucas { root := 3, primeFactors := [2, 3, 5, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 131, 3169] }, .lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 797] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 2689] }, .lucas { root := 19, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 197, 1181] }, .lucas { root := 7, primeFactors := [2, 5, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 43, 7237] }, .lucas { root := 2, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 19, 1409] }, .lucas { root := 3, primeFactors := [2, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 1889] }, .lucas { root := 3, primeFactors := [2, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 18301] }, .lucas { root := 6, primeFactors := [2, 3, 5, 61] }]), by simp⟩

@[expose] noncomputable def primes35 : List ℕ := [2922391, 3330391, 3484093, 3562849, 4279111, 4666801, 6586781, 7834583, 8932457, 9250723, 11827061, 12190573, 12865927, 14686393, 15349897, 19622651, 22951667, 38745181, 46574123, 52932601, 61562537, 68409301, 70350157, 87653303]

theorem primes35_valid : ∀ p ∈ primes35, p.Prime := by
  simp only [primes35, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 19, 1709] }, .lucas { root := 3, primeFactors := [2, 7, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 15859] }, .lucas { root := 2, primeFactors := [2, 3, 881] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 199, 1459] }, .lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 89, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 11, 12967] }, .lucas { root := 3, primeFactors := [2, 3, 2161] }, .lucas { root := 23, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 3889] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61, 5399] }, .lucas { root := 7, primeFactors := [2, 2699] }, .lucas { root := 2, primeFactors := [2, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 23, 29, 839] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 85889] }, .lucas { root := 3, primeFactors := [2, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 3041] }, .lucas { root := 3, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 23, 3673] }, .lucas { root := 5, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 97, 3491] }, .lucas { root := 2, primeFactors := [2, 5, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 112859] }, .lucas { root := 2, primeFactors := [2, 73, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 19, 43, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 213193] }, .lucas { root := 5, primeFactors := [2, 3, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 601, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 277, 2437] }, .lucas { root := 2, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19, 11329] }, .lucas { root := 7, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 83, 149, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 4201] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 23, 47797] }, .lucas { root := 5, primeFactors := [2, 3, 7, 569] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 6163] }, .lucas { root := 3, primeFactors := [2, 3, 13, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 233, 8387] }, .lucas { root := 2, primeFactors := [2, 7, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 1129, 3529] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 17, primeFactors := [2, 3, 7] }]), by simp⟩

@[expose] noncomputable def primes36 : List ℕ := [103052953, 112210253, 113229229, 143700157, 194086693, 250801819, 256128979, 930600469, 1434250513, 1445413861, 1525344143, 3196717033, 3276517921, 4992178363, 12081356831, 40254284197, 46685826619, 49275341281, 193091463181, 687183137093, 3937230404603, 9468940004449, 17748600316039, 18871143464293]

theorem primes36_valid : ∀ p ∈ primes36, p.Prime := by
  simp only [primes36, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 47, 10151] }, .lucas { root := 7, primeFactors := [2, 5, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 139, 2621] }, .lucas { root := 2, primeFactors := [2, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 1347967] }, .lucas { root := 6, primeFactors := [2, 3, 74887] }, .lucas { root := 3, primeFactors := [2, 3, 7, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 11987] }, .lucas { root := 2, primeFactors := [2, 13, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 43, 13931] }, .lucas { root := 2, primeFactors := [2, 5, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 491, 85133] }, .lucas { root := 2, primeFactors := [2, 21283] }, .lucas { root := 11, primeFactors := [2, 3, 3547] }, .lucas { root := 2, primeFactors := [2, 3, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 233, 3739] }, .lucas { root := 7, primeFactors := [2, 3, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 17, 19, 37, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 263, 37871] }, .lucas { root := 7, primeFactors := [2, 5, 7, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 59, 12373] }, .lucas { root := 2, primeFactors := [2, 3, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 6409009] }, .lucas { root := 7, primeFactors := [2, 3, 44507] }, .lucas { root := 2, primeFactors := [2, 7, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47, 2833969] }, .lucas { root := 7, primeFactors := [2, 3, 17, 23, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 5, 13, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 12379, 67213] }, .lucas { root := 2, primeFactors := [2, 3, 2063] }, .lucas { root := 5, primeFactors := [2, 1031] }, .lucas { root := 14, primeFactors := [2, 5, 103] }, .lucas { root := 2, primeFactors := [2, 3, 1867] }, .lucas { root := 2, primeFactors := [2, 3, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 61, 2833, 6991] }, .lucas { root := 5, primeFactors := [2, 3, 59] }, .lucas { root := 6, primeFactors := [2, 3, 5, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 197, 115837] }, .lucas { root := 11, primeFactors := [2, 3, 7, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 41, 127, 1009, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 11, 61, 89, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 11, 13931563] }, .lucas { root := 2, primeFactors := [2, 3, 151, 15377] }, .lucas { root := 3, primeFactors := [2, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 10105634369] }, .lucas { root := 3, primeFactors := [2, 907, 174091] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 619256119] }, .lucas { root := 3, primeFactors := [2, 3, 13, 263, 30187] }, .lucas { root := 5, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 19, 4603, 1127809] }, .lucas { root := 2, primeFactors := [2, 3, 13, 59] }, .lucas { root := 17, primeFactors := [2, 3, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 53, 127, 146491361] }, .lucas { root := 3, primeFactors := [2, 5, 41, 137, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19, 41, 67, 163, 26407] }, .lucas { root := 5, primeFactors := [2, 3, 163] }]), by simp⟩

@[expose] noncomputable def primes37 : List ℕ := [68917740951781, 219900698580377, 1648012040336791, 9619414659135667, 13045594560392321, 20760232154805019, 81750272028928231, 365834083876629007, 542484773057617547, 722035775587170997, 837197335075000483, 3081128010533825683, 3325433255988398101, 32607907713428723311, 2519545342349331183143, 6675101063687544353791, 14583624599616691862381, 149861247689324730312041, 249802177797238939226759, 6713462860391040872837261, 7858179685661558917710821, 33899939683211028917156831, 91264002187709396686868598317, 701028891746359469869552194901]

theorem primes37_valid : ∀ p ∈ primes37, p.Prime := by
  simp only [primes37, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 7877, 47237] }, .lucas { root := 2, primeFactors := [2, 11, 179] }, .lucas { root := 2, primeFactors := [2, 7, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 9029, 276760613] }, .lucas { root := 2, primeFactors := [2, 37, 61] }, .lucas { root := 2, primeFactors := [2, 17, 19, 214211] }, .lucas { root := 2, primeFactors := [2, 5, 31, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 283, 64704045557] }, .lucas { root := 2, primeFactors := [2, 23, 31, 37, 613169] }, .lucas { root := 3, primeFactors := [2, 19, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 11, 373, 461, 571, 70687] }, .lucas { root := 5, primeFactors := [2, 3, 7, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 37, 167, 10687, 308681] }, .lucas { root := 5, primeFactors := [2, 3, 13, 137] }, .lucas { root := 11, primeFactors := [2, 5, 7717] }, .lucas { root := 2, primeFactors := [2, 3, 643] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 419, 2633, 15797, 66179] }, .lucas { root := 3, primeFactors := [2, 7, 47] }, .lucas { root := 2, primeFactors := [2, 11, 359] }, .lucas { root := 2, primeFactors := [2, 7, 29, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 13, 4013, 7462037027] }, .lucas { root := 2, primeFactors := [2, 17, 59] }, .lucas { root := 2, primeFactors := [2, 173, 283, 76207] }, .lucas { root := 3, primeFactors := [2, 3, 13, 977] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1373, 73421, 604842197] }, .lucas { root := 2, primeFactors := [2, 7] }, .lucas { root := 2, primeFactors := [2, 5, 3671] }, .lucas { root := 13, primeFactors := [2, 5, 367] }, .lucas { root := 2, primeFactors := [2, 7, 131, 269, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 59, 1223, 84731, 3412663] }, .lucas { root := 5, primeFactors := [2, 13, 47] }, .lucas { root := 2, primeFactors := [2, 5, 37, 229] }, .lucas { root := 5, primeFactors := [2, 3, 11, 29, 1783] }, .lucas { root := 10, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 79, 277, 463, 947, 298621] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 4228269369065659] }, .lucas { root := 3, primeFactors := [2, 3, 7, 13873, 89589673] }, .lucas { root := 5, primeFactors := [2, 3, 17] }, .lucas { root := 5, primeFactors := [2, 3, 414767] }, .lucas { root := 5, primeFactors := [2, 11, 17, 1109] }, .lucas { root := 2, primeFactors := [2, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101, 10139, 501466579973] }, .lucas { root := 2, primeFactors := [2, 37, 137] }, .lucas { root := 2, primeFactors := [2, 17, 821, 8982349] }, .lucas { root := 7, primeFactors := [2, 3, 191, 3919] }, .lucas { root := 3, primeFactors := [2, 3, 653] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 127, 911, 350947567] }, .lucas { root := 3, primeFactors := [2, 3, 1451, 1493] }, .lucas { root := 2, primeFactors := [2, 5, 29] }, .lucas { root := 2, primeFactors := [2, 373] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 223, 397, 731363, 16787009] }, .lucas { root := 2, primeFactors := [2, 503, 727] }, .lucas { root := 3, primeFactors := [2, 7, 53, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 23, 42899, 2197469, 581024467] }, .lucas { root := 2, primeFactors := [2, 89, 241] }, .lucas { root := 2, primeFactors := [2, 7, 13, 6037] }, .lucas { root := 5, primeFactors := [2, 3, 503] }, .lucas { root := 17, primeFactors := [2, 3, 11, 2934467] }, .lucas { root := 2, primeFactors := [2, 61, 67, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 23, 37, 157, 1665357120432199] }, .lucas { root := 6, primeFactors := [2, 3, 92519840024011] }, .lucas { root := 10, primeFactors := [2, 3, 5, 7, 2331061729] }, .lucas { root := 7, primeFactors := [2, 3, 24281893] }, .lucas { root := 5, primeFactors := [2, 3, 47, 113, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 19, 31, 59, 2333, 347509, 25881377] }, .lucas { root := 2, primeFactors := [2, 11, 53] }, .lucas { root := 2, primeFactors := [2, 3, 7, 197] }, .lucas { root := 3, primeFactors := [2, 808793] }, .lucas { root := 3, primeFactors := [2, 17, 19, 313] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7, 19, 29, 32143, 4317131381393] }, .lucas { root := 6, primeFactors := [2, 3, 11, 487] }, .lucas { root := 3, primeFactors := [2, 107, 9479, 266029] }, .lucas { root := 7, primeFactors := [2, 7, 677] }, .lucas { root := 10, primeFactors := [2, 3, 7, 3167] }, .lucas { root := 5, primeFactors := [2, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 124901088898619469613379] }, .lucas { root := 2, primeFactors := [2, 31764795529, 1966030110041] }, .lucas { root := 7, primeFactors := [2, 3, 17, 77854891] }, .lucas { root := 2, primeFactors := [2, 3, 5, 1433, 1811] }, .lucas { root := 3, primeFactors := [2, 179] }, .lucas { root := 6, primeFactors := [2, 5, 181] }, .lucas { root := 3, primeFactors := [2, 5, 37, 4567, 290869] }, .lucas { root := 3, primeFactors := [2, 3, 761] }, .lucas { root := 2, primeFactors := [2, 3, 24239] }, .lucas { root := 13, primeFactors := [2, 12119] }, .lucas { root := 7, primeFactors := [2, 73, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 41, 12757, 160967, 1609669, 2476913] }, .lucas { root := 2, primeFactors := [2, 3, 1063] }, .lucas { root := 3, primeFactors := [2, 3, 59] }, .lucas { root := 5, primeFactors := [2, 13, 41, 151] }, .lucas { root := 6, primeFactors := [2, 3, 61, 733] }, .lucas { root := 3, primeFactors := [2, 154807] }, .lucas { root := 3, primeFactors := [2, 3, 25801] }, .lucas { root := 7, primeFactors := [2, 3, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 197, 349, 167429, 1674289, 20386337] }, .lucas { root := 2, primeFactors := [2, 19, 2203] }, .lucas { root := 5, primeFactors := [2, 3, 367] }, .lucas { root := 26, primeFactors := [2, 3, 7, 11, 151] }, .lucas { root := 3, primeFactors := [2, 637073] }, .lucas { root := 3, primeFactors := [2, 29, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 641, 983, 2671, 2014250546320891] }, .lucas { root := 7, primeFactors := [2, 3, 5, 89] }, .lucas { root := 2, primeFactors := [2, 3, 5, 17, 3949510875139] }, .lucas { root := 2, primeFactors := [2, 3, 197, 367, 3034859] }, .lucas { root := 2, primeFactors := [2, 269, 5641] }, .lucas { root := 14, primeFactors := [2, 3, 5, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 197, 787, 5171, 570821, 672901, 6735661] }, .lucas { root := 2, primeFactors := [2, 5, 11, 47] }, .lucas { root := 2, primeFactors := [2, 5, 28541] }, .lucas { root := 2, primeFactors := [2, 5, 1427] }, .lucas { root := 2, primeFactors := [2, 23, 31] }, .lucas { root := 2, primeFactors := [2, 3, 5, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }, .lucas { root := 6, primeFactors := [2, 3, 5, 112261] }, .lucas { root := 6, primeFactors := [2, 3, 5, 1871] }, .lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 19, 1260407548013, 8870689561099] }, .lucas { root := 2, primeFactors := [2, 315101887003] }, .lucas { root := 2, primeFactors := [2, 3, 7, 2500808627] }, .lucas { root := 2, primeFactors := [2, 31, 40335623] }, .lucas { root := 5, primeFactors := [2, 20167811] }, .lucas { root := 2, primeFactors := [2, 5, 13, 155137] }, .lucas { root := 13, primeFactors := [2, 3, 101] }, .lucas { root := 2, primeFactors := [2, 3, 41, 36059713663] }, .lucas { root := 3, primeFactors := [2, 3, 7, 858564611] }, .lucas { root := 2, primeFactors := [2, 5, 269, 319169] }, .lucas { root := 3, primeFactors := [2, 4987] }, .lucas { root := 2, primeFactors := [2, 3, 277] }]), by simp⟩

@[expose] noncomputable def primes38 : List ℕ := [1730263451729489729947159213315224702803351, 568972471024107865287021434301977158534824481, 90123690753556476823252943045319588283717753022055796172566741673982216281, 3, 877, 907, 1033, 1087, 1103, 1117, 1259, 1321, 1453, 1481, 1571, 1669, 1783, 1847, 2011, 2087, 2113, 2143, 2203, 2213]

theorem primes38_valid : ∀ p ∈ primes38, p.Prime := by
  simp only [primes38, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 7, 17, 290800580122603315957505750137012555093] }, .lucas { root := 5, primeFactors := [2, 3, 1038043, 4552184388149, 5128363887584176913] }, .lucas { root := 2, primeFactors := [2, 3, 47, 409] }, .lucas { root := 2, primeFactors := [2, 17, 66943888061] }, .lucas { root := 2, primeFactors := [2, 5, 7, 31, 2659, 5801] }, .lucas { root := 2, primeFactors := [2, 3, 443] }, .lucas { root := 3, primeFactors := [2, 5, 29] }, .lucas { root := 3, primeFactors := [2, 953, 336330265450169] }, .lucas { root := 3, primeFactors := [2, 11, 1723, 2218186207] }, .lucas { root := 3, primeFactors := [2, 3, 7, 41] }, .lucas { root := 3, primeFactors := [2, 3, 3259, 37813] }, .lucas { root := 3, primeFactors := [2, 3, 181] }, .lucas { root := 2, primeFactors := [2, 3, 23, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 7, 11, 19, 31, 41, 331, 2521, 17351, 21821, 327412201, 880374069121] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7] }, .lucas { root := 11, primeFactors := [2, 5, 347] }, .lucas { root := 2, primeFactors := [2, 5, 1091] }, .lucas { root := 2, primeFactors := [2, 5, 109] }, .lucas { root := 11, primeFactors := [2, 3, 5, 191, 2857] }, .lucas { root := 11, primeFactors := [2, 3, 7, 17] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7, 13, 23, 31, 37, 191] }]),
    (OddPerfect.prime_of_largeOrderCubeCheck (b := 58823305105074774823208560387562286956038137426863590828961952222945158141) (factors := [(3081128010533825683, 1), (47, 1), (41, 1), (37, 1), (5, 1), (2, 3)]) (by simp only [List.forall_mem_cons]; exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101, 10139, 501466579973] }, .lucas { root := 2, primeFactors := [2, 37, 137] }, .lucas { root := 2, primeFactors := [2, 17, 821, 8982349] }, .lucas { root := 7, primeFactors := [2, 3, 191, 3919] }, .lucas { root := 3, primeFactors := [2, 3, 653] }]), by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩) (by decide +kernel)),
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 79] }]), by simp⟩

@[expose] noncomputable def primes39 : List ℕ := [2237, 2339, 2341, 2357, 2437, 2521, 2659, 2699, 2707, 2953, 3001, 3061, 3329, 3433, 3631, 3739, 4001, 4201, 4481, 4789, 4801, 5171, 5231, 5279]

theorem primes39_valid : ∀ p ∈ primes39, p.Prime := by
  simp only [primes39, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 5, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 13, 29] }]), by simp⟩

@[expose] noncomputable def primes40 : List ℕ := [5347, 5413, 5503, 5657, 5669, 5689, 5701, 5741, 5903, 6113, 6131, 6257, 6577, 6703, 6971, 7019, 7069, 7211, 7297, 7589, 8053, 8089, 8513, 8713]

theorem primes40_valid : ∀ p ∈ primes40, p.Prime := by
  simp only [primes40, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1117] }, .lucas { root := 2, primeFactors := [2, 3, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11] }]), by simp⟩

@[expose] noncomputable def primes41 : List ℕ := [8737, 8761, 8821, 8941, 9001, 9007, 9109, 9181, 9283, 9421, 9539, 9721, 9803, 9857, 10193, 10333, 10453, 10627, 10781, 10903, 11251, 11257, 11311, 11317]

theorem primes41_valid : ∀ p ∈ primes41, p.Prime := by
  simp only [primes41, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41] }]), by simp⟩

@[expose] noncomputable def primes42 : List ℕ := [11743, 12143, 12541, 12703, 12923, 13291, 13397, 13873, 13963, 14411, 14533, 14561, 14621, 14771, 14951, 15233, 15497, 15541, 15727, 15889, 16183, 16253, 16369, 16759]

theorem primes42_valid : ∀ p ∈ primes42, p.Prime := by
  simp only [primes42, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 13, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 11, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 197] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 173] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 13, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2621] }, .lucas { root := 2, primeFactors := [2, 5, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19] }]), by simp⟩

@[expose] noncomputable def primes43 : List ℕ := [17401, 17881, 18013, 18097, 18121, 18131, 18307, 18397, 19471, 20411, 21433, 21481, 22247, 22447, 22621, 22751, 25771, 26029, 26407, 26801, 27197, 27941, 28351, 28429]

theorem primes43_valid : ∀ p ∈ primes43, p.Prime := by
  simp only [primes43, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 13, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 859] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 103] }]), by simp⟩

@[expose] noncomputable def primes44 : List ℕ := [28771, 29527, 29947, 30187, 30493, 31039, 31123, 31247, 32561, 33161, 36653, 39551, 40237, 40771, 40961, 41203, 41221, 44041, 46901, 50159, 53233, 54151, 55721, 56533]

theorem primes44_valid : ∀ p ∈ primes44, p.Prime := by
  simp only [primes44, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 739] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 17, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 479] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 367] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 31, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1109] }, .lucas { root := 2, primeFactors := [2, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 673] }]), by simp⟩

@[expose] noncomputable def primes45 : List ℕ := [57041, 57787, 59699, 62581, 64171, 66491, 67957, 71713, 72073, 72091, 72229, 72953, 73039, 85889, 93169, 95231, 95929, 96581, 102913, 104707, 107857, 108557, 109279, 110311]

theorem primes45_valid : ∀ p ∈ primes45, p.Prime := by
  simp only [primes45, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9631] }, .lucas { root := 3, primeFactors := [2, 3, 5, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 1571] }, .lucas { root := 2, primeFactors := [2, 5, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 61, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 809] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 829] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 37, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 647] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 89, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 571] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 439] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 277] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 3877] }, .lucas { root := 2, primeFactors := [2, 3, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 13, 467] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 3677] }, .lucas { root := 2, primeFactors := [2, 919] }]), by simp⟩

@[expose] noncomputable def primes46 : List ℕ := [110969, 113233, 124001, 125269, 126691, 127189, 132911, 134947, 137537, 140761, 140977, 145091, 146521, 148663, 163147, 163991, 166393, 166849, 176419, 178561, 180307, 182953, 185441, 186037]

theorem primes46_valid : ∀ p ∈ primes46, p.Prime := by
  simp only [primes46, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 11, 13, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 41, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3533] }, .lucas { root := 2, primeFactors := [2, 883] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 13291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 1319] }, .lucas { root := 13, primeFactors := [2, 659] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 27191] }, .lucas { root := 26, primeFactors := [2, 5, 2719] }, .lucas { root := 3, primeFactors := [2, 3, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2311] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 19, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37, 419] }]), by simp⟩

@[expose] noncomputable def primes47 : List ℕ := [197891, 204511, 211219, 215143, 217421, 218107, 232919, 233881, 243311, 244753, 245561, 261031, 265871, 266683, 269167, 271241, 287701, 288653, 292631, 324871, 326119, 331937, 349927, 357421]

theorem primes47_valid : ∀ p ∈ primes47, p.Prime := by
  simp only [primes47, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 401] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 47, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 1553] }, .lucas { root := 3, primeFactors := [2, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 127, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 1949] }, .lucas { root := 2, primeFactors := [2, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 29, 839] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5099] }, .lucas { root := 2, primeFactors := [2, 2549] }, .lucas { root := 2, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 877] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 11, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 2417] }, .lucas { root := 3, primeFactors := [2, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 113, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 6781] }, .lucas { root := 2, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 2251] }, .lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 37, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 23, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 58321] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 23, 37] }]), by simp⟩

@[expose] noncomputable def primes48 : List ℕ := [377011, 382873, 386621, 395173, 434803, 438611, 443791, 452201, 452873, 487681, 537241, 554117, 558223, 600727, 624607, 652237, 652937, 667801, 686269, 721687, 723901, 779341, 787021, 797161]

theorem primes48_valid : ∀ p ∈ primes48, p.Prime := by
  simp only [primes48, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 59, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 20, primeFactors := [2, 3, 7, 43, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 1487] }, .lucas { root := 5, primeFactors := [2, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3659] }, .lucas { root := 2, primeFactors := [2, 31, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 72467] }, .lucas { root := 2, primeFactors := [2, 19, 1907] }, .lucas { root := 2, primeFactors := [2, 953] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 23, 1907] }, .lucas { root := 2, primeFactors := [2, 953] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 4931] }, .lucas { root := 6, primeFactors := [2, 5, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 7, 17, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 8087] }, .lucas { root := 5, primeFactors := [2, 13, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 23, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13291] }, .lucas { root := 2, primeFactors := [2, 3, 5, 443] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 14303] }, .lucas { root := 5, primeFactors := [2, 7151] }, .lucas { root := 7, primeFactors := [2, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 5479] }, .lucas { root := 3, primeFactors := [2, 3, 11, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 37, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 4801] }, .lucas { root := 7, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 1733] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 7, 17183] }, .lucas { root := 5, primeFactors := [2, 11, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13, 1009] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }]), by simp⟩

@[expose] noncomputable def primes49 : List ℕ := [838171, 926659, 1018177, 1074481, 1197941, 1333691, 1376461, 1401247, 1405249, 1489303, 1558681, 1600201, 1608751, 1647127, 1718141, 1770683, 1793161, 1886503, 1949473, 2373001, 2401393, 2608387, 3144079, 3256411]

theorem primes49_valid : ∀ p ∈ primes49, p.Prime := by
  simp only [primes49, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 67, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 51481] }, .lucas { root := 17, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5303] }, .lucas { root := 5, primeFactors := [2, 11, 241] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 89, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 197, 677] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 2549] }, .lucas { root := 2, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 11, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 31, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 31, 419] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 7039] }, .lucas { root := 3, primeFactors := [2, 3, 17, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 271, 317] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 30529] }, .lucas { root := 13, primeFactors := [2, 3, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 17, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 229, 1373] }, .lucas { root := 2, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 1021] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 39521] }, .lucas { root := 3, primeFactors := [2, 5, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 7, 24953] }, .lucas { root := 3, primeFactors := [2, 3119] }, .lucas { root := 7, primeFactors := [2, 1559] }, .lucas { root := 19, primeFactors := [2, 19, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 19, 29, 197] }]), by simp⟩

@[expose] noncomputable def primes50 : List ℕ := [3581839, 3634031, 3655499, 3683077, 3685501, 3718919, 3834091, 4105333, 4312807, 5610593, 6294091, 6801001, 7221259, 7550947, 7668337, 8346157, 8676949, 8880191, 9749851, 9843907, 10790137, 10865297, 11631811, 13097927]

theorem primes50_valid : ∀ p ∈ primes50, p.Prime := by
  simp only [primes50, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 15307] }, .lucas { root := 3, primeFactors := [2, 3, 2551] }, .lucas { root := 6, primeFactors := [2, 3, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 363403] }, .lucas { root := 2, primeFactors := [2, 3, 13, 1553] }, .lucas { root := 3, primeFactors := [2, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 3391] }, .lucas { root := 3, primeFactors := [2, 3, 5, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 53, 5791] }, .lucas { root := 6, primeFactors := [2, 3, 5, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 103, 2579] }, .lucas { root := 2, primeFactors := [2, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 29, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 11, 1481] }, .lucas { root := 3, primeFactors := [2, 5, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 718801] }, .lucas { root := 7, primeFactors := [2, 3, 5, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 13487] }, .lucas { root := 5, primeFactors := [2, 11, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11, 19073] }, .lucas { root := 3, primeFactors := [2, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 37, primeFactors := [2, 3, 5, 2267] }, .lucas { root := 2, primeFactors := [2, 11, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 12157] }, .lucas { root := 2, primeFactors := [2, 3, 1013] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 23, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 12289] }, .lucas { root := 11, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 13, 7643] }, .lucas { root := 2, primeFactors := [2, 3821] }, .lucas { root := 3, primeFactors := [2, 5, 191] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 53, 1949] }, .lucas { root := 2, primeFactors := [2, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 11, 41, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 19, 311] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 523, 3137] }, .lucas { root := 3, primeFactors := [2, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 79, 271] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 52237] }, .lucas { root := 6, primeFactors := [2, 3, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 387727] }, .lucas { root := 3, primeFactors := [2, 3, 64621] }, .lucas { root := 6, primeFactors := [2, 3, 5, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 37, 263, 673] }]), by simp⟩

@[expose] noncomputable def primes51 : List ℕ := [13560749, 14104031, 14669689, 14746751, 14864609, 16293691, 17049871, 17200201, 19271071, 19587401, 20750263, 20933761, 21278317, 21472771, 22366891, 25668151, 26466301, 28878847, 29701387, 32831761, 37680901, 38421091, 38786029, 56094673]

theorem primes51_valid : ∀ p ∈ primes51, p.Prime := by
  simp only [primes51, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 116903] }, .lucas { root := 5, primeFactors := [2, 58451] }, .lucas { root := 10, primeFactors := [2, 5, 7, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 37, 38119] }, .lucas { root := 3, primeFactors := [2, 3, 6353] }, .lucas { root := 3, primeFactors := [2, 397] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 181, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 61, 967] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 349] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 37, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 389, 487] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 109, 263] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 7, 13, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 823] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 266029] }, .lucas { root := 10, primeFactors := [2, 3, 7, 3167] }, .lucas { root := 5, primeFactors := [2, 1583] }, .lucas { root := 5, primeFactors := [2, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 10903] }, .lucas { root := 3, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 151, 11743] }, .lucas { root := 3, primeFactors := [2, 3, 19, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 31, 2099] }, .lucas { root := 2, primeFactors := [2, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 13, 2731] }, .lucas { root := 3, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 211, 811] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 4201] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 23, 209267] }, .lucas { root := 2, primeFactors := [2, 19, 5507] }, .lucas { root := 2, primeFactors := [2, 2753] }, .lucas { root := 3, primeFactors := [2, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 1049] }, .lucas { root := 3, primeFactors := [2, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 13, 17, 619] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 43, 127] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 31, 47, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1168639] }, .lucas { root := 3, primeFactors := [2, 3, 31, 61, 103] }]), by simp⟩

@[expose] noncomputable def primes52 : List ℕ := [57083519, 60055811, 77572057, 86961547, 121798751, 140262931, 197824999, 200286379, 201252871, 201815909, 254322041, 280314943, 280787851, 339147187, 459186991, 476381093, 480393499, 527532101, 539314889, 743732383, 778986167, 875335231, 911193301, 996625831]

theorem primes52_valid : ∀ p ∈ primes52, p.Prime := by
  simp only [primes52, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 17, 73, 109, 211] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 29, 37, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367, 8807] }, .lucas { root := 5, primeFactors := [2, 7, 17, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29, 7933] }, .lucas { root := 2, primeFactors := [2, 3, 661] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 139, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37, 73, 577] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 19, 247901] }, .lucas { root := 2, primeFactors := [2, 5, 37, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3709007] }, .lucas { root := 5, primeFactors := [2, 7, 37847] }, .lucas { root := 5, primeFactors := [2, 127, 149] }]),
    by primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 5, 7, 13, 8191] }, .lucas { root := 17, primeFactors := [2, 3, 5, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 37, 1637] }, .lucas { root := 2, primeFactors := [2, 409] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 23, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 2458903] }, .lucas { root := 3, primeFactors := [2, 3, 409817] }, .lucas { root := 3, primeFactors := [2, 11, 4657] }, .lucas { root := 15, primeFactors := [2, 3, 97] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 43, 691] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 8074933] }, .lucas { root := 5, primeFactors := [2, 3, 17, 23, 1721] }, .lucas { root := 3, primeFactors := [2, 5, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 15306233] }, .lucas { root := 3, primeFactors := [2, 853, 2243] }, .lucas { root := 2, primeFactors := [2, 19, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 31, 311, 1123] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2287, 2693] }, .lucas { root := 19, primeFactors := [2, 3, 127] }, .lucas { root := 2, primeFactors := [2, 673] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 310313] }, .lucas { root := 3, primeFactors := [2, 79, 491] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 2053, 4691] }, .lucas { root := 2, primeFactors := [2, 3, 19] }, .lucas { root := 2, primeFactors := [2, 5, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 123955397] }, .lucas { root := 2, primeFactors := [2, 29, 829, 1289] }, .lucas { root := 6, primeFactors := [2, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 31, 607, 2957] }, .lucas { root := 2, primeFactors := [2, 739] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 11, 126311] }, .lucas { root := 23, primeFactors := [2, 5, 17, 743] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23, 67, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 139, 199, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]), by simp⟩

@[expose] noncomputable def primes53 : List ℕ := [1172025763, 1497157061, 1638258961, 1738389269, 2057738783, 2609647069, 3652120847, 4356227321, 4811040361, 5732075647, 6314964913, 9228620761, 12936304421, 30982393921, 31898495803, 34179328063, 43713558101, 62995328779, 66613372141, 67164484721, 75619334851, 75755912653, 81760848073, 131327761273]

theorem primes53_valid : ∀ p ∈ primes53, p.Prime := by
  simp only [primes53, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1259, 155153] }, .lucas { root := 2, primeFactors := [2, 17, 37] }, .lucas { root := 3, primeFactors := [2, 9697] }, .lucas { root := 10, primeFactors := [2, 3, 101] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 19, 562841] }, .lucas { root := 3, primeFactors := [2, 5, 14071] }, .lucas { root := 7, primeFactors := [2, 3, 5, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 11, 19, 42437] }, .lucas { root := 2, primeFactors := [2, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 93533581] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 19, 3907] }, .lucas { root := 2, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 23, 1350749] }, .lucas { root := 2, primeFactors := [2, 7, 19, 2539] }, .lucas { root := 2, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 9765029] }, .lucas { root := 10, primeFactors := [2, 7, 13, 139, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 97, 1122739] }, .lucas { root := 2, primeFactors := [2, 3, 187123] }, .lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 5, 7, 70709] }, .lucas { root := 2, primeFactors := [2, 11, 1607] }, .lucas { root := 5, primeFactors := [2, 11, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 31, 9433] }, .lucas { root := 5, primeFactors := [2, 3, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43853923] }, .lucas { root := 3, primeFactors := [2, 3, 7, 7103] }, .lucas { root := 5, primeFactors := [2, 53, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 53, 1451041] }, .lucas { root := 13, primeFactors := [2, 3, 5, 3023] }, .lucas { root := 5, primeFactors := [2, 1511] }, .lucas { root := 11, primeFactors := [2, 5, 151] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 41, 277, 337] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 17, 1898431] }, .lucas { root := 13, primeFactors := [2, 3, 5, 63281] }, .lucas { root := 6, primeFactors := [2, 5, 7, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 103, 178601] }, .lucas { root := 3, primeFactors := [2, 5, 19, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 47, 3672827] }, .lucas { root := 2, primeFactors := [2, 1836413] }, .lucas { root := 2, primeFactors := [2, 23, 19961] }, .lucas { root := 6, primeFactors := [2, 5, 499] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 229, 457, 4177] }, .lucas { root := 5, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 244167941] }, .lucas { root := 7, primeFactors := [2, 5, 17, 89, 8069] }, .lucas { root := 2, primeFactors := [2, 2017] }, .lucas { root := 5, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 158603267] }, .lucas { root := 2, primeFactors := [2, 4231, 18743] }, .lucas { root := 3, primeFactors := [2, 3, 5, 47] }, .lucas { root := 5, primeFactors := [2, 9371] }, .lucas { root := 2, primeFactors := [2, 5, 937] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 19, 673, 65657] }, .lucas { root := 3, primeFactors := [2, 29, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 504128899] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 53, 5807] }, .lucas { root := 5, primeFactors := [2, 2903] }, .lucas { root := 5, primeFactors := [2, 1451] }, .lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 17, 17683453] }, .lucas { root := 5, primeFactors := [2, 3, 19, 103, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 31, 4073, 26981] }, .lucas { root := 3, primeFactors := [2, 509] }, .lucas { root := 3, primeFactors := [2, 5, 19, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 23, 83, 2866417] }, .lucas { root := 13, primeFactors := [2, 3, 7, 19, 449] }]), by simp⟩

@[expose] noncomputable def primes54 : List ℕ := [136850668961, 278014221827, 320374117039, 332207361361, 637135506367, 713406215047, 714060279761, 809829339481, 1037517185381, 1409655816661, 1855860368209, 3090276117871, 3135617002117, 4242586390571, 5070427577437, 5889307277311, 25322743716601, 60854076719167, 82753268919751, 99995282631947, 115512048133057, 132197305635599, 149933923993001, 155445494017421]

theorem primes54_valid : ∀ p ∈ primes54, p.Prime := by
  simp only [primes54, List.forall_mem_cons]
  exact ⟨by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 855316681] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7127639] }, .lucas { root := 7, primeFactors := [2, 7, 257, 283] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 23, 9137, 60133] }, .lucas { root := 3, primeFactors := [2, 571] }, .lucas { root := 6, primeFactors := [2, 3, 5011] }, .lucas { root := 2, primeFactors := [2, 3, 5, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 38011, 1404743] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 181] }, .lucas { root := 5, primeFactors := [2, 37, 41, 463] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 23, 293, 9781] }, .lucas { root := 6, primeFactors := [2, 3, 5, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 83, 1327, 56713] }, .lucas { root := 3, primeFactors := [2, 3, 13, 17] }, .lucas { root := 5, primeFactors := [2, 3, 17, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 16985862263] }, .lucas { root := 5, primeFactors := [2, 8492931131] }, .lucas { root := 2, primeFactors := [2, 5, 1277, 665069] }, .lucas { root := 2, primeFactors := [2, 11, 29] }, .lucas { root := 2, primeFactors := [2, 23, 7229] }, .lucas { root := 2, primeFactors := [2, 13, 139] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 23, 37, 101, 113, 919] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 31, 419, 2749] }, .lucas { root := 6, primeFactors := [2, 3, 229] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 13, 101, 1009, 39157] }, .lucas { root := 6, primeFactors := [2, 3, 13, 251] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 83, 241, 12907] }, .lucas { root := 2, primeFactors := [2, 3, 239] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 7, 11, 71732389] }, .lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 163] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 29851, 202987] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }, .lucas { root := 2, primeFactors := [2, 3, 7, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 4861, 1054013] }, .lucas { root := 11, primeFactors := [2, 3, 5] }, .lucas { root := 2, primeFactors := [2, 263503] }, .lucas { root := 5, primeFactors := [2, 3, 14639] }, .lucas { root := 11, primeFactors := [2, 13, 563] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 38568967187] }, .lucas { root := 2, primeFactors := [2, 53, 363858181] }, .lucas { root := 6, primeFactors := [2, 3, 5, 7, 866329] }, .lucas { root := 11, primeFactors := [2, 3, 36097] }, .lucas { root := 5, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 23, 5923, 18353] }, .lucas { root := 2, primeFactors := [2, 3, 7, 47] }, .lucas { root := 3, primeFactors := [2, 31, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41, 1973, 2426789] }, .lucas { root := 2, primeFactors := [2, 17, 29] }, .lucas { root := 2, primeFactors := [2, 7, 13, 59, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 17, 2243, 100621] }, .lucas { root := 2, primeFactors := [2, 19, 59] }, .lucas { root := 18, primeFactors := [2, 3, 5, 13, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19, 113, 4723961863] }, .lucas { root := 3, primeFactors := [2, 3, 41, 19203097] }, .lucas { root := 10, primeFactors := [2, 3, 11, 72739] }, .lucas { root := 2, primeFactors := [2, 3, 449] }]),
    by primality (cert := .witnesses [.lucas { root := 24, primeFactors := [2, 3, 5, 11, 13, 257197417] }, .lucas { root := 15, primeFactors := [2, 3, 7, 1530937] }, .lucas { root := 10, primeFactors := [2, 3, 11, 1933] }, .lucas { root := 5, primeFactors := [2, 3, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 17, 4639, 48767767] }, .lucas { root := 3, primeFactors := [2, 3, 773] }, .lucas { root := 5, primeFactors := [2, 3, 8127961] }, .lucas { root := 17, primeFactors := [2, 3, 5, 67733] }, .lucas { root := 2, primeFactors := [2, 7, 41, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 233, 16876357] }, .lucas { root := 5, primeFactors := [2, 3, 7, 200909] }, .lucas { root := 2, primeFactors := [2, 50227] }, .lucas { root := 2, primeFactors := [2, 3, 11, 761] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 937, 10077550361] }, .lucas { root := 3, primeFactors := [2, 5, 17, 14819927] }, .lucas { root := 5, primeFactors := [2, 11, 79, 8527] }, .lucas { root := 5, primeFactors := [2, 3, 7, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 7, 3499, 6121501] }, .lucas { root := 2, primeFactors := [2, 3, 11, 53] }, .lucas { root := 2, primeFactors := [2, 3, 5, 7, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 41, 67, 166433429] }, .lucas { root := 3, primeFactors := [2, 7, 23, 258437] }, .lucas { root := 2, primeFactors := [2, 64609] }, .lucas { root := 35, primeFactors := [2, 3, 673] }]), by simp⟩

end OddPerfect.FactorBudget.Count45
