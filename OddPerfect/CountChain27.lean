module

public import OddPerfect.ChainPlan
import Mathlib.Tactic.Primality

/-! Replay data for the exact-exponent factor-count certificates. -/

public section

namespace OddPerfect.FactorBudget

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def splitPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 61, 67, 71, 73, 79, 89, 97, 103, 113, 127, 131, 151, 157, 163, 191, 197, 199, 211, 223, 229, 271, 281, 307, 331, 379, 397, 409, 419, 421, 431, 433, 443, 467, 541, 547, 599, 613, 617, 631, 701, 733, 743, 757, 761, 769, 787, 811, 859, 883, 911, 947, 967, 991, 1051, 1063, 1093, 1123, 1361, 1451, 1459, 1471, 1483, 1499, 1597, 1621, 1723, 1871, 2311, 2557, 2633, 2671, 2801, 3169, 3217, 3221, 3229, 3313, 3499, 3571, 3851, 4027, 4051, 4447, 4733, 4751, 5113, 5209, 5419, 6301, 6491, 7561, 7673, 8011, 8387, 8647, 10847, 12011, 12601, 12893, 13537, 14009, 14713, 15797, 17293, 17351, 17707, 18457, 19531, 21491, 24517, 28387, 29251, 30941, 33151, 37861, 37871, 39103, 42407, 43609, 45319, 56773, 70001, 70841, 86353, 104281, 151841, 187123, 292561, 398581, 583367, 732541, 797161, 830833, 1609669, 1717451, 1774921, 1806113, 1866871, 2180921, 2384047, 2426789, 3044803, 3500201, 5229043, 5471551, 6619231, 7908811, 10378063, 12207031, 12865927, 22406023, 22576753, 52932601, 62060021, 87653303, 88009573, 262209281, 305175781, 366340651, 381510691, 917087137, 1434250513, 12346432697, 16148168401, 52379047267, 297134095231, 502628805631, 3090276117871, 31747594185191, 50544702849929377, 6115909044841454629, 109912203092239643840221, 751670559138758105956097, 62065212901958868055012327674641, 1247451159302262598804596798564656994853573]

private theorem prime_proofs : ∀ p ∈ splitPrimes, p.Prime := by
  simp only [splitPrimes, List.forall_mem_cons]
  exact ⟨by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by norm_num,
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 41] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 269] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 137] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 599] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 17, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 293] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 23, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 41669] }, .lucas { root := 2, primeFactors := [2, 11, 947] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 19, 911] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 701] }]),
    by primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 2113] }, .lucas { root := 5, primeFactors := [2, 3, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20743] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 53] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 59, 113] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29851] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 37, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73547] }, .lucas { root := 2, primeFactors := [2, 11, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 2897] }, .lucas { root := 3, primeFactors := [2, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 112859] }, .lucas { root := 2, primeFactors := [2, 73, 773] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 4751] }, .lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 4201] }, .lucas { root := 11, primeFactors := [2, 3, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 282091] }, .lucas { root := 3, primeFactors := [2, 3, 5, 9403] }, .lucas { root := 3, primeFactors := [2, 3, 1567] }, .lucas { root := 3, primeFactors := [2, 3, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 1129, 3529] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 17, primeFactors := [2, 3, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 337, 3109] }, .lucas { root := 6, primeFactors := [2, 3, 7, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 13, 31, 601] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 43, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 19, 71, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 263, 37871] }, .lucas { root := 7, primeFactors := [2, 5, 7, 541] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 13, 61, 1123, 1733] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 557, 16603] }, .lucas { root := 2, primeFactors := [2, 3, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 89, 373, 8011] }, .lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 29851, 202987] }, .lucas { root := 2, primeFactors := [2, 3, 5, 199] }, .lucas { root := 2, primeFactors := [2, 3, 7, 179] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 244212262963] }, .lucas { root := 3, primeFactors := [2, 3, 19, 3001, 713833] }, .lucas { root := 14, primeFactors := [2, 3, 5] }, .lucas { root := 5, primeFactors := [2, 3, 7, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 61, 7321, 6304673] }, .lucas { root := 7, primeFactors := [2, 3, 5, 61] }, .lucas { root := 3, primeFactors := [2, 11, 17911] }, .lucas { root := 3, primeFactors := [2, 3, 5, 199] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 7, 11, 19, 37, 590077, 1772893] }, .lucas { root := 6, primeFactors := [2, 3, 37, 443] }, .lucas { root := 17, primeFactors := [2, 3, 11, 37] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 19, 127, 199, 523, 29989, 236377] }, .lucas { root := 2, primeFactors := [2, 3, 7, 17] }, .lucas { root := 10, primeFactors := [2, 3, 7, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 31, 37, 409, 1129, 25085030513] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 3, primeFactors := [2, 1229, 1275683] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 2, primeFactors := [2, 637841] }, .lucas { root := 21, primeFactors := [2, 5, 7, 17, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 17, 97, 233, 941, 189977, 230512752775793] }, .lucas { root := 3, primeFactors := [2, 23747] }, .lucas { root := 2, primeFactors := [2, 31, 383] }, .lucas { root := 3, primeFactors := [2, 31, 106747, 4353691] }, .lucas { root := 2, primeFactors := [2, 3, 17791] }, .lucas { root := 3, primeFactors := [2, 3, 5, 593] }, .lucas { root := 2, primeFactors := [2, 3, 5, 11, 79, 167] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 73, 179, 857, 3221, 3643, 6053, 10378063, 107637315400441] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }, .lucas { root := 2, primeFactors := [2, 3, 607] }, .lucas { root := 2, primeFactors := [2, 17, 89] }, .lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 19, primeFactors := [2, 3, 5, 7, 23, 179, 3221] }]), by simp⟩

private def seed3Tree : ChoiceTree :=
  (.node 25791738629551784043818754730385097 (.basic (.groups [43, 733, 17707, 249561007])) -- 3^4 * 11^10 * 15797^2 * 1806113 * 17^2 * 307^2
    (.node 208733303157424551376224237 (.basic (.groups [379, 1609669, 52379047267])) -- 3^8 * 13^8 * 61^6 * 757
      (.node 303694946067530640249 (.basic (.split 398581)) -- 3^4 * 11^12 * 1093^2
        (.node 19914826458249801 (.basic (.split 97)) -- 3^8 * 13^8 * 61^2
          (.node 2768539915449 (.basic (.split 19)) -- 3^4 * 11^2 * 7^10
            (.node 2436053373 (.basic (.split 7)) -- 3^8 * 13^5
              (.node 4782969 (.basic (.split 11)) -- 3^14
                (.node 92781 (.basic (.split 31)) -- 3^2 * 13^2 * 61
                  (.node 1521 (.basic (.split 61)) -- 3^2 * 13^2
                    (.node 81 (.basic (.split 11)) -- 3^4
                      (.node 9 (.basic (.split 13)) -- 3^2
                        (.node 1 (.basic (.split 3)) .empty .empty)
                        .empty)
                      (.node 729 (.basic (.split 1093)) -- 3^6
                        (.node 117 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 9801 (.basic (.split 7)) -- 3^4 * 11^2
                      (.node 6561 (.basic (.split 13)) -- 3^8
                        (.node 5733 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 85293 (.basic (.split 7)) -- 3^8 * 13
                        (.node 59049 (.basic (.split 23)) .empty .empty)
                        .empty)))
                  (.node 1108809 (.basic (.split 61)) -- 3^8 * 13^2
                    (.node 480249 (.basic (.split 19)) -- 3^4 * 11^2 * 7^2
                      (.node 280917 (.basic (.split 2801)) -- 3^2 * 13 * 7^4
                        (.node 257049 (.basic (.split 30941)) .empty .empty)
                        .empty)
                      (.node 796797 (.basic (.split 547)) -- 3^6 * 1093
                        (.node 531441 (.basic (.split 797161)) .empty .empty)
                        .empty))
                    (.node 3341637 (.basic (.split 7)) -- 3^2 * 13^5
                      (.node 2069613 (.basic (.split 127)) -- 3^2 * 13 * 7^2 * 19^2
                        (.node 1185921 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 4179357 (.basic (.split 19)) .empty .empty))))
                (.node 187388721 (.basic (.split 757)) -- 3^8 * 13^4
                  (.node 43046721 (.basic (.split 1871)) -- 3^16
                    (.node 13764933 (.basic (.split 29)) -- 3^2 * 13 * 7^6
                      (.node 5929605 (.basic (.split 3221)) -- 3^4 * 11^4 * 5
                        (.node 5659641 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 31236921 (.basic (.split 7)) -- 3^10 * 23^2
                        (.node 23532201 (.basic (.split 19)) .empty .empty)
                        .empty))
                    (.node 89162541 (.basic (.split 331)) -- 3^2 * 13^2 * 61 * 31^2
                      (.node 67637349 (.basic (.split 31)) -- 3^8 * 13^2 * 61
                        (.node 43441281 (.basic (.split 5229043)) .empty .empty)
                        .empty)
                      (.node 163740213 (.basic (.split 19)) -- 3^2 * 13^5 * 7^2
                        (.node 143496441 (.basic (.split 43)) .empty .empty)
                        .empty)))
                  (.node 747130293 (.basic (.split 151)) -- 3^2 * 13 * 7^2 * 19^4
                    (.node 548985177 (.basic (.split 7)) -- 3^2 * 13^2 * 61^2 * 97
                      (.node 387420489 (.basic (.split 1597)) -- 3^18
                        (.node 204788493 (.basic (.split 757)) .empty .empty)
                        .empty)
                      (.node 674481717 (.basic (.split 19)) -- 3^2 * 13 * 7^8
                        (.node 578739249 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 1508747877 (.basic (.split 127)) -- 3^8 * 13 * 7^2 * 19^2
                      (.node 1153077849 (.basic (.split 19)) -- 3^4 * 11^2 * 7^6
                        (.node 870899121 (.basic (.split 398581)) .empty .empty)
                        .empty)
                      (.node 1530609129 (.basic (.split 19)) .empty .empty)))))
              (.node 265324919409 (.basic (.split 631)) -- 3^4 * 11^6 * 43^2
                (.node 45328197213 (.basic (.split 7)) -- 3^20 * 13
                  (.node 16524331209 (.basic (.split 3851)) -- 3^10 * 23^4
                    (.node 7341576489 (.basic (.split 61)) -- 3^2 * 13^8
                      (.node 4125878289 (.basic (.split 97)) -- 3^8 * 13^2 * 61^2
                        (.node 3486784401 (.basic (.split 13)) .empty .empty)
                        .empty)
                      (.node 10034636157 (.basic (.split 29)) -- 3^8 * 13 * 7^6
                        (.node 8023270437 (.basic (.split 61)) .empty .empty)
                        .empty))
                    (.node 28358223201 (.basic (.split 13)) -- 3^14 * 11^2 * 7^2
                      (.node 21059524161 (.basic (.split 5)) -- 3^2 * 13^2 * 61^4
                        (.node 17363069361 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 33049604133 (.basic (.split 1123)) -- 3^2 * 13 * 7^10
                        (.node 31668693849 (.basic (.split 757)) .empty .empty)
                        .empty)))
                  (.node 95440494357 (.basic (.split 7)) -- 3^2 * 13^9
                    (.node 70027449129 (.basic (.split 5)) -- 3^14 * 11^4
                      (.node 64999492389 (.basic (.split 331)) -- 3^8 * 13^2 * 61 * 31^2
                        (.node 56500814601 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 85685201901 (.basic (.split 5)) -- 3^2 * 13^2 * 61 * 31^4
                        (.node 74999847321 (.basic (.split 79)) .empty .empty)
                        .empty))
                    (.node 141853261797 (.basic (.split 379)) -- 3^8 * 13^4 * 757
                      (.node 119366615277 (.basic (.split 19)) -- 3^8 * 13^5 * 7^2
                        (.node 105297620805 (.basic (.split 131)) .empty .empty)
                        .empty)
                      (.node 238408833573 (.basic (.split 163)) .empty .empty))))
                (.node 589266563769 (.basic (.split 61)) -- 3^20 * 13^2
                  (.node 447836165829 (.basic (.split 31)) -- 3^2 * 13^8 * 61
                    (.node 393140251413 (.basic (.split 29)) -- 3^2 * 13^5 * 7^6
                      (.node 350137245645 (.basic (.split 13)) -- 3^14 * 11^4 * 5
                        (.node 269714035773 (.basic (.split 701)) .empty .empty)
                        .empty)
                      (.node 423644039001 (.basic (.split 398581)) -- 3^12 * 797161
                        (.node 400210194033 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 544657983597 (.basic (.split 151)) -- 3^8 * 13 * 7^2 * 19^4
                      (.node 526488104025 (.basic (.split 31)) -- 3^2 * 13^2 * 61^4 * 5^2
                        (.node 491697171693 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 552549895569 (.basic (.split 79)) .empty .empty)))
                  (.node 1389552936849 (.basic (.split 13)) -- 3^14 * 11^2 * 7^4
                    (.node 1240726426641 (.basic (.split 23)) -- 3^2 * 13^10
                      (.node 850790398689 (.basic (.split 19)) -- 3^4 * 11^8 * 7^2
                        (.node 618710520933 (.basic (.split 17)) .empty .empty)
                        .empty)
                      (.node 1318113409977 (.basic (.split 2801)) -- 3^2 * 13^2 * 61^2 * 97 * 7^4
                        (.node 1284630973821 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 2203962696117 (.basic (.split 37)) -- 3^2 * 13 * 7^4 * 2801^2
                      (.node 2100931392681 (.basic (.split 15797)) -- 3^4 * 11^10
                        (.node 1619430602517 (.basic (.split 16148168401)) .empty .empty)
                        .empty)
                      (.node 2221081663437 (.basic (.groups [19, 1093, 368089])) .empty .empty))))))
            (.node 286599243280077 (.basic (.groups [29, 61, 157, 757, 4733])) -- 3^8 * 13^5 * 7^6
              (.node 64587557088873 (.basic (.split 29)) -- 3^2 * 13^2 * 61^2 * 97 * 7^6
                (.node 21338788298373 (.basic (.split 61)) -- 3^2 * 13^5 * 7^2 * 19^4
                  (.node 8741371209561 (.basic (.split 29)) -- 3^10 * 23^6
                    (.node 5352009260481 (.basic (.split 61)) -- 3^8 * 13^8
                      (.node 4676584223493 (.basic (.split 11)) -- 3^2 * 13^9 * 7^2
                        (.node 3674992518729 (.basic (.split 29)) .empty .empty)
                        .empty)
                      (.node 8473321344609 (.basic (.split 13)) -- 3^14 * 11^6
                        (.node 5848964148573 (.basic (.split 61)) .empty .empty)
                        .empty))
                    (.node 15352393113369 (.basic (.split 5)) -- 3^8 * 13^2 * 61^4
                      (.node 13162202600625 (.basic (.split 11)) -- 3^2 * 13^2 * 61^4 * 5^4
                        (.node 9735675577173 (.basic (.split 4733)) .empty .empty)
                        .empty)
                      (.node 19610299507617 (.basic (.split 19)) -- 3^8 * 13^2 * 61^2 * 97 * 7^2
                        (.node 17035317810693 (.basic (.split 911)) .empty .empty)
                        .empty)))
                  (.node 38820388821201 (.basic (.split 757)) -- 3^8 * 13^2 * 61^2 * 97^2
                    (.node 24334594508133 (.basic (.split 757)) -- 3^8 * 13 * 7^2 * 19^2 * 127^2
                      (.node 24093161412957 (.basic (.split 757)) -- 3^8 * 13 * 7^10
                        (.node 23973201243693 (.basic (.split 379)) .empty .empty)
                        .empty)
                      (.node 35945260389909 (.basic (.groups [31, 1093, 368089])) -- 3^20 * 13^2 * 61
                        (.node 29854589296077 (.basic (.split 97)) .empty .empty)
                        .empty))
                    (.node 61518709067805 (.basic (.split 10378063)) -- 3^4 * 11^4 * 5 * 3221^2
                      (.node 43091348114997 (.basic (.split 61)) -- 3^8 * 13^5 * 7^2 * 19^2
                        (.node 41688729535761 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 62464512185829 (.basic (.split 5)) .empty .empty))))
                (.node 150691116448161 (.basic (.split 7)) -- 3^16 * 1871^2
                  (.node 82343479026861 (.basic (.split 917087137)) -- 3^2 * 13^2 * 61 * 31^6
                    (.node 76761965566845 (.basic (.split 131)) -- 3^8 * 13^2 * 61^4 * 5
                      (.node 69576120386253 (.basic (.split 7)) -- 3^8 * 13^9
                        (.node 68088093905601 (.basic (.groups [13, 19, 29, 4561])) .empty .empty)
                        .empty)
                      (.node 79352099523333 (.basic (.split 19)) -- 3^2 * 13 * 7^14
                        (.node 78362489403081 (.basic (.split 52379047267)) .empty .empty)
                        .empty))
                    (.node 107382919180329 (.basic (.split 14713)) -- 3^8 * 13^4 * 757^2
                      (.node 106574783043141 (.basic (.split 5)) -- 3^10 * 23^2 * 7^6 * 29
                        (.node 87899131841157 (.basic (.split 37)) .empty .empty)
                        .empty)
                      (.node 135658455857001 (.basic (.split 19)) -- 3^4 * 11^2 * 7^12
                        (.node 110153177479917 (.basic (.groups [7, 43, 4561, 45319])) .empty .empty)
                        .empty)))
                  (.node 209682766102329 (.basic (.split 53)) -- 3^2 * 13^12
                    (.node 180074633417721 (.basic (.groups [19, 37, 79, 1063, 3851])) -- 3^10 * 23^2 * 7^8
                      (.node 178807340549637 (.basic (.split 47)) -- 3^18 * 1597 * 17^2
                        (.node 177502678981173 (.basic (.split 37)) .empty .empty)
                        .empty)
                      (.node 199470512300409 (.basic (.split 79)) -- 3^10 * 23^2 * 7^2 * 19^4
                        (.node 196621532078517 (.basic (.split 701)) .empty .empty)
                        .empty))
                    (.node 253499765077269 (.basic (.split 5)) -- 3^10 * 23^6 * 29
                      (.node 246084698545569 (.basic (.split 157)) -- 3^2 * 13^4 * 30941^2
                        (.node 229152626951157 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 254212698514401 (.basic (.split 1093)) .empty .empty)))))
              (.node 3017224930984173 (.basic (.split 43)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2
                (.node 943929743642613 (.basic (.split 61)) -- 3^2 * 13^5 * 7^10
                  (.node 490585775987241 (.basic (.split 45319)) -- 3^4 * 11^6 * 43^4
                    (.node 330630951438333 (.basic (.split 61)) -- 3^2 * 13^5 * 7^6 * 29^2
                      (.node 329055065015625 (.basic (.split 131)) -- 3^2 * 13^2 * 61^4 * 5^6
                        (.node 326472564889341 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 468074047130361 (.basic (.split 43)) -- 3^10 * 23^2 * 7^4 * 79^2
                        (.node 347123842547301 (.basic (.split 17)) .empty .empty)
                        .empty))
                    (.node 656344279693089 (.basic (.split 7)) -- 3^2 * 13^10 * 23^2
                      (.node 538398730893933 (.basic (.split 262209281)) -- 3^2 * 13 * 7^2 * 19^2 * 127^4
                        (.node 501043948448121 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 936495979915509 (.basic (.split 7)) -- 3^8 * 13^2 * 61^5
                        (.node 904489565021289 (.basic (.split 23)) .empty .empty)
                        .empty)))
                  (.node 1431991307238921 (.basic (.groups [43, 61, 4561, 45319])) -- 3^14 * 11^6 * 13^2
                    (.node 1025271882697689 (.basic (.groups [7, 13, 19, 4561])) -- 3^14 * 11^8
                      (.node 988080701930001 (.basic (.split 43)) -- 3^18 * 1597^2
                        (.node 960904675873233 (.basic (.split 757)) .empty .empty)
                        .empty)
                      (.node 1180564909234893 (.basic (.split 757)) -- 3^8 * 13 * 7^12
                        (.node 1040418764003529 (.basic (.split 11)) .empty .empty)
                        .empty))
                    (.node 2192660883784449 (.basic (.groups [97, 1093, 368089])) -- 3^20 * 13^2 * 61^2
                      (.node 2042747747252289 (.basic (.split 19)) -- 3^4 * 11^8 * 7^6
                        (.node 1807012470634605 (.basic (.split 17293)) .empty .empty)
                        .empty)
                      (.node 2725875959330277 (.basic (.split 7)) .empty .empty))))
                (.node 7351493187240801 (.basic (.split 13)) -- 3^10 * 23^6 * 29^2
                  (.node 4624185369857769 (.basic (.split 7)) -- 3^10 * 23^8
                    (.node 3336316601374449 (.basic (.groups [13, 19, 37])) -- 3^14 * 11^2 * 7^8
                      (.node 3090668708251089 (.basic (.groups [13, 67, 79, 3851, 4733])) -- 3^10 * 23^2 * 7^6 * 29^2
                        (.node 3084398968144221 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 3888252876643317 (.basic (.split 14009)) -- 3^2 * 13 * 7^16
                        (.node 3409229898926397 (.basic (.groups [11, 19, 757, 2411, 30941])) .empty .empty)
                        .empty))
                    (.node 7097307495759117 (.basic (.split 757)) -- 3^8 * 13 * 7^6 * 29^4
                      (.node 6647264336993049 (.basic (.split 19)) -- 3^4 * 11^2 * 7^14
                        (.node 6334284299201037 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 7121409385631229 (.basic (.split 7)) .empty .empty)))
                  (.node 11228478720606693 (.basic (.split 11)) -- 3^2 * 13^9 * 7^6
                    (.node 8187703160402493 (.basic (.split 4733)) -- 3^2 * 13 * 7^6 * 29^6
                      (.node 7703302575712653 (.basic (.split 61)) -- 3^2 * 13^5 * 7^2 * 19^6
                        (.node 7383864705959889 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 8823657037468329 (.basic (.groups [79, 1123, 3851, 293459])) -- 3^10 * 23^2 * 7^10
                        (.node 8226376625390625 (.basic (.split 19)) .empty .empty)
                        .empty))
                    (.node 15555976669513917 (.basic (.groups [61, 151, 157, 757, 911])) -- 3^8 * 13^5 * 7^2 * 19^4
                      (.node 14043362920723773 (.basic (.groups [19, 37, 61, 157])) -- 3^8 * 13^5 * 7^8
                        (.node 12418746683995197 (.basic (.split 757)) .empty .empty)
                        .empty)
                      (.node 18147713341475601 (.basic (.split 14713)) .empty .empty)))))))
          (.node 4904637341152745889 (.basic (.groups [19, 1123, 293459, 1772893])) -- 3^4 * 11^8 * 7^10
            (.node 278060630159638053 (.basic (.split 61)) -- 3^2 * 13^5 * 7^6 * 29^4
              (.node 70980373080344637 (.basic (.split 127)) -- 3^8 * 13 * 7^2 * 19^8
                (.node 41131883126953125 (.basic (.split 11)) -- 3^2 * 13^2 * 61^4 * 5^9
                  (.node 31731586594657677 (.basic (.split 37)) -- 3^2 * 13 * 7^8 * 19^6
                    (.node 28646107927923213 (.basic (.split 31)) -- 3^2 * 13 * 7^14 * 19^2
                      (.node 21763995596840133 (.basic (.split 97)) -- 3^8 * 13^5 * 7^4 * 61^2
                        (.node 20375944377782877 (.basic (.split 61)) .empty .empty)
                        .empty)
                      (.node 30759736520242521 (.basic (.split 5)) -- 3^4 * 11^14
                        (.node 29387034337649157 (.basic (.split 379)) .empty .empty)
                        .empty))
                    (.node 35149402855973133 (.basic (.split 104281)) -- 3^2 * 13 * 7^2 * 19^10
                      (.node 33188413210181757 (.basic (.split 2633)) -- 3^4 * 11^10 * 15797
                        (.node 32160869704961361 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 38635297671654333 (.basic (.split 79)) -- 3^2 * 13^4 * 30941^2 * 157
                        (.node 35436387471293601 (.basic (.split 61)) .empty .empty)
                        .empty)))
                  (.node 57126254774846049 (.basic (.split 757)) -- 3^8 * 13^2 * 61^6
                    (.node 46252557438488037 (.basic (.split 61)) -- 3^2 * 13^5 * 7^12
                      (.node 45888303015859941 (.basic (.split 19)) -- 3^8 * 13^2 * 61^5 * 7^2
                        (.node 41679814210646157 (.basic (.split 127)) .empty .empty)
                        .empty)
                      (.node 51675321418845093 (.basic (.groups [47, 88741, 363889])) -- 3^18 * 1597 * 17^4
                        (.node 47084329117788417 (.basic (.split 29)) .empty .empty)
                        .empty))
                    (.node 60626317762222641 (.basic (.split 7)) -- 3^2 * 13^2 * 61^2 * 97^4 * 11^2
                      (.node 60028396210581669 (.basic (.split 757)) -- 3^8 * 13^2 * 61 * 31^6
                        (.node 57847680552509757 (.basic (.groups [19, 31, 757])) .empty .empty)
                        .empty)
                      (.node 64078467112203453 (.basic (.groups [37, 151, 757, 911])) .empty .empty))))
                (.node 151135549439066829 (.basic (.split 29)) -- 3^2 * 13^2 * 61^5 * 7^6
                  (.node 101650300756032249 (.basic (.split 5)) -- 3^2 * 13^8 * 61^4
                    (.node 95569411434130413 (.basic (.split 7)) -- 3^10 * 23^6 * 29^2 * 13
                      (.node 72008854940447649 (.basic (.split 79)) -- 3^10 * 23^2 * 7^2 * 19^6
                        (.node 71334068684543757 (.basic (.split 431)) .empty .empty)
                        .empty)
                      (.node 100318790496169989 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581 * 17^2
                        (.node 100094639615362161 (.basic (.split 19)) .empty .empty)
                        .empty))
                    (.node 125890670444427009 (.basic (.split 7)) -- 3^6 * 1093^4 * 11^2
                      (.node 111088926770702517 (.basic (.split 5)) -- 3^2 * 13^5 * 7^4 * 61^4
                        (.node 105642035236806849 (.basic (.split 307)) .empty .empty)
                        .empty)
                      (.node 133567922007183573 (.basic (.split 19)) -- 3^2 * 13^13 * 7^2
                        (.node 132537746892887973 (.basic (.split 70841)) .empty .empty)
                        .empty)))
                  (.node 205659415634765625 (.basic (.split 131)) -- 3^2 * 13^2 * 61^4 * 5^10
                    (.node 155074724570384073 (.basic (.split 1123)) -- 3^2 * 13^2 * 61^2 * 97 * 7^10
                      (.node 153798682601212605 (.basic (.split 7)) -- 3^4 * 11^14 * 5
                        (.node 152858736488597841 (.basic (.split 53)) .empty .empty)
                        .empty)
                      (.node 190524390955522533 (.basic (.split 419)) -- 3^2 * 13 * 7^18
                        (.node 167052265047393453 (.basic (.groups [11, 757, 2411, 2801])) .empty .empty)
                        .empty))
                    (.node 245059153220043009 (.basic (.split 13)) -- 3^10 * 23^4 * 3851^2
                      (.node 242006530923377649 (.basic (.groups [43, 4561, 30941])) -- 3^14 * 11^6 * 13^4
                        (.node 226585083123030681 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 277854479476240293 (.basic (.split 547)) .empty .empty)))))
              (.node 1242402348643695369 (.basic (.split 61)) -- 3^10 * 23^6 * 29^2 * 13^2
                (.node 413586103702563909 (.basic (.split 5)) -- 3^2 * 13^8 * 61 * 31^4
                  (.node 348949059895930221 (.basic (.split 19)) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^2
                    (.node 325715952512659401 (.basic (.split 19)) -- 3^4 * 11^2 * 7^16
                      (.node 313740134858656701 (.basic (.split 331)) -- 3^8 * 13^8 * 61 * 31^2
                        (.node 310379930660850813 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 347206123957644081 (.basic (.split 419)) -- 3^2 * 13^10 * 23^4
                        (.node 337712505774076161 (.basic (.split 61)) .empty .empty)
                        .empty))
                    (.node 388422281401611093 (.basic (.split 5)) -- 3^2 * 13 * 7^2 * 19^4 * 151^4
                      (.node 365261038418680209 (.basic (.split 11)) -- 3^8 * 13^2 * 61^2 * 97^4
                        (.node 361809370592034561 (.basic (.groups [157, 2801, 3187, 34511])) .empty .empty)
                        .empty)
                      (.node 394985415274148133 (.basic (.groups [37, 61, 307])) -- 3^18 * 1597 * 17^2 * 47^2
                        (.node 392492674821677157 (.basic (.split 757)) .empty .empty)
                        .empty)))
                  (.node 865468913144037489 (.basic (.split 631)) -- 3^10 * 23^2 * 7^4 * 79^2 * 43^2
                    (.node 550195457309727957 (.basic (.groups [11, 19, 37, 1063, 2411])) -- 3^2 * 13^9 * 7^8
                      (.node 478474979896261881 (.basic (.groups [7, 79, 419, 757, 859])) -- 3^8 * 13^10 * 23^2
                        (.node 432359194835948121 (.basic (.groups [79, 3851, 16148168401])) .empty .empty)
                        .empty)
                      (.node 688124783115464877 (.basic (.groups [61, 157, 757])) -- 3^8 * 13^5 * 7^10
                        (.node 588998889981442161 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 1137177709055857197 (.basic (.split 547)) -- 3^6 * 1093^5
                      (.node 1070272611384284061 (.basic (.split 5)) -- 3^2 * 13^2 * 61 * 31^2 * 331^4
                        (.node 907093099800408609 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 1230277770302037093 (.basic (.split 67)) .empty .empty))))
                (.node 2446194060654759801 (.basic (.split 11)) -- 3^10 * 23^10
                  (.node 1987163574351771933 (.basic (.groups [7, 29, 757, 22079])) -- 3^8 * 13^13
                    (.node 1579924889900180577 (.basic (.split 7)) -- 3^8 * 13^4 * 757^2 * 14713
                      (.node 1575882615543106689 (.basic (.split 79)) -- 3^2 * 13^10 * 23^2 * 7^4
                        (.node 1317312091092627045 (.basic (.split 757)) .empty .empty)
                        .empty)
                      (.node 1931738166450230697 (.basic (.split 7)) -- 3^8 * 13^8 * 61^2 * 97
                        (.node 1826961217868571849 (.basic (.groups [73, 271, 631, 363889])) .empty .empty)
                        .empty))
                    (.node 2266375314485913813 (.basic (.groups [19, 31, 61, 157])) -- 3^2 * 13^5 * 7^14
                      (.node 2248526847777137109 (.basic (.groups [31, 97, 523, 757, 2801])) -- 3^8 * 13^2 * 61^5 * 7^4
                        (.node 2161619635748909661 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 2307132126771632433 (.basic (.groups [19, 37, 757, 1063])) .empty .empty)))
                  (.node 3443534599845306213 (.basic (.split 61)) -- 3^8 * 13^6 * 757 * 379^2
                    (.node 2665575158851519929 (.basic (.groups [127, 157, 3187, 34511])) -- 3^16 * 1871^2 * 7^2 * 19^2
                      (.node 2599252383639165849 (.basic (.groups [79, 3851, 4733, 732541])) -- 3^10 * 23^2 * 7^6 * 29^4
                        (.node 2541257518900806225 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 3185768991860559117 (.basic (.split 7)) -- 3^10 * 23^4 * 3851^2 * 13
                        (.node 2921250128140583001 (.basic (.split 2801)) .empty .empty)
                        .empty))
                    (.node 4130580930517332837 (.basic (.split 11)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^4
                      (.node 3721928118949345041 (.basic (.split 50544702849929377)) -- 3^4 * 11^16
                        (.node 3512362576094162973 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 4714322510948370489 (.basic (.split 43)) .empty .empty))))))
            (.node 57687288758368983909 (.basic (.split 331)) -- 3^8 * 13^2 * 61 * 31^8
              (.node 15960081673120310649 (.basic (.groups [19, 419, 4534166740403])) -- 3^4 * 11^2 * 7^18
                (.node 8101513033895685573 (.basic (.split 757)) -- 3^8 * 13^12 * 53
                  (.node 6065741734449730281 (.basic (.split 433)) -- 3^2 * 13^4 * 30941^2 * 157^2
                    (.node 5615707577694524037 (.basic (.groups [61, 157, 701, 757])) -- 3^8 * 13^5 * 7^2 * 19^6
                      (.node 5578848897389735877 (.basic (.split 67)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2
                        (.node 5141485390869140625 (.basic (.split 131)) .empty .empty)
                        .empty)
                      (.node 5988749482648618569 (.basic (.split 103)) -- 3^2 * 13^16
                        (.node 5968835603933417397 (.basic (.split 757)) .empty .empty)
                        .empty))
                    (.node 6544828178351995077 (.basic (.split 29)) -- 3^2 * 13^13 * 7^4
                      (.node 6182605770469513641 (.basic (.split 3851)) -- 3^10 * 23^6 * 29^4
                        (.node 6168642851776923441 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 7598661503948819577 (.basic (.split 16148168401)) -- 3^2 * 13^2 * 61^2 * 97 * 7^12
                        (.node 7335784449228939561 (.basic (.split 5)) .empty .empty)
                        .empty)))
                  (.node 11102669073028503369 (.basic (.groups [19, 79, 2801, 3851])) -- 3^10 * 23^8 * 7^4
                    (.node 9335695156820604117 (.basic (.groups [19, 29, 4733])) -- 3^2 * 13 * 7^20
                      (.node 8683833130588245357 (.basic (.split 43)) -- 3^2 * 13 * 7^2 * 19^2 * 127^6
                        (.node 8185560987322279197 (.basic (.groups [11, 29, 757])) .empty .empty)
                        .empty)
                      (.node 10341391887428961177 (.basic (.split 37)) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2
                        (.node 10341244961980279893 (.basic (.groups [31, 151, 911, 2801])) .empty .empty)
                        .empty))
                    (.node 15208616602381689837 (.basic (.split 19)) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4
                      (.node 14137967992768145253 (.basic (.split 1093)) -- 3^2 * 13 * 7^2 * 19^4 * 151^2 * 911^2
                        (.node 12688934431006301013 (.basic (.split 599)) .empty .empty)
                        .empty)
                      (.node 15232771123775668089 (.basic (.split 5)) .empty .empty))))
                (.node 26959577408176669893 (.basic (.groups [11, 1123, 2411, 30941])) -- 3^2 * 13^9 * 7^10
                  (.node 21521863188954091089 (.basic (.split 127)) -- 3^10 * 23^2 * 7^2 * 19^2 * 79^4
                    (.node 17728659159009693489 (.basic (.groups [29, 157, 3187])) -- 3^16 * 1871^2 * 7^6
                      (.node 17291411932618231317 (.basic (.split 5)) -- 3^2 * 13 * 7^4 * 2801^4
                        (.node 17098503934900580829 (.basic (.split 757)) .empty .empty)
                        .empty)
                      (.node 20600462852218645821 (.basic (.split 31)) -- 3^12 * 797161^2 * 61
                        (.node 17786796207200728461 (.basic (.split 5)) .empty .empty)
                        .empty))
                    (.node 25707426954345703125 (.basic (.groups [29, 131, 449, 19531])) -- 3^2 * 13^2 * 61^4 * 5^13
                      (.node 25623914682004413957 (.basic (.split 757)) -- 3^8 * 13 * 7^2 * 19^10
                        (.node 23132326627505446533 (.basic (.groups [37, 701, 757])) .empty .empty)
                        .empty)
                      (.node 25995196633501601289 (.basic (.groups [79, 127, 523, 3851])) -- 3^10 * 23^2 * 7^2 * 19^8
                        (.node 25833126466573035129 (.basic (.groups [61, 757, 4651, 30941])) .empty .empty)
                        .empty)))
                  (.node 43244574864558459093 (.basic (.split 379)) -- 3^8 * 13^2 * 61^6 * 757
                    (.node 35430320726611980273 (.basic (.split 7)) -- 3^8 * 13^2 * 61^2 * 97^5
                      (.node 28992130453393126821 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581 * 17^4
                        (.node 28860945609090665889 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 41414996894187268521 (.basic (.split 61)) -- 3^10 * 23^4 * 3851^2 * 13^2
                        (.node 36215083369117366029 (.basic (.split 127)) .empty .empty)
                        .empty))
                    (.node 45681551965375184313 (.basic (.split 4733)) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4
                      (.node 44447561890220021841 (.basic (.split 19)) -- 3^4 * 11^6 * 43^6 * 7^2
                        (.node 44196585648660305289 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 48218019844593269853 (.basic (.split 29)) .empty .empty)))))
              (.node 138356968286345779881 (.basic (.split 1621)) -- 3^6 * 1093^2 * 398581^2
                (.node 77853743274432041397 (.basic (.groups [7, 19, 61, 157, 271])) -- 3^2 * 13^17
                  (.node 75786543267265417509 (.basic (.groups [31, 67, 3851, 5336717])) -- 3^10 * 23^6 * 29^2 * 13^2 * 61
                    (.node 67249501302930093693 (.basic (.split 11)) -- 3^8 * 13 * 7^4 * 757^4
                      (.node 63531437972520155625 (.basic (.split 11)) -- 3^2 * 13^8 * 61^4 * 5^4
                        (.node 61535674453368353121 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 75378319125535809621 (.basic (.groups [5, 13, 67])) -- 3^10 * 23^2 * 7^6 * 29^5
                        (.node 74103069251147509521 (.basic (.groups [5, 131, 757, 21491, 1609669])) .empty .empty)
                        .empty))
                    (.node 76163855618878340445 (.basic (.split 31)) -- 3^6 * 1093^4 * 11^4 * 5
                      (.node 76045932094365697581 (.basic (.split 23)) -- 3^2 * 13^2 * 61 * 31^10
                        (.node 75818889029730085317 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 77416319605108848273 (.basic (.split 19)) -- 3^8 * 13^4 * 757^2 * 14713 * 7^2
                        (.node 77218248161612227761 (.basic (.groups [29, 79, 419, 859, 4733])) .empty .empty)
                        .empty)))
                  (.node 111052390409809776837 (.basic (.groups [61, 157, 14009])) -- 3^2 * 13^5 * 7^16
                    (.node 94655170156061304153 (.basic (.split 19)) -- 3^8 * 13^8 * 61^2 * 97 * 7^2
                      (.node 81797215007414075841 (.basic (.groups [79, 127, 3851, 7792003])) -- 3^10 * 23^8 * 7^2 * 19^2
                        (.node 80983827615842134893 (.basic (.groups [5, 131, 157, 757])) .empty .empty)
                        .empty)
                      (.node 110177815541079718341 (.basic (.groups [29, 31, 97, 523])) -- 3^8 * 13^2 * 61^5 * 7^6
                        (.node 96620017484915332317 (.basic (.split 757)) .empty .empty)
                        .empty))
                    (.node 128537134771728515625 (.basic (.groups [11, 31, 71, 131])) -- 3^2 * 13^2 * 61^4 * 5^14
                      (.node 113049474211809989217 (.basic (.groups [757, 1123, 293459])) -- 3^8 * 13^2 * 61^2 * 97 * 7^10
                        (.node 112047154968567143493 (.basic (.split 67)) .empty .empty)
                        .empty)
                      (.node 131858797780683489321 (.basic (.split 97)) .empty .empty))))
                (.node 218091682214494175997 (.basic (.split 732541)) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2
                  (.node 183672039573593718849 (.basic (.split 29)) -- 3^2 * 13^10 * 23^6
                    (.node 168295599545472352053 (.basic (.split 11)) -- 3^6 * 1093 * 547^2 * 163^4
                      (.node 164737124830554644277 (.basic (.groups [11, 41, 151, 911, 1063])) -- 3^2 * 13 * 7^8 * 19^4 * 37^4
                        (.node 156102680601167396733 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 179295567343615895589 (.basic (.groups [5, 13, 67, 271])) -- 3^10 * 23^6 * 29^5
                        (.node 172105766228613985677 (.basic (.split 97)) .empty .empty)
                        .empty))
                    (.node 209965996920784517361 (.basic (.groups [67, 3851, 30941, 5336717])) -- 3^10 * 23^6 * 29^2 * 13^4
                      (.node 204777434570668811397 (.basic (.groups [157, 757, 2801, 3169])) -- 3^8 * 13^5 * 7^4 * 61^2 * 97^2
                        (.node 187378602145672377609 (.basic (.split 757)) .empty .empty)
                        .empty)
                      (.node 212566794017202148329 (.basic (.split 19)) .empty .empty)))
                  (.node 283159843141774486797 (.basic (.split 5)) -- 3^8 * 13 * 7^2 * 19^4 * 151^4
                    (.node 241122892768794692253 (.basic (.split 7)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2
                      (.node 240327229716484548561 (.basic (.groups [19, 1772893, 16148168401])) -- 3^4 * 11^8 * 7^12
                        (.node 233848989964255602573 (.basic (.split 61)) .empty .empty)
                        .empty)
                      (.node 267007306393130517513 (.basic (.split 7)) -- 3^8 * 13^6 * 757^2 * 14713
                        (.node 253113264365122535049 (.basic (.groups [419, 757, 859, 18041])) .empty .empty)
                        .empty))
                    (.node 301504269599169089661 (.basic (.groups [5, 11, 757, 17351])) -- 3^8 * 13^8 * 61 * 31^4
                      (.node 295989481339225935921 (.basic (.groups [7, 19, 3851, 3937230404603])) -- 3^10 * 23^10 * 11^2
                        (.node 295453469911933116693 (.basic (.groups [5, 131, 151, 157, 911, 21491])) .empty .empty)
                        .empty)
                      (.node 302263499737069248609 (.basic (.split 19)) .empty .empty))))))))
        (.node 640405556136672640704117 (.basic (.groups [5, 131, 157])) -- 3^2 * 13^5 * 7^12 * 61^4
          (.node 13069501145646380422533 (.basic (.groups [5, 131, 157, 1123])) -- 3^2 * 13^5 * 7^10 * 61^4
            (.node 2926821026369110235157 (.basic (.split 11)) -- 3^8 * 13^4 * 757 * 379^4
              (.node 1144842437412878650173 (.basic (.groups [523, 757, 5419, 29989])) -- 3^8 * 13 * 7^2 * 19^8 * 127^2
                (.node 672253723403511866253 (.basic (.split 3313)) -- 3^2 * 13 * 7^10 * 1123^2 * 127^2
                  (.node 429380190796471335369 (.basic (.groups [7, 409, 757, 264031])) -- 3^8 * 13^12 * 53^2
                    (.node 378240769113195998529 (.basic (.split 1609669)) -- 3^2 * 13^8 * 61^6
                      (.node 362876454203199456429 (.basic (.groups [31, 97, 523, 1123, 293459])) -- 3^2 * 13^2 * 61^5 * 7^10
                        (.node 320696580739247758773 (.basic (.groups [29, 4733, 22079, 5229043])) .empty .empty)
                        .empty)
                      (.node 413361896513784065757 (.basic (.split 157)) -- 3^2 * 13^5 * 7^4 * 61^6
                        (.node 397456245658163916549 (.basic (.split 1609669)) .empty .empty)
                        .empty))
                    (.node 524277363481241215329 (.basic (.split 1806113)) -- 3^4 * 11^10 * 15797^2
                      (.node 450353302392870749961 (.basic (.split 6115909044841454629)) -- 3^4 * 11^18
                        (.node 444669905180018211525 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 544030784578396665081 (.basic (.groups [19, 29, 79])) -- 3^10 * 23^8 * 7^6
                        (.node 527515500574206771201 (.basic (.groups [5, 71, 151, 34511, 228729421])) .empty .empty)
                        .empty)))
                  (.node 962272632345398694369 (.basic (.groups [151, 157, 911])) -- 3^16 * 1871^2 * 7^2 * 19^4
                    (.node 837826692810128460621 (.basic (.groups [29, 757, 4733, 5233])) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^6
                      (.node 780228733699143080469 (.basic (.split 5)) -- 3^8 * 13^2 * 61 * 31^2 * 331^4
                        (.node 745222213516702802013 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 887629918356701686881 (.basic (.split 31)) -- 3^2 * 13^2 * 61^2 * 97^4 * 11^6
                        (.node 872522782340593225797 (.cut 5 7 556978920450403) .empty .empty)
                        .empty))
                    (.node 1034663604824013195213 (.basic (.split 97)) -- 3^2 * 13^5 * 7^6 * 29^4 * 61^2
                      (.node 1012098662567616538161 (.basic (.split 12865927)) -- 3^2 * 13^18
                        (.node 1003902094969448651613 (.basic (.split 61)) .empty .empty)
                        .empty)
                      (.node 1084994568639244436121 (.basic (.split 199)) .empty .empty))))
                (.node 1843165305976855838769 (.basic (.split 31)) -- 3^6 * 1093^4 * 11^6
                  (.node 1414186334845442628561 (.basic (.split 409)) -- 3^2 * 13^12 * 53^2 * 7^4
                    (.node 1256628233985337395081 (.basic (.split 13)) -- 3^12 * 797161^2 * 61^2
                      (.node 1242935235998051916321 (.basic (.split 7)) -- 3^6 * 1093^6
                        (.node 1187810198070661942569 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 1321019293000656824757 (.basic (.groups [11, 2411, 30941])) -- 3^2 * 13^9 * 7^12
                        (.node 1294036658086367934729 (.basic (.split 3851)) .empty .empty)
                        .empty))
                    (.node 1654497881957871030249 (.basic (.split 11)) -- 3^2 * 13^12 * 53^4
                      (.node 1600252020403325317161 (.basic (.split 2801)) -- 3^10 * 23^2 * 7^4 * 79^2 * 43^4
                        (.node 1588285949313003890625 (.basic (.split 131)) .empty .empty)
                        .empty)
                      (.node 1736085715603987033377 (.basic (.groups [19, 67, 139, 757, 3169])) -- 3^8 * 13^2 * 61^2 * 97^5 * 7^2
                        (.node 1677215141530955518041 (.basic (.groups [19, 181, 199, 631, 3079, 45319])) .empty .empty)
                        .empty)))
                  (.node 2526314810545423379781 (.basic (.split 31)) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61
                    (.node 2177930532620781070209 (.basic (.split 2801)) -- 3^4 * 11^6 * 43^6 * 7^4
                      (.node 2077316469954702184221 (.basic (.split 331)) -- 3^2 * 13^14 * 61 * 31^2
                        (.node 2027270435547723177357 (.basic (.groups [61, 127, 157])) .empty .empty)
                        .empty)
                      (.node 2520009914928591920409 (.basic (.split 31)) -- 3^18 * 1597^4
                        (.node 2185971254640538479009 (.basic (.groups [79, 3851, 4733])) .empty .empty)
                        .empty))
                    (.node 2729557959970198725693 (.basic (.groups [7, 61, 67])) -- 3^10 * 23^6 * 29^2 * 13^5
                      (.node 2643005324931992930637 (.basic (.split 11)) -- 3^2 * 13^5 * 7^4 * 61^2 * 97^4
                        (.node 2626466171016733211673 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 2848507219459519122141 (.basic (.groups [5, 11, 97, 523, 2801, 17351])) .empty .empty)))))
              (.node 6330514352198830865253 (.basic (.split 43)) -- 3^8 * 13 * 7^2 * 19^2 * 127^6
                (.node 4622979139303190468049 (.basic (.groups [67, 97, 3851, 5336717])) -- 3^10 * 23^6 * 29^2 * 13^2 * 61^2
                  (.node 3793399660650333565377 (.basic (.split 1051)) -- 3^8 * 13^4 * 757^2 * 14713 * 7^4
                    (.node 3436741110481362086481 (.basic (.split 43)) -- 3^8 * 13^2 * 61^2 * 97^6
                      (.node 3378051291838989348801 (.cut 5 31 25197303266533487) -- 3^18 * 1597^2 * 43^4
                        (.node 3213428369293212890625 (.basic (.groups [131, 409, 21491])) .empty .empty)
                        .empty)
                      (.node 3783694159918999160289 (.basic (.groups [19, 37, 79, 419])) -- 3^2 * 13^10 * 23^2 * 7^8
                        (.node 3733189431274881041373 (.basic (.groups [31, 701, 2801])) .empty .empty)
                        .empty))
                    (.node 4520287224319998080781 (.basic (.groups [7, 31, 97, 523])) -- 3^8 * 13^8 * 61^5
                      (.node 4221182999294262560637 (.basic (.split 787)) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2
                        (.node 4135292096602383124317 (.basic (.groups [37, 1063, 104281, 62060021])) .empty .empty)
                        .empty)
                      (.node 4580705329593274665693 (.basic (.groups [31, 127, 151, 211, 911])) -- 3^2 * 13 * 7^2 * 19^14
                        (.node 4577863583293880023053 (.basic (.groups [5, 67, 131, 157, 4733])) .empty .empty)
                        .empty)))
                  (.node 5490310593459790031157 (.basic (.split 67)) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2
                    (.node 5326489147634217846621 (.basic (.groups [5, 419, 859, 18041, 5336717])) -- 3^2 * 13^10 * 23^6 * 29
                      (.node 5199571452964860972081 (.basic (.groups [7, 3851, 5336717, 88009573])) -- 3^10 * 23^6 * 29^6
                        (.node 4638103337647003903497 (.basic (.groups [757, 2801, 1609669])) .empty .empty)
                        .empty)
                      (.node 5398712961512906198709 (.basic (.groups [19, 31, 37])) -- 3^8 * 13^2 * 61^5 * 7^8
                        (.node 5347786863487896939969 (.basic (.groups [5, 31, 757, 3221, 262321])) .empty .empty)
                        .empty))
                    (.node 5654765293878228653853 (.basic (.split 43)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6
                      (.node 5539424236378689471633 (.cut 5 101 12224163479557) -- 3^8 * 13^2 * 61^2 * 97 * 7^12
                        (.node 5504200497994027859757 (.basic (.groups [67, 2801, 22079, 5229043])) .empty .empty)
                        .empty)
                      (.node 5791006878992635651533 (.basic (.split 23)) .empty .empty))))
                (.node 9835083403604528846049 (.basic (.groups [43, 419, 859, 2801, 18041])) -- 3^2 * 13^10 * 23^2 * 7^4 * 79^2
                  (.node 8350769912529466198413 (.cut 5 257 12620972402677) -- 3^8 * 13 * 7^8 * 19^8
                    (.node 7649031349457202439917 (.basic (.split 2801)) -- 3^10 * 23^4 * 3851^2 * 13 * 7^4
                      (.node 7445816608857570727641 (.basic (.groups [7, 19, 191, 2521, 30941, 62081])) -- 3^8 * 13^4 * 757^4 * 11^2
                        (.node 6999134475117648380049 (.basic (.split 30941)) .empty .empty)
                        .empty)
                      (.node 8182421608921772985801 (.basic (.split 467)) -- 3^10 * 23^2 * 7^4 * 79^4 * 2801
                        (.node 7769392611212426883129 (.basic (.groups [151, 911, 3851, 39449441])) .empty .empty)
                        .empty))
                    (.node 9250233200203593438477 (.basic (.groups [599, 757, 29251])) -- 3^8 * 13 * 7^2 * 19^12
                      (.node 8856416438238134531493 (.basic (.split 911)) -- 3^2 * 13 * 7^2 * 19^4 * 151^6
                        (.node 8378725701030613651269 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 9384265984694078065329 (.basic (.groups [79, 3851, 104281])) .empty .empty)))
                  (.node 11116747629500455288125 (.basic (.groups [11, 31, 71, 131, 21491, 1238411])) -- 3^2 * 13^2 * 61^9 * 5^4
                    (.node 10399528982619251677449 (.basic (.split 11)) -- 3^8 * 13^6 * 757^4
                      (.node 10315291611273621636573 (.basic (.split 67)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4
                        (.node 9956656179033808711401 (.basic (.split 433)) .empty .empty)
                        .empty)
                      (.node 10466159093674918782381 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2
                        (.node 10418801364881730385929 (.basic (.split 127)) .empty .empty)
                        .empty))
                    (.node 12813392246024384418573 (.basic (.split 97)) -- 3^8 * 13^6 * 757 * 379^2 * 61^2
                      (.node 12790303384726298464137 (.basic (.split 7)) -- 3^2 * 13^14 * 61^2 * 97
                        (.node 11815021745670939920397 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 12966574435049331048069 (.basic (.groups [5, 11, 31, 131, 757])) .empty .empty))))))
            (.node 97162508934431077271121 (.basic (.groups [7, 19, 79, 419, 859])) -- 3^2 * 13^10 * 23^8
              (.node 36515888462318437298637 (.basic (.groups [19, 37, 67, 613, 1063])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^8
                (.node 20363767545002154598413 (.basic (.split 7)) -- 3^6 * 1093 * 547^2 * 163^4 * 11^2
                  (.node 16336167041809386136053 (.basic (.split 7)) -- 3^12 * 797161^2 * 61^2 * 13
                    (.node 13251087932909532844077 (.basic (.split 7)) -- 3^6 * 1093 * 547^4 * 431^2
                      (.node 13083358013263395358137 (.basic (.split 19)) -- 3^8 * 13^6 * 757^2 * 14713 * 7^2
                        (.node 13073645096251369136469 (.basic (.split 151)) .empty .empty)
                        .empty)
                      (.node 15714132456223140179877 (.basic (.groups [19, 29, 37])) -- 3^2 * 13^13 * 7^8
                        (.node 14810911487116393181841 (.basic (.split 19)) .empty .empty)
                        .empty))
                    (.node 18231522049725378509241 (.basic (.groups [281, 337, 1289, 2017])) -- 3^10 * 23^2 * 7^4 * 79^6
                      (.node 17780946255956773365021 (.basic (.groups [31, 97, 523, 16148168401])) -- 3^2 * 13^2 * 61^5 * 7^12
                        (.node 17406705163898170416933 (.basic (.groups [29, 151, 911, 22079])) .empty .empty)
                        .empty)
                      (.node 19797044800982118633981 (.basic (.split 151)) -- 3^12 * 797161^2 * 61 * 31^2
                        (.node 18244386270981115804377 (.basic (.split 14009)) .empty .empty)
                        .empty)))
                  (.node 32736143172470753533401 (.basic (.split 14713)) -- 3^8 * 13^2 * 61^6 * 757^2
                    (.node 26455282239703573592973 (.basic (.groups [5, 11, 127])) -- 3^2 * 13 * 7^14 * 19^2 * 31^4
                      (.node 23245434905101356829401 (.basic (.split 19)) -- 3^8 * 13^4 * 757^2 * 14713^2
                        (.node 21343795357033652988213 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 29528794617676481378601 (.basic (.groups [79, 151, 911])) -- 3^10 * 23^8 * 7^2 * 19^4
                        (.node 27947291377444294226553 (.basic (.split 127)) .empty .empty)
                        .empty))
                    (.node 35484253479612583434009 (.basic (.groups [67, 3851, 5229043])) -- 3^10 * 23^6 * 29^2 * 13^6
                      (.node 34399212420077614838781 (.basic (.split 14713)) -- 3^8 * 13^2 * 61 * 31^6 * 757^2
                        (.node 34373682915249286818261 (.basic (.groups [7, 757, 5233, 1609669])) .empty .empty)
                        .empty)
                      (.node 35814727242046338246441 (.basic (.groups [5, 3221, 3851])) .empty .empty))))
                (.node 60903826563904543899729 (.basic (.split 19)) -- 3^6 * 1093^6 * 7^2
                  (.node 41053507947696294570429 (.basic (.groups [19, 37, 757])) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^8
                    (.node 40228298077919454020349 (.basic (.split 7)) -- 3^2 * 13^2 * 61 * 31^10 * 23^2
                      (.node 39707148732825097265625 (.basic (.groups [19, 31, 131, 829])) -- 3^2 * 13^8 * 61^4 * 5^8
                        (.node 38418185202880530007233 (.basic (.split 4733)) .empty .empty)
                        .empty)
                      (.node 40551354689302939946373 (.basic (.groups [67, 127, 22079, 5229043])) -- 3^2 * 13^13 * 7^2 * 19^2 * 29^2
                        (.node 40449022943652738800973 (.basic (.split 67)) .empty .empty)
                        .empty))
                    (.node 52563622415657977331253 (.basic (.split 41)) -- 3^2 * 13 * 7^10 * 1123^4
                      (.node 46582505561199843312597 (.basic (.split 163)) -- 3^8 * 13^4 * 757^5
                        (.node 42062538391922251804689 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 59470102063830226583997 (.basic (.groups [11, 41, 701, 1063])) -- 3^2 * 13 * 7^8 * 19^6 * 37^4
                        (.node 55437484496792593536549 (.basic (.groups [23, 397, 617, 757])) .empty .empty)
                        .empty)))
                  (.node 73080140742685435375341 (.basic (.split 42407)) -- 3^2 * 13^2 * 61 * 31^12
                    (.node 65129181360912042820173 (.basic (.split 5)) -- 3^2 * 13 * 7^2 * 19^6 * 701^4
                      (.node 63534643261419194398521 (.basic (.split 443)) -- 3^2 * 13^16 * 103^2
                        (.node 60955854328127952504441 (.basic (.split 859)) .empty .empty)
                        .empty)
                      (.node 69295130407426688799489 (.basic (.groups [29, 409, 4733, 264031])) -- 3^2 * 13^12 * 53^2 * 7^6
                        (.node 67302978560200879692561 (.basic (.split 1621)) .empty .empty)
                        .empty))
                    (.node 85068200064595364635473 (.basic (.groups [67, 139, 757, 2801])) -- 3^8 * 13^2 * 61^2 * 97^5 * 7^4
                      (.node 83136560949606381828237 (.basic (.split 163)) -- 3^4 * 11^12 * 1093 * 547^2
                        (.node 76736612640209975546769 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 90988748176529428940637 (.basic (.groups [7, 61, 157, 292561])) .empty .empty)))))
              (.node 227267063544703191271353 (.cut 5 101 5767252476389) -- 3^8 * 13^8 * 61^2 * 97 * 7^6
                (.node 154468185281392317552009 (.basic (.groups [67, 419, 859, 18041, 5336717])) -- 3^2 * 13^10 * 23^6 * 29^2
                  (.node 128696842379819927371977 (.basic (.split 19)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^2
                    (.node 106895302542812625881949 (.basic (.groups [31, 97, 523, 4733, 732541])) -- 3^2 * 13^2 * 61^5 * 7^6 * 29^4
                      (.node 106718596098418272440241 (.basic (.groups [29, 4733, 5839, 45319])) -- 3^4 * 11^6 * 43^6 * 7^6
                        (.node 106658702638207855126173 (.basic (.groups [5, 131, 157, 701, 21491])) .empty .empty)
                        .empty)
                      (.node 117260137575873546007221 (.basic (.split 2180921)) -- 3^2 * 13^2 * 61 * 31^2 * 331^6
                        (.node 107403220121160904112601 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 141845601824273989850013 (.basic (.split 379)) -- 3^8 * 13^8 * 61^2 * 97^2 * 757
                      (.node 134317948162262482486449 (.basic (.groups [127, 281, 337, 1289])) -- 3^10 * 23^2 * 7^2 * 19^2 * 79^6
                        (.node 133896916849149821040921 (.basic (.groups [29, 419, 757])) .empty .empty)
                        .empty)
                      (.node 154105203443270826166641 (.basic (.split 97)) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^2
                        (.node 149514468012451401696369 (.basic (.split 11)) .empty .empty)
                        .empty)))
                  (.node 200194243716902394660129 (.basic (.groups [7, 19, 131, 5581, 264031])) -- 3^2 * 13^12 * 53^4 * 11^2
                    (.node 185401013836030958854161 (.basic (.groups [79, 419, 859])) -- 3^2 * 13^10 * 23^2 * 7^10
                      (.node 183415104742389602013477 (.basic (.split 22406023)) -- 3^2 * 13 * 7^6 * 29^6 * 4733^2
                        (.node 171044673973927194949209 (.basic (.groups [43, 61, 337, 547])) .empty .empty)
                        .empty)
                      (.node 196667000559938961763893 (.basic (.groups [61, 67, 157, 4733])) -- 3^2 * 13^5 * 7^6 * 29^8
                        (.node 185876583371866344703473 (.basic (.groups [29, 1051, 4733, 30941])) .empty .empty)
                        .empty))
                    (.node 224276645592166509187101 (.basic (.split 811)) -- 3^6 * 1093^2 * 398581^2 * 1621
                      (.node 223023002023199556491049 (.basic (.split 7)) -- 3^6 * 1093^4 * 11^8
                        (.node 212370171543522019768689 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 225525123893029308015213 (.basic (.groups [71, 151, 911, 1063])) .empty .empty))))
                (.node 344595967926343110657729 (.basic (.groups [307, 433, 2801, 3851])) -- 3^10 * 23^2 * 7^4 * 79^2 * 43^2 * 631^2
                  (.node 277918690737511382203125 (.basic (.groups [11, 31, 131, 19531, 21491])) -- 3^2 * 13^2 * 61^9 * 5^6
                    (.node 264536935114132403736741 (.cut 5 31 392336023518358289) -- 3^8 * 13^2 * 61^5 * 7^10
                      (.node 235588074095847754723689 (.basic (.split 5)) -- 3^2 * 13^4 * 30941^4
                        (.node 230084947189681754754573 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 275737520683519882927641 (.basic (.split 757)) -- 3^8 * 13^8 * 61^6
                        (.node 269025219079529711526693 (.basic (.groups [29, 67, 127, 613, 4733])) .empty .empty)
                        .empty))
                    (.node 301340822558548583936853 (.basic (.groups [157, 757, 2801])) -- 3^8 * 13^5 * 7^4 * 61^6
                      (.node 289745603084801495164221 (.basic (.groups [757, 1609669, 917087137])) -- 3^8 * 13^8 * 61 * 31^6
                        (.node 282122086079625647464557 (.basic (.groups [5, 131, 787, 21491, 30941])) .empty .empty)
                        .empty)
                      (.node 340253805148893976057173 (.basic (.split 163)) .empty .empty)))
                  (.node 494632753456379629741533 (.basic (.split 11)) -- 3^8 * 13^6 * 757 * 379^4
                    (.node 362408656283970963232293 (.basic (.groups [61, 157, 599, 29251])) -- 3^2 * 13^5 * 7^2 * 19^12
                      (.node 354145344190662338453997 (.basic (.groups [7, 19, 41, 30941, 45869891])) -- 3^8 * 13^4 * 757 * 379^4 * 11^2
                        (.node 347126131374640535174481 (.basic (.split 3851)) .empty .empty)
                        .empty)
                      (.node 490646586541923263763441 (.basic (.groups [5, 131, 4651, 21491, 30941])) -- 3^2 * 13^14 * 61^4
                        (.node 374802536123402919555933 (.basic (.groups [29, 4733, 292561])) .empty .empty)
                        .empty))
                    (.node 578936065537876056099453 (.basic (.split 43)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4
                      (.node 578402210951786035081449 (.basic (.groups [5, 41, 2801, 264031])) -- 3^2 * 13^12 * 53^2 * 7^4 * 409
                        (.node 532165029847905992366205 (.basic (.split 127)) .empty .empty)
                        .empty)
                      (.node 584113079660493996681741 (.basic (.split 307)) .empty .empty)))))))
          (.node 10928127099136778268061401 (.basic (.split 19)) -- 3^6 * 1093^4 * 11^8 * 7^2
            (.node 3101170796690736752857809 (.basic (.split 45319)) -- 3^4 * 11^6 * 43^10
              (.node 1206128955947287981051521 (.basic (.groups [11, 131, 757])) -- 3^8 * 13^12 * 53^4
                (.node 893974927278074674414473 (.cut 5 31 1899815864228857) -- 3^2 * 13^2 * 61^2 * 97 * 7^18
                  (.node 731844627232728067025877 (.basic (.groups [61, 157])) -- 3^8 * 13^5 * 7^2 * 19^10
                    (.node 649303308712567109359773 (.basic (.split 19)) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2
                      (.node 647082210482035529736249 (.basic (.groups [31, 43, 757, 45319])) -- 3^8 * 13^2 * 61^2 * 97^4 * 11^6
                        (.node 641084542649906372548713 (.basic (.split 1051)) .empty .empty)
                        .empty)
                      (.node 725734662868703265910209 (.basic (.groups [19, 31, 37, 1063, 4189129561])) -- 3^6 * 1093^4 * 11^2 * 7^8
                        (.node 713379926880730372747653 (.basic (.split 787)) .empty .empty)
                        .empty))
                    (.node 790961040538009193932209 (.basic (.split 199)) -- 3^8 * 13^2 * 61^10
                      (.node 763077718495487255992677 (.basic (.split 223)) -- 3^2 * 13 * 7^16 * 14009^2
                        (.node 754884376488538835510205 (.basic (.split 14713)) .empty .empty)
                        .empty)
                      (.node 870152091656995097174133 (.basic (.groups [97, 157, 4733, 88009573])) -- 3^2 * 13^5 * 7^6 * 29^6 * 61^2
                        (.node 800472185048659920666597 (.basic (.split 19)) .empty .empty)
                        .empty)))
                  (.node 1099382361542303127214653 (.basic (.split 151)) -- 3^2 * 13^5 * 7^2 * 19^4 * 61^6
                    (.node 997824609705105575322237 (.basic (.split 19)) -- 3^6 * 1093 * 547^2 * 163^4 * 11^2 * 7^2
                      (.node 992678718320627431640625 (.basic (.groups [131, 21491, 1609669])) -- 3^2 * 13^8 * 61^4 * 5^10
                        (.node 900943809671766058044561 (.basic (.groups [5, 191, 2521, 3221, 30941])) .empty .empty)
                        .empty)
                      (.node 1045845972494648996422437 (.basic (.split 19)) -- 3^6 * 1093 * 547^6 * 7^2
                        (.node 1007570836501906951741401 (.basic (.split 127)) .empty .empty)
                        .empty))
                    (.node 1177940370479238773618445 (.basic (.split 11)) -- 3^2 * 13^4 * 30941^4 * 5
                      (.node 1141485600345906126808809 (.basic (.split 331)) -- 3^2 * 13^6 * 5229043^2 * 31^2
                        (.node 1137259852050245480654409 (.basic (.split 37)) .empty .empty)
                        .empty)
                      (.node 1182853726294882576228281 (.basic (.split 292561)) .empty .empty))))
                (.node 2011621889437118433951021 (.basic (.groups [757, 1123])) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^10
                  (.node 1771281859043758461057009 (.basic (.split 43)) -- 3^6 * 1093^4 * 11^6 * 31^2
                    (.node 1504847973770047674350973 (.basic (.split 433)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4
                      (.node 1492840446873460307878437 (.basic (.groups [37, 599, 1063])) -- 3^2 * 13 * 7^8 * 19^12
                        (.node 1258343006896929452971329 (.basic (.groups [7, 19, 191, 2521, 62081])) .empty .empty)
                        .empty)
                      (.node 1763045267588631400923081 (.basic (.groups [11, 31, 757, 262321])) -- 3^8 * 13^8 * 61^2 * 97^4
                        (.node 1653634623983172154315173 (.basic (.split 3044803)) .empty .empty)
                        .empty))
                    (.node 1971186605818053246997101 (.basic (.groups [19, 79, 397, 617, 150332843])) -- 3^2 * 13^2 * 61 * 31^10 * 23^2 * 7^2
                      (.node 1926750881875422846434373 (.basic (.groups [11, 31, 157])) -- 3^8 * 13^5 * 7^4 * 61^2 * 97^4
                        (.node 1789278534653603427633213 (.basic (.groups [19, 67, 613, 1123])) .empty .empty)
                        .empty)
                      (.node 1996301127626468799036381 (.basic (.groups [5, 11, 4651, 17351])) -- 3^2 * 13^14 * 61 * 31^4
                        (.node 1982002124238984201247677 (.basic (.groups [67, 151, 613, 911, 2801])) .empty .empty)
                        .empty)))
                  (.node 2804750732647686104809569 (.basic (.groups [701, 3851, 70841])) -- 3^10 * 23^2 * 7^2 * 19^6 * 79^4
                    (.node 2427788532934151867969541 (.basic (.split 331)) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61 * 31^2
                      (.node 2421729528246376835513049 (.cut 5 101 25288724263997428529) -- 3^18 * 1597^4 * 31^2
                        (.node 2421451727597847345216741 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 2737415437900597876377501 (.basic (.split 97)) -- 3^2 * 13^2 * 61^5 * 7^4 * 31^6
                        (.node 2464015872945260706407973 (.basic (.groups [5, 31, 613, 1301, 1601, 3221])) .empty .empty)
                        .empty))
                    (.node 3024719978072051528108109 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2
                      (.node 2984287501631322651086721 (.basic (.split 29)) -- 3^6 * 1093^6 * 7^4
                        (.node 2958865985725748511430689 (.basic (.groups [2801, 3851, 5839])) .empty .empty)
                        .empty)
                      (.node 3063442638987104259660957 (.basic (.split 79)) .empty .empty)))))
              (.node 4870236785232806582939253 (.basic (.groups [521, 4733, 148123, 4748492087])) -- 3^2 * 13 * 7^6 * 29^12
                (.node 4311232125521639172036633 (.basic (.split 7)) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433
                  (.node 3849983273550153099387573 (.basic (.groups [5, 131, 157, 4733])) -- 3^2 * 13^5 * 7^6 * 29^4 * 61^4
                    (.node 3634276499143035052114809 (.basic (.split 5)) -- 3^10 * 23^4 * 3851^4
                      (.node 3395461389963907751174961 (.basic (.groups [19, 37, 409])) -- 3^2 * 13^12 * 53^2 * 7^8
                        (.node 3339334185273497231290197 (.cut 5 257 1696607242487) .empty .empty)
                        .empty)
                      (.node 3778283432816645680439541 (.basic (.split 151)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^4
                        (.node 3761187292722304669320369 (.basic (.groups [151, 409, 911, 264031])) .empty .empty)
                        .empty))
                    (.node 4168341803165172867138177 (.basic (.groups [29, 67, 139])) -- 3^8 * 13^2 * 61^2 * 97^5 * 7^6
                      (.node 4037264789906628546806241 (.basic (.split 187123)) -- 3^2 * 13^2 * 61^12
                        (.node 3928478498962129304168769 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 4302634869034782139307097 (.basic (.split 7)) -- 3^2 * 13^2 * 61^2 * 97^9
                        (.node 4221644014785631389967557 (.cut 5 101 67877289797922147097) .empty .empty)
                        .empty)))
                  (.node 4642563942560888721922077 (.basic (.groups [14713, 264031, 1803647])) -- 3^8 * 13^12 * 53 * 757^2
                    (.node 4482305909149714213367961 (.basic (.groups [467, 3851, 3500201])) -- 3^10 * 23^2 * 7^4 * 79^2 * 43^4 * 2801
                      (.node 4471445784323654921696157 (.basic (.split 613)) -- 3^6 * 1093 * 547^2 * 163^6
                        (.node 4372839591943448077520121 (.basic (.groups [13, 67, 3851])) .empty .empty)
                        .empty)
                      (.node 4629032618812977430055637 (.basic (.groups [2801, 22079, 732541])) -- 3^2 * 13^13 * 7^4 * 29^4
                        (.node 4552802362779491809765413 (.basic (.split 29251)) .empty .empty)
                        .empty))
                    (.node 4719585879746744258265309 (.basic (.split 307)) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^6
                      (.node 4675913658659440447096401 (.basic (.split 5)) -- 3^12 * 797161^2 * 61^4
                        (.node 4647484550419659723969441 (.basic (.split 29)) .empty .empty)
                        .empty)
                      (.node 4723092242788085724287457 (.basic (.split 127)) .empty .empty))))
                (.node 7443451426100367628036593 (.basic (.groups [7, 127, 757, 903870199])) -- 3^8 * 13^2 * 61^8 * 19^2 * 97
                  (.node 6306145276611176441226873 (.basic (.split 31)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4
                    (.node 6100383421870807777655409 (.basic (.groups [467, 5839, 45319, 158341])) -- 3^4 * 11^6 * 43^6 * 7^4 * 2801
                      (.node 5889701852396193868092225 (.basic (.split 11)) -- 3^2 * 13^4 * 30941^4 * 5^2
                        (.node 5229211208822495349571809 (.basic (.groups [19, 37, 1063])) .empty .empty)
                        .empty)
                      (.node 6283820564167239520512813 (.basic (.groups [29, 701, 22079])) -- 3^2 * 13^13 * 7^2 * 19^6
                        (.node 6211693978120041622577613 (.basic (.split 787)) .empty .empty)
                        .empty))
                    (.node 6456327583475600073458397 (.basic (.groups [757, 911, 1499, 7960598843])) -- 3^8 * 13 * 7^2 * 19^4 * 151^6
                      (.node 6354534313280038497903369 (.basic (.split 631)) -- 3^8 * 13^2 * 61^2 * 97^6 * 43^2
                        (.node 6320277043655664246053949 (.basic (.groups [7, 757, 3637, 5233])) .empty .empty)
                        .empty)
                      (.node 6947967268437784555078125 (.basic (.groups [11, 19, 31, 131])) .empty .empty)))
                  (.node 9798280581390842943477621 (.basic (.split 2801)) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^4 * 757^2
                    (.node 7911836578788422592887757 (.basic (.groups [11, 191, 1123])) -- 3^8 * 13 * 7^10 * 757^4
                      (.node 7872443439842773519828893 (.basic (.groups [163, 379, 3511, 14713, 5229043])) -- 3^8 * 13^6 * 757^5
                        (.node 7741373687319295027124757 (.basic (.groups [43, 67, 73, 127, 4933, 92251])) .empty .empty)
                        .empty)
                      (.node 9107952585221450890470177 (.basic (.groups [19, 37, 1051])) -- 3^8 * 13^4 * 757^2 * 14713 * 7^8
                        (.node 8391602000741589815413761 (.basic (.split 127)) .empty .empty)
                        .empty))
                    (.node 10455661028380844780974197 (.basic (.split 71)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^2
                      (.node 10188957387168263436844293 (.basic (.split 2801)) -- 3^2 * 13^5 * 7^4 * 61^6 * 157^2
                        (.node 10088972187257390215785633 (.basic (.groups [151, 911, 1051, 30941])) .empty .empty)
                        .empty)
                      (.node 10842780304775242890794637 (.basic (.split 3313)) .empty .empty))))))
            (.node 46305344043007287526576197 (.basic (.split 31)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^2
              (.node 24646004254040997449863773 (.basic (.split 31)) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2 * 67^2
                (.node 18465163673032319748640317 (.basic (.groups [523, 757, 29989])) -- 3^8 * 13 * 7^2 * 19^8 * 127^4
                  (.node 16117330514752799976163689 (.basic (.split 967)) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^4
                    (.node 12995789634660469397624721 (.basic (.split 31)) -- 3^2 * 13^2 * 61^2 * 97^4 * 11^10
                      (.node 12748039454597722409657601 (.basic (.split 11)) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^4
                        (.node 11733396534526131876515013 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 14948204733997270138164177 (.basic (.split 7)) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^2 * 97
                        (.node 14602097282658638707151253 (.basic (.split 67)) .empty .empty)
                        .empty))
                    (.node 18091250629506619605260649 (.basic (.split 7)) -- 3^2 * 13^4 * 30941^2 * 157^4 * 11^2
                      (.node 17202105377347171731610329 (.basic (.groups [5, 67, 131])) -- 3^10 * 23^6 * 29^2 * 13^2 * 61^4
                        (.node 17034230393436527565780213 (.basic (.groups [67, 157, 4733, 52379047267])) .empty .empty)
                        .empty)
                      (.node 18365324270046743058240717 (.cut 5 101 354867453742783) -- 3^10 * 23^4 * 3851^2 * 13 * 7^8
                        (.node 18171382495715175260574045 (.basic (.split 292561)) .empty .empty)
                        .empty)))
                  (.node 21986281389569540347802169 (.basic (.split 29)) -- 3^6 * 1093^6 * 7^2 * 19^2
                    (.node 19381433361135749308447497 (.basic (.split 11)) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2 * 37^4
                      (.node 19072974189244926406023477 (.basic (.split 67)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^6
                        (.node 19024960053743816007255741 (.basic (.groups [5, 11, 151, 17351, 22996651])) .empty .empty)
                        .empty)
                      (.node 21280769683219391176764621 (.basic (.split 397)) -- 3^2 * 13^2 * 61 * 31^10 * 23^4
                        (.node 20599906639721635917562833 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 23473771477954870066329933 (.basic (.split 7)) -- 3^2 * 13^4 * 30941^2 * 157^5
                      (.node 23379568293297202235482005 (.basic (.split 131)) -- 3^12 * 797161^2 * 61^4 * 5
                        (.node 22918962926589886133228601 (.basic (.groups [37, 43, 3851, 4933])) .empty .empty)
                        .empty)
                      (.node 24223503489745189753875609 (.basic (.groups [5, 131, 3221, 5581])) .empty .empty))))
                (.node 32336297108519135871699729 (.basic (.split 757)) -- 3^8 * 13^2 * 61^2 * 97^8
                  (.node 28367867211355926748873197 (.basic (.split 29)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^6
                    (.node 25423526232355134222847053 (.cut 5 101 52155140944753955729) -- 3^2 * 13 * 7^14 * 19^2 * 31^6
                      (.node 24868037102285121484363533 (.basic (.groups [43, 157, 967, 2801, 20241187])) -- 3^2 * 13^5 * 7^4 * 61^2 * 97^6
                        (.node 24791476212966556007531253 (.basic (.groups [97, 157, 761, 4733])) .empty .empty)
                        .empty)
                      (.node 27701917163115801172383609 (.basic (.groups [97, 151, 757, 911])) -- 3^8 * 13^2 * 61^8 * 19^4
                        (.node 26985783244807146335416929 (.basic (.split 31)) .empty .empty)
                        .empty))
                    (.node 30709518426727842612392937 (.basic (.groups [2801, 4651, 30941])) -- 3^2 * 13^14 * 61^2 * 97 * 7^4
                      (.node 29929441779057319089569901 (.basic (.groups [7, 31, 97, 523])) -- 3^2 * 13^14 * 61^5
                        (.node 29688297390688223814756957 (.basic (.split 86353)) .empty .empty)
                        .empty)
                      (.node 31815862126915788358628877 (.basic (.split 67)) -- 3^6 * 1093 * 547^4 * 431^2 * 7^4
                        (.node 31413142589845412254886937 (.basic (.groups [29, 1051, 4733])) .empty .empty)
                        .empty)))
                  (.node 39223137067384336112663253 (.basic (.groups [97, 151, 2801, 22996651])) -- 3^12 * 797161^2 * 61^2 * 13 * 7^4
                    (.node 35560998480566460029600241 (.basic (.groups [19, 31, 1123, 293459])) -- 3^6 * 1093^4 * 11^2 * 7^10
                      (.node 35262956709828281387635929 (.basic (.split 7)) -- 3^8 * 13^4 * 757^6
                        (.node 34103689293703772494899693 (.basic (.groups [127, 22079, 732541])) .empty .empty)
                        .empty)
                      (.node 38537259472142787260679957 (.basic (.split 2801)) -- 3^8 * 13 * 7^4 * 757^6
                        (.node 35890558990855221340908441 (.basic (.split 97)) .empty .empty)
                        .empty))
                    (.node 42851586647070142952933637 (.basic (.groups [5, 41, 3221, 30941])) -- 3^8 * 13^4 * 757 * 379^4 * 11^4
                      (.node 42692051960552212849415421 (.cut 5 31 60974822792938895861) -- 3^2 * 13^2 * 61^5 * 7^16
                        (.node 42078614525859082784213133 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 42966869912682718914827721 (.basic (.split 859)) .empty .empty)))))
              (.node 91689286279822751668271841 (.basic (.groups [13, 732541, 1141081, 5336717])) -- 3^10 * 23^6 * 29^4 * 3851^2
                (.node 78296947468326299098086129 (.basic (.groups [7, 19, 31])) -- 3^8 * 13^2 * 61^2 * 97^4 * 11^8
                  (.node 51246452652237800824699413 (.basic (.split 29)) -- 3^6 * 1093 * 547^6 * 7^4
                    (.node 48488779286576756177608089 (.basic (.groups [151, 281, 337])) -- 3^10 * 23^2 * 7^2 * 19^4 * 79^6
                      (.node 47678632547456734421510133 (.basic (.groups [5, 131, 787, 21491])) -- 3^8 * 13^6 * 757 * 379^2 * 61^4
                        (.node 47479173212104879215906117 (.basic (.groups [5, 101, 757, 70841])) .empty .empty)
                        .empty)
                      (.node 48893405875550173190789613 (.basic (.groups [19, 31, 613, 1301, 1601])) -- 3^6 * 1093 * 547^2 * 163^4 * 11^2 * 7^4
                        (.node 48631613762950181552245293 (.basic (.groups [157, 1123, 293459])) .empty .empty)
                        .empty))
                    (.node 59850563168221935198725493 (.basic (.groups [7, 19, 41, 5229043])) -- 3^8 * 13^6 * 757 * 379^4 * 11^2
                      (.node 53275422601417682388623589 (.basic (.groups [757, 42407, 2426789])) -- 3^8 * 13^2 * 61 * 31^12
                        (.node 51398967226314039876423009 (.basic (.groups [11, 419, 859, 18041])) .empty .empty)
                        .empty)
                      (.node 70230015253720703395702701 (.basic (.groups [5, 11, 331, 2521, 17351])) -- 3^2 * 13^2 * 61 * 31^14
                        (.node 61380755521895864528191809 (.basic (.groups [419, 859, 2801, 18041])) .empty .empty)
                        .empty)))
                  (.node 86544337547308356881514909 (.basic (.split 5)) -- 3^6 * 1093^6 * 7^4 * 29
                    (.node 83060665935475113466400853 (.basic (.split 127)) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^2
                      (.node 81414569725383580193491893 (.basic (.groups [71, 701, 1063])) -- 3^2 * 13 * 7^8 * 19^6 * 37^6
                        (.node 81134434533404545239232377 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 85853468014082340942110949 (.basic (.groups [5, 11, 31, 131, 21491])) -- 3^2 * 13^8 * 61^9
                        (.node 85482640292811815039264109 (.basic (.split 757)) .empty .empty)
                        .empty))
                    (.node 89898949438505418366719109 (.basic (.groups [31, 97, 523, 4733])) -- 3^2 * 13^2 * 61^5 * 7^6 * 29^6
                      (.node 88359449280721059893836293 (.basic (.split 1723)) -- 3^2 * 13 * 7^10 * 1123^4 * 41^2
                        (.node 87674648198026567954027437 (.basic (.groups [19, 67, 613])) .empty .empty)
                        .empty)
                      (.node 90856912478575876302870225 (.basic (.split 31)) .empty .empty))))
                (.node 134777051962170131995113789 (.basic (.groups [5, 264031, 1803647, 778986167])) -- 3^2 * 13^12 * 53^6 * 29
                  (.node 113782929112336087276173081 (.basic (.groups [43, 397, 2801])) -- 3^10 * 23^2 * 7^4 * 79^8
                    (.node 107377120580975410316459841 (.basic (.split 3169)) -- 3^8 * 13^8 * 61^2 * 97^2 * 757^2
                      (.node 102104865986614943025665637 (.basic (.groups [37, 757, 2179, 5419])) -- 3^8 * 13 * 7^2 * 19^2 * 127^8
                        (.node 97118104087710225861136173 (.basic (.groups [29, 67, 151, 613])) .empty .empty)
                        .empty)
                      (.node 112420059172017151815468117 (.basic (.split 631)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^4
                        (.node 109014200970283693023391881 (.basic (.groups [43, 191, 2521, 30941])) .empty .empty)
                        .empty))
                    (.node 121047035298542430121086669 (.basic (.split 17)) -- 3^4 * 11^12 * 1093^2 * 398581
                      (.node 120561207642843432994353357 (.basic (.split 787)) -- 3^8 * 13^6 * 757 * 379^2 * 61^2 * 97^2
                        (.node 116897841466486011177410025 (.basic (.groups [31, 131, 151, 21491, 22996651])) .empty .empty)
                        .empty)
                      (.node 129907743821650939061239569 (.basic (.groups [419, 859, 18041, 732541])) .empty .empty)))
                  (.node 168808680021882765041023149 (.basic (.split 617)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2
                    (.node 147242546309904846702305625 (.basic (.split 11)) -- 3^2 * 13^4 * 30941^4 * 5^4
                      (.node 146230087579934809903249329 (.basic (.split 29)) -- 3^6 * 1093^6 * 7^6
                        (.node 135661518749961528238886517 (.basic (.split 71)) .empty .empty)
                        .empty)
                      (.node 165396947470908666843434013 (.basic (.groups [23, 61, 157])) -- 3^2 * 13^5 * 7^6 * 29^10
                        (.node 152259503834528463809530809 (.basic (.groups [5, 191, 2521, 3221])) .empty .empty)
                        .empty))
                    (.node 199902279743835155382579489 (.basic (.groups [61, 292561, 1141081])) -- 3^10 * 23^4 * 3851^2 * 13^8
                      (.node 173699181710944613876953125 (.basic (.groups [11, 31, 131])) -- 3^2 * 13^2 * 61^9 * 5^10
                        (.node 171015390956097245889538857 (.basic (.groups [7, 67, 139])) .empty .empty)
                        .empty)
                      (.node 204248748355093470489770673 (.cut 5 101 354459143281) .empty .empty)))))))))
      (.node 4221283387030964569825396742709 (.basic (.split 617)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^4 * 151^2 * 7^2
        (.node 26533182271394840803264623393 (.basic (.split 43)) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2 * 37^6
          (.node 2614469893089888107919178053 (.basic (.split 37)) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2 * 787^2
            (.node 1049328428018177475628230069 (.cut 5 13 2165497125429542929) -- 3^10 * 23^6 * 29^2 * 13^2 * 61^5
              (.node 446289676675851093633038673 (.cut 5 31 10716778421192887) -- 3^8 * 13^4 * 757^2 * 14713 * 7^10
                (.node 315546832273083829954514433 (.basic (.groups [11, 191, 2521, 2801])) -- 3^8 * 13^2 * 61^2 * 97 * 7^4 * 757^4
                  (.node 278445524564494236852816381 (.cut 5 7 119322938533162382593) -- 3^8 * 13^8 * 61 * 31^8
                    (.node 234398494445236726478878053 (.basic (.split 67)) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2 * 19^2
                      (.node 216560219794615158527096109 (.basic (.split 191)) -- 3^10 * 23^4 * 3851^2 * 13^4 * 30941
                        (.node 211250374150560319429795017 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 246273152184304341355180701 (.basic (.split 31)) -- 3^2 * 13^2 * 61^13
                        (.node 236566504279280488348312641 (.basic (.groups [2801, 55897, 264031, 1803647])) .empty .empty)
                        .empty))
                    (.node 298145920626376545475364733 (.basic (.groups [31, 43, 613, 1301, 1601])) -- 3^6 * 1093 * 547^2 * 163^4 * 11^6
                      (.node 298092181839627467680629669 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2
                        (.node 285230733178225867272880461 (.basic (.groups [7, 13, 31, 97, 151])) .empty .empty)
                        .empty)
                      (.node 310946933472924036296512413 (.basic (.groups [11, 31, 157])) -- 3^2 * 13^5 * 7^10 * 61^2 * 97^4
                        (.node 309001118553947645620116777 (.basic (.split 29)) .empty .empty)
                        .empty)))
                  (.node 387679992360632707051500093 (.cut 5 31 482712101503812128791) -- 3^8 * 13 * 7^12 * 757^4
                    (.node 367059189446473198375249029 (.basic (.groups [23, 397, 617, 1609669])) -- 3^2 * 13^8 * 61 * 31^10
                      (.node 363552442504901911392290721 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^2 * 1621^2
                        (.node 362808863624629411842827601 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 382233129020330234700138813 (.basic (.split 43)) -- 3^2 * 13 * 7^2 * 19^10 * 104281^2
                        (.node 377550396070568287708499757 (.basic (.split 29)) .empty .empty)
                        .empty))
                    (.node 417355582296373867512788409 (.basic (.split 89)) -- 3^2 * 13^2 * 61^2 * 97^10
                      (.node 396877032516771428924489733 (.basic (.groups [157, 701, 70841, 52379047267])) -- 3^2 * 13^5 * 7^2 * 19^6 * 61^6
                        (.node 387948306759123468434963445 (.basic (.groups [127, 757, 21491, 189967])) .empty .empty)
                        .empty)
                      (.node 420411499048685363288186637 (.basic (.split 7)) .empty .empty))))
                (.node 699799549275777882767638149 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581 * 17^10
                  (.node 596962099257925147707777453 (.basic (.split 109912203092239643840221)) -- 3^2 * 13 * 7^2 * 19^18
                    (.node 481646874496562196736928913 (.basic (.split 7)) -- 3^8 * 13^2 * 61^6 * 757^2 * 14713
                      (.node 466577266881117877431809733 (.basic (.groups [7, 97, 151, 157])) -- 3^12 * 797161^2 * 61^2 * 13^5
                        (.node 451392418507193286973400781 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 573425462012410744166071161 (.basic (.groups [5, 131, 21491, 292561])) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^4
                        (.node 535478227857702135135008649 (.basic (.groups [19, 31, 2801, 1772893])) .empty .empty)
                        .empty))
                    (.node 637602160297516670086262901 (.basic (.split 5)) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29
                      (.node 608842440577669089756176901 (.basic (.split 5)) -- 3^2 * 13^8 * 61^6 * 1609669
                        (.node 606334947201627168472459317 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 674039030360396233373909289 (.basic (.groups [11, 443, 10332211, 15798461357509])) -- 3^2 * 13^16 * 103^4
                        (.node 665133695524479846339451413 (.basic (.split 39103)) .empty .empty)
                        .empty)))
                  (.node 938404888217757437240832849 (.basic (.split 433)) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^4
                    (.node 736212731549524233511528125 (.basic (.split 7)) -- 3^2 * 13^4 * 30941^4 * 5^5
                      (.node 722014788331735659919549521 (.basic (.groups [127, 757, 3169, 903870199])) -- 3^8 * 13^2 * 61^8 * 19^2 * 97^2
                        (.node 715502766850273296650411397 (.basic (.groups [67, 613, 701, 2801])) .empty .empty)
                        .empty)
                      (.node 874144073662822891623243501 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581 * 17^8 * 19^2
                        (.node 819744869830699498570028001 (.basic (.groups [5, 43, 17351, 45319, 262321])) .empty .empty)
                        .empty))
                    (.node 1023325647544887497223779457 (.basic (.split 732541)) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^2
                      (.node 1009395425346360159960578817 (.basic (.split 19)) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97 * 7^2
                        (.node 946904161789195015141506177 (.basic (.split 17)) .empty .empty)
                        .empty)
                      (.node 1026019314463377484373752161 (.basic (.groups [19, 97, 757])) .empty .empty)))))
              (.node 1727884878781585787994160521 (.basic (.split 19)) -- 3^8 * 13^4 * 757^6 * 7^2
                (.node 1484871336749836723780966329 (.basic (.split 56773)) -- 3^6 * 1093^8
                  (.node 1150214802419788633250166717 (.basic (.split 19)) -- 3^2 * 13^4 * 30941^2 * 157^5 * 7^2
                    (.node 1091923912084010601647027349 (.basic (.split 151)) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^4
                      (.node 1070452785179532827727888597 (.basic (.split 433)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4 * 43^2
                        (.node 1049776282302287034215616597 (.basic (.split 787)) .empty .empty)
                        .empty)
                      (.node 1121289200740359280829030013 (.cut 5 31 29186797351426543847) -- 3^8 * 13^5 * 7^4 * 61^8
                        (.node 1096967661932415787863265449 (.basic (.split 5)) .empty .empty)
                        .empty))
                    (.node 1363960319246809090638674301 (.basic (.split 617)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^6
                      (.node 1357788612672751985624653209 (.basic (.groups [409, 701, 70841])) -- 3^2 * 13^12 * 53^2 * 7^2 * 19^6
                        (.node 1237650590255518636972389693 (.basic (.groups [7, 19, 67, 379, 3511])) .empty .empty)
                        .empty)
                      (.node 1449975859197735203401925169 (.basic (.split 3169)) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^2 * 97^2
                        (.node 1418180738125328678804925609 (.basic (.split 127)) .empty .empty)
                        .empty)))
                  (.node 1572490545793916797112591241 (.basic (.groups [31, 1093, 262321, 3158528101])) -- 3^2 * 13^2 * 61^2 * 97^4 * 11^12
                    (.node 1539745448917582561366057437 (.basic (.split 43)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^2 * 19^4
                      (.node 1539243986902425200489459913 (.cut 5 31 216152328234883) -- 3^8 * 13^6 * 757^2 * 14713 * 7^8
                        (.node 1504766402909664288007253913 (.cut 5 31 110320050835925113) .empty .empty)
                        .empty)
                      (.node 1558977244218873629572814973 (.basic (.groups [29, 67, 397, 4733, 208097431])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^6
                        (.node 1542512774006324411568569721 (.basic (.groups [7, 19, 191, 2521, 3169])) .empty .empty)
                        .empty))
                    (.node 1703770502588574677233776549 (.basic (.groups [127, 307, 523, 617, 29989])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^8
                      (.node 1702201866541051881075785649 (.basic (.groups [5, 43, 17351, 45319, 4189129561])) -- 3^6 * 1093^4 * 11^6 * 31^4
                        (.node 1620561156024178153360646253 (.basic (.groups [4733, 292561, 18944890940537])) .empty .empty)
                        .empty)
                      (.node 1705036299646498946467771977 (.basic (.groups [151, 911, 1051])) .empty .empty))))
                (.node 2257875777477347705151805653 (.basic (.split 127)) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^2 * 67^4
                  (.node 1918445383649036515873962141 (.basic (.groups [4651, 30941, 161971])) -- 3^2 * 13^14 * 61 * 31^6
                    (.node 1825695948522496464463763961 (.basic (.groups [4651, 30941, 161971, 52379047267])) -- 3^2 * 13^14 * 61^6
                      (.node 1784496146268140548700354289 (.basic (.groups [19, 3851, 11503])) -- 3^10 * 23^2 * 7^4 * 79^4 * 2801 * 467^2
                        (.node 1742488925547756541450411809 (.basic (.groups [19, 31, 4189129561])) .empty .empty)
                        .empty)
                      (.node 1866763510350869761491862089 (.basic (.split 37)) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^2
                        (.node 1846642389445591765743839841 (.basic (.split 911)) .empty .empty)
                        .empty))
                    (.node 2189041326170300972236538529 (.basic (.split 5)) -- 3^2 * 13^4 * 30941^2 * 157^4 * 11^4
                      (.node 1998190944052998684003594801 (.basic (.split 151)) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97^2
                        (.node 1921933716301832469520499397 (.basic (.groups [29, 97, 151])) .empty .empty)
                        .empty)
                      (.node 2208855287870091958794428853 (.basic (.groups [7, 19, 67, 613])) .empty .empty)))
                  (.node 2395776887901958486348691037 (.basic (.groups [19, 29, 31, 613])) -- 3^6 * 1093 * 547^2 * 163^4 * 11^2 * 7^6
                    (.node 2330650432020847280266657917 (.basic (.groups [11, 191, 2521])) -- 3^8 * 13 * 7^6 * 29^4 * 757^4
                      (.node 2271422811964396907571755625 (.basic (.groups [11, 71, 292561, 2289401])) -- 3^10 * 23^4 * 3851^4 * 5^4
                        (.node 2259052652260785207216681837 (.basic (.split 23)) .empty .empty)
                        .empty)
                      (.node 2382949074384558896060019357 (.cut 5 31 132794631124378405180519) -- 3^2 * 13^5 * 7^12 * 61^6
                        (.node 2333104780149719945118728901 (.basic (.groups [5, 11, 17351])) .empty .empty)
                        .empty))
                    (.node 2511076179959652240410271237 (.basic (.split 29)) -- 3^6 * 1093 * 547^6 * 7^6
                      (.node 2509785788871942349563932361 (.basic (.split 13)) -- 3^6 * 1093^6 * 7^4 * 29^2
                        (.node 2461535345505207730648587597 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 2598729636669857019973533357 (.cut 5 7 1917587487414548733707) .empty .empty))))))
            (.node 10330626320552511916476339897 (.basic (.groups [11, 31, 2801, 3931, 22291])) -- 3^2 * 13^2 * 61^2 * 97^9 * 7^4
              (.node 5237061548859022797468767889 (.basic (.split 199)) -- 3^2 * 13^8 * 61^10
                (.node 3685382122038914600413799481 (.basic (.split 433)) -- 3^2 * 13^4 * 30941^2 * 157^6
                  (.node 3237835933055678756584948893 (.basic (.groups [5, 131, 157])) -- 3^2 * 13^5 * 7^6 * 29^6 * 61^4
                    (.node 2943166031841932210621749689 (.basic (.split 757)) -- 3^8 * 13^2 * 61^12
                      (.node 2931043922259167960218948689 (.basic (.groups [43, 131, 5581])) -- 3^2 * 13^12 * 53^4 * 11^6
                        (.node 2922446036662150279435250625 (.basic (.groups [11, 71, 131, 151])) .empty .empty)
                        .empty)
                      (.node 3136620819526356179554873713 (.basic (.groups [7, 11, 31, 757])) -- 3^8 * 13^2 * 61^2 * 97^9
                        (.node 3029368322267713923364367721 (.basic (.split 151)) .empty .empty)
                        .empty))
                    (.node 3481384222112956470068118777 (.basic (.groups [7, 151, 30941, 22996651])) -- 3^12 * 797161^2 * 61^2 * 13^4 * 97
                      (.node 3275100157371909394494409641 (.basic (.split 331)) -- 3^6 * 1093^4 * 11^6 * 31^2 * 43^2
                        (.node 3265279772621664706585448409 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 3681063657747621167557640625 (.basic (.split 11)) -- 3^2 * 13^4 * 30941^4 * 5^6
                        (.node 3642118959599917867898613513 (.basic (.groups [701, 1051, 30941])) .empty .empty)
                        .empty)))
                  (.node 4190193058554019106648999577 (.basic (.split 2801)) -- 3^8 * 13^4 * 757^2 * 14713 * 7^4 * 1051^2
                    (.node 3893016432421714018676790717 (.cut 5 31 28460638261269736067281) -- 3^2 * 13^13 * 7^4 * 29^6
                      (.node 3767324570827877232775947501 (.basic (.groups [5, 67, 271])) -- 3^2 * 13^10 * 23^6 * 29^5
                        (.node 3766015073877627113095493421 (.basic (.groups [5, 757, 37861])) .empty .empty)
                        .empty)
                      (.node 4078132072128162890377805997 (.basic (.groups [11, 191, 911, 1093])) -- 3^8 * 13 * 7^2 * 19^4 * 151^2 * 757^4
                        (.node 3908534506902933827858299881 (.basic (.groups [67, 264031, 1803647, 778986167])) .empty .empty)
                        .empty))
                    (.node 4885534801783044025325660133 (.basic (.split 11)) -- 3^2 * 13 * 7^6 * 29^4 * 4733^4
                      (.node 4342479542773615346923828125 (.cut 7 257 8122159051268690581) -- 3^2 * 13^2 * 61^9 * 5^12
                        (.node 4296057761703301829747344413 (.cut 5 13 205819715373429431) .empty .empty)
                        .empty)
                      (.node 5185041984295487297304970077 (.basic (.groups [41, 43, 30941])) .empty .empty))))
                (.node 6625822830390218721626658045 (.basic (.split 769)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2
                  (.node 5872278899203840335486658293 (.cut 5 13 140084898561947735646683) -- 3^2 * 13 * 7^18 * 419^4
                    (.node 5598797372941577191829204049 (.basic (.groups [3851, 39449441, 262209281])) -- 3^10 * 23^2 * 7^2 * 19^2 * 79^4 * 127^4
                      (.node 5484838309662078939316327245 (.basic (.split 11)) -- 3^2 * 13^6 * 5229043^2 * 31^4 * 5
                        (.node 5271357119039768573281602333 (.basic (.groups [67, 127, 523, 613])) .empty .empty)
                        .empty)
                      (.node 5734064803081172256034088841 (.basic (.split 45319)) -- 3^4 * 11^6 * 43^12
                        (.node 5723343094588308482804966637 (.basic (.groups [157, 199, 859, 2801])) .empty .empty)
                        .empty))
                    (.node 6065504469454532406613526529 (.basic (.groups [97, 151, 5229043, 22996651])) -- 3^12 * 797161^2 * 61^2 * 13^6
                      (.node 6060205610823340560019024953 (.basic (.split 331)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4 * 31^2
                        (.node 5959439683960979554510472001 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 6621709329206060106421928205 (.basic (.split 7)) -- 3^4 * 11^4 * 5 * 3221^6
                        (.node 6386255664982682276950223517 (.basic (.split 163)) .empty .empty)
                        .empty)))
                  (.node 9040203349000964049863029437 (.basic (.split 7)) -- 3^6 * 1093^5 * 547^2 * 163^2
                    (.node 7241918143354854159045784653 (.basic (.groups [5, 41, 3221])) -- 3^8 * 13^6 * 757 * 379^4 * 11^4
                      (.node 7165274291416805685259217121 (.basic (.groups [19, 29, 37, 1063, 14939])) -- 3^6 * 1093^6 * 7^8
                        (.node 6712191732020792077182667077 (.basic (.groups [11, 31, 787, 30941])) .empty .empty)
                        .empty)
                      (.node 7937047581634604065556583009 (.basic (.split 29)) -- 3^6 * 1093^6 * 7^2 * 19^4
                        (.node 7350125986839030848511202053 (.basic (.split 1499)) .empty .empty)
                        .empty))
                    (.node 9421159861844107672479800589 (.basic (.split 307)) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^4
                      (.node 9391756204298867535624422493 (.basic (.split 281)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^6
                        (.node 9132484077219914734996444005 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 10000392095884804223230482849 (.basic (.groups [97, 701, 757])) .empty .empty)))))
              (.node 17087173964660132585212800609 (.basic (.groups [37, 4933, 5839, 45319])) -- 3^4 * 11^6 * 43^6 * 7^4 * 2801^2
                (.node 13899868786513885887897991533 (.basic (.groups [5, 131, 157])) -- 3^2 * 13^5 * 7^2 * 19^10 * 61^4
                  (.node 11673364561048304998159308201 (.basic (.groups [11, 31, 4651, 30941])) -- 3^2 * 13^14 * 61^2 * 97^4
                    (.node 10701470741700471469632166401 (.basic (.groups [31, 859, 18041, 292561, 996625831])) -- 3^2 * 13^10 * 23^4 * 419^4
                      (.node 10597940577940114892133792333 (.basic (.split 43)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^10
                        (.node 10351268333377455652059955833 (.basic (.groups [31, 733, 2801, 45319])) .empty .empty)
                        .empty)
                      (.node 11357114059821984537858778125 (.basic (.groups [7, 31, 292561])) -- 3^10 * 23^4 * 3851^4 * 5^5
                        (.node 11257527162423057932508484509 (.basic (.groups [29, 397, 617, 5336717])) .empty .empty)
                        .empty))
                    (.node 12554938851528349511643658761 (.basic (.groups [37, 3851, 4933])) -- 3^10 * 23^2 * 7^4 * 79^2 * 43^4 * 2801^2
                      (.node 12468610205410255481515347729 (.basic (.groups [7, 3571, 28099, 15798461357509])) -- 3^2 * 13^16 * 103^2 * 443^2
                        (.node 11749533945254791182623329281 (.basic (.groups [757, 967, 3500201, 20241187])) .empty .empty)
                        .empty)
                      (.node 13190718317404326855830417601 (.basic (.groups [7, 19, 191])) -- 3^8 * 13^4 * 757^4 * 11^8
                        (.node 13054784102128824164630159769 (.basic (.groups [7, 37, 163, 307])) .empty .empty)
                        .empty)))
                  (.node 15236399740173277778529108237 (.cut 5 31 20616629925738815107) -- 3^2 * 13^5 * 7^12 * 61^2 * 97^4
                    (.node 14612230183310751397176253125 (.basic (.groups [7, 31, 131])) -- 3^12 * 797161^2 * 61^4 * 5^5
                      (.node 14606516910141745916350853781 (.basic (.split 307)) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2 * 7^2
                        (.node 14325787760880119682821159133 (.basic (.groups [157, 4733, 732541])) .empty .empty)
                        .empty)
                      (.node 15221061014441727243904422525 (.basic (.split 31)) -- 3^2 * 13^8 * 61^6 * 1609669 * 5^2
                        (.node 15022662283242564822666022761 (.basic (.split 5)) .empty .empty)
                        .empty))
                    (.node 16747662348666155700806776929 (.basic (.split 7)) -- 3^4 * 11^6 * 43^2 * 631^6
                      (.node 16588492922741432851285269129 (.basic (.groups [43, 757, 967])) -- 3^8 * 13^8 * 61^2 * 97^6
                        (.node 16251110021939257224637056729 (.basic (.split 5419)) .empty .empty)
                        .empty)
                      (.node 16771901195780512755043414617 (.basic (.split 31)) .empty .empty))))
                (.node 19712434278113057105748613269 (.basic (.groups [11, 191, 2521, 62081])) -- 3^8 * 13^2 * 61 * 31^6 * 757^4
                  (.node 18490462648627983432501624129 (.basic (.split 13)) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^2
                    (.node 18128799047565853562101015557 (.cut 5 101 6515850210450947621) -- 3^8 * 13^5 * 7^4 * 61^2 * 97^6
                      (.node 17814069682740193658222245329 (.basic (.split 13)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2
                        (.node 17399074723871777903645708121 (.basic (.split 151)) .empty .empty)
                        .empty)
                      (.node 18423399963977944120953227889 (.basic (.groups [43, 191, 2521])) -- 3^8 * 13^6 * 757^4 * 11^6
                        (.node 18282986611647807182972767101 (.basic (.split 151)) .empty .empty)
                        .empty))
                    (.node 19190823740789111831985950529 (.cut 5 101 26143014359764824396361) -- 3^10 * 23^12 * 3851^2
                      (.node 19118945509918517684544032637 (.basic (.groups [43, 4733, 18944890940537])) -- 3^2 * 13 * 7^6 * 29^10 * 23^2 * 79^2
                        (.node 18759414108841192841561909649 (.basic (.groups [11, 191, 2521, 62081, 52379047267])) .empty .empty)
                        .empty)
                      (.node 19332517241476182000021290253 (.basic (.split 71)) .empty .empty)))
                  (.node 23857376324750334395802358677 (.basic (.groups [43, 67, 433, 4733, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^6 * 29^2
                    (.node 22118228506852471061696638269 (.basic (.groups [19, 331, 1093, 22996651])) -- 3^12 * 797161^2 * 61 * 31^2 * 151^2 * 7^2
                      (.node 20600163453385582801121145213 (.basic (.groups [19, 43, 30941, 9872250674161])) -- 3^8 * 13^4 * 757 * 379^6 * 7^2
                        (.node 20374844091640540176045717333 (.basic (.groups [787, 3169, 1609669])) .empty .empty)
                        .empty)
                      (.node 23684810088133398549319085853 (.basic (.groups [127, 331, 613, 2801])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2 * 67^2 * 31^2
                        (.node 23600696850331547640109516737 (.basic (.split 19)) .empty .empty)
                        .empty))
                    (.node 25933337698259667628335668769 (.basic (.groups [331, 15797, 1806113, 4189129561])) -- 3^6 * 1093^4 * 11^10 * 31^2
                      (.node 24875207265170775900444964533 (.basic (.split 431)) -- 3^4 * 11^12 * 1093 * 547^4
                        (.node 24478576911148985854876694853 (.basic (.groups [379, 1153, 3169, 240813217])) .empty .empty)
                        .empty)
                      (.node 26238433165027404621615423801 (.basic (.groups [19, 29, 31])) .empty .empty)))))))
          (.node 375566557081064120566650569025 (.basic (.groups [31, 97, 131, 21491, 188565401138641])) -- 3^2 * 13^2 * 61^14 * 5^2
            (.node 123042732818022959780103290613 (.basic (.groups [19, 29, 37, 1063])) -- 3^6 * 1093 * 547^6 * 7^8
              (.node 60011248004332776919815255117 (.basic (.groups [37, 43, 4933])) -- 3^10 * 23^4 * 3851^2 * 13 * 7^4 * 2801^2
                (.node 37947091863062085753259834533 (.basic (.groups [16651, 125731, 2767631689])) -- 3^2 * 13 * 7^16 * 14009^2 * 223^2
                  (.node 32004544849933538753875832373 (.basic (.split 70841)) -- 3^2 * 13 * 7^2 * 19^6 * 701^6
                    (.node 29800944121777927155926660961 (.basic (.split 7)) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^6
                      (.node 27190053662720127094627771761 (.basic (.groups [419, 859, 18041])) -- 3^2 * 13^10 * 23^12
                        (.node 27172452448478544144045763473 (.basic (.groups [23, 4733, 18944890940537])) .empty .empty)
                        .empty)
                      (.node 31322848166345702088909408609 (.basic (.groups [757, 859, 13267, 4242586390571])) -- 3^8 * 13^2 * 61^10 * 199^2
                        (.node 29984900402706515961370707933 (.basic (.groups [151, 911, 365017, 1806113])) .empty .empty)
                        .empty))
                    (.node 34982593201278762304994047341 (.basic (.groups [19, 307, 617, 3158528101])) -- 3^4 * 11^12 * 1093^2 * 398581 * 17^2
                      (.node 34978953182757055394130340821 (.basic (.groups [7, 31, 97])) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^5
                        (.node 32627215255335250544331120693 (.basic (.split 67)) .empty .empty)
                        .empty)
                      (.node 36075656395791562002519132693 (.basic (.groups [7, 19, 31, 613])) -- 3^6 * 1093 * 547^2 * 163^4 * 11^8
                        (.node 35059635575663391535870158453 (.basic (.groups [29, 67, 613])) .empty .empty)
                        .empty)))
                  (.node 51197681119962392775467269029 (.cut 5 7 39473785172947616108827) -- 3^8 * 13^2 * 61 * 31^14
                    (.node 47229458495583379899395656053 (.cut 5 31 2915870274278058363040457) -- 3^2 * 13^5 * 7^2 * 19^16
                      (.node 44978166747493381721929429521 (.basic (.split 13537)) -- 3^2 * 13^10 * 23^4 * 419^2 * 859^2
                        (.node 43098266680531990493572206333 (.basic (.split 13)) .empty .empty)
                        .empty)
                      (.node 49460375841971647838068362033 (.basic (.groups [151, 2801, 22996651])) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97 * 7^4
                        (.node 48785708526324119096855690061 (.basic (.split 617)) .empty .empty)
                        .empty))
                    (.node 56360525318569643029258169133 (.basic (.groups [79, 433, 2801, 3499, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^5 * 7^4
                      (.node 55052073644921898693257407509 (.basic (.split 43)) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^2
                        (.node 52706987244067838540890927077 (.basic (.split 631)) .empty .empty)
                        .empty)
                      (.node 56785570299109922689293890625 (.basic (.groups [19531, 292561, 2289401])) .empty .empty))))
                (.node 86148640551652338159701974341 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^4 * 151^2
                  (.node 71049543339227826395703541653 (.basic (.groups [7, 43, 5229043, 9872250674161])) -- 3^8 * 13^6 * 757 * 379^6
                    (.node 67491044658825595963270295661 (.basic (.split 751670559138758105956097)) -- 3^2 * 13^2 * 61 * 31^16
                      (.node 66289508573436329293785764637 (.basic (.groups [113, 3823, 293147, 293459, 15852481])) -- 3^2 * 13 * 7^10 * 1123^6
                        (.node 61538383637630193266214689925 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 69070249882982181175198897293 (.basic (.split 19)) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^2 * 37
                        (.node 68111249174465580124044545997 (.basic (.groups [43, 433, 1123, 14083])) .empty .empty)
                        .empty))
                    (.node 76389884966724807849067933677 (.basic (.groups [19, 37, 67, 397])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^8
                      (.node 73366528611396887385167577357 (.basic (.groups [7, 19, 41, 3169])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^4 * 11^2
                        (.node 73061150916553756985881265625 (.basic (.groups [131, 151, 19531])) .empty .empty)
                        .empty)
                      (.node 84666359060297703611713865529 (.basic (.groups [2801, 30941, 878837, 30629717273])) -- 3^8 * 13^4 * 757^6 * 7^4
                        (.node 84617856494730458258874977133 (.basic (.groups [67, 151, 397, 911, 208097431])) .empty .empty)
                        .empty)))
                  (.node 110635913096390037552438476997 (.basic (.groups [127, 613, 761, 2801])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2 * 67^4
                    (.node 94174752098789791006504470453 (.cut 5 31 13247937315205207) -- 3^12 * 797161^2 * 61^2 * 13 * 7^8
                      (.node 92026591443690529188941015625 (.basic (.groups [11, 19, 31, 829, 69617111, 239371661])) -- 3^2 * 13^4 * 30941^4 * 5^8
                        (.node 91598025011938019706719531853 (.basic (.groups [11, 31, 157])) .empty .empty)
                        .empty)
                      (.node 109252412554008439750502477529 (.basic (.groups [7, 419, 859])) -- 3^2 * 13^10 * 23^6 * 29^6
                        (.node 101807000784795417682090676157 (.basic (.split 431)) .empty .empty)
                        .empty))
                    (.node 118801843043695187614545195333 (.basic (.split 7)) -- 3^6 * 1093 * 547^2 * 163^8
                      (.node 117393067507195965831085860813 (.basic (.groups [19, 31, 37])) -- 3^6 * 1093 * 547^2 * 163^4 * 11^2 * 7^8
                        (.node 111288936720006869917807794717 (.basic (.groups [97, 157, 4733])) .empty .empty)
                        .empty)
                      (.node 122979503654725175128632685689 (.basic (.groups [13, 67, 4733, 14939, 562731116179])) .empty .empty)))))
              (.node 231582905875622517556889189277 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13
                (.node 176848065886904799716240678601 (.basic (.split 7)) -- 3^12 * 797161 * 398581^2 * 1621^2
                  (.node 142821405087724973941885028853 (.basic (.split 31)) -- 3^6 * 1093 * 547^4 * 431^2 * 7^4 * 67^2
                    (.node 136295692981475151862768412277 (.basic (.split 29)) -- 3^6 * 1093 * 547^6 * 7^2 * 19^4
                      (.node 135348148669961102132808551169 (.basic (.split 5419)) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^2
                        (.node 130830904243895306658689308761 (.basic (.split 1806113)) .empty .empty)
                        .empty)
                      (.node 139098832823034188815328004933 (.cut 5 31 16610470461567623407861961) -- 3^2 * 13^5 * 7^6 * 29^12
                        (.node 137204675185520699282592036369 (.basic (.groups [5, 11, 41])) .empty .empty)
                        .empty))
                    (.node 148532234240892101681538808533 (.basic (.groups [5, 19571, 293459, 579281])) -- 3^2 * 13 * 7^10 * 1123^4 * 41^4
                      (.node 147511459615525348589049256821 (.basic (.split 31)) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2
                        (.node 147210725230827157274924909997 (.basic (.groups [757, 911, 1093])) .empty .empty)
                        .empty)
                      (.node 174883203535719892585626700173 (.basic (.groups [43, 3313, 86353, 162709])) -- 3^2 * 13 * 7^10 * 1123^2 * 127^6
                        (.node 158011110490170385391801747409 (.basic (.groups [14713, 1609669, 52379047267])) .empty .empty)
                        .empty)))
                  (.node 207864689409059713706800548333 (.basic (.split 761)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^4
                    (.node 186644045654765253799796936241 (.basic (.groups [5, 191, 2521, 3169])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^4 * 11^4
                      (.node 179533127942357864847926731029 (.basic (.groups [31, 757, 50689400581])) -- 3^8 * 13^2 * 61^13
                        (.node 177412191709086508782439204893 (.basic (.groups [787, 5229043, 52379047267])) .empty .empty)
                        .empty)
                      (.node 202242069740699808119847425061 (.basic (.groups [19, 617, 212057, 2919196853])) -- 3^6 * 1093^2 * 398581 * 17^12
                        (.node 190271356041063932450623540161 (.basic (.groups [5, 7, 19])) .empty .empty)
                        .empty))
                    (.node 215503317832110978322507660533 (.cut 5 31 13226101772099503808773267) -- 3^2 * 13 * 7^2 * 19^20
                      (.node 214604700345297830583979243281 (.basic (.split 5)) -- 3^12 * 797161^4
                        (.node 213223712401048474922414489001 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 230174379867403517901140907261 (.basic (.groups [5, 151, 911, 14939, 562731116179])) .empty .empty))))
                (.node 292012544514087998171013128049 (.basic (.groups [19, 878837, 5229043, 30629717273])) -- 3^8 * 13^6 * 757^6 * 7^2
                  (.node 259869940703869969966518209457 (.basic (.groups [31, 67, 4733, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^6 * 29^2
                    (.node 251147610636310525454774978157 (.basic (.groups [11, 31, 2801, 1793161])) -- 3^2 * 13^5 * 7^4 * 61^6 * 157^4
                      (.node 246638030389924463732136032793 (.basic (.groups [41, 19571, 293459, 1983851])) -- 3^2 * 13^2 * 61^2 * 97 * 7^10 * 1123^4
                        (.node 236668499249116472042328653661 (.basic (.split 331)) .empty .empty)
                        .empty)
                      (.node 258296498832948660090798514317 (.basic (.groups [67, 127, 523])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^8
                        (.node 252627637288555815679117371789 (.basic (.split 127)) .empty .empty)
                        .empty))
                    (.node 273655302757077359375895285153 (.basic (.split 307)) -- 3^4 * 11^10 * 15797^2 * 1806113 * 17^2
                      (.node 265990939456798612806610881501 (.basic (.groups [7, 5233, 292561])) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61 * 31^2 * 331^2
                        (.node 264874000466606417640621162009 (.basic (.groups [31, 43, 433, 14083, 45319, 1793161])) .empty .empty)
                        .empty)
                      (.node 282142441754172468416389576797 (.basic (.split 37)) .empty .empty)))
                  (.node 340278095121111075292861236129 (.basic (.groups [5, 317, 14713])) -- 3^8 * 13^8 * 61^2 * 97^2 * 757^2 * 3169
                    (.node 315566010592279063875990903861 (.basic (.groups [151, 307, 617, 911])) -- 3^6 * 1093^2 * 398581 * 17^8 * 19^4
                      (.node 304252219494056549416822750161 (.basic (.split 89)) -- 3^8 * 13^2 * 61^2 * 97^10
                        (.node 297824624882338285225819672893 (.basic (.groups [43, 523])) .empty .empty)
                        .empty)
                      (.node 337694269544956777596607521369 (.basic (.groups [151, 3169, 30941, 22996651])) -- 3^12 * 797161^2 * 61^2 * 13^4 * 97^2
                        (.node 317519883095347929962848295637 (.basic (.split 13)) .empty .empty)
                        .empty))
                    (.node 351098440279423478577701638929 (.basic (.groups [29, 1123, 14939, 293459])) -- 3^6 * 1093^6 * 7^10
                      (.node 348659317943268864780957324561 (.basic (.split 331)) -- 3^4 * 11^12 * 1093^4 * 31^2
                        (.node 346056869018557141383922117641 (.basic (.groups [19, 7699, 1141081])) .empty .empty)
                        .empty)
                      (.node 352743881058060743638614316869 (.basic (.groups [42407, 1609669, 2426789])) .empty .empty))))))
            (.node 1314804944415570350311399478193 (.basic (.groups [127, 523])) -- 3^8 * 13^4 * 757^2 * 14713 * 7^2 * 19^8
              (.node 623766441240152469465891948081 (.basic (.groups [127, 30941, 878837, 30629717273])) -- 3^8 * 13^4 * 757^6 * 7^2 * 19^2
                (.node 442969964101047238443288442413 (.basic (.split 19)) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^2
                  (.node 401216771481273287563106687805 (.basic (.groups [151, 17293, 21491, 22996651])) -- 3^12 * 797161^2 * 61^4 * 5 * 131^2
                    (.node 394184532262327827194576872989 (.basic (.groups [617, 701, 70841, 25646167])) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^6
                      (.node 383077295212152090520445079969 (.basic (.groups [281, 337, 419])) -- 3^2 * 13^10 * 23^2 * 7^4 * 79^6
                        (.node 380526525361043181097610563125 (.basic (.groups [11, 71, 160967, 52379047267])) .empty .empty)
                        .empty)
                      (.node 396550087941719947144210567893 (.basic (.groups [547, 398581, 1193557, 3158528101])) -- 3^4 * 11^12 * 1093^5
                        (.node 395098852487221429496839257489 (.basic (.groups [5, 7, 19])) .empty .empty)
                        .empty))
                    (.node 424153798319358257076304569009 (.basic (.groups [61, 67, 2801, 14939, 562731116179])) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13^2
                      (.node 422670391720483700939099611293 (.cut 5 101 722678364046928556123481) -- 3^2 * 13 * 7^8 * 19^4 * 37^10
                        (.node 406329316598288970325280623617 (.basic (.groups [7, 31, 1051, 1621, 5231])) .empty .empty)
                        .empty)
                      (.node 441845411932191090238341090957 (.basic (.groups [37, 151, 3169, 30941])) -- 3^8 * 13^4 * 757 * 379^2 * 61^2 * 97^2 * 787^2
                        (.node 432585737062380691150287465045 (.basic (.groups [11, 191, 2521, 17293])) .empty .empty)
                        .empty)))
                  (.node 507212148335495326950937835817 (.basic (.groups [29, 31, 733])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433 * 7^6
                    (.node 492389675248098081720561422661 (.basic (.groups [127, 523, 617, 29989])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^8
                      (.node 460132957218452645944705078125 (.basic (.groups [11, 71, 521, 69617111, 239371661])) -- 3^2 * 13^4 * 30941^4 * 5^9
                        (.node 444816249580250899597247107941 (.basic (.groups [43, 617, 701, 733, 70841])) .empty .empty)
                        .empty)
                      (.node 506200689707073083907340654953 (.basic (.groups [11, 29, 31, 3931])) -- 3^2 * 13^2 * 61^2 * 97^9 * 7^6
                        (.node 504653645623184994499636377213 (.basic (.split 631)) .empty .empty)
                        .empty))
                    (.node 615061151434475458481393334189 (.basic (.groups [307, 617, 104281, 62060021])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^10
                      (.node 555848107059247304653146734757 (.basic (.groups [43, 433, 701, 14083, 70841])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^2 * 19^6
                        (.node 511963246463243653048578144849 (.basic (.groups [151, 911, 3798019, 5229043])) .empty .empty)
                        .empty)
                      (.node 615518104172386119674865683697 (.basic (.groups [701, 1051])) .empty .empty))))
                (.node 872889414454269489252890021121 (.basic (.split 13)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4
                  (.node 741911685648028297133900381577 (.basic (.groups [31, 1123, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^10
                    (.node 692455873179958230461916706389 (.basic (.groups [5, 757, 3637])) -- 3^8 * 13^2 * 61 * 31^8 * 331^4
                      (.node 683869716018556063852226932197 (.basic (.split 211)) -- 3^2 * 13 * 7^4 * 2801^6 * 71^2
                        (.node 627390080099753962973901379317 (.cut 5 13 1960117187618310210857) .empty .empty)
                        .empty)
                      (.node 715719328596945549901191835269 (.basic (.groups [307, 617, 911, 2801])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2 * 7^4
                        (.node 708142626895629229023680928513 (.basic (.groups [2801, 368551, 5229043])) .empty .empty)
                        .empty))
                    (.node 820635455084641629339532069521 (.basic (.split 19)) -- 3^4 * 11^6 * 43^2 * 631^6 * 7^2
                      (.node 815093155669322521559801840733 (.basic (.groups [151, 613, 761, 911])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^4 * 67^4
                        (.node 787774819907302218125796908961 (.basic (.groups [43, 45319, 262321, 917087137])) .empty .empty)
                        .empty)
                      (.node 860616869585250385165198523337 (.basic (.split 22406023)) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^6 * 4733^2
                        (.node 857276851536790243127781867837 (.cut 5 101 478522967474897869338257) .empty .empty)
                        .empty)))
                  (.node 1073023501726489152919896216405 (.basic (.split 2671)) -- 3^12 * 797161^4 * 5
                    (.node 1009408009215893557254936115437 (.basic (.groups [43, 2801, 30941])) -- 3^8 * 13^4 * 757 * 379^6 * 7^4
                      (.node 892253934711140898708670908933 (.basic (.groups [11, 41, 45869891, 52379047267])) -- 3^8 * 13^2 * 61^6 * 757 * 379^4
                        (.node 876272095345937353244539943013 (.cut 5 13 19163840688089356153261) .empty .empty)
                        .empty)
                      (.node 1054185923117051572136598096489 (.basic (.split 4051)) -- 3^2 * 13^6 * 5229043^2 * 31^6
                        (.node 1025070255337815976717685983401 (.basic (.groups [97, 151, 1609669])) .empty .empty)
                        .empty))
                    (.node 1134360402711513861043870736013 (.basic (.groups [11, 31, 787])) -- 3^8 * 13^6 * 757 * 379^2 * 61^2 * 97^4
                      (.node 1093601964338644726334536747281 (.basic (.groups [701, 30941, 70841, 3798019])) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^6
                        (.node 1083793196835771082023135275181 (.basic (.groups [331, 1093, 2801])) .empty .empty)
                        .empty)
                      (.node 1156434145666245834365366320113 (.basic (.groups [1051, 2801, 52379047267])) .empty .empty)))))
              (.node 2530127736709893408363703304409 (.basic (.groups [307, 433, 757, 967])) -- 3^8 * 13^2 * 61^2 * 97^6 * 43^2 * 631^2
                (.node 1960077013329532562704259308197 (.cut 5 101 12451777027495169978519) -- 3^8 * 13 * 7^6 * 29^6 * 757^4
                  (.node 1633550040567644440835639949813 (.basic (.groups [11, 2221, 29251, 5278271])) -- 3^2 * 13 * 7^2 * 19^12 * 599^4
                    (.node 1595107382447487614687725936797 (.basic (.split 1717451)) -- 3^4 * 11^10 * 15797 * 2633^4
                      (.node 1538459590940754831655367248125 (.basic (.groups [11, 71, 191, 510101, 208097431])) -- 3^6 * 1093 * 547^4 * 431^4 * 5^4
                        (.node 1339685480873278105099579358037 (.basic (.split 5419)) .empty .empty)
                        .empty)
                      (.node 1622964371067571539092596197597 (.basic (.split 11)) -- 3^6 * 1093^9
                        (.node 1595770458842850021979175175273 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 1680230710929515486270843219733 (.basic (.split 7)) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2
                      (.node 1646849383498112416060961059173 (.basic (.groups [23, 757, 47834644354838156839])) -- 3^8 * 13 * 7^2 * 19^2 * 127^10
                        (.node 1635815993745950857713830008689 (.basic (.groups [43, 45319, 917087137, 4189129561])) .empty .empty)
                        .empty)
                      (.node 1902959919973356454954658442213 (.basic (.groups [67, 613, 104281])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^10
                        (.node 1701531015412148351746092579321 (.basic (.split 71)) .empty .empty)
                        .empty)))
                  (.node 2227976686104342683440664514573 (.basic (.groups [379, 187123, 14421466756460791])) -- 3^8 * 13^2 * 61^12 * 757
                    (.node 2111815067346067534185038110317 (.basic (.groups [13, 67, 4733, 132197305635599])) -- 3^6 * 1093 * 547^6 * 7^6 * 29^2
                      (.node 2110729848441303515983267115601 (.basic (.split 2801)) -- 3^6 * 1093^6 * 7^4 * 29^4
                        (.node 1979267199796956198468866015853 (.basic (.split 433)) .empty .empty)
                        .empty)
                      (.node 2133716144148180379041950790081 (.basic (.groups [292561, 1141081, 52379047267])) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^6
                        (.node 2131408061578340120268747825849 (.basic (.split 11)) .empty .empty)
                        .empty))
                    (.node 2423558416256610744065349739617 (.cut 5 101 16435315526633) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97 * 7^6
                      (.node 2300664786092263229723525390625 (.basic (.split 11)) -- 3^2 * 13^4 * 30941^4 * 5^10
                        (.node 2242113693723880867259098473861 (.cut 5 13 306156516620365753417) .empty .empty)
                        .empty)
                      (.node 2528060642625398051390026101021 (.basic (.groups [23, 97, 397])) .empty .empty))))
                (.node 3337451209548813426078182753853 (.basic (.groups [43, 433, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^12
                  (.node 2925699697046742257513885293917 (.cut 5 31 43546950609701764391603) -- 3^2 * 13^5 * 7^10 * 61^2 * 97^6
                    (.node 2722715200072947117346662370221 (.basic (.split 617)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^4
                      (.node 2710395340717467758706291156489 (.basic (.groups [409, 264031, 1803647])) -- 3^2 * 13^12 * 53^2 * 7^2 * 19^2 * 127^4
                        (.node 2660416624720574721208724302773 (.cut 5 7 156590015226068236134157) .empty .empty)
                        .empty)
                      (.node 2865274176970092067665926466249 (.basic (.groups [29, 701, 14939, 70841, 562731116179])) -- 3^6 * 1093^6 * 7^2 * 19^6
                        (.node 2761665740609912508433650287517 (.basic (.groups [29, 79, 433, 3499, 4733])) .empty .empty)
                        .empty))
                    (.node 3287077520305367349228830199921 (.basic (.groups [264031, 732541, 1803647])) -- 3^2 * 13^12 * 53^6 * 29^4
                      (.node 3137933861489419783028615921049 (.basic (.groups [331, 3158528101, 4189129561])) -- 3^6 * 1093^4 * 11^12 * 31^2
                        (.node 3010577776383092728239559460601 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 3305873567369577404568796987689 (.basic (.split 8011)) .empty .empty)))
                  (.node 3847330687534232059734273586197 (.basic (.split 37)) -- 3^8 * 13^2 * 61^6 * 757 * 379^2 * 787^2
                    (.node 3579209283640056819741354754557 (.basic (.groups [7, 67, 151, 3169])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2 * 787^2 * 37^2
                      (.node 3444625943696244672787857801093 (.cut 5 31 1226717151355122716161741613) -- 3^2 * 13 * 7^6 * 29^16
                        (.node 3354040829002525023978695151189 (.basic (.groups [617, 1699, 292561, 150332843])) .empty .empty)
                        .empty)
                      (.node 3743104363369515584604328750173 (.basic (.groups [67, 397, 1123])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^10
                        (.node 3580498772247873888310975158537 (.cut 5 31 77598893275393957) .empty .empty)
                        .empty))
                    (.node 4108734768299540025298880171853 (.basic (.groups [11, 41, 101, 88009573, 11018941331])) -- 3^2 * 13 * 7^6 * 29^6 * 4733^4
                      (.node 3926898673826581719427826140281 (.basic (.split 53)) -- 3^2 * 13^2 * 61^2 * 97^12
                        (.node 3906217546446810054316309357437 (.basic (.groups [19, 97, 787])) .empty .empty)
                        .empty)
                      (.node 4148651593954587476973979410921 (.basic (.groups [29, 4733, 30941])) .empty .empty))))))))
        (.node 267034221683187609098755416630717 (.basic (.split 127)) -- 3^6 * 1093 * 547^6 * 7^2 * 19^2 * 29^4
          (.node 48985741537155517796435258398341 (.basic (.split 14713)) -- 3^8 * 13^2 * 61 * 31^2 * 331^6 * 757^2
            (.node 14099069764107670418991294427629 (.basic (.groups [307, 617, 5419, 1270657])) -- 3^6 * 1093^2 * 398581 * 17^8 * 19^2 * 127^2
              (.node 7150880073093443639863803647001 (.cut 5 101 4098477667972992590313149) -- 3^2 * 13^16 * 103^6
                (.node 5823857592001230278178282979833 (.basic (.groups [5, 11, 2801, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4 * 31^4
                  (.node 5147950300638325439385123300681 (.basic (.groups [13, 5419, 1141081])) -- 3^10 * 23^2 * 7^2 * 19^2 * 79^4 * 127^2 * 3851^2
                    (.node 4594973497797622859580700860561 (.basic (.groups [5, 317, 292561])) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^2 * 97^2 * 3169
                      (.node 4533870039638126778431736261093 (.cut 5 31 8871121154792457807089957) -- 3^8 * 13 * 7^10 * 757^6
                        (.node 4365154423890779002304815055853 (.basic (.groups [31, 613, 1301])) .empty .empty)
                        .empty)
                      (.node 5031994362342580897974763320969 (.basic (.split 30941)) -- 3^8 * 13^4 * 757^2 * 14713^4
                        (.node 4604323382699711952024091732293 (.basic (.split 23)) .empty .empty)
                        .empty))
                    (.node 5614894888885441157916907236429 (.basic (.groups [11, 191, 2521])) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^4 * 757^4
                      (.node 5483727123624481527521439705693 (.basic (.split 151)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37 * 19^4
                        (.node 5365117508632445764599481082025 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 5821290309141064193112714571317 (.basic (.split 19)) -- 3^6 * 1093 * 547^2 * 163^8 * 7^2
                        (.node 5752260307852602325723207179837 (.cut 5 101 420781165828371041) .empty .empty)
                        .empty)))
                  (.node 6675057016154702019133086310569 (.basic (.groups [13, 67, 151, 911, 14939])) -- 3^6 * 1093^6 * 7^2 * 19^4 * 29^2
                    (.node 6054656331676765104570672676737 (.basic (.groups [31, 701, 8269, 14083, 70841])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^2 * 19^6
                      (.node 6029093908083125029225061240037 (.basic (.groups [29, 1123, 293459])) -- 3^6 * 1093 * 547^6 * 7^10
                        (.node 5955231868921797646296988305261 (.basic (.groups [7, 19, 79])) .empty .empty)
                        .empty)
                      (.node 6657580892293317841812407679645 (.basic (.groups [19, 757, 17293])) -- 3^8 * 13^2 * 61^4 * 5 * 131^8
                        (.node 6055660190980660470420163426209 (.basic (.groups [331, 45319, 3500201, 4189129561])) .empty .empty)
                        .empty))
                    (.node 6796799838125345890586037082869 (.basic (.groups [5, 307, 617, 911, 104670301])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^4
                      (.node 6793437143413300824183041443089 (.basic (.groups [11, 31, 127])) -- 3^8 * 13^2 * 61^8 * 19^2 * 97^4
                        (.node 6700589760665187619986880708569 (.basic (.groups [157, 433, 14083, 292561])) .empty .empty)
                        .empty)
                      (.node 7086470464467919600590435096969 (.basic (.split 19)) .empty .empty))))
                (.node 10135604365095813848426455576317 (.basic (.groups [127, 613, 175897, 522061])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^2 * 67^6
                  (.node 8665555228458335186095793251449 (.basic (.split 13)) -- 3^12 * 797161 * 398581^2 * 1621^2 * 7^2
                    (.node 7446479004308424448020476142189 (.basic (.split 19)) -- 3^8 * 13^2 * 61 * 31^6 * 757^2 * 14713^2
                      (.node 7305251261417770229131878595449 (.basic (.split 7)) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^6
                        (.node 7283607069009906393413702870277 (.basic (.groups [61, 67, 2801, 132197305635599])) .empty .empty)
                        .empty)
                      (.node 8414513230455899657441792288757 (.cut 5 257 1012858215203696936101) -- 3^8 * 13 * 7^2 * 19^10 * 757^4
                        (.node 7900333378327355598226993152429 (.basic (.groups [7, 31, 292561])) .empty .empty)
                        .empty))
                    (.node 9389163927026603014166264225625 (.basic (.groups [11, 71, 97, 131])) -- 3^2 * 13^2 * 61^14 * 5^4
                      (.node 9365563553120755267516815046149 (.basic (.groups [7, 757, 5233, 3844747])) -- 3^8 * 13^2 * 61 * 31^2 * 331^8
                        (.node 8877349961979023373605276860197 (.basic (.groups [5, 41, 3169])) .empty .empty)
                        .empty)
                      (.node 10109969435169562306143279681549 (.basic (.groups [19, 617, 88741])) -- 3^4 * 11^12 * 1093^2 * 398581 * 17^4
                        (.node 9513163134026079527440264078125 (.basic (.groups [19531, 160967, 52379047267])) .empty .empty)
                        .empty)))
                  (.node 12001884639191271358563779962641 (.basic (.groups [5, 15797, 17351])) -- 3^2 * 13^2 * 61^2 * 97^4 * 11^10 * 31^4
                    (.node 10824549045377052262054825563813 (.basic (.groups [701, 70841, 365017])) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^6
                      (.node 10602285820897087501407030267009 (.basic (.groups [631, 45319, 3500201])) -- 3^4 * 11^6 * 43^14
                        (.node 10292198534382514136280511207581 (.basic (.groups [5, 331, 22996651, 104670301])) .empty .empty)
                        .empty)
                      (.node 11347562387905503360287570274573 (.basic (.split 2801)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13
                        (.node 10951520804483829755723530592769 (.basic (.groups [5, 97, 131])) .empty .empty)
                        .empty))
                    (.node 13325913319391607697329917784213 (.cut 5 7 1934797676950149622919) -- 3^12 * 797161^2 * 61^2 * 13^9
                      (.node 12656528442814484344449127201533 (.cut 5 31 387203412092213867) -- 3^6 * 1093 * 547^2 * 163^2 * 7^6 * 19^8
                        (.node 12047987506900180653252594830853 (.cut 5 31 3425497583462120188759271) .empty .empty)
                        .empty)
                      (.node 13642822859191490528808713915121 (.basic (.groups [11, 31, 262321])) .empty .empty)))))
              (.node 24896957119427525728153870584549 (.basic (.groups [7, 617, 911, 25646167])) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^4 * 151^2
                (.node 20177513284715072032572299144853 (.basic (.split 11)) -- 3^2 * 13 * 7^2 * 19^4 * 151^2 * 911^2 * 1093^4
                  (.node 17203823573691750450307380307521 (.basic (.groups [29, 14939, 16148168401])) -- 3^6 * 1093^6 * 7^12
                    (.node 14508580651200017287331161703877 (.basic (.split 43)) -- 3^2 * 13 * 7^4 * 2801^2 * 37^12
                      (.node 14308614681190311910379643274401 (.basic (.groups [2801, 878837, 5229043])) -- 3^8 * 13^6 * 757^6 * 7^4
                        (.node 14200876480392782981062365604293 (.basic (.groups [163, 379, 3511, 14713])) .empty .empty)
                        .empty)
                      (.node 15550479087496134066733865892489 (.basic (.split 127)) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^4
                        (.node 15221873376119243873216858308173 (.basic (.groups [151, 157, 199])) .empty .empty)
                        .empty))
                    (.node 19487106023304423829381285314969 (.basic (.split 187123)) -- 3^2 * 13^8 * 61^12
                      (.node 18800978592594664617789823482609 (.basic (.groups [11, 31, 151, 262321])) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97^4
                        (.node 17569950133793542702836829184061 (.cut 5 101 340042360272295856821) .empty .empty)
                        .empty)
                      (.node 20064053489115031226869783647357 (.basic (.groups [43, 433, 4733, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^6 * 29^4
                        (.node 19595592128611272435555382023717 (.basic (.groups [631, 2663, 4933, 1855860368209])) .empty .empty)
                        .empty)))
                  (.node 22583929524226595709775429285161 (.basic (.groups [43, 191, 2521])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^4 * 11^6
                    (.node 21705528240951314683721133678237 (.basic (.groups [19, 67, 613, 2801, 398581])) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^4
                      (.node 21296559654963095864517280856277 (.basic (.groups [157, 2801, 187123])) -- 3^2 * 13^5 * 7^4 * 61^12
                        (.node 20207402079610386820903381477521 (.basic (.groups [19, 14713, 30941, 25875541, 127588339])) .empty .empty)
                        .empty)
                      (.node 21980330685612084674333971766241 (.basic (.split 5)) -- 3^6 * 1093^2 * 398581^4
                        (.node 21724888264776108896670535840569 (.basic (.groups [7, 757, 967])) .empty .empty)
                        .empty))
                    (.node 22873837125223426260444645147561 (.basic (.split 5419)) -- 3^8 * 13^6 * 757^2 * 14713^2 * 19^2 * 127^2
                      (.node 22852032509170455625142487080793 (.cut 5 101 1734412703515466576993) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^12
                        (.node 22761102494696196005895641504733 (.basic (.groups [5, 11, 127])) .empty .empty)
                        .empty)
                      (.node 23331313195601549751575481799917 (.basic (.groups [757, 70841, 16975792017452101])) .empty .empty))))
                (.node 36245642278327404005094225526053 (.basic (.split 2801)) -- 3^6 * 1093 * 547^6 * 7^4 * 29^4
                  (.node 31728579553251276061160934711117 (.basic (.groups [11, 191, 2521])) -- 3^8 * 13 * 7^2 * 19^6 * 701^2 * 757^4
                    (.node 25800069200526865465612153169121 (.basic (.split 7)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^4 * 11^2
                      (.node 24935302404291077432281681075341 (.basic (.groups [5, 4651, 30941])) -- 3^2 * 13^14 * 61 * 31^2 * 331^4
                        (.node 24921937528027540590830577687009 (.basic (.groups [5, 15797, 17351])) .empty .empty)
                        .empty)
                      (.node 30547046194597695431453866745013 (.basic (.groups [67, 397, 701, 70841])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2 * 19^6
                        (.node 27078447534971032898097224764329 (.basic (.groups [5, 757, 837197335075000483])) .empty .empty)
                        .empty))
                    (.node 35070247101250331945158399928181 (.basic (.groups [29, 307, 617])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2 * 7^6
                      (.node 32883138532498874665719421753317 (.basic (.groups [11, 31, 379, 1301])) -- 3^8 * 13^4 * 757^5 * 163^4
                        (.node 32049754056459376534515160603089 (.basic (.groups [7, 19, 31, 433, 14083])) .empty .empty)
                        .empty)
                      (.node 35745824379489460518039365677797 (.basic (.groups [71, 4933, 5839, 158341])) .empty .empty)))
                  (.node 39573081402342319371394086899121 (.basic (.groups [71, 2801, 8971])) -- 3^2 * 13^12 * 53^2 * 7^4 * 409^4
                    (.node 36436260228314204607197861348973 (.basic (.split 12346432697)) -- 3^2 * 13 * 7^2 * 19^2 * 127^12
                      (.node 36417278414932141136393473377237 (.basic (.groups [613, 761, 5419, 26881])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^2 * 67^4 * 127^2
                        (.node 36353672596753386559561118697273 (.basic (.groups [31, 8269, 14083])) .empty .empty)
                        .empty)
                      (.node 38461489773518870791384181203125 (.basic (.groups [71, 191, 19531, 510101])) -- 3^6 * 1093 * 547^4 * 431^4 * 5^6
                        (.node 36670888542879867078446118791121 (.basic (.groups [264031, 1803647, 178250690949465223])) .empty .empty)
                        .empty))
                    (.node 45560751715352422993965965057601 (.basic (.groups [7, 1093, 3169, 22996651])) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97^2 * 151^2
                      (.node 42771581308259204973391611034929 (.basic (.split 13)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^6
                        (.node 40211137299147439837637071406529 (.basic (.groups [2801, 45319, 6032531, 1497157061])) .empty .empty)
                        .empty)
                      (.node 48247048376328340340092845616689 (.basic (.split 1621)) .empty .empty))))))
            (.node 113919329823812742059232716293821 (.basic (.groups [307, 617, 701])) -- 3^6 * 1093^2 * 398581 * 17^8 * 19^6
              (.node 69254885610924782759590214672109 (.basic (.split 43)) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^2
                (.node 59138386675762615728832317017925 (.basic (.groups [71, 191, 331, 510101, 208097431])) -- 3^6 * 1093 * 547^4 * 431^4 * 5^2 * 31^2
                  (.node 55899326355945583705140270693681 (.basic (.split 103)) -- 3^2 * 13^2 * 61^16
                    (.node 51721411754618169388868426494293 (.cut 5 101 53219936554724888353279019) -- 3^2 * 13^5 * 7^2 * 19^10 * 61^6
                      (.node 49460992451578784305491869656413 (.cut 5 31 62166365889079429548019) -- 3^8 * 13^4 * 757 * 379^6 * 7^6
                        (.node 49202745166312529822459396831997 (.basic (.groups [29, 701, 70841, 132197305635599])) .empty .empty)
                        .empty)
                      (.node 53897050971867537572908092546609 (.basic (.groups [7, 29, 1373, 292561, 1777973])) -- 3^10 * 23^4 * 3851^6
                        (.node 53105866644952783019133628483869 (.cut 5 31 39377601040873289) .empty .empty)
                        .empty))
                    (.node 58447958155062244546635905842629 (.basic (.groups [19, 307, 617])) -- 3^6 * 1093^2 * 398581 * 17^14
                      (.node 57516619652306580743088134765625 (.basic (.groups [11, 69617111, 239371661, 305175781])) -- 3^2 * 13^4 * 30941^4 * 5^12
                        (.node 56665273137646045883902949685537 (.cut 5 31 260553442281161261) .empty .empty)
                        .empty)
                      (.node 58687076143420473253209180195357 (.basic (.groups [31, 613, 1301])) -- 3^4 * 11^12 * 1093 * 547^2 * 163^4
                        (.node 58613950471029232289832020778813 (.basic (.groups [7, 43, 397, 433, 14083, 204104071])) .empty .empty)
                        .empty)))
                  (.node 64263607588850527940702061569661 (.basic (.split 97)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^2
                    (.node 61532351571807377906436995425209 (.basic (.groups [11, 191, 2521])) -- 3^8 * 13^8 * 61^2 * 97^2 * 757^4
                      (.node 61211165604797801963514746352429 (.basic (.groups [5, 13, 67, 271])) -- 3^6 * 1093^6 * 7^4 * 29^5
                        (.node 60388328134852214268078416725317 (.basic (.groups [37, 61, 163, 199])) .empty .empty)
                        .empty)
                      (.node 63583818857815550807831458132629 (.cut 5 31 141014486725085920443481) -- 3^2 * 13^2 * 61^5 * 7^6 * 29^10
                        (.node 63155012006583632654211714527493 (.basic (.groups [43, 787, 967])) .empty .empty)
                        .empty))
                    (.node 65206703231164743641839469191077 (.basic (.groups [67, 4933, 6038099, 3664405207])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^10
                      (.node 64858893917131397720702754130221 (.basic (.groups [571, 14251, 88770666332610762169])) -- 3^2 * 13^2 * 61 * 31^18
                        (.node 64741957047526885579465679918241 (.basic (.groups [13, 19, 97, 151])) .empty .empty)
                        .empty)
                      (.node 69072627116026145166630948406521 (.basic (.groups [7, 911, 1093, 30941])) .empty .empty))))
                (.node 88443722309635420702511255185401 (.basic (.split 433)) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^6
                  (.node 79086382496795356859633737409217 (.basic (.split 17707)) -- 3^4 * 11^10 * 15797^2 * 1806113 * 17^4
                    (.node 74671874616540294250279644371733 (.basic (.groups [37, 151, 3169])) -- 3^8 * 13^6 * 757 * 379^2 * 61^2 * 97^2 * 787^2
                      (.node 71681991915971545445895472162521 (.basic (.groups [67, 2801, 14939, 30941])) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13^4
                        (.node 71552066836388803101379912967361 (.basic (.groups [967, 2801, 5839, 158341])) .empty .empty)
                        .empty)
                      (.node 78192752483299651076979583588377 (.basic (.split 19)) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433 * 7^2
                        (.node 76873399927640578788190966795221 (.basic (.groups [37, 43, 4933])) .empty .empty)
                        .empty))
                    (.node 83601429021099728838036997328997 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13 * 19^2
                      (.node 82331304835546258827271317766917 (.basic (.split 19)) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^2
                        (.node 79938494265724714788369022005093 (.basic (.groups [37, 43, 4933, 8269])) .empty .empty)
                        .empty)
                      (.node 87094558150988928106552528753197 (.basic (.groups [7, 43, 3169, 9872250674161])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^6
                        (.node 84300600401298480319216801396317 (.basic (.split 28387)) .empty .empty)
                        .empty)))
                  (.node 97455219414281433462107324165373 (.basic (.groups [4933, 5113, 3500201, 37140797])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^4 * 71^2
                    (.node 92325867469653989641405473737433 (.basic (.groups [7, 31, 37, 1693, 8269, 14083, 14389])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^5
                      (.node 91198577061168649460161371215829 (.basic (.groups [151, 617, 911])) -- 3^6 * 1093^2 * 398581 * 17^10 * 19^4
                        (.node 90840983926137205985599743407169 (.basic (.groups [19, 37, 433, 2593, 8269, 14083, 2738539])) .empty .empty)
                        .empty)
                      (.node 95325248088855653127636075797709 (.cut 5 7 6735662275055687168449483) -- 3^2 * 13^12 * 53^6 * 29^5
                        (.node 93245036078694466292778263668437 (.cut 5 31 744501353133755602771) .empty .empty)
                        .empty))
                    (.node 109834687154903501727680930863209 (.basic (.groups [43, 967, 4651])) -- 3^2 * 13^14 * 61^2 * 97^6
                      (.node 103425762573623872283180088664449 (.basic (.groups [4733, 14939, 732541, 562731116179])) -- 3^6 * 1093^6 * 7^6 * 29^4
                        (.node 101791284169460590683832946484141 (.basic (.split 617)) .empty .empty)
                        .empty)
                      (.node 109901653428060423371669858831205 (.basic (.split 1866871)) .empty .empty)))))
              (.node 177752672764563407501122673580621 (.basic (.groups [617, 88741, 104281])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^10
                (.node 147518311042771543683738413569449 (.basic (.split 61)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2
                  (.node 134127937715811144114987027050625 (.basic (.groups [11, 71, 2671, 178601, 169299992707751])) -- 3^12 * 797161^4 * 5^4
                    (.node 119010020499023617936832321078253 (.basic (.groups [19, 3931, 293459, 262209281])) -- 3^2 * 13 * 7^10 * 1123^2 * 127^4 * 3313^2
                      (.node 117031555208705022115036300905957 (.basic (.split 43)) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2
                        (.node 114624677797420602716588234724957 (.basic (.groups [13, 67, 151, 911])) .empty .empty)
                        .empty)
                      (.node 131423937774041922766398171969309 (.basic (.split 1471)) -- 3^2 * 13^2 * 61 * 31^12 * 42407^2
                        (.node 119321338927401468869239307687517 (.cut 5 257 3537280236622234695503861) .empty .empty)
                        .empty))
                    (.node 141758512690519859994076335804981 (.basic (.split 73)) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2
                      (.node 138439880642537788985855140257405 (.basic (.split 21491)) -- 3^2 * 13^2 * 61^4 * 5 * 131^6 * 127^4
                        (.node 137251370289303699958151512727733 (.basic (.groups [331, 397, 2801, 208097431])) .empty .empty)
                        .empty)
                      (.node 146463569281199939693502400790877 (.basic (.groups [31, 2801, 14939, 562731116179])) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13 * 67^2
                        (.node 142300616146700345617242251149029 (.basic (.groups [127, 523, 617])) .empty .empty)
                        .empty)))
                  (.node 161600431340752825202511335548605 (.basic (.split 21491)) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4
                    (.node 151953887411683612649426703699981 (.basic (.groups [7, 43, 307, 617, 86353])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^6
                      (.node 149897143266149274473794976726157 (.basic (.groups [79, 151, 433, 911, 3499])) -- 3^2 * 13^4 * 30941^2 * 157^5 * 7^2 * 19^4
                        (.node 149755590219471563097542582010837 (.basic (.groups [337901, 2767631689, 113990869481])) .empty .empty)
                        .empty)
                      (.node 159912157040478053078027127711093 (.basic (.groups [67, 127, 613, 398581, 1193557])) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^2 * 19^2
                        (.node 156722559249170956767273975569805 (.basic (.groups [23, 67, 353, 1453, 15401])) .empty .empty)
                        .empty))
                    (.node 169676426762924885416290488623173 (.basic (.groups [7, 19, 67, 613, 1747, 5111046132733])) -- 3^6 * 1093 * 547^8 * 163^2
                      (.node 163535109267891857877830954938797 (.cut 5 31 3639955090392078977) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^14
                        (.node 163411609299561903071395400025645 (.basic (.groups [19, 17293, 21491, 3798019])) .empty .empty)
                        .empty)
                      (.node 175940594087059124150846510026161 (.basic (.groups [37, 1051, 1621, 1693, 5231])) .empty .empty))))
                (.node 227438427778400929632677836168221 (.basic (.groups [5, 11, 17351, 50689400581])) -- 3^2 * 13^2 * 61^13 * 31^4
                  (.node 206842885964517263921444440392741 (.basic (.groups [617, 911, 2801])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^4 * 151^2 * 7^4
                    (.node 183412113805106263645612108758477 (.cut 5 13 89383076373092906826769) -- 3^6 * 1093 * 547^4 * 431^2 * 7^12
                      (.node 180823796687258415671604541316217 (.basic (.groups [2801, 878837, 30629717273])) -- 3^8 * 13^2 * 61^2 * 97 * 7^4 * 757^6
                        (.node 179813038455816537236744445234201 (.basic (.groups [5, 3851, 1956611])) .empty .empty)
                        .empty)
                      (.node 196378688899176156230204139909237 (.basic (.groups [7, 19, 31, 547, 4189129561, 1425881675401])) -- 3^6 * 1093^9 * 11^2
                        (.node 184818731973230958750536710290489 (.basic (.groups [701, 70841, 3798019])) .empty .empty)
                        .empty))
                    (.node 225179685287695041477186993257241 (.basic (.groups [151, 911, 30941])) -- 3^8 * 13^4 * 757^6 * 7^2 * 19^4
                      (.node 222037075667845640511782993642229 (.basic (.groups [307, 599, 617])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^12
                        (.node 218550620131954644741841814153337 (.basic (.groups [31, 4733, 8269, 14083])) .empty .empty)
                        .empty)
                      (.node 225539178113153008848720067799409 (.basic (.split 7)) .empty .empty)))
                  (.node 249682685758939622926666737143973 (.basic (.groups [43, 19571, 293459])) -- 3^2 * 13 * 7^10 * 1123^4 * 41^6
                    (.node 237829078350651988186006601953125 (.cut 7 257 6989546126083139681) -- 3^2 * 13^8 * 61^6 * 1609669 * 5^8
                      (.node 235853245584889604267909870144133 (.cut 5 31 36106708044096079110497797) -- 3^2 * 13^5 * 7^6 * 29^2 * 61^10
                        (.node 234729098175665075354156605640625 (.basic (.groups [97, 131, 19531])) .empty .empty)
                        .empty)
                      (.node 242341420515640079465827048106781 (.basic (.groups [11, 523, 2801])) -- 3^2 * 13^2 * 61^5 * 7^4 * 31^6 * 97^4
                        (.node 240189162779606613840810829111653 (.basic (.groups [11, 31, 613, 1301, 1601, 398581])) .empty .empty)
                        .empty))
                    (.node 262315259503705751417568724281597 (.basic (.groups [19571, 293459, 990151, 1983851])) -- 3^2 * 13 * 7^10 * 1123^4 * 41^2 * 1723^2
                      (.node 262114153543858279776171087982041 (.basic (.split 3500201)) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^4
                        (.node 257900375450979154552518486927729 (.basic (.groups [7, 19, 41, 1693, 4271, 8269])) .empty .empty)
                        .empty)
                      (.node 265695922697345974084631163395157 (.basic (.groups [5, 11, 211, 631])) .empty .empty)))))))
          (.node 2558215837672918975813147070005809 (.basic (.split 127)) -- 3^8 * 13^2 * 61^6 * 757^2 * 14713^2 * 19^2
            (.node 961537244337971769784604530078125 (.basic (.groups [19, 31, 71])) -- 3^6 * 1093 * 547^4 * 431^4 * 5^8
              (.node 496644613889694878572896323239533 (.basic (.groups [127, 613, 2801])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2 * 67^6
                (.node 386253002761462109262037330635093 (.basic (.split 7)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^2 * 37^2
                  (.node 335061604543481379054499988903121 (.basic (.groups [5, 17351, 3158528101])) -- 3^4 * 11^12 * 1093^4 * 31^4
                    (.node 294248629196625430283088464504613 (.basic (.groups [613, 701, 761])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^6 * 67^4
                      (.node 287583098261532903715440673828125 (.basic (.groups [11, 29, 449])) -- 3^2 * 13^4 * 30941^4 * 5^13
                        (.node 285243225147912145462523013994533 (.basic (.groups [19, 67, 613, 2801])) .empty .empty)
                        .empty)
                      (.node 302347961451902923875177931319157 (.basic (.groups [37, 43, 4933, 878837])) -- 3^8 * 13 * 7^4 * 757^6 * 2801^2
                        (.node 295425601496073126432028000761813 (.cut 5 13 61907586253301450782708771) .empty .empty)
                        .empty))
                    (.node 358823248341823765170202014677601 (.basic (.groups [7, 631, 5233, 45319])) -- 3^6 * 1093^4 * 11^6 * 31^2 * 43^2 * 331^2
                      (.node 357957311809470741227462051177001 (.basic (.groups [19, 3169, 878837, 30629717273])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^6 * 7^2
                        (.node 349997623792174220712347731204521 (.basic (.split 733)) .empty .empty)
                        .empty)
                      (.node 384341810717351410643874213867717 (.basic (.groups [761, 4933, 5839, 26881])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^6 * 67^4
                        (.node 380909171361178426784499135607257 (.basic (.groups [7, 43, 71, 113, 967])) .empty .empty)
                        .empty)))
                  (.node 422288137194432869353038685848117 (.basic (.split 433)) -- 3^2 * 13 * 7^12 * 16148168401^2
                    (.node 396716302779000407981025790866921 (.basic (.groups [7, 1093, 22996651, 52379047267])) -- 3^12 * 797161^2 * 61^6 * 151^2
                      (.node 394790309126250746206767765768441 (.basic (.groups [127, 523, 29989])) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^8
                        (.node 389178980043472504125511566533721 (.cut 5 31 658294419080814289721) .empty .empty)
                        .empty)
                      (.node 416870377732181651578962062669901 (.cut 5 257 23051296579012758391) -- 3^12 * 797161^2 * 61 * 31^6 * 151^2
                        (.node 412608377509106704137855354698181 (.cut 5 7 1607364884680791600251221) .empty .empty)
                        .empty))
                    (.node 450963893537387887935282110882181 (.basic (.groups [5, 13, 67, 127])) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^5
                      (.node 433429246120299902228622150707049 (.basic (.groups [7, 29, 14939, 3158528101])) -- 3^4 * 11^12 * 1093^6
                        (.node 424612206194458424118693869321001 (.basic (.groups [13, 2801, 9631, 32668561])) .empty .empty)
                        .empty)
                      (.node 457257267316392893253012280606317 (.basic (.groups [29, 953, 967, 1009, 238267, 208097431])) .empty .empty))))
                (.node 670639688579055720574935135253125 (.basic (.groups [7, 31, 2671, 178601])) -- 3^12 * 797161^4 * 5^5
                  (.node 608869443260817908369758687425777 (.basic (.groups [7, 967, 18041, 246247])) -- 3^2 * 13^10 * 23^4 * 419^2 * 859^2 * 13537
                    (.node 549508267140302116858349294156025 (.basic (.split 31)) -- 3^6 * 1093^2 * 398581^4 * 5^2
                      (.node 519244689973748505906146280973389 (.basic (.groups [97, 701, 3931, 70841])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^6 * 617^2
                        (.node 508787644208742671072485548841569 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 571553059759219548216169330911453 (.basic (.groups [5, 157, 911])) -- 3^2 * 13^5 * 7^2 * 19^4 * 61^6 * 151^4
                        (.node 556030557007369664654090943454077 (.basic (.split 29)) .empty .empty)
                        .empty))
                    (.node 650198886193285218095092236067293 (.basic (.groups [37, 151, 30941])) -- 3^8 * 13^4 * 757 * 379^2 * 61^6 * 787^2
                      (.node 641125287438797408025121894521117 (.basic (.groups [397, 761, 2801, 26881])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^4 * 67^4
                        (.node 636548400709713233533466776223577 (.basic (.split 71)) .empty .empty)
                        .empty)
                      (.node 660150765349510899179456281406853 (.cut 5 7 6855329730511270044637) -- 3^8 * 13^6 * 757 * 379^2 * 61^8
                        (.node 658963402911090179945755019979633 (.cut 5 13 2564587436211563741917) .empty .empty)
                        .empty)))
                  (.node 861845817337324827420524075204877 (.cut 5 101 10654437965645886089609) -- 3^2 * 13^5 * 7^6 * 29^4 * 61^2 * 97^6
                    (.node 741582461647642879480440024469773 (.basic (.groups [109, 337, 433, 727, 1289, 2017])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^6 * 281^2
                      (.node 690968608678954059516982850893209 (.basic (.split 37)) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2
                        (.node 686968531110381680238631697638893 (.cut 5 31 95953226876575534951) .empty .empty)
                        .empty)
                      (.node 850407047235896171757735001243761 (.basic (.split 1774921)) -- 3^8 * 13^6 * 757^2 * 14713^4
                        (.node 786864692821081716913185424993869 (.basic (.split 617)) .empty .empty)
                        .empty))
                    (.node 933104590757269054829827661466837 (.basic (.groups [4933, 175897, 522061, 3500201])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^6
                      (.node 931865894907630090796641138112773 (.basic (.groups [61, 67, 157])) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13^5
                        (.node 887934895818945304023548725712661 (.basic (.split 43)) .empty .empty)
                        .empty)
                      (.node 955285303576022963352750182419161 (.basic (.split 5)) .empty .empty)))))
              (.node 1710215916361568376382271145860001 (.basic (.split 19)) -- 3^4 * 11^10 * 15797^2 * 1806113^2
                (.node 1323353817341574581294445249766737 (.cut 5 13 9852461534301993577) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^2 * 97^5
                  (.node 1086818577274296474894480965276961 (.basic (.split 61)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^2 * 19^2
                    (.node 1064346147166216915912536296661717 (.basic (.split 37)) -- 3^2 * 13 * 7^4 * 2801^8
                      (.node 1063570883806614419502335550233613 (.basic (.groups [19, 29, 67, 613])) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^6
                        (.node 1034363977886203236427399454315889 (.basic (.groups [29, 127, 523, 14939])) .empty .empty)
                        .empty)
                      (.node 1078341283438800997603077257292801 (.basic (.groups [14713, 1609669, 3348577])) -- 3^8 * 13^8 * 61^2 * 97^2 * 757^2 * 3169^2
                        (.node 1074159345399461828206238500083837 (.cut 5 13 11614020221397140863) .empty .empty)
                        .empty))
                    (.node 1230929594662674180486915785076813 (.basic (.groups [67, 2801, 30941])) -- 3^6 * 1093 * 547^6 * 7^4 * 29^2 * 13^4
                      (.node 1215387855986682474461524912542153 (.cut 5 31 234830519207596222689047) -- 3^2 * 13^2 * 61^2 * 97^9 * 7^10
                        (.node 1188713467421569853592258404213109 (.cut 5 257 4273771813748166542161705963) .empty .empty)
                        .empty)
                      (.node 1306779003727834026723069274023213 (.basic (.groups [67, 179743, 3500201, 62060021])) -- 3^2 * 13 * 7^2 * 19^10 * 104281^2 * 43^4
                        (.node 1240416110235456148422901490325009 (.basic (.groups [71, 757, 859])) .empty .empty)
                        .empty)))
                  (.node 1464478833609458646450189059494881 (.basic (.groups [19, 61, 9631, 32668561])) -- 3^12 * 797161 * 398581^2 * 1621^2 * 7^2 * 13^2
                    (.node 1376649612263949410870151618005469 (.basic (.groups [43, 617, 733, 911])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2 * 7^2 * 307^2
                      (.node 1359770545076313651613556724670041 (.basic (.groups [5, 732541, 2289401])) -- 3^10 * 23^6 * 29^4 * 3851^4
                        (.node 1335576899419114513109528052678933 (.cut 5 101 93329676920283331936596053) .empty .empty)
                        .empty)
                      (.node 1437915491307664518577203369140625 (.basic (.groups [11, 31, 71])) -- 3^2 * 13^4 * 30941^4 * 5^14
                        (.node 1407545279071965799539656753458341 (.basic (.split 11)) .empty .empty)
                        .empty))
                    (.node 1619321603213190907513793391508557 (.basic (.split 3169)) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2 * 787^4
                      (.node 1572019169989858774262990638350129 (.basic (.groups [43, 331, 3637])) -- 3^6 * 1093^4 * 11^6 * 31^8
                        (.node 1532567298491074963817893304682561 (.cut 5 31 1350914336777827692907083841) .empty .empty)
                        .empty)
                      (.node 1686578351380987411364583037531761 (.basic (.groups [14713, 187123, 14421466756460791])) .empty .empty))))
                (.node 1970345727658224552044216498919921 (.basic (.groups [29, 4733, 45319])) -- 3^4 * 11^6 * 43^2 * 631^6 * 7^6
                  (.node 1823694923481682467925612877813073 (.basic (.groups [7, 67, 139])) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97^5
                    (.node 1775123802539136256941927644220441 (.basic (.groups [2801, 14939, 88009573, 562731116179])) -- 3^6 * 1093^6 * 7^4 * 29^6
                      (.node 1773900057576855692228207643973521 (.basic (.split 23)) -- 3^6 * 1093^10
                        (.node 1718442107961266265312761596480869 (.cut 5 101 183432033667) .empty .empty)
                        .empty)
                      (.node 1781329957240915941418494816166377 (.cut 5 13 952155674869986977003) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^14
                        (.node 1776036471638042796249617050776597 (.basic (.groups [4733, 732541, 132197305635599])) .empty .empty)
                        .empty))
                    (.node 1910825171263803381403999428298053 (.basic (.split 23)) -- 3^6 * 1093 * 547^10
                      (.node 1887070931258214462423858311491557 (.cut 5 13 78583129451553962888209) -- 3^2 * 13 * 7^16 * 14009^2 * 223^4
                        (.node 1878760904883676471680092765525961 (.basic (.groups [859, 7603, 18041, 292561])) .empty .empty)
                        .empty)
                      (.node 1964275153218224962379364716949141 (.basic (.groups [5, 617, 911, 88741])) .empty .empty)))
                  (.node 2183030289897802616300069121804801 (.basic (.split 30941)) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^4
                    (.node 2069360834048224596414148804417161 (.basic (.split 151)) -- 3^4 * 11^6 * 43^4 * 45319^4
                      (.node 2066735794340814159287315010497517 (.basic (.groups [7, 19, 2633, 12763, 1806113])) -- 3^4 * 11^10 * 15797^5
                        (.node 1979625491628437831435239733755173 (.basic (.groups [701, 1693, 8269, 14083, 70841])) .empty .empty)
                        .empty)
                      (.node 2101485801599924173713689960245437 (.basic (.groups [67, 127, 613, 6251791302919])) -- 3^6 * 1093 * 547^2 * 163^8 * 7^2 * 19^2
                        (.node 2095807484104701043696188940711521 (.basic (.groups [13, 19, 37, 1063, 9631])) .empty .empty)
                        .empty))
                    (.node 2429466277563007527385815083081181 (.cut 5 31 115655768064837738674294843) -- 3^2 * 13^2 * 61^5 * 7^4 * 31^12
                      (.node 2409981830612421927930653004025281 (.basic (.groups [757, 8011, 837197335075000483])) -- 3^8 * 13^2 * 61^2 * 97^10 * 89^2
                        (.node 2201549444546625262008356319109773 (.basic (.groups [89, 157, 2801])) .empty .empty)
                        .empty)
                      (.node 2446952284201557227991905476468521 (.cut 5 101 197974073434382276449278149) .empty .empty))))))
            (.node 7442885890604482686396237392954397 (.basic (.groups [7, 29, 3158528101])) -- 3^4 * 11^12 * 1093 * 547^6
              (.node 3918253214802390133439862128149245 (.basic (.split 31)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^2
                (.node 3356551745988090013025562872841597 (.basic (.groups [23, 757])) -- 3^8 * 13 * 7^2 * 19^4 * 151^10
                  (.node 2999347114635092296212222571269021 (.basic (.groups [5, 13, 67])) -- 3^6 * 1093^6 * 7^6 * 29^5
                    (.node 2917897636300747624647915773587281 (.basic (.split 71)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^6
                      (.node 2862709133219578073462885256264849 (.basic (.groups [53, 79, 757])) -- 3^8 * 13^2 * 61^2 * 97^12
                        (.node 2688178920555341225735391887330229 (.basic (.groups [127, 3798019, 917087137])) .empty .empty)
                        .empty)
                      (.node 2926662980167338831427382883429453 (.cut 5 7 105526873052022052301) -- 3^8 * 13^8 * 61^2 * 97^2 * 757 * 379^4
                        (.node 2921781166764003506475407827967661 (.cut 5 13 949611523284040837841) .empty .empty)
                        .empty))
                    (.node 3156446167827937439730851294802477 (.basic (.split 23)) -- 3^6 * 1093 * 547^2 * 163^10
                      (.node 3150317658659630954891106813483069 (.cut 5 13 144984098219098502227512221) -- 3^2 * 13^2 * 61 * 31^10 * 23^10
                        (.node 3121808373263750721339070533463641 (.basic (.groups [5, 1811, 3221, 8269, 14083, 1768661])) .empty .empty)
                        .empty)
                      (.node 3353198442895278602874675676265625 (.basic (.groups [2671, 19531, 178601, 169299992707751])) -- 3^12 * 797161^4 * 5^6
                        (.node 3177365382148498320406480168560921 (.basic (.groups [11, 31, 151])) .empty .empty)
                        .empty)))
                  (.node 3659665052424572010968933263312197 (.basic (.groups [433, 2801, 5839, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4 * 43^6
                    (.node 3498615367322696423067349744582329 (.basic (.groups [41, 733, 1693, 4271])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^2 * 37^4
                      (.node 3447387238449541117879075965205077 (.basic (.groups [5, 11, 211, 1597, 2221, 2884629032993])) -- 3^2 * 13 * 7^4 * 2801^6 * 71^4
                        (.node 3415050951454155372732671469701049 (.basic (.groups [19, 14713, 5229043, 25875541])) .empty .empty)
                        .empty)
                      (.node 3658953175799588799281950463050437 (.basic (.groups [151, 613, 911])) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^4 * 67^6
                        (.node 3506051274983051351967615735400689 (.basic (.groups [29, 967, 4733])) .empty .empty)
                        .empty))
                    (.node 3895473314996553924542784246238413 (.basic (.groups [193, 51343, 1477807, 133338869])) -- 3^2 * 13 * 7^2 * 19^12 * 599^2 * 29251^2
                      (.node 3878020240831584560676334432973769 (.basic (.groups [31, 433, 14083, 15797])) -- 3^2 * 13^4 * 30941^2 * 157^4 * 11^10
                        (.node 3831444871681682902771999595830473 (.basic (.groups [31, 2801, 12503, 14083, 1205476469])) .empty .empty)
                        .empty)
                      (.node 3907662205381115866601792028536493 (.cut 5 13 1313183460061450130849) .empty .empty))))
                (.node 5495096288779047038231285849250453 (.cut 5 101 5654305743070467591874797407) -- 3^2 * 13^5 * 7^2 * 19^6 * 61^10
                  (.node 4723392423783793148919775590247413 (.basic (.groups [127, 397, 761, 26881])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2 * 19^2 * 67^4
                    (.node 4074631161827116751088484089584781 (.basic (.groups [617, 5419, 2141993519227])) -- 3^6 * 1093^2 * 398581 * 17^10 * 19^2 * 127^2
                      (.node 4034233936941766682536294570578933 (.basic (.split 2801)) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^4
                        (.node 3949259379899140020347406475012701 (.cut 5 31 375315029607288827535161) .empty .empty)
                        .empty)
                      (.node 4628491442671828059223591581753777 (.basic (.groups [5, 71, 241])) -- 3^8 * 13^4 * 757^2 * 14713 * 7^4 * 1051^4
                        (.node 4620843376785388502042557056614613 (.basic (.groups [7, 67, 397])) .empty .empty)
                        .empty))
                    (.node 5155877925795780379780101319826025 (.basic (.split 331)) -- 3^12 * 797161^4 * 5^2 * 31^2
                      (.node 4899937509303237786225914658988533 (.basic (.groups [11, 41, 151])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2 * 787^2 * 37^4
                        (.node 4776426517880114816763750912095805 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 5266995711234363689776220539503693 (.basic (.groups [7, 67, 151])) -- 3^8 * 13^2 * 61^6 * 757 * 379^2 * 787^2 * 37^2
                        (.node 5188602888960244029940817400315741 (.basic (.groups [617, 1051, 1621, 5231, 5419])) .empty .empty)
                        .empty)))
                  (.node 6369221055113175022774318484891649 (.basic (.groups [127, 5390701, 6038099, 3664405207])) -- 3^4 * 11^6 * 43^10 * 45319^2
                    (.node 5912154305484091148269131190798401 (.basic (.groups [467, 14939, 732541, 562731116179])) -- 3^6 * 1093^6 * 7^4 * 29^4 * 2801
                      (.node 5613722950586104398090925587188529 (.basic (.groups [151, 911, 14939, 732541])) -- 3^6 * 1093^6 * 7^2 * 19^4 * 29^4
                        (.node 5596727145913182297329329943619513 (.basic (.groups [2801, 8269, 14083, 917087137])) .empty .empty)
                        .empty)
                      (.node 6190537454574418141934748436591893 (.basic (.groups [2801, 12503, 1205476469])) -- 3^2 * 13^5 * 7^4 * 61^6 * 157^6
                        (.node 6100023909123435320827265319027813 (.basic (.groups [5, 11, 701, 1499, 17884211])) .empty .empty)
                        .empty))
                    (.node 6668265988407265219988927108827569 (.basic (.groups [19, 307, 433, 45319, 1107391795387489])) -- 3^4 * 11^6 * 43^2 * 631^8
                      (.node 6630759443204399932749194340328317 (.basic (.groups [79, 433, 1123])) -- 3^2 * 13^4 * 30941^2 * 157^5 * 7^10
                        (.node 6614239374713654723942312134940397 (.basic (.groups [19, 61, 157, 9631, 32668561])) .empty .empty)
                        .empty)
                      (.node 7228397241095805640503182264903001 (.basic (.groups [29, 61, 4733, 9631, 32668561])) .empty .empty)))))
              (.node 15727065343802190877193337903924573 (.basic (.groups [397, 59023, 70841, 492103, 266527927])) -- 3^2 * 13 * 7^2 * 19^6 * 701^8
                (.node 11196915693123241209806882175060441 (.basic (.groups [7, 331, 5839])) -- 3^6 * 1093^4 * 11^6 * 31^2 * 43^6
                  (.node 10673197029112633918561779755146317 (.cut 5 7 3463600968120984612127) -- 3^8 * 13^6 * 757 * 379^2 * 61^2 * 97^6
                    (.node 9001304035000120832933095494121053 (.basic (.groups [151, 733, 911])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^2 * 37 * 19^4
                      (.node 8998616973609064164708043227736389 (.basic (.split 31)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61
                        (.node 8577417848692639841152052692357161 (.basic (.split 859)) .empty .empty)
                        .empty)
                      (.node 10205627454790024211305252426578573 (.basic (.groups [37, 61, 163])) -- 3^8 * 13^6 * 757 * 379^8
                        (.node 10135301412261345932150777579244309 (.cut 5 101 236082808956311) .empty .empty)
                        .empty))
                    (.node 11027483676249768050754845894949693 (.basic (.groups [67, 127, 397])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2 * 19^8
                      (.node 10750063495657336716664210762449801 (.basic (.groups [7, 878837, 30629717273, 52379047267])) -- 3^8 * 13^2 * 61^6 * 757^6
                        (.node 10692209747023413368826279385619721 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 11051419727544497433587283322171041 (.basic (.split 19)) -- 3^2 * 13^4 * 30941^6 * 7^2
                        (.node 11030658374778868049872763628049329 (.basic (.groups [7, 79, 409, 20359, 8224356155341457])) .empty .empty)
                        .empty)))
                  (.node 13976918032247695127663627685732117 (.basic (.groups [19, 29, 67])) -- 3^6 * 1093 * 547^2 * 163^8 * 7^6
                    (.node 13077952912584248750123181215583249 (.basic (.groups [127, 14939, 88009573, 562731116179])) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^6
                      (.node 12114256633799191180356334795466049 (.basic (.groups [67, 2801, 14939])) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13^6
                        (.node 11296190750638409261392137085187181 (.basic (.groups [7, 878837, 917087137])) .empty .empty)
                        .empty)
                      (.node 13737706678507552921458732353900625 (.basic (.split 11)) -- 3^6 * 1093^2 * 398581^4 * 5^4
                        (.node 13701951073150440784034058847259289 (.basic (.split 5)) .empty .empty)
                        .empty))
                    (.node 14561471014520666842011241027117809 (.basic (.groups [292561, 1141081, 3348577])) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61^2 * 97^2 * 3169^2
                      (.node 14535035490328580212110987119023077 (.cut 5 7 17659809437162472591525337) -- 3^8 * 13^4 * 757 * 379^2 * 61^10
                        (.node 14262034476403541339739159714925533 (.basic (.groups [11, 31, 79, 433, 14083, 1793161])) .empty .empty)
                        .empty)
                      (.node 15297003374265062823423859778483397 (.basic (.groups [11, 191, 281, 379])) .empty .empty))))
                (.node 20805998103528462781815999596729049 (.basic (.groups [13, 29, 4733])) -- 3^12 * 797161 * 398581^2 * 1621^2 * 7^6
                  (.node 17539908278664066320145640507673049 (.basic (.groups [2801, 3169, 878837])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^6 * 7^4
                    (.node 16873868984345741261797488047427237 (.basic (.groups [43, 433, 4733])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^6 * 29^6
                      (.node 16515740442553289155635519524293053 (.basic (.split 199)) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^2 * 1499^2
                        (.node 16185390293558008622900181541740489 (.cut 5 31 72875234186184657427480271) .empty .empty)
                        .empty)
                      (.node 16891459906812988673977776788519781 (.cut 5 7 606108599380845367902203) -- 3^6 * 1093^2 * 398581 * 17^16
                        (.node 16884722078575594537426192845882621 (.cut 5 7 2941026373995197985462461) .empty .empty)
                        .empty))
                    (.node 18911770272784381584042846093600477 (.basic (.groups [7, 67, 397, 398581, 1193557, 208097431])) -- 3^6 * 1093^5 * 547^4 * 431^2
                      (.node 18572182593177802574862895793632029 (.basic (.groups [97, 3931, 5419, 25646167])) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2 * 127^2 * 617^2
                        (.node 17762191005038823265907842256350917 (.basic (.groups [29, 127, 523])) .empty .empty)
                        .empty)
                      (.node 19862246911492823666356360372607613 (.basic (.groups [11, 41, 43])) .empty .empty)))
                  (.node 23761821356800314903854700929017677 (.basic (.groups [5, 31, 547, 3221, 4189129561])) -- 3^6 * 1093^9 * 11^4
                    (.node 21873419497403044361665711486048413 (.cut 5 101 199980618117946187) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2 * 67^2 * 31^6
                      (.node 21607787121005102557151115465778773 (.basic (.groups [365017, 1806113, 262209281])) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^2 * 127^4
                        (.node 20985866748085294661279672415905397 (.basic (.groups [307, 433, 4933, 5113])) .empty .empty)
                        .empty)
                      (.node 22923813571765165297796581288520073 (.basic (.groups [11, 41, 101, 732541])) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^4
                        (.node 22855964541573858132434150111263713 (.basic (.groups [17707, 25646167, 249561007])) .empty .empty)
                        .empty))
                    (.node 24930594566228390882551791893236881 (.basic (.split 2801)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^4
                      (.node 24038431108449294244615113251953125 (.cut 7 31 17572140099703262740814621) -- 3^6 * 1093 * 547^4 * 431^4 * 5^10
                        (.node 23882132589400574083818754560479025 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 25565838521121300202128365483048733 (.basic (.split 19)) .empty .empty))))))))))
    (.node 1037863309940019575795340643486141681356402441 (.basic (.split 2384047)) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^2 * 127^4
      (.node 603118023345696852581209837279552672821 (.basic (.groups [5, 5233])) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^4 * 757^2 * 2801^4
        (.node 3249470756635043620688847473377700133 (.cut 5 13 2792826470433643051) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^2 * 37 * 19^6
          (.node 250813677202225146362350522979955081 (.basic (.groups [5419, 14939, 732541, 562731116179])) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^4 * 127^2
            (.node 85985111871277511411250057754225161 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^6
              (.node 49727455418939626234687229842848273 (.basic (.groups [43, 2663, 4933])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2 * 37^10
                (.node 32874582850384470857144497730310777 (.basic (.groups [37, 43, 4933])) -- 3^8 * 13^4 * 757^2 * 14713 * 7^4 * 1051^2 * 2801^2
                  (.node 29721601045632199436644945713857037 (.basic (.split 127)) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^2 * 19^2
                    (.node 26826365624068831964275317990468573 (.basic (.groups [631, 4933, 6765811783780036261])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^12 * 43^2
                      (.node 26562033706441055158647240923401317 (.basic (.groups [757, 12346432697])) -- 3^8 * 13 * 7^2 * 19^2 * 127^12
                        (.node 26185824527134422621589440939484569 (.basic (.split 131)) .empty .empty)
                        .empty)
                      (.node 29142233317826312817705094788131061 (.cut 5 13 803875755036835758301) -- 3^10 * 23^4 * 3851^2 * 13^2 * 61 * 31^2 * 331^4
                        (.node 28227583646471174038789629675404097 (.basic (.groups [31, 127, 12503, 14083, 1205476469])) .empty .empty)
                        .empty))
                    (.node 30482585156073346768284243667410573 (.basic (.groups [2801, 88009573, 132197305635599])) -- 3^6 * 1093 * 547^6 * 7^4 * 29^6
                      (.node 30461570897817852129240669122259813 (.basic (.split 7)) -- 3^6 * 1093^5 * 547^6
                        (.node 30180115876617002110531356035767917 (.basic (.split 151)) .empty .empty)
                        .empty)
                      (.node 32478164413260860240122526484696081 (.basic (.split 151)) -- 3^2 * 13^6 * 5229043^4
                        (.node 31205945429568477700854736918255209 (.basic (.groups [5, 41, 1693, 3221, 4271])) .empty .empty)
                        .empty)))
                  (.node 39977100614360177514728570128308489 (.basic (.split 743)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^6
                    (.node 36232249845802242733341901361852733 (.basic (.groups [2663, 4933, 3500201])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^10 * 43^4
                      (.node 33188534657807163998359009384385001 (.basic (.groups [181, 631, 13537, 18041])) -- 3^2 * 13^10 * 23^4 * 419^2 * 859^4
                        (.node 32922686319081882455118255008914269 (.cut 5 7 65630546048698884295919) .empty .empty)
                        .empty)
                      (.node 38296131760072137164187373495278633 (.basic (.groups [7, 31, 659, 45319])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^6 * 433
                        (.node 38199463533182480094266465436227721 (.basic (.groups [7, 5233, 3158528101])) .empty .empty)
                        .empty))
                    (.node 43914673461976564055684317369294509 (.basic (.groups [7, 43, 617, 86353])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^6
                      (.node 41923486706689067036140942676331309 (.basic (.groups [617, 701, 1051, 1621])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^6 * 307^4
                        (.node 41124878066396399883383010582069381 (.cut 5 7 479423443408676803427) .empty .empty)
                        .empty)
                      (.node 46579990139858185075172805536883213 (.cut 5 7 16278624231412806340171) .empty .empty))))
                (.node 68688533392537764607293661769503125 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^4 * 5^5
                  (.node 56831989595407873715407856654225925 (.basic (.groups [11, 71, 191, 17351])) -- 3^6 * 1093 * 547^4 * 431^4 * 5^2 * 31^4
                    (.node 52898604262048041930920465364092733 (.basic (.split 11)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^4
                      (.node 52114973306524106555614441961447037 (.basic (.groups [19, 37, 67])) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^8
                        (.node 51370522428958824767824452664799469 (.cut 5 7 102405842606498266131139) .empty .empty)
                        .empty)
                      (.node 56640590832539706452239929764711733 (.cut 5 101 58281615502488922328315681561) -- 3^2 * 13^5 * 7^2 * 19^4 * 61^12
                        (.node 54112868719079888085039986598142677 (.basic (.groups [79, 433, 701, 3499])) .empty .empty)
                        .empty))
                    (.node 64168714868007390107905285162604181 (.cut 5 7 127918627108150153406357) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^12
                      (.node 62329397054363273209595346719142381 (.cut 5 7 231394515482128341590226896107) -- 3^2 * 13^2 * 61 * 31^20
                        (.node 57728288691612577161167793103704573 (.basic (.groups [67, 151, 613, 911])) .empty .empty)
                        .empty)
                      (.node 67382329741336486877497012233690921 (.basic (.groups [29, 211, 859, 883, 11552213])) -- 3^2 * 13^2 * 61^10 * 199^6
                        (.node 66094029277676012497854787138246653 (.basic (.groups [19, 71, 181])) .empty .empty)
                        .empty)))
                  (.node 79244498476117679711868802066206717 (.cut 5 31 22645109479211603662794364469) -- 3^2 * 13^5 * 7^4 * 61^14
                    (.node 74035733053146392751902692741416897 (.basic (.groups [7, 19, 43, 127, 1051])) -- 3^8 * 13^4 * 757^2 * 14713^5
                      (.node 72438681160068167989702735620266997 (.basic (.groups [43, 433, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^2 * 19^10
                        (.node 68699181438729529840570584040290405 (.basic (.split 24517)) .empty .empty)
                        .empty)
                      (.node 78208465418028239691290502744652869 (.basic (.split 811)) -- 3^4 * 11^12 * 1093^2 * 398581^2 * 1621
                        (.node 75866157921469403687638056268685229 (.cut 5 7 295421012742161580084724219) .empty .empty)
                        .empty))
                    (.node 83599621657709184525942747570895173 (.basic (.groups [127, 577, 3313, 293459])) -- 3^2 * 13 * 7^10 * 1123^8
                      (.node 80987680307932777031590025069933133 (.basic (.groups [5419, 257611, 293459, 467791631])) -- 3^2 * 13 * 7^10 * 1123^2 * 127^2 * 3313^4
                        (.node 80155384316092276224753660704844669 (.cut 5 7 53251738905034341089053) .empty .empty)
                        .empty)
                      (.node 83829961072381965071866891906640625 (.basic (.groups [19, 31, 829])) .empty .empty)))))
              (.node 170312978767707861744298467168459261 (.basic (.groups [7, 19, 23, 89, 703207451121161180833])) -- 3^2 * 13^2 * 61 * 31^2 * 331^10 * 11^2
                (.node 120567194274423610993761178534301373 (.basic (.groups [67, 4933, 40911050578149780601])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^12
                  (.node 101883497564478499138609224420127761 (.basic (.groups [967, 6038099, 20241187, 3664405207])) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^10
                    (.node 96399354027630726884650705403688837 (.basic (.groups [151, 911, 732541])) -- 3^6 * 1093 * 547^6 * 7^2 * 19^4 * 29^4
                      (.node 90711670082626953133041897720611793 (.basic (.groups [71, 4933, 3500201])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2 * 37^6 * 43^4
                        (.node 86981066324417676590154454566801609 (.basic (.groups [4733, 14939, 88009573])) .empty .empty)
                        .empty)
                      (.node 101242743656938095840421638659168601 (.basic (.groups [1141081, 5229043, 168820969])) -- 3^10 * 23^4 * 3851^2 * 13^6 * 292561^2
                        (.node 97021384729782947799338066245564941 (.basic (.split 5)) .empty .empty)
                        .empty))
                    (.node 109442277014299684511043431755111437 (.basic (.split 70001)) -- 3^2 * 13 * 7^6 * 29^4 * 4733^6
                      (.node 104983177448936132218101315588012693 (.basic (.split 911)) -- 3^2 * 13 * 7^2 * 19^4 * 151^12
                        (.node 102694566721130351141113258094864529 (.basic (.groups [13, 1123, 9631, 293459])) .empty .empty)
                        .empty)
                      (.node 120378806795264070461596040351155293 (.basic (.groups [4933, 26881, 579883, 3500201])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^4 * 761^2
                        (.node 114250745692645627483342728190387845 (.basic (.groups [23, 67])) .empty .empty)
                        .empty)))
                  (.node 151548971102011437568446567611557593 (.basic (.groups [7, 13, 31, 37])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^5
                    (.node 134059149144311500870678133670771009 (.basic (.groups [5, 5839, 45319])) -- 3^4 * 11^6 * 43^6 * 7^4 * 2801^4
                      (.node 131898566848020855659783603731351413 (.basic (.groups [5, 11, 397])) -- 3^6 * 1093 * 547^4 * 431^2 * 7^4 * 67^2 * 31^4
                        (.node 128164247435842989831412198030045053 (.basic (.groups [7, 43, 52379047267])) .empty .empty)
                        .empty)
                      (.node 141364895772889184877060906859102089 (.basic (.split 19)) -- 3^2 * 13^2 * 61^12 * 187123^2
                        (.node 136229930695589585454307358708586741 (.basic (.groups [5, 11, 73, 97, 17351, 32668561])) .empty .empty)
                        .empty))
                    (.node 162797965566997027544636842028467341 (.basic (.groups [5, 13, 67])) -- 3^6 * 1093^6 * 7^2 * 19^4 * 29^5
                      (.node 155694937565241795564237151914101829 (.basic (.split 191)) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941
                        (.node 154973833109096011651252231526496069 (.basic (.groups [307, 617, 911, 1499])) .empty .empty)
                        .empty)
                      (.node 167534794319956837962298646451663969 (.basic (.groups [7, 433, 9697, 144409])) .empty .empty))))
                (.node 208027101497991936502288767677981397 (.cut 5 101 1936234373223183294421357) -- 3^6 * 1093 * 547^6 * 7^4 * 29^2 * 13^6
                  (.node 187740798712402462235827980195693177 (.basic (.groups [29, 31, 4733, 12503])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433 * 7^6
                    (.node 183672339559356104257167283131806409 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^4 * 19^2
                      (.node 176898407577723199388784449147868081 (.basic (.groups [43, 151, 967])) -- 3^12 * 797161^2 * 61^2 * 13^2 * 97^6
                        (.node 171074497531957963926155477553125241 (.basic (.groups [61, 151, 691, 398581, 22996651, 919630771])) .empty .empty)
                        .empty)
                      (.node 187670506113219654702046448895481893 (.basic (.groups [86353, 162709, 6038099])) -- 3^2 * 13 * 7^2 * 19^2 * 127^6 * 43^10
                        (.node 183801071530973856227888965702956417 (.basic (.groups [31, 4733, 8269])) .empty .empty)
                        .empty))
                    (.node 197677462910146567444278433958367717 (.basic (.groups [29, 4733, 17923])) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^6
                      (.node 188212084429332632174407118049176709 (.basic (.groups [617, 733, 5419, 3500201])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^2 * 43^4
                        (.node 188123750801091245569921507255169457 (.basic (.split 23)) .empty .empty)
                        .empty)
                      (.node 208001393370473516966826947251187001 (.basic (.split 229)) .empty .empty)))
                  (.node 234672418782455704821331936044054381 (.cut 5 257 90832226560518544568017) -- 3^12 * 797161^2 * 61 * 31^2 * 151^6
                    (.node 218568329095043293377003400557660381 (.basic (.groups [917087137, 50689400581, 52379047267])) -- 3^2 * 13^2 * 61^13 * 31^6
                      (.node 216391345580895585890702120375114493 (.basic (.split 271)) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2 * 43^2
                        (.node 214992551314177613980331816778179409 (.basic (.split 6619231)) .empty .empty)
                        .empty)
                      (.node 227403896225292616187910587823228141 (.basic (.groups [307, 617, 1270657])) -- 3^6 * 1093^2 * 398581 * 17^8 * 19^2 * 127^4
                        (.node 224575780435560779252053305386432997 (.basic (.groups [127, 88009573, 132197305635599])) .empty .empty)
                        .empty))
                    (.node 247496922879998511250081951054634889 (.basic (.groups [19, 9631, 30941])) -- 3^12 * 797161 * 398581^2 * 1621^2 * 7^2 * 13^4
                      (.node 240904822173847541241191794975774761 (.cut 5 31 2518363848664908036233424611) -- 3^12 * 797161^2 * 61^10
                        (.node 236295396956654483995245323514255993 (.basic (.split 17)) .empty .empty)
                        .empty)
                      (.node 247892824037860192682981081556572205 (.basic (.groups [7, 17293, 21491])) .empty .empty))))))
            (.node 873672107669962600993499316563879373 (.basic (.groups [379, 3511, 14713])) -- 3^8 * 13^4 * 757^5 * 163^6
              (.node 503656320714742120800121191100997001 (.cut 5 31 76614132384700604550625163) -- 3^10 * 23^2 * 7^4 * 79^4 * 2801^5
                (.node 368932118992728642154711681585011369 (.basic (.groups [3798019, 5229043, 262209281])) -- 3^8 * 13^6 * 757^2 * 14713^2 * 19^2 * 127^4
                  (.node 308204442068404337079428576350409337 (.cut 5 7 155375954510929591951673) -- 3^12 * 797161^2 * 61^2 * 13^4 * 97^5
                    (.node 273665350943029263369831083164946133 (.basic (.groups [3169, 30941, 570821])) -- 3^8 * 13^4 * 757 * 379^2 * 61^2 * 97^2 * 787^4
                      (.node 267305243675585334220656984640493025 (.basic (.split 31)) -- 3^12 * 797161 * 398581^4 * 5^2
                        (.node 256548258239663703782150886972913893 (.basic (.groups [367, 1811, 45319, 1768661])) .empty .empty)
                        .empty)
                      (.node 288212061974760259578918937193762349 (.cut 5 7 89325640054852587221) -- 3^10 * 23^4 * 3851^2 * 13^4 * 30941 * 191^4
                        (.node 277682785922299073125899869857690353 (.cut 5 7 25739430314462498133309702403) .empty .empty)
                        .empty))
                    (.node 324907212717015596704710522676087533 (.cut 5 13 225076612980215772016134211) -- 3^2 * 13^4 * 30941^2 * 157^5 * 7^12
                      (.node 324097729360969081473173294612079453 (.basic (.groups [61, 157, 2801, 9631])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^5
                        (.node 311042372627615049022044982900203297 (.basic (.groups [113, 3823, 293147])) .empty .empty)
                        .empty)
                      (.node 365809664889693438720841641680571933 (.basic (.split 433)) -- 3^2 * 13^4 * 30941^2 * 157 * 79^10
                        (.node 343442666962688823036468308847515625 (.basic (.split 19531)) .empty .empty)
                        .empty)))
                  (.node 464693228695132414831182372959810241 (.basic (.split 5)) -- 3^12 * 797161 * 398581^2 * 1621^4
                    (.node 377738813164913837282027534549100561 (.basic (.groups [43, 1811, 8269, 14083, 45319])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^4 * 11^6
                      (.node 373405396016919368350291203008035929 (.basic (.groups [29, 14939, 104281])) -- 3^6 * 1093^6 * 7^2 * 19^10
                        (.node 371090828022731520694729220446263117 (.basic (.groups [37, 1693, 2801, 14083])) .empty .empty)
                        .empty)
                      (.node 419716594760777506139726785139018613 (.cut 5 31 93253302311690918825024780411) -- 3^2 * 13 * 7^10 * 1123^4 * 41^8
                        (.node 392341506396021027436907628464982921 (.basic (.groups [61, 151, 911, 9631, 32668561])) .empty .empty)
                        .empty))
                    (.node 477222962666968596324770192235909969 (.basic (.groups [31, 313, 1009, 3500201, 5390701])) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^2 * 5419^2
                      (.node 470824307354041238934879485361190317 (.cut 5 101 4111217130393536613948041) -- 3^10 * 23^4 * 3851^2 * 13 * 7^4 * 2801^4
                        (.node 469240449140621731841836466389826049 (.basic (.groups [31, 433, 1093])) .empty .empty)
                        .empty)
                      (.node 491271761067392706082483021117645293 (.basic (.groups [5, 11, 211])) .empty .empty))))
                (.node 594225507969945399643478021989181637 (.cut 5 7 21425992279223287208423) -- 3^8 * 13^4 * 757 * 379^2 * 61^2 * 97^8
                  (.node 557738042398481972317674375469908261 (.basic (.split 3217)) -- 3^2 * 13^2 * 61 * 31^2 * 331^6 * 2180921^2
                    (.node 528780360780441627579729105639442317 (.basic (.groups [11, 41, 1693, 4271, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^2 * 37^4
                      (.node 528627021018258966504258164083747101 (.basic (.groups [617, 292561, 150332843])) -- 3^2 * 13^2 * 61 * 31^10 * 23^4 * 397^4
                        (.node 528077444721830334300873671683940025 (.basic (.split 331)) .empty .empty)
                        .empty)
                      (.node 548915635390152914047190636891919729 (.basic (.split 97)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2
                        (.node 541519566649680374245776882786381009 (.basic (.split 2801)) .empty .empty)
                        .empty))
                    (.node 586119388105711393016268449632854213 (.basic (.groups [29251, 133338869, 46268622795238201])) -- 3^2 * 13 * 7^2 * 19^12 * 599^6
                      (.node 577947608663493892828413860363592405 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5 * 11^2
                        (.node 567675519280067014127636403198301749 (.basic (.groups [5, 617, 911])) .empty .empty)
                        .empty)
                      (.node 593035953310226697527833131789261729 (.basic (.split 3571)) -- 3^2 * 13^2 * 61^16 * 103^2
                        (.node 587374283554440504388890332101455573 (.basic (.groups [613, 761, 26881])) .empty .empty)
                        .empty)))
                  (.node 684868983580137061255517756600873733 (.cut 5 13 3645708490664256036750259) -- 3^6 * 1093 * 547^2 * 163^8 * 7^8
                    (.node 617387945806526183873999883655460361 (.basic (.split 127)) -- 3^4 * 11^10 * 15797^2 * 1806113^2 * 19^2
                      (.node 604656283803494617394065697308940349 (.basic (.groups [3169, 3931, 5419, 88741])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^2 * 97^2
                        (.node 597053314735014352095468864011975625 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 657474962503306529284132277150246853 (.basic (.groups [761, 2801, 14939])) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13 * 67^4
                        (.node 631378614015273104760508485835849677 (.basic (.split 131)) .empty .empty)
                        .empty))
                    (.node 782215053811538942008786977316388313 (.cut 5 31 3577582015992978819743) -- 3^8 * 13^6 * 757^2 * 14713 * 7^4 * 1051^4
                      (.node 758636374377572626710642075648602757 (.basic (.groups [67, 151, 613])) -- 3^6 * 1093 * 547^2 * 163^8 * 7^2 * 19^4
                        (.node 755431114127780333908432793504743749 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 789048867800447705192754633905042577 (.basic (.groups [31, 8269, 14083])) .empty .empty)))))
              (.node 1559256926054538553864514708610440133 (.cut 5 7 36537887638072793456324509) -- 3^4 * 11^12 * 1093 * 547^2 * 163^6
                (.node 1036507726800570165155583551057062269 (.basic (.groups [97, 3931, 88741, 262209281])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^4 * 617^2
                  (.node 973562837902982584951163210667617769 (.basic (.groups [23, 397, 617, 4051, 72577051])) -- 3^2 * 13^6 * 5229043^2 * 31^10
                    (.node 938393130458156661188721843661992609 (.basic (.split 7)) -- 3^6 * 1093^10 * 23^2
                      (.node 927393459630270524338151630854858293 (.basic (.groups [67, 1693, 2801, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^2 * 37^2 * 7^4
                        (.node 923515917399923750268546092272097049 (.basic (.groups [151, 911, 3798019])) .empty .empty)
                        .empty)
                      (.node 970432590320478182490476471326212669 (.cut 5 13 479140695986600290283) -- 3^8 * 13^2 * 61 * 31^6 * 757^2 * 14713^2 * 19^4
                        (.node 945936025281488107478749522872803121 (.basic (.groups [7, 67, 1693, 12503, 14083, 1205476469])) .empty .empty)
                        .empty))
                    (.node 1017019091405953336574486567065082517 (.basic (.split 7561)) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^2 * 39103^2
                      (.node 1010826515598551988762715697569670037 (.basic (.split 7)) -- 3^6 * 1093 * 547^10 * 23^2
                        (.node 1007398189776147869367500471386791849 (.basic (.groups [5, 11, 41])) .empty .empty)
                        .empty)
                      (.node 1026100508443463067864409773271130589 (.basic (.groups [11, 23, 89])) -- 3^8 * 13^2 * 61 * 31^2 * 331^10
                        (.node 1019493907072894676308983980239723401 (.cut 5 13 3056562844966194187) .empty .empty)
                        .empty)))
                  (.node 1492616973993074754332792786990730837 (.basic (.groups [19, 29, 398581, 1193557, 132197305635599])) -- 3^6 * 1093^5 * 547^6 * 7^2
                    (.node 1320882096463651556540784117161207757 (.cut 5 31 2795392907668118698861) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^6 * 67^6
                      (.node 1221599133745191153245037802768607169 (.basic (.groups [29, 4733, 9631, 30941])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^6 * 13^4
                        (.node 1038830699861750596685417969278360401 (.basic (.groups [5, 3169, 22996651])) .empty .empty)
                        .empty)
                      (.node 1457089875470550957884262190129890573 (.basic (.split 43)) -- 3^2 * 13 * 7^4 * 2801^8 * 37^2
                        (.node 1339373146317321055360625694674986437 (.basic (.groups [631, 883, 4933])) .empty .empty)
                        .empty))
                    (.node 1548517477096733223594808045701459981 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^2 * 1621^5
                      (.node 1493646672647593991645927939703118077 (.cut 5 13 55066696315360345001811391) -- 3^6 * 1093 * 547^6 * 7^6 * 29^6
                        (.node 1492879117935413592088161148789390881 (.basic (.groups [13, 67, 2801])) .empty .empty)
                        .empty)
                      (.node 1555323857049105325972828866923096445 (.basic (.groups [13, 2289401, 19218301, 168820969])) .empty .empty))))
                (.node 2425534618244573694983451656139123525 (.basic (.split 31)) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^2
                  (.node 2229437671750840309913731595022263637 (.cut 5 31 203829952652716550291) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4 * 19^2 * 67^8
                    (.node 1641791622369229867139541593842710189 (.basic (.groups [617, 631, 733, 262209281])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^4 * 307^2 * 43^2
                      (.node 1606996151325430871122260460585146501 (.basic (.groups [97, 911, 3931])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^4 * 151^2 * 7^2 * 617^2
                        (.node 1574924970872512135944352254617085321 (.basic (.groups [5, 911, 30941])) .empty .empty)
                        .empty)
                      (.node 1725310388310190482380351346052181613 (.basic (.groups [4933, 5839, 158341])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^6 * 67^6
                        (.node 1669760022780978905617620334950510333 (.basic (.groups [7, 79, 613, 579189657172292026411])) .empty .empty)
                        .empty))
                    (.node 2280190425631657507693966695636702429 (.cut 5 101 26295888588444072546605879) -- 3^2 * 13^2 * 61^5 * 7^4 * 31^6 * 97^6
                      (.node 2239139412795355990339048075243308681 (.basic (.split 433)) -- 3^2 * 13^4 * 30941^2 * 157^10
                        (.node 2232896834883491998552857557211685245 (.basic (.groups [7, 43, 21491, 86353])) .empty .empty)
                        .empty)
                      (.node 2382917360607389776605557296809249693 (.basic (.groups [570821, 672901, 52379047267])) .empty .empty)))
                  (.node 2875180384172838103366418812411138917 (.basic (.groups [31, 43, 547, 45319])) -- 3^6 * 1093^9 * 11^6
                    (.node 2585193570250795617158632302563694093 (.basic (.groups [11, 191, 281])) -- 3^8 * 13^6 * 757^9
                      (.node 2553633692019681221225107656110904813 (.cut 5 13 122342069985979078422715181) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^10
                        (.node 2450864250063044988422603303976993549 (.basic (.groups [37, 307, 617, 2179])) .empty .empty)
                        .empty)
                      (.node 2731936666716534734558213260295435301 (.cut 5 7 30746803008161789702119929257) -- 3^2 * 13^14 * 61 * 31^2 * 331^6
                        (.node 2689515839275022789083188694753423605 (.basic (.split 79)) .empty .empty)
                        .empty))
                    (.node 3208840487977664410242206018943051657 (.basic (.split 211)) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^6 * 71^2
                      (.node 2985266573675071760477344320059878125 (.basic (.groups [7, 11, 31, 32668561, 125613804731])) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^5
                        (.node 2878011415312761564624772184505294213 (.basic (.groups [397, 2801, 175897])) .empty .empty)
                        .empty)
                      (.node 3217609901180913170103125774928402021 (.basic (.groups [2801, 5233])) .empty .empty)))))))
          (.node 43293494420126994170556673314892335549 (.cut 5 13 214424087029274667636472631651) -- 3^6 * 1093^6 * 7^4 * 29^9
            (.node 11617330717378310370779559323995256025 (.basic (.groups [11, 31, 32668561, 125613804731])) -- 3^12 * 797161 * 398581^2 * 1621^4 * 5^2
              (.node 7655208259980689700816393302821423605 (.basic (.groups [7, 19, 31, 577, 178601])) -- 3^12 * 797161^4 * 5 * 2671^2
                (.node 4785997986582918623162895465673105041 (.basic (.split 211)) -- 3^6 * 1093^8 * 56773^2
                  (.node 4156604466918972654370117272411037293 (.basic (.groups [5, 41, 3181, 62060021, 181345750520141])) -- 3^2 * 13 * 7^2 * 19^10 * 104281^4
                    (.node 3974574316004811612308219610674890809 (.basic (.groups [31, 313, 1009, 30941])) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^2 * 5419^2
                      (.node 3775919396977785801803423167108880289 (.basic (.groups [41, 43, 1693, 4271])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^4 * 11^6
                        (.node 3337938385806307753801517746601458053 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 3989562521643563573525009279303745801 (.basic (.split 127)) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^2
                        (.node 3980921607126166266322499368076839173 (.cut 5 31 35821942599371036274300269) .empty .empty)
                        .empty))
                    (.node 4306994961528132947153826114836834493 (.basic (.groups [5419, 732541, 132197305635599])) -- 3^6 * 1093 * 547^6 * 7^2 * 19^2 * 29^4 * 127^2
                      (.node 4227639182508890194509863478062339289 (.basic (.groups [7, 86353, 162709, 3500201])) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^6
                        (.node 4213270481692598059151252829957032889 (.basic (.groups [2801, 9631, 5229043, 32668561])) .empty .empty)
                        .empty)
                      (.node 4721141001442913798794468418825552889 (.basic (.groups [151, 911, 14939])) -- 3^6 * 1093^6 * 7^2 * 19^4 * 29^6
                        (.node 4508132982664151280625421992229083437 (.basic (.groups [11, 31, 613, 1301, 1601])) .empty .empty)
                        .empty)))
                  (.node 6412150952819015198992731054542681037 (.cut 5 13 24810625134166424892789745271) -- 3^6 * 1093 * 547^6 * 7^2 * 19^10
                    (.node 5032033769335387205914549646648361921 (.basic (.groups [13, 9631, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^12
                      (.node 4954798686689744944968677368352810025 (.basic (.groups [11, 2671, 17351, 178601])) -- 3^12 * 797161^4 * 5^2 * 31^4
                        (.node 4789604437864771403179201800333208401 (.basic (.groups [71, 733, 1693])) .empty .empty)
                        .empty)
                      (.node 6400731115707813073641376309055220693 (.basic (.groups [7, 19, 1811, 14083, 1768661])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^4 * 11^2
                        (.node 6381585865891368123136502918667508557 (.basic (.split 613)) .empty .empty)
                        .empty))
                    (.node 6708014450236132529343277168155301677 (.cut 5 13 1261852969814653) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2 * 787^2 * 37^6
                      (.node 6682631091889633355516424616012325625 (.basic (.groups [11, 71, 1866871, 2703853428809791])) -- 3^12 * 797161 * 398581^4 * 5^4
                        (.node 6605373752514845000273469382155213057 (.cut 5 13 32752316823764710174669) .empty .empty)
                        .empty)
                      (.node 7210517128679843891303645918580555717 (.cut 5 7 15234936741658889057) .empty .empty))))
                (.node 9505061482671473837651913990936412701 (.cut 5 7 2207489616985851512924287) -- 3^12 * 797161^2 * 61 * 31^6 * 151^4
                  (.node 8647670911638310662284429541854669829 (.basic (.groups [331, 2801, 9631, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61 * 31^2
                    (.node 8242265653421692025601423351682743249 (.basic (.groups [523, 18041, 116803, 246247])) -- 3^2 * 13^10 * 23^4 * 419^2 * 859^2 * 13537^2
                      (.node 8212965218970496373543205376699816689 (.basic (.groups [71, 859, 1609669])) -- 3^2 * 13^8 * 61^10 * 199^4
                        (.node 8081598228241642264774495318225376133 (.basic (.groups [127, 1093, 2683, 3727, 830833])) .empty .empty)
                        .empty)
                      (.node 8586066674067220575911707721187890625 (.basic (.groups [19, 31, 829, 1866871, 2703853428809791])) -- 3^6 * 1093^2 * 398581^4 * 5^8
                        (.node 8335732383960828765790983289968858849 (.basic (.groups [433, 733, 45319, 279067340218231])) .empty .empty)
                        .empty))
                    (.node 9045528419663988302375369057556665721 (.cut 5 31 126079843806067517077937917) -- 3^12 * 797161^2 * 61^6 * 151^4
                      (.node 8760942185001950321580708800560104021 (.basic (.split 17)) -- 3^6 * 1093^2 * 398581^5
                        (.node 8674239841618306909681051856841259197 (.basic (.groups [30941, 900329, 1129019])) .empty .empty)
                        .empty)
                      (.node 9229267706124789372968339939380592613 (.basic (.groups [127, 1693, 12503, 14083, 1205476469])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2 * 37 * 19^2
                        (.node 9199299136907720649555571029588965673 (.basic (.groups [19, 31, 37])) .empty .empty)
                        .empty)))
                  (.node 10895021831458737761901819528912218037 (.basic (.groups [701, 9631, 70841, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13 * 19^6
                    (.node 10190157696376093828003056312820879017 (.basic (.groups [31, 151, 911, 12503])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433 * 7^2 * 19^4
                      (.node 10169336676043921229546507093220805773 (.basic (.groups [11, 89, 631])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^10
                        (.node 9686195682597181804769643263960018133 (.cut 5 13 252753693468706750206871) .empty .empty)
                        .empty)
                      (.node 10729497977473223996628825402702390357 (.basic (.groups [151, 911, 17923])) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^2 * 19^4
                        (.node 10618759983410260502729484977374315329 (.basic (.groups [11, 191, 1153])) .empty .empty)
                        .empty))
                    (.node 11465030635631797149473943331961013717 (.cut 5 257 164812855286981777930964148007) -- 3^8 * 13 * 7^2 * 19^6 * 701^8
                      (.node 11058383404112490463981836037047257133 (.basic (.groups [7, 29, 232919, 1806113])) -- 3^4 * 11^10 * 15797 * 2633^6
                        (.node 10998558399483353198853595402305512409 (.basic (.groups [13, 67, 127])) .empty .empty)
                        .empty)
                      (.node 11579831554318652557331861852311931529 (.basic (.groups [89, 30941, 6654649, 104476284376746280087])) .empty .empty)))))
              (.node 20839912217672140355181573310437350853 (.basic (.groups [67, 613, 701])) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^2 * 19^6
                (.node 15330557723546046585148373529639258957 (.basic (.split 3090276117871)) -- 3^2 * 13 * 7^2 * 19^16 * 3044803^2
                  (.node 13031981315569964918876876914112039853 (.cut 5 101 89397010530839245863578371313) -- 3^2 * 13^5 * 7^2 * 19^4 * 61^6 * 151^6
                    (.node 12512038885981740375071555073299455593 (.basic (.groups [7, 19, 43, 127])) -- 3^8 * 13^6 * 757^2 * 14713^5
                      (.node 12510349427366200622153311782637970277 (.basic (.groups [37, 163, 199])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^8
                        (.node 11776689730904260617109714878564659001 (.basic (.groups [127, 5390701, 40911050578149780601])) .empty .empty)
                        .empty)
                      (.node 12691340630511227012092767719726113101 (.basic (.groups [7, 43, 617])) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2 * 127^6
                        (.node 12655063979025527897202458037050954757 (.basic (.groups [89, 2801, 6654649])) .empty .empty)
                        .empty))
                    (.node 14531483906245899428501259760464052209 (.basic (.groups [19, 61, 9631, 1609669])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^8
                      (.node 14190923815834768401171687447886306317 (.cut 5 31 49461653775846884392217) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^6 * 29^8
                        (.node 14092855804242711875018662549977850569 (.basic (.split 3500201)) .empty .empty)
                        .empty)
                      (.node 14926332868375358802386721600299390625 (.basic (.split 11)) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^6
                        (.node 14709121984592068775850143414653483521 (.basic (.groups [1693, 5113, 8269, 14083, 37140797])) .empty .empty)
                        .empty)))
                  (.node 17822197272227807744142066946019312757 (.basic (.groups [5, 11, 41, 761])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^4 * 631^4
                    (.node 16582225052111235392093132723455648089 (.basic (.groups [37, 659, 1693, 45319])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^6 * 433^2
                      (.node 16559944209660939306301836465426321201 (.basic (.groups [37, 43, 4933, 14939])) -- 3^6 * 1093^6 * 7^4 * 29^4 * 2801^2
                        (.node 15880788738687484992185491435991893197 (.basic (.groups [29, 61, 157])) .empty .empty)
                        .empty)
                      (.node 17378279069024136775228421940598793157 (.basic (.groups [211, 883, 1597, 21020917, 2884629032993])) -- 3^2 * 13 * 7^4 * 2801^6 * 71^6
                        (.node 17299824564090609646756428858840479889 (.basic (.split 5471551)) .empty .empty)
                        .empty))
                    (.node 20607870430892651271060114527383570581 (.basic (.groups [5, 23, 89, 3221])) -- 3^2 * 13^2 * 61 * 31^2 * 331^10 * 11^4
                      (.node 19278927213854504015446924863645381393 (.basic (.groups [11, 41, 101])) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^6 * 4733^4
                        (.node 18182030784411090495572212475270885733 (.cut 5 257 938408681088378898592153123) .empty .empty)
                        .empty)
                      (.node 20714378723739197090236624606503854157 (.cut 5 31 308300389677023649827993698217) .empty .empty))))
                (.node 32648225343201841274261715220829276049 (.basic (.groups [43, 337, 1806113, 11704523461, 91626924397])) -- 3^4 * 11^10 * 15797^6
                  (.node 26534458765834338338043067256532669441 (.basic (.split 29)) -- 3^2 * 13^4 * 30941^6 * 7^6
                    (.node 24464448509391918631217927116892676429 (.basic (.split 5419)) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^4
                      (.node 23394101632278068350666335828972033081 (.basic (.groups [181, 631, 13267, 4772771, 4242586390571])) -- 3^2 * 13^2 * 61^10 * 199^2 * 859^4
                        (.node 21203308590365447445500872624620636957 (.basic (.groups [127, 397, 175897])) .empty .empty)
                        .empty)
                      (.node 26150363898784608644282687558916385917 (.cut 5 101 14246473773380685666859) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^2 * 19^12
                        (.node 25635854116257684632127048924292291893 (.cut 5 13 191849054104724070803817340519) .empty .empty)
                        .empty))
                    (.node 30985119374753840352092593031190565161 (.basic (.groups [11, 79, 131, 5581])) -- 3^2 * 13^2 * 61^2 * 97^12 * 53^4
                      (.node 28071230202125432317729428389910911709 (.basic (.groups [11, 191, 2521])) -- 3^8 * 13^2 * 61 * 31^2 * 331^6 * 757^4
                        (.node 27191416021833675599241857350099822197 (.cut 5 31 2689715708891048642477006657639) .empty .empty)
                        .empty)
                      (.node 31040625385531181619461270849275283121 (.basic (.groups [127, 9631, 5229043, 32668561])) .empty .empty)))
                  (.node 39340615709398581465266108712776363757 (.basic (.groups [31, 313, 1009])) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^2 * 127^2 * 5419^2
                    (.node 37628690240753872408617678102893145237 (.basic (.groups [11, 631, 1811, 2801])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4 * 43^2 * 433^4
                      (.node 35210095545761658398303814865589635329 (.basic (.groups [7, 43, 30941])) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^6
                        (.node 32986926044788628127918061318294899729 (.basic (.groups [1051, 1621, 1811, 5231])) .empty .empty)
                        .empty)
                      (.node 39313033911578553535812502930092643161 (.basic (.groups [5, 631, 37861])) -- 3^6 * 1093^4 * 11^6 * 31^2 * 43^2 * 331^4
                        (.node 38750822179187782806837680564101153149 (.basic (.groups [97, 631, 733, 3931])) .empty .empty)
                        .empty))
                    (.node 42930333370336102879558538605939453125 (.basic (.groups [11, 71, 521, 1866871])) -- 3^6 * 1093^2 * 398581^4 * 5^9
                      (.node 41826979966719748401263849728233296241 (.cut 5 31 1645218562701111613) -- 3^12 * 797161 * 398581^2 * 1621^2 * 7^2 * 13^6
                        (.node 41261463245826510160890249092123693361 (.basic (.groups [5419, 3798019, 52379047267])) .empty .empty)
                        .empty)
                      (.node 43238763375259597439247497622172448601 (.basic (.groups [5, 11, 211, 859])) .empty .empty))))))
            (.node 167065777297240833887910615400308140625 (.basic (.groups [19531, 1866871, 2703853428809791])) -- 3^12 * 797161 * 398581^4 * 5^6
              (.node 72744361161954626029959631927847227113 (.basic (.groups [5, 2801, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4 * 31^2 * 331^4
                (.node 54615542001186966640506950244711113925 (.basic (.groups [71, 191, 510101])) -- 3^6 * 1093 * 547^4 * 431^4 * 5^2 * 31^6
                  (.node 46249444309371945509501453054875896477 (.cut 5 7 6364958379213458276507) -- 3^8 * 13^6 * 757 * 379^2 * 61^2 * 97^2 * 787^4
                    (.node 45494928200729782133246419676519722893 (.cut 5 13 1069643988099857814436919080099) -- 3^2 * 13 * 7^10 * 1123^2 * 127^10
                      (.node 45442279521883255692569429911888056357 (.basic (.groups [29, 67, 1693])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^2 * 37^2 * 7^6
                        (.node 44787437768528747367211894911157363941 (.basic (.groups [617, 911, 1499])) .empty .empty)
                        .empty)
                      (.node 45981263392449676398247370339437637841 (.basic (.groups [19, 79, 6491, 2608387, 6254429058851062673])) -- 3^6 * 1093^10 * 23^2 * 7^2
                        (.node 45706396392954574311125331680441167881 (.basic (.groups [7, 19, 1811, 8269])) .empty .empty)
                        .empty))
                    (.node 49530499264329047449373069180913831813 (.basic (.groups [19, 79, 10847, 9630092768572369626677])) -- 3^6 * 1093 * 547^10 * 23^2 * 7^2
                      (.node 47632319081838435385403370920521823229 (.basic (.groups [5, 23, 607127818287731321660577427051])) -- 3^2 * 13^2 * 61^18 * 229
                        (.node 47183496377133569022839006889515687961 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 53244816632844832662577491778516213713 (.basic (.split 2801)) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2 * 97
                        (.node 49601950038903270301945062964376391477 (.cut 5 31 116821831878509622834989478113) .empty .empty)
                        .empty)))
                  (.node 66993429964888346813949175618065703317 (.cut 5 31 22540286821652642252086167089) -- 3^2 * 13 * 7^4 * 2801^2 * 37^10 * 43^6
                    (.node 65620704487170952467137363775804437769 (.basic (.groups [733, 743, 5209, 45319])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^6
                      (.node 60638365456114342374586291403478088125 (.basic (.groups [11, 71, 6781, 12774841, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^4
                        (.node 58556092754159529406655024772157745853 (.basic (.groups [5, 31, 271, 337, 433])) .empty .empty)
                        .empty)
                      (.node 66305714580927553636837389210582113649 (.basic (.groups [151, 911, 9631, 30941])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^4 * 19^4
                        (.node 65719726009109566078306159880912932749 (.cut 5 7 346538408219816720350579) .empty .empty)
                        .empty))
                    (.node 68289369720473145874625898495619981977 (.basic (.groups [307, 17707, 17311991, 3597318971])) -- 3^4 * 11^10 * 15797^4 * 1806113 * 17^2
                      (.node 68076886468528348315286817654859285737 (.cut 5 31 1435157229763637511647059) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2 * 37^12
                        (.node 67545140199727910750940438697762347741 (.basic (.groups [191, 3798019, 262209281])) .empty .empty)
                        .empty)
                      (.node 69830595380005722862027569092956503681 (.basic (.groups [467, 9631, 30941, 32668561])) .empty .empty))))
                (.node 122207860134422947108533501418618061397 (.cut 5 31 287822276677069043912978940803) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^10
                  (.node 83863618233020469836208988051607011413 (.basic (.split 613)) -- 3^6 * 1093 * 547^2 * 163^12
                    (.node 79174380554447024242131870170977608213 (.basic (.split 37)) -- 3^2 * 13 * 7^12 * 16148168401^2 * 433^2
                      (.node 75877356377739927956145594239371539069 (.basic (.groups [13, 19, 811, 9631, 2626021, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^5 * 7^2
                        (.node 73138231725660662962306846562545811013 (.basic (.groups [29, 2801, 398581, 1193557])) .empty .empty)
                        .empty)
                      (.node 83686975996039775958915443849692586589 (.basic (.groups [617, 1051, 1621, 5231])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^4 * 307^4
                        (.node 81071856737237441309991243244502311917 (.cut 5 31 1600471120185354831775655347) .empty .empty)
                        .empty))
                    (.node 92040954969026034673787526106048718517 (.basic (.groups [70001, 69655517, 88009573, 329422297])) -- 3^2 * 13 * 7^6 * 29^6 * 4733^6
                      (.node 89028446818113805068975521633760203373 (.basic (.groups [37, 43, 4933, 9631, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13 * 2801^2
                        (.node 84940567233960460243572814257710052237 (.basic (.groups [7, 67, 397, 23839957, 208097431])) .empty .empty)
                        .empty)
                      (.node 118158307505110036166745202073144163405 (.cut 7 13 380061504408954076073010467) -- 3^12 * 797161^2 * 61^4 * 5 * 131^6
                        (.node 99517464173777268906488477337984642753 (.basic (.groups [7, 79, 4591])) .empty .empty)
                        .empty)))
                  (.node 141635283808963590904723653875858834481 (.basic (.groups [61, 701, 9631, 70841])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^2 * 19^6
                    (.node 129549013472608417664779597731116862201 (.basic (.groups [11, 1811, 12503, 14083, 1768661, 1205476469])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^4
                      (.node 126775922442623776539581904949082300649 (.basic (.groups [7, 13, 9631, 32668561])) -- 3^4 * 11^12 * 1093^2 * 398581^2 * 1621^2
                        (.node 126754522740948042289052043185828707893 (.cut 5 13 212217374130252053728859) .empty .empty)
                        .empty)
                      (.node 130916963398461591621589371718951858101 (.basic (.split 73)) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^6
                        (.node 129747849306264968025100919845397447781 (.basic (.groups [617, 911, 1051])) .empty .empty)
                        .empty))
                    (.node 154576701157549013087654620156186346697 (.cut 5 31 680968412226586524422177) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^6 * 29^8
                      (.node 154212068320403644963364333565649298301 (.basic (.split 53)) -- 3^2 * 13^2 * 61 * 31^2 * 331^12
                        (.node 147800268971541769431290877679516544493 (.basic (.groups [11, 19, 41, 1693])) .empty .empty)
                        .empty)
                      (.node 160613121081791520590096299183893627813 (.basic (.split 39103)) .empty .empty)))))
              (.node 329837143222283125044628766008503239121 (.basic (.groups [37, 859, 13537])) -- 3^2 * 13^10 * 23^4 * 419^8
                (.node 222928742213409256727464419109923238677 (.cut 5 31 8333783362462286696626660241) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^14
                  (.node 197670741781416344964904921557478485021 (.basic (.groups [701, 70841, 88741])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^6 * 617^4
                    (.node 188382586996720744907288455952816230089 (.basic (.groups [967, 20241187, 40911050578149780601])) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^12
                      (.node 188049873289673494872316600151145883569 (.basic (.groups [19, 1811, 9439, 45319])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^4 * 733^2
                        (.node 167725877982777236342994468885411205257 (.cut 5 101 169392506017698961499) .empty .empty)
                        .empty)
                      (.node 188909290781196692570516376886032678717 (.basic (.groups [11, 19, 2411])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^9
                        (.node 188868231346306615350976829829990150477 (.cut 5 31 669124484972398785930431501) .empty .empty)
                        .empty))
                    (.node 207417916079431761585609961681657271049 (.basic (.split 502628805631)) -- 3^2 * 13^2 * 61^2 * 97^10 * 89^6
                      (.node 206450253602937304898411388667894611561 (.basic (.groups [29, 4733, 9631])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^6 * 13^6
                        (.node 204243789969173921453117165919488601357 (.cut 5 31 13096353962513312806957) .empty .empty)
                        .empty)
                      (.node 222877048436155952378513957999621190321 (.basic (.groups [151, 911, 249561007, 171686630257])) -- 3^4 * 11^10 * 15797^2 * 1806113^2 * 19^4
                        (.node 214651666851680514397792693029697265625 (.basic (.split 1866871)) .empty .empty)
                        .empty)))
                  (.node 284380504936920648200765786832241555869 (.basic (.groups [823, 877, 1222567, 2426789])) -- 3^2 * 13^2 * 61 * 31^12 * 42407^2 * 1471^2
                    (.node 257986773694509646630471877342707900533 (.basic (.groups [1693, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37 * 19^10
                      (.node 256880339172237506186051362239513797025 (.basic (.split 331)) -- 3^12 * 797161 * 398581^4 * 5^2 * 31^2
                        (.node 236768672181515258223269785511220921309 (.basic (.split 4447)) .empty .empty)
                        .empty)
                      (.node 284368847304487759189771260881426942853 (.basic (.groups [37, 43, 4933])) -- 3^6 * 1093 * 547^6 * 7^4 * 29^4 * 2801^2
                        (.node 273867731150303718242541789309145595277 (.cut 5 31 12750947284904412721851709) .empty .empty)
                        .empty))
                    (.node 299550733045364777729963646255490995741 (.basic (.groups [97, 3931, 25646167])) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2 * 127^4 * 617^2
                      (.node 290433267934457759269488983099881400625 (.basic (.groups [11, 71, 32668561])) -- 3^12 * 797161 * 398581^2 * 1621^4 * 5^4
                        (.node 284846641275961621574584422839720370297 (.cut 5 101 272064876748463948681887) .empty .empty)
                        .empty)
                      (.node 318958193585017242766754266666859859861 (.cut 5 31 9722191736064934948172804077) .empty .empty))))
                (.node 449374934710153826609096395962494688609 (.basic (.groups [691, 701, 17293, 837197335075000483])) -- 3^2 * 13^2 * 61^2 * 97^10 * 89^4 * 131^2
                  (.node 373158321709383970059668040007484765625 (.basic (.groups [11, 19, 31, 829])) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^8
                    (.node 347896826484913410507336676301747808957 (.basic (.groups [7, 19, 31])) -- 3^6 * 1093^9 * 11^8
                      (.node 347645516153720798308689179592082067961 (.basic (.split 62065212901958868055012327674641)) -- 3^2 * 13^2 * 61^2 * 97^16
                        (.node 347002765803343141544083884007746020157 (.cut 5 101 574817045486102469001585636477) .empty .empty)
                        .empty)
                      (.node 348511998474691299144290341347545829717 (.cut 5 13 398304737081250700828031) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^2 * 127^6
                        (.node 348004144109836036890478761272927734941 (.basic (.groups [7, 617, 733])) .empty .empty)
                        .empty))
                    (.node 400107597979075938311908220573586697557 (.basic (.groups [271, 3500201, 15349897, 22406023])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2 * 43^4
                      (.node 393269848390729423786210096577143034637 (.basic (.groups [4733, 9631, 732541])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^6 * 13 * 29^4
                        (.node 375499676753216513938769452411829596209 (.cut 5 101 13281175414209232979267963) .empty .empty)
                        .empty)
                      (.node 402713033942648872246339183160763198117 (.cut 5 7 622505304144602666608213087) .empty .empty)))
                  (.node 507482424377678951263139598488266364025 (.basic (.split 11)) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^4
                    (.node 479379703265001744713646329418800149773 (.basic (.groups [5419, 17923, 18871143464293])) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^2 * 19^2 * 127^2
                      (.node 456886247034312082018214203220174514969 (.basic (.groups [7, 19, 41])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^4 * 11^8
                        (.node 450765657708478311828222980449859317977 (.cut 5 13 2168488039918346241353516927) .empty .empty)
                        .empty)
                      (.node 496409966012364873768833855297194090161 (.basic (.split 6491)) -- 3^6 * 1093^10 * 23^4
                        (.node 489020633681614039577892099162358273509 (.basic (.groups [617, 659, 5419, 1274564409623])) .empty .empty)
                        .empty))
                    (.node 564883141428111494189087680701459125025 (.basic (.groups [7, 2671, 5233, 178601])) -- 3^12 * 797161^4 * 5^2 * 31^2 * 331^2
                      (.node 534727226751634002055476604014355449573 (.basic (.split 10847)) -- 3^6 * 1093 * 547^10 * 23^4
                        (.node 517795815448370157897521223720025380801 (.basic (.groups [56773, 398581, 3158528101])) .empty .empty)
                        .empty)
                      (.node 571736088668671345946509264941632140077 (.basic (.groups [13, 313, 82889, 169693879967, 12560063349523])) .empty .empty))))))))
        (.node 210300222571717353525630135996717724478613 (.cut 5 31 9249955904035774898640945878230217) -- 3^2 * 13 * 7^2 * 19^12 * 599^8
          (.node 6751780030585615440072914126856606628917 (.cut 5 101 2046525065000457257096638427) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^2 * 71^8
            (.node 2430845574096626094345873814584065007153 (.basic (.groups [1051, 1621, 5231])) -- 3^4 * 11^10 * 15797^2 * 1806113 * 17^2 * 307^4
              (.node 1355511459231529090909936353451462541877 (.basic (.groups [5, 1361, 1597, 5113, 292661])) -- 3^2 * 13 * 7^4 * 2801^6 * 71^2 * 211^4
                (.node 799304099220040927581279166992813338409 (.basic (.groups [13, 73, 292561, 1141081])) -- 3^10 * 23^4 * 3851^8
                  (.node 723900313908424588156649145620396531973 (.basic (.groups [71, 1693, 14083, 37140797])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^2 * 37^6
                    (.node 671703059404813162480089114204056546721 (.basic (.groups [31, 313, 1009])) -- 3^8 * 13^6 * 757^2 * 14713^2 * 19^2 * 127^2 * 5419^2
                      (.node 654039837265552803852322208681529191853 (.basic (.groups [11299, 13267, 830833, 7960598843])) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^2 * 1499^2 * 199^2
                        (.node 627165530549664088068342787412179645893 (.basic (.groups [5, 8269, 1956611])) .empty .empty)
                        .empty)
                      (.node 712042711406049071996561728262738558241 (.basic (.groups [61, 2801, 9631])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^8
                        (.node 708299768268220001654132354849351135661 (.basic (.groups [37, 617, 2179])) .empty .empty)
                        .empty))
                    (.node 773973184731531956633563070721666830721 (.cut 5 257 1076800435669188201608257768981) -- 3^2 * 13^2 * 61^20
                      (.node 769499304209195811803248950439447413789 (.basic (.groups [5, 4733, 2384047, 3060947, 17177163455369])) -- 3^2 * 13^4 * 30941^6 * 7^6 * 29
                        (.node 740534626786760874335033726377555342881 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 778742918031176871700127381267781180213 (.basic (.groups [6101, 19571, 293459])) -- 3^2 * 13 * 7^10 * 1123^4 * 41^2 * 1723^4
                        (.node 774488465000645381910606533395681703853 (.basic (.groups [5, 1811, 3221, 14083])) .empty .empty)
                        .empty)))
                  (.node 1002957602060550839195910699105263440533 (.basic (.groups [113, 3169, 2105339491746149])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^2 * 787^6
                    (.node 917452222348366294730833818325827890241 (.basic (.split 583367)) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^4 * 3500201
                      (.node 883303052051137841071721157188819966157 (.cut 5 101 103871811143985534581301914023) -- 3^6 * 1093 * 547^2 * 163^10 * 23^4
                        (.node 858372486515030553527927441393787125493 (.cut 5 7 4546731985822080498382387991) .empty .empty)
                        .empty)
                      (.node 969547365740389143816807816580352658873 (.basic (.groups [7, 31, 14083, 28447, 321910472390668481])) -- 3^2 * 13^4 * 30941^2 * 157^10 * 433
                        (.node 935593887224766264138067845451580676009 (.basic (.groups [4051, 42407, 2426789, 7908811])) .empty .empty)
                        .empty))
                    (.node 1300188479525882578564110295570100802609 (.basic (.groups [19, 37, 1063, 2384047, 3060947])) -- 3^2 * 13^4 * 30941^6 * 7^8
                      (.node 1294986418610357219138408096812867472649 (.basic (.groups [11, 41, 1693, 4271, 12503])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2 * 37^4
                        (.node 1089287740410942876558744318304466805561 (.basic (.split 7673)) .empty .empty)
                        .empty)
                      (.node 1306250295686647760742515514352951502157 (.basic (.groups [257611, 293459, 262209281])) .empty .empty))))
                (.node 2042515079286758993169596359874833311609 (.basic (.groups [5, 131, 2801, 9631])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^4
                  (.node 1516796306185754728262421048684653206209 (.basic (.split 467)) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801
                    (.node 1501199461525435442739555521364574962129 (.basic (.split 4051)) -- 3^2 * 13^6 * 5229043^2 * 31^2 * 331^6
                      (.node 1465946533233493867736097763806172804293 (.cut 5 7 320598674897665626443380190557343) -- 3^8 * 13^6 * 757 * 379^10
                        (.node 1440232070313326450042528349828652234161 (.basic (.split 151)) .empty .empty)
                        .empty)
                      (.node 1515959136402858559364657285086952203125 (.basic (.groups [6781, 19531, 12774841, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^6
                        (.node 1509405326686984069072410766142577517881 (.basic (.groups [73, 12157, 5229043, 26403131021])) .empty .empty)
                        .empty))
                    (.node 1865791608546919850298340200037423828125 (.basic (.groups [11, 71, 521])) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^9
                      (.node 1611956950771405846920509831007633675741 (.basic (.groups [1774921, 917087137, 26403131021])) -- 3^8 * 13^2 * 61 * 31^6 * 757^2 * 14713^4
                        (.node 1534025049291900880441345284181624149561 (.basic (.split 1774921)) .empty .empty)
                        .empty)
                      (.node 1994756039519184261343554938287820194437 (.basic (.groups [11, 41, 43, 4271, 4933])) -- 3^2 * 13 * 7^4 * 2801^8 * 37^4
                        (.node 1956991532679852282189084653040716428401 (.basic (.groups [89, 5229043, 6654649])) .empty .empty)
                        .empty)))
                  (.node 2317102139358756231701130307964465672445 (.basic (.split 541)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^4
                    (.node 2253081906230034143514121146632444254209 (.basic (.groups [79, 2801, 6491, 2608387])) -- 3^6 * 1093^10 * 23^2 * 7^4
                      (.node 2226978444441876660113931794108492171973 (.cut 5 7 2817964579729636303380020420269) -- 3^4 * 11^12 * 1093 * 547^8
                        (.node 2119187929884133075864736033665322889129 (.basic (.groups [13, 131, 937, 58782569, 8209505981, 3778501876319])) .empty .empty)
                        .empty)
                      (.node 2311991322479544882119111337586268710089 (.basic (.groups [19, 1093, 3500201, 27935336611728311])) -- 3^4 * 11^6 * 43^4 * 45319^4 * 151^2 * 7^2
                        (.node 2283018118576576751056772685728449433853 (.basic (.groups [433, 14083, 8346157, 551604349222681])) .empty .empty)
                        .empty))
                    (.node 2393721429013192750704928096722277413093 (.basic (.groups [5, 601, 911])) -- 3^2 * 13 * 7^2 * 19^4 * 151^14
                      (.node 2372101468715011031458019853135509478357 (.basic (.groups [5, 878837, 1956611])) -- 3^8 * 13 * 7^4 * 757^6 * 2801^4
                        (.node 2330938768133035320879097041549697707525 (.basic (.split 331)) .empty .empty)
                        .empty)
                      (.node 2426994463952123325019280389864777758837 (.basic (.groups [79, 2801, 10847])) .empty .empty)))))
              (.node 3951246698618737879089247706301549541941 (.basic (.groups [617, 659, 701])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^6 * 307^6
                (.node 3035672709760706024341012407015171139461 (.basic (.groups [617, 733, 3500201])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^4 * 307^2 * 43^4
                  (.node 2655043454210225127256011206577893700609 (.basic (.split 89)) -- 3^4 * 11^6 * 43^2 * 631^10
                    (.node 2493552322138010803798273857813412040301 (.basic (.groups [23, 43, 89])) -- 3^2 * 13^2 * 61 * 31^2 * 331^10 * 11^6
                      (.node 2476500947540726631361796909454049922013 (.cut 5 101 11903308241423653550519019511) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^4 * 71^6
                        (.node 2455820780155557003416712899518424823321 (.basic (.groups [19, 23, 419])) .empty .empty)
                        .empty)
                      (.node 2531912291465563642936824843361870062069 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581^5 * 17^2
                        (.node 2510146830373804555447183842082066629201 (.basic (.split 211)) .empty .empty)
                        .empty))
                    (.node 2840877008246673431817937077547982821581 (.basic (.groups [5, 37861, 63601])) -- 3^2 * 13^2 * 61^13 * 31^2 * 331^4
                      (.node 2754319835478776931793460416437385019469 (.basic (.groups [5, 31, 70911041])) -- 3^4 * 11^18 * 6115909044841454629
                        (.node 2694159179745048721128000789550167669477 (.basic (.groups [67, 631, 4933, 143879023, 3356457657661])) .empty .empty)
                        .empty)
                      (.node 2951405106677343009956469792127458123117 (.cut 5 257 2162296520949304051164812642677) -- 3^6 * 1093^6 * 7^4 * 29^2 * 13 * 67^6
                        (.node 2850910771385514877248881721779468426493 (.basic (.groups [5, 911, 1693, 8269])) .empty .empty)
                        .empty)))
                  (.node 3667797442217744606494809871000846686189 (.cut 5 7 1017905297086071892531691) -- 3^6 * 1093^2 * 398581 * 17^8 * 19^2 * 127^6
                    (.node 3513069357642699507433383133193318207997 (.basic (.groups [5, 71, 191, 398581, 510101])) -- 3^6 * 1093^5 * 547^4 * 431^4
                      (.node 3331765641911048963641570718116393933293 (.basic (.groups [151, 911, 1693, 12503])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2 * 37 * 19^4
                        (.node 3169004066088873201709581980213294678757 (.basic (.groups [11, 191, 281])) .empty .empty)
                        .empty)
                      (.node 3583773354557372485153035481564744739637 (.basic (.groups [29, 4733, 398581])) -- 3^6 * 1093^5 * 547^6 * 7^6
                        (.node 3533558368720498161660202131035636869269 (.basic (.groups [7, 307, 617])) .empty .empty)
                        .empty))
                    (.node 3873348769867833862783005970375562918877 (.cut 5 31 16796222617636115450481499) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^2 * 19^6
                      (.node 3717990462509256469851134117729205414381 (.basic (.groups [13, 811, 2801, 9631, 2626021])) -- 3^6 * 1093^2 * 398581^2 * 1621^5 * 7^4
                        (.node 3678646928391769871909103328928337325137 (.basic (.groups [31, 701, 12503])) .empty .empty)
                        .empty)
                      (.node 3933102881156604332046556849937310711357 (.basic (.groups [127, 523, 9631])) .empty .empty))))
                (.node 5350765820658772525631189473740483941181 (.cut 5 7 230118399756264943522540081) -- 3^12 * 797161^2 * 61 * 31^2 * 151^8
                  (.node 4994104769156526854723400473006471934777 (.basic (.groups [37, 43, 4933, 143879023, 3356457657661])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^8
                    (.node 4176644432431020847197765385007703515625 (.cut 7 31 129722013004981482119463739) -- 3^12 * 797161 * 398581^4 * 5^8
                      (.node 4045373799594689385678351585143695501449 (.basic (.groups [14939, 732541, 262209281])) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^4 * 127^4
                        (.node 4025692407186941399398038356586779438421 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 4817357063206146396553061717374224691089 (.basic (.groups [157, 433, 14083, 1774921, 26403131021])) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941^2
                        (.node 4761561537908844892114898950987050434025 (.basic (.groups [2671, 178601, 917087137])) .empty .empty)
                        .empty))
                    (.node 5164747213385948768270016702516072730161 (.basic (.groups [2801, 3169, 9631, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2 * 97^2
                      (.node 5112636276066743946046438484796803827977 (.cut 5 31 575945155810463670271979) -- 3^8 * 13^4 * 757^2 * 14713 * 7^4 * 1051^6
                        (.node 5062537942683630564896284860832881592773 (.basic (.split 1499)) .empty .empty)
                        .empty)
                      (.node 5168695050520888028411880118861436265273 (.cut 5 31 12011322325469474152895489) .empty .empty)))
                  (.node 6160313136122941148147709313211096013249 (.basic (.groups [19, 14713, 25875541])) -- 3^8 * 13^2 * 61^6 * 757^8
                    (.node 5530473963547503491646165133333381313601 (.basic (.groups [1811, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^4 * 11^10
                      (.node 5468609951947045468957762474142112146241 (.basic (.groups [1693, 2663, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^10
                        (.node 5366291671292012859944817325742431640625 (.basic (.groups [1866871, 305175781, 2703853428809791])) .empty .empty)
                        .empty)
                      (.node 5689210974307080855060764145979819743741 (.basic (.groups [11, 31, 3931])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^2 * 97^4
                        (.node 5679907017317585943978935538978348823749 (.basic (.groups [7, 31, 1774921, 26403131021])) .empty .empty)
                        .empty))
                    (.node 6414779327407688922011585525634610126689 (.basic (.groups [5, 11, 292561])) -- 3^10 * 23^4 * 3851^2 * 13^4 * 30941^4
                      (.node 6329113659611173778629117792689194315841 (.basic (.groups [5113, 246247, 22199431, 4242586390571])) -- 3^2 * 13^2 * 61^10 * 199^4 * 71^2 * 859^2
                        (.node 6291518428668195034072781695152277682961 (.basic (.groups [11, 10332211, 362759437743508955104646759])) .empty .empty)
                        .empty)
                      (.node 6473270813462589788831502764529428884869 (.cut 5 7 846380911960372283735577012661) .empty .empty))))))
            (.node 45650152338761162399434270341468197114997 (.cut 5 101 327296893283089483372167877) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^12
              (.node 12919393243338986663600602336244265722157 (.cut 5 13 216302248328590947667153187) -- 3^6 * 1093 * 547^4 * 431^2 * 7^4 * 67^8
                (.node 9256555248278637935955302467415601257133 (.cut 5 31 65742475433564083047041) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^9
                  (.node 7728295637009740399243683439326439096773 (.basic (.split 89)) -- 3^2 * 13 * 7^2 * 19^6 * 701^10
                    (.node 7107851352828285161744444154086133934341 (.basic (.split 331)) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^2 * 97^2
                      (.node 7070225619214264484421980936781983487981 (.basic (.groups [5419, 25646167, 145159381141])) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2 * 127^2 * 617^4
                        (.node 7052043164339210095130496093456551809317 (.cut 5 31 90203669842194622031604530711) .empty .empty)
                        .empty)
                      (.node 7523208310579642668220547965067883657933 (.cut 5 31 38919067663850799300508783) -- 3^6 * 1093^5 * 547^2 * 163^2 * 7^2 * 19^8
                        (.node 7260831698361443981737224577497035015625 (.cut 7 31 80147846014298060399321) .empty .empty)
                        .empty))
                    (.node 8355753690284389007629775648789308774917 (.basic (.groups [5, 11, 41])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^2 * 71^2 * 631^4
                      (.node 8350435196553418601700310681625463556917 (.basic (.split 23)) -- 3^2 * 13 * 7^4 * 2801^10
                        (.node 8310411746084416546455336789722337705669 (.basic (.groups [5, 11, 2801])) .empty .empty)
                        .empty)
                      (.node 9114376166765181717737971367402236387917 (.basic (.groups [163, 613, 1747, 398581, 1193557])) -- 3^6 * 1093^5 * 547^8
                        (.node 8461730938442214084900807329583356401605 (.basic (.groups [43, 45319, 32668561, 125613804731])) .empty .empty)
                        .empty)))
                  (.node 10604059517769756458816000140616021939829 (.basic (.groups [19, 2180921, 3798019])) -- 3^8 * 13^2 * 61 * 31^2 * 331^6 * 757^2 * 14713^2
                    (.node 9478697836477376792740033656596356803693 (.basic (.groups [527532101, 75755912653, 115512048133057])) -- 3^2 * 13 * 7^2 * 19^2 * 127^16
                      (.node 9473759819449570895288412166464376936917 (.cut 5 31 7576140388888098734363) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^2 * 67^4 * 127^6
                        (.node 9328958042734599251491701000187119140625 (.basic (.groups [11, 12207031, 32668561])) .empty .empty)
                        .empty)
                      (.node 9957850177913460819703744123478920162569 (.basic (.split 5419)) -- 3^4 * 11^10 * 15797^2 * 1806113^2 * 19^2 * 127^2
                        (.node 9917906414487125333586347130648382417437 (.basic (.groups [743, 5209, 14083, 39449441, 1706822489])) .empty .empty)
                        .empty))
                    (.node 11205665764176756564625518776588377206681 (.basic (.groups [151, 911, 9631])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^6 * 19^4
                      (.node 10907801069741001703257371940799497519441 (.basic (.groups [97, 181, 607127818287731321660577427051])) -- 3^2 * 13^2 * 61^18 * 229^2
                        (.node 10835088395116101750795086125429016306997 (.basic (.groups [17293, 20161, 53551, 18871143464293])) .empty .empty)
                        .empty)
                      (.node 12511666540894179215672600009545002415797 (.cut 5 31 377920025676026683209638527) .empty .empty))))
                (.node 23936362963714846862898297505020143027289 (.basic (.groups [701, 9631, 30941])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^4 * 19^6
                  (.node 18422814582018691462363454442785043340569 (.basic (.groups [151, 911, 4729, 129901])) -- 3^2 * 13^2 * 61^12 * 187123^2 * 19^4
                    (.node 16175764899895406292030960541491923402937 (.basic (.groups [5, 11, 211, 1597])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^6 * 71^4
                      (.node 14283338977393475979388520550821691582657 (.basic (.groups [7, 13, 31])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^4 * 433^5
                        (.node 12943569515104807989124237629324478178949 (.cut 5 7 172017796009563768310122553) .empty .empty)
                        .empty)
                      (.node 18409640665931922902373879537233701457973 (.cut 5 7 40723616606492534740508350423) -- 3^8 * 13^2 * 61^6 * 757 * 379^8
                        (.node 16262135978886265693352628475621565694477 (.basic (.groups [570821, 672901, 3348577])) .empty .empty)
                        .empty))
                    (.node 22069318417056921636828392410762573043961 (.basic (.split 5209)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^6 * 743^2
                      (.node 19735627849216739157766884665234174791353 (.basic (.groups [17707, 88741, 17311991])) -- 3^4 * 11^10 * 15797^4 * 1806113 * 17^4
                        (.node 18803103514005210353431491615365269874277 (.cut 5 101 32636253841702958500977379) .empty .empty)
                        .empty)
                      (.node 23212594228683236345796283341785711061237 (.cut 5 7 33747106018601323403444544623993) -- 3^8 * 13^4 * 757^5 * 163^8
                        (.node 22315479822066678542294219562743974999881 (.basic (.groups [67, 4733, 2384047, 3060947, 17177163455369])) .empty .empty)
                        .empty)))
                  (.node 35374098187178595820013338379254033903005 (.basic (.groups [17293, 21491, 1774921])) -- 3^8 * 13^2 * 61^4 * 5 * 131^2 * 757^2 * 14713^4
                    (.node 26831458356460064299724086628712158203125 (.cut 7 31 44265795772758928516540938659) -- 3^6 * 1093^2 * 398581^4 * 5^13
                      (.node 24796574253236465582956956955116730954233 (.basic (.groups [7, 88741, 2133031])) -- 3^4 * 11^10 * 15797^2 * 1806113 * 17^4 * 17707^2
                        (.node 24489189141837407978273144203559388922881 (.basic (.groups [1009, 13537, 18041])) .empty .empty)
                        .empty)
                      (.node 31650989809904261626273435219228647323733 (.basic (.groups [37, 43, 4933])) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^4 * 2801^2
                        (.node 29389846221954540978215537705739925801797 (.cut 5 13 20920984056493654265974898991476119) .empty .empty)
                        .empty))
                    (.node 37898978410071463984116432127173805078125 (.basic (.groups [19, 31, 829])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^8
                      (.node 37110885290157683286002168006606014384053 (.basic (.groups [11, 131, 830833, 3506165161])) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^2 * 1499^4
                        (.node 36286196712551282842416652592500211801169 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 39529989489266852618268168689844928951821 (.basic (.groups [23, 307, 617])) .empty .empty)))))
              (.node 87037200323683537549028093824614297537249 (.basic (.groups [29, 79, 20359])) -- 3^2 * 13^2 * 61^2 * 97^12 * 53^6
                (.node 67931258943136451307842967595701835024773 (.basic (.split 7)) -- 3^6 * 1093^8 * 56773 * 28387^2
                  (.node 55192547385992729805867196006672315677969 (.basic (.groups [433, 14083, 245753, 251057, 281420912955937])) -- 3^2 * 13^4 * 30941^2 * 157^12
                    (.node 51439350083210951837995280755715829651549 (.basic (.groups [31, 73, 97])) -- 3^4 * 11^12 * 1093^2 * 398581^2 * 1621 * 811^2
                      (.node 48326261389924318417484004293927560200645 (.basic (.split 21491)) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^6
                        (.node 47914497488583217108121099582076096488013 (.basic (.groups [7, 19, 31, 43])) .empty .empty)
                        .empty)
                      (.node 52644738547928175251532404511793876016337 (.cut 5 13 321465408923438886023) -- 3^4 * 11^16 * 50544702849929377 * 23^4
                        (.node 52485535863140674941527179185167380481925 (.cut 7 31 140963310343368484645703980211) .empty .empty)
                        .empty))
                    (.node 63709235496768246349641404482934939327841 (.basic (.groups [1123, 293459, 2384047, 3060947])) -- 3^2 * 13^4 * 30941^6 * 7^10
                      (.node 57856692921168453256338020343364153079025 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2 * 331^2
                        (.node 56094722833639444848849565817573601333033 (.basic (.groups [7, 31, 37, 1693, 12503])) .empty .empty)
                        .empty)
                      (.node 63940269806834762879934920498972206364805 (.basic (.groups [421, 189967, 211093, 1097113])) -- 3^2 * 13^2 * 61^4 * 5 * 131^6 * 127^4 * 21491^2
                        (.node 63813002185857570209528432269099218559461 (.basic (.split 71)) .empty .empty)
                        .empty)))
                  (.node 74148683924328618699060572953268210429361 (.basic (.groups [5, 11, 211, 1693])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^6 * 71^4
                    (.node 69467521734487256304644061406203303537597 (.cut 5 31 25392332735349807018472234579) -- 3^6 * 1093 * 547^6 * 7^2 * 19^2 * 29^4 * 127^4
                      (.node 68585288260503733132331878557048751146237 (.basic (.groups [37, 1693, 5479, 14083])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^10 * 433^2
                        (.node 68187592374685889947249588037667470392281 (.basic (.groups [37, 2179, 5419])) .empty .empty)
                        .empty)
                      (.node 69713894970080123749789960484201404437453 (.basic (.groups [5, 4933, 26881])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^4 * 761^4
                        (.node 69575448255153910083534086812249425543213 (.basic (.groups [11, 1811, 2801])) .empty .empty)
                        .empty))
                    (.node 80458614485452298808643538837863249705881 (.basic (.groups [701, 70841, 249561007])) -- 3^4 * 11^10 * 15797^2 * 1806113^2 * 19^6
                      (.node 80003843555030628963453738520680694966173 (.basic (.groups [5, 11, 41])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^6 * 631^4
                        (.node 74637273109969060707486334373903530552005 (.basic (.split 421)) .empty .empty)
                        .empty)
                      (.node 83316376155666777451769624983075296841509 (.cut 5 13 106510844442023060524668777491977) .empty .empty))))
                (.node 124593419836492298583345377952364832008149 (.basic (.groups [31, 97, 523])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^5
                  (.node 110401013405271673032191936184989768456241 (.basic (.groups [29, 79, 4733])) -- 3^6 * 1093^10 * 23^2 * 7^6
                    (.node 93133225303717982433600347720717552092413 (.cut 5 7 460605836335149465118434691) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37 * 19^12
                      (.node 87603904786950673483926475002558516304437 (.basic (.groups [37, 211, 1597, 5113])) -- 3^2 * 13 * 7^4 * 2801^6 * 71^8
                        (.node 87127743611598523786578861934119082187253 (.basic (.split 830833)) .empty .empty)
                        .empty)
                      (.node 105429907261565126172017651301335458630317 (.basic (.groups [11, 265871, 293459])) -- 3^2 * 13 * 7^10 * 1123^10
                        (.node 93713104265078091211183390540877486166213 (.basic (.groups [43, 1811, 14083])) .empty .empty)
                        .empty))
                    (.node 118922728733654042925944739103374110183013 (.cut 5 13 1132665583772545814753233029538957) -- 3^6 * 1093 * 547^10 * 23^2 * 7^6
                      (.node 113287574801497699223836455541727166794361 (.basic (.groups [1093, 2801, 3500201])) -- 3^4 * 11^6 * 43^4 * 45319^4 * 151^2 * 7^4
                        (.node 112420597805574257178292599169358338461429 (.cut 5 7 1313245310685869824935458482487821) .empty .empty)
                        .empty)
                      (.node 119776585216403835374936836911534517837653 (.basic (.groups [613, 1747, 5111046132733, 18871143464293])) .empty .empty)))
                  (.node 175604894373311251772498738596672492242213 (.cut 5 13 1362915553715849345985862323997123) -- 3^6 * 1093^5 * 547^6 * 7^8
                    (.node 142054734922071745556789625804912145503045 (.basic (.groups [19, 14713])) -- 3^8 * 13^2 * 61^4 * 5 * 131^2 * 757^8
                      (.node 136373917527073142481338026641726870240801 (.basic (.groups [7, 547, 78919, 95957, 75820095037, 116720967413])) -- 3^12 * 797161^6
                        (.node 125811201825921589548347386221912735635061 (.basic (.groups [73, 97, 331, 3637])) .empty .empty)
                        .empty)
                      (.node 169552354870867759663613746046077034850933 (.basic (.groups [7, 19, 67, 613])) -- 3^6 * 1093^5 * 547^2 * 163^8
                        (.node 169499834748233091824108908148789521450077 (.cut 5 7 23326907405647868849654273) .empty .empty)
                        .empty))
                    (.node 195595497659396029736539221029371166810481 (.basic (.groups [37, 43, 4933, 9631])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^4 * 2801^2
                      (.node 184089628129449346138427789793454890139809 (.basic (.groups [7673, 8387, 5229043, 157639514028457693])) -- 3^8 * 13^6 * 757^2 * 14713^6
                        (.node 182181532662953567022705571768731065304669 (.basic (.groups [13, 29, 811, 4733])) .empty .empty)
                        .empty)
                      (.node 204698633029515580478044250551462478206029 (.cut 5 7 119930063606212288697968631) .empty .empty)))))))
          (.node 12228605049266166971397736594508864055911469 (.cut 5 101 472118200220451949459) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2 * 7^2 * 307^6
            (.node 2089914182919781286544848113747464801454281 (.basic (.groups [157, 433, 14083])) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^4 * 30941^2
              (.node 643459662459086832210495229593643381905909 (.cut 5 13 171505870085043711029) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^2 * 43^8
                (.node 330739942496603445404202691221377292129717 (.cut 5 101 131059288566173233417919) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^6 * 13 * 29^6
                  (.node 237252510409905159302751513214051397276613 (.basic (.groups [43, 71, 55721, 312410911])) -- 3^6 * 1093 * 547^2 * 163^6 * 613^6
                    (.node 217966606174683630691246635513371313397641 (.basic (.groups [7, 859, 883])) -- 3^2 * 13^2 * 61^10 * 199^4 * 71^6
                      (.node 215918912955081139682875169541777820620729 (.basic (.groups [19, 37, 157, 433, 14083, 115201, 1275319, 8495240355559])) -- 3^2 * 13^4 * 30941^8
                        (.node 213077416360658120021835269027232309530361 (.basic (.groups [13, 31, 37, 398581, 5091991, 10010548486153])) .empty .empty)
                        .empty)
                      (.node 236346718061897229285928327147936356158541 (.basic (.split 2426789)) -- 3^2 * 13^2 * 61 * 31^12 * 42407^4
                        (.node 236298867424710036325784997385432539354201 (.basic (.groups [5, 45319, 112614002823949502163679249])) .empty .empty)
                        .empty))
                    (.node 262600872020541018223713109452215673695169 (.basic (.groups [29, 6491, 2608387, 5336717])) -- 3^6 * 1093^10 * 23^6
                      (.node 257920860085559254941283728537423962341977 (.cut 5 31 140433088795078618566091) -- 3^8 * 13^4 * 757^2 * 14713 * 7^4 * 1051^2 * 2801^4
                        (.node 246862005944520243444795359112172758941025 (.basic (.groups [11, 17351, 1866871])) .empty .empty)
                        .empty)
                      (.node 301719830978699307259591136795422856876421 (.cut 5 13 48488353000243864842849184985017) -- 3^2 * 13^2 * 61 * 31^2 * 331^10 * 11^8
                        (.node 282870702951614387087347123523594032824117 (.cut 5 101 557460736477978101586982261189423) .empty .empty)
                        .empty)))
                  (.node 467267314535051917926940492152885762097053 (.cut 5 7 54948196616206584112269005076799) -- 3^6 * 1093 * 547^2 * 163^10 * 23^6
                    (.node 426776188283574100052104516988303434285209 (.basic (.split 19)) -- 3^4 * 11^10 * 15797^4 * 1806113^2
                      (.node 419814009365588499272677784579292701292009 (.basic (.groups [37, 1693, 14083, 28447, 321910472390668481])) -- 3^2 * 13^4 * 30941^2 * 157^10 * 433^2
                        (.node 394587090007982255602913946468361978123341 (.basic (.groups [88741, 262209281, 145159381141])) .empty .empty)
                        .empty)
                      (.node 437785274863621712454825833410247483500341 (.basic (.groups [7, 4447, 5839, 38047, 158341])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^2 * 43^6
                        (.node 433181699912013838702090412985908878927509 (.basic (.groups [7, 409, 37181, 10999171])) .empty .empty)
                        .empty))
                    (.node 519923777383110848465352734288143456532121 (.basic (.groups [701, 70841, 2384047, 3060947, 17177163455369])) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^6
                      (.node 513522972803233707968712280656130537574097 (.basic (.groups [70001, 732541, 69655517])) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^6
                        (.node 487690609826949472163877154147223975828025 (.basic (.split 1866871)) .empty .empty)
                        .empty)
                      (.node 611765757851926952896662212479698836319189 (.cut 5 101 11735127252710301191) .empty .empty))))
                (.node 1023869443551507904272997686879586124594205 (.basic (.groups [7, 19, 1772893])) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5 * 11^8
                  (.node 785634441455924150347034384096274977659401 (.basic (.groups [23, 433, 26731])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^10
                    (.node 713628891843823350024729544058044053040605 (.basic (.split 33151)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4
                      (.node 712743084256970114100675158695150545700605 (.basic (.split 381510691)) -- 3^4 * 11^4 * 5 * 3221^10
                        (.node 697656497950401821751449761890294451820229 (.basic (.groups [97, 1801, 32668561, 917087137])) .empty .empty)
                        .empty)
                      (.node 739798948663311409938718299840561803782893 (.basic (.groups [271, 5839, 158341])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2 * 43^6
                        (.node 731722652233547892808742379731580447937941 (.basic (.groups [19, 617, 1621, 88741, 32668561, 158866414981])) .empty .empty)
                        .empty))
                    (.node 914020337219068475100193768453635092406909 (.basic (.groups [127, 307, 617, 1621, 32668561, 158866414981])) -- 3^6 * 1093^2 * 398581^5 * 17^2 * 19^2
                      (.node 899105725623000379836683199478969029644649 (.basic (.groups [5, 11, 331])) -- 3^2 * 13^6 * 5229043^2 * 31^14
                        (.node 888918268441780614782644135876808899880877 (.basic (.groups [29, 211, 5419])) .empty .empty)
                        .empty)
                      (.node 1021198368560223968719798415869299055218741 (.cut 5 7 1379642151145769090598319) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^4 * 151^8
                        (.node 947474460251786599602910803179345126953125 (.cut 7 31 34545326380461464190449011) .empty .empty)
                        .empty)))
                  (.node 1475905142722038398546407417367448173103717 (.cut 5 7 12461151472891622316493400479) -- 3^8 * 13^2 * 61^6 * 757 * 379^2 * 787^6
                    (.node 1221046980141706433639422881666488741471481 (.basic (.groups [211, 4105333, 32668561, 20957295829])) -- 3^12 * 797161 * 398581^2 * 1621^6
                      (.node 1202767396729888675874607029240018209918773 (.basic (.groups [701, 1693, 12503])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2 * 37 * 19^6
                        (.node 1075830900895022507289752196087847201198761 (.basic (.groups [5, 3500201, 104670301, 27935336611728311])) .empty .empty)
                        .empty)
                      (.node 1419850140097534163868807022827369166799877 (.cut 5 257 2036190904373542960361891) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13 * 19^10
                        (.node 1245976485089895222813495969768535312316277 (.cut 5 7 272491070803748539834140115448579861) .empty .empty)
                        .empty))
                    (.node 1778023638915012859278415977032510378257281 (.basic (.split 1093)) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4
                      (.node 1772836407077579033000480684536815570056481 (.basic (.groups [71, 1693, 12503, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2 * 37^6
                        (.node 1642957313265178983519616506480407243979129 (.basic (.groups [73, 8011, 6807972547])) .empty .empty)
                        .empty)
                      (.node 1796999102096308423566723857769900688558557 (.cut 5 7 194295055663283390516978312069) .empty .empty)))))
              (.node 5703596448423637616594629668252676514701017 (.cut 5 13 28280912550773126327307826009) -- 3^4 * 11^10 * 15797^4 * 1806113 * 17^6
                (.node 3328631688213686114084305412189389916213877 (.basic (.groups [19, 3541, 10837, 398581, 10010548486153])) -- 3^6 * 1093^8 * 56773 * 28387^2 * 7^2
                  (.node 2451648076215384365340707606298028527442293 (.basic (.groups [37, 379, 732541, 22406023])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^8
                    (.node 2316272407363357451920156484796197917817997 (.basic (.groups [7, 29, 547, 2213, 8387])) -- 3^6 * 1093^13
                      (.node 2240032156175846943364812256929259496931525 (.basic (.groups [11, 6781, 17351, 12774841])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^2 * 31^4
                        (.node 2228172472833120863078236603543146686231997 (.cut 5 31 1313390725486125687471611449621) .empty .empty)
                        .empty)
                      (.node 2398936078029277013694153559021464071819049 (.basic (.groups [89, 3169, 6654649])) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^10
                        (.node 2398002139240133508262880565244771022955333 (.basic (.groups [7, 17923, 398581, 1193557])) .empty .empty)
                        .empty))
                    (.node 3121752539341644071132428819663812027064209 (.basic (.groups [2384047, 3060947, 16148168401])) -- 3^2 * 13^4 * 30941^6 * 7^12
                      (.node 3108984792795283412428149361187976004558521 (.basic (.groups [659, 1811, 45319])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^6 * 433^4
                        (.node 2730821018101763253779326710516025846184253 (.basic (.groups [43, 71, 4933, 37140797])) .empty .empty)
                        .empty)
                      (.node 3270996661490358991286456490781900177445049 (.basic (.groups [21433, 280314943, 97199158345481611029493])) -- 3^2 * 13^2 * 61^2 * 97^18
                        (.node 3245450445198140714451523135112524317354393 (.basic (.groups [7, 11, 31, 41, 1811])) .empty .empty)
                        .empty)))
                  (.node 4623647639961190601478887411034347770298733 (.basic (.groups [7, 29, 337, 433])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^6 * 281^6
                    (.node 4248546453626298993863041357365713630591409 (.basic (.groups [37, 43, 4933, 2384047, 3060947, 17177163455369])) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^2
                      (.node 3491945097040262361125960494436046820794201 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^6
                        (.node 3333048777146139780467775524093541415711413 (.basic (.groups [5, 41, 51343])) .empty .empty)
                        .empty)
                      (.node 4417380218976758440299464350579870221609093 (.basic (.groups [79, 1372537, 10196539, 45437789, 2033125998091])) -- 3^2 * 13 * 7^4 * 2801^10 * 23^2
                        (.node 4250077618721012917284857241316054012030521 (.basic (.groups [7, 953, 4327, 7841, 3500201])) .empty .empty)
                        .empty))
                    (.node 4981500323348595085365673459878260020862973 (.basic (.groups [67, 4933, 3500201, 143879023])) -- 3^2 * 13 * 7^4 * 2801^8 * 37^2 * 43^4
                      (.node 4704989249495515438981997364925073568444597 (.basic (.groups [7717, 1806113, 2545021, 382226209])) -- 3^4 * 11^10 * 15797 * 2633^4 * 1717451^2
                        (.node 4663357044045066449147815950100799682029493 (.cut 5 7 2140743324971998707425084006749221893) .empty .empty)
                        .empty)
                      (.node 5612958840347545439006531940571051436863389 (.cut 5 13 109640007598741006372759) .empty .empty))))
                (.node 7711723254560949818438703251112371351219049 (.basic (.groups [5, 691, 701])) -- 3^2 * 13^2 * 61^2 * 97^10 * 89^4 * 131^4
                  (.node 7096103888107496159215349517293995586639877 (.basic (.groups [761, 4933, 26881])) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^4 * 631^6
                    (.node 6650636064108747617913207053845400645945409 (.basic (.groups [701, 4729, 70841])) -- 3^2 * 13^2 * 61^12 * 187123^2 * 19^6
                      (.node 6635810892370749529326466102605500050761921 (.basic (.groups [53, 79, 262033020407643669411475094379221443])) -- 3^8 * 13^4 * 757^12
                        (.node 6184685777211375099075229398505792455290481 (.basic (.groups [743, 1051, 1621])) .empty .empty)
                        .empty)
                      (.node 7054965504548702784019319849833332907339893 (.basic (.groups [631, 743, 2801])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4 * 43^2 * 433^6
                        (.node 6707088083180531990023913928996922385675493 (.basic (.groups [67, 1093, 472319, 50390258557])) .empty .empty)
                        .empty))
                    (.node 7600198610026030213584068055094254752497089 (.basic (.groups [2801, 9631, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^6
                      (.node 7486527024215505247003176827100551528203929 (.basic (.groups [1693, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^12
                        (.node 7251971758116599735963971375674012572544093 (.cut 5 31 99320236912430048374525557114650667701) .empty .empty)
                        .empty)
                      (.node 7664854839270702210530085438016487433119529 (.basic (.groups [5, 1866871, 3158528101, 2703853428809791])) .empty .empty)))
                  (.node 8665229939600858579521149773047553561441133 (.basic (.groups [79, 433, 3011, 12503])) -- 3^2 * 13^4 * 30941^2 * 157^13
                    (.node 7969944953264910782468407233646870049727393 (.basic (.groups [2801, 8269, 14083])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4 * 31^2 * 331^6
                      (.node 7887413800650752844351821667389676593426661 (.basic (.groups [617, 659, 262209281])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^4 * 307^6
                        (.node 7731915233961213140486401647195827615688717 (.cut 5 31 88686390719686751673837359) .empty .empty)
                        .empty)
                      (.node 8358104832173164691835245154350173799069553 (.basic (.groups [1279, 8387, 30941, 157639514028457693])) -- 3^8 * 13^4 * 757^2 * 14713^6 * 7673
                        (.node 7986305687987124301143578654923166535147909 (.basic (.groups [2801, 9631])) .empty .empty)
                        .empty))
                    (.node 11339285616074449036553190255446175826111773 (.cut 5 13 59942549270797458323531426171) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^4 * 11^8
                      (.node 9313346438591900111799721456202756097079581 (.basic (.groups [7, 5419, 88741])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^6
                        (.node 8926895100484724784112573016667822199928781 (.basic (.groups [13, 19, 37])) .empty .empty)
                        .empty)
                      (.node 11424166962398120406679500751365184467076269 (.cut 5 7 60239293233064004604021278509) .empty .empty))))))
            (.node 123888202669732456417032720112429921075898805 (.cut 7 257 117081131750204339557692684551) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5 * 11^10
              (.node 48595106530748391960652587153973728318084849 (.basic (.groups [11, 31, 2801])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2 * 97^4
                (.node 18767318530358076654069438652267682974899921 (.basic (.groups [4733, 732541, 2384047, 3060947])) -- 3^2 * 13^4 * 30941^6 * 7^6 * 29^4
                  (.node 14844325435772718128133062206486420786247157 (.basic (.groups [11, 1811, 1768661, 200741603328100897])) -- 3^2 * 13 * 7^12 * 16148168401^2 * 433^4
                    (.node 14013920020797589000459414891085340585177609 (.basic (.groups [1031, 3500201, 5390701, 836561914831])) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^2 * 5419^4
                      (.node 13178074441133513204499326145196238310715641 (.basic (.groups [7, 211, 3500201, 20241187])) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^4 * 967^6
                        (.node 13081181111400268047825338153030169526883889 (.basic (.groups [151, 6038099, 3664405207])) .empty .empty)
                        .empty)
                      (.node 14752011744572817848952229776267103891139661 (.basic (.groups [631, 733, 5419])) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^2 * 43^2 * 617^4
                        (.node 14248316078036415503345318331631252916676573 (.basic (.groups [7, 43, 433])) .empty .empty)
                        .empty))
                    (.node 16086190396097776864242531209410058043930741 (.cut 5 7 248560078583588787375097843902559) -- 3^8 * 13^2 * 61 * 31^2 * 331^6 * 757^6
                      (.node 15778644709947729055306329549326477013597357 (.basic (.split 87653303)) -- 3^6 * 1093 * 547^4 * 431^10
                        (.node 15690207680764671989051862462000181026063117 (.basic (.groups [5, 911, 9631])) .empty .empty)
                        .empty)
                      (.node 17262063106526973352658026547817712741841361 (.basic (.groups [1009, 13267, 4242586390571, 398633408201869])) -- 3^2 * 13^2 * 61^10 * 199^2 * 859^6
                        (.node 16884930025364934695713103995134639373029681 (.basic (.split 5)) .empty .empty)
                        .empty)))
                  (.node 31513347959803868929882415231164315071651597 (.cut 5 31 6343581844791501295630697321083) -- 3^6 * 1093 * 547^2 * 163^12 * 613^2
                    (.node 24289014986965879619551861999009369377203289 (.basic (.groups [743, 5209, 12503, 14083, 1205476469])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^6
                      (.node 21452914837899210717392146402250947627345509 (.basic (.groups [97, 331, 32668561, 153436090543])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^6
                        (.node 21030599200799193232994864767303496002523889 (.basic (.groups [8011, 45319, 112614002823949502163679249])) .empty .empty)
                        .empty)
                      (.node 28144066840049513415249973298323371115856025 (.basic (.groups [7, 5233, 1866871])) -- 3^12 * 797161 * 398581^4 * 5^2 * 31^2 * 331^2
                        (.node 25900631595553156585355811785997237526570653 (.basic (.groups [71, 11299, 830833])) .empty .empty)
                        .empty))
                    (.node 41293929930799297777993812291588665152542045 (.basic (.groups [19, 463, 22777, 10378063, 45548808606973099])) -- 3^4 * 11^4 * 5 * 3221^8 * 24517^2
                      (.node 37877739859221931626936142897125007736103189 (.basic (.groups [331, 3169, 28792661, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^4 * 97^2
                        (.node 32838731435214156387419688904443099591104961 (.basic (.groups [911, 1093, 2384047, 3060947, 17177163455369])) .empty .empty)
                        .empty)
                      (.node 46089705703858441616176752453953104919949741 (.basic (.groups [43, 617, 733])) .empty .empty))))
                (.node 81542030860372743118128072089660785874205417 (.basic (.groups [211, 883, 1597])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^6 * 71^6
                  (.node 62801042091544389195197428058761828711368717 (.basic (.groups [5, 45121, 487681, 22406023, 2617241417881])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^4
                    (.node 60348725676446906656401276392012563826905917 (.basic (.groups [1597, 5113, 307189, 41233879])) -- 3^2 * 13 * 7^4 * 2801^6 * 71^2 * 211^6
                      (.node 54579242302929807908823065533364647295933493 (.cut 5 31 66993894021582009888651908963489399887) -- 3^2 * 13 * 7^2 * 19^4 * 151^16
                        (.node 53529786057255323765266729849524123968859069 (.cut 5 13 1591026524698253727331003) .empty .empty)
                        .empty)
                      (.node 61889161858005323414850635385332563196864025 (.basic (.groups [2671, 37861, 63601])) -- 3^12 * 797161^4 * 5^2 * 31^2 * 331^4
                        (.node 61215829740754153702409216522904724085538933 (.basic (.groups [8011, 70841, 322411222976532914376077399])) .empty .empty)
                        .empty))
                    (.node 75251077018025606948344689682794926984159469 (.cut 5 7 243524385149563706025223350727) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^6 * 617^6
                      (.node 66877773378761335086853475045796434188214469 (.basic (.groups [11, 331, 1801, 262321])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^2 * 97^4
                        (.node 65003616498361124716151752138293659592466893 (.basic (.groups [911, 1499, 1693])) .empty .empty)
                        .empty)
                      (.node 80568664365196078584014268789743556256202469 (.cut 5 7 1070525650291762741746167429549) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^10
                        (.node 76664332983473217402251770893841112006120637 (.basic (.groups [19, 7057, 365017])) .empty .empty)
                        .empty)))
                  (.node 111754247035072152613064071833335688398657721 (.basic (.groups [13, 31, 37, 4105333, 32668561, 20957295829])) -- 3^6 * 1093^2 * 398581^2 * 1621^6 * 211^2
                    (.node 101037128369935382386452113778609020636904441 (.basic (.groups [1811, 5641, 45319])) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^4 * 733^4
                      (.node 87123158306835630104642382874593008534606769 (.basic (.groups [29, 1093, 4733, 151841, 32607907713428723311])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^6
                        (.node 84424650126824673478565519975673196865148405 (.basic (.split 151841)) .empty .empty)
                        .empty)
                      (.node 105671610955072068852912899345250675229994121 (.basic (.groups [11, 859, 75449464927])) -- 3^2 * 13^2 * 61^10 * 199^10
                        (.node 104756859790545118911636115398930124442062005 (.cut 7 101 21247631483812652098015171417085209) .empty .empty)
                        .empty))
                    (.node 116715604525672571694745373778669757220028849 (.basic (.groups [1031, 30941, 3798019])) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^2 * 5419^4
                      (.node 114959079634449504806239096067662242985992849 (.basic (.groups [5, 521, 8269, 14083, 552793])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^6 * 743^2 * 5209
                        (.node 114035669012306871869242130529356611677645549 (.cut 5 7 976147920837300182057292707) .empty .empty)
                        .empty)
                      (.node 120904564954710647555961838159258138945293621 (.cut 5 101 1202983155662741839927) .empty .empty)))))
              (.node 329961341736083719511169950411762268358894149 (.basic (.groups [151, 307, 617, 911, 1621])) -- 3^6 * 1093^2 * 398581^5 * 17^2 * 19^4
                (.node 185940951948587422145394472998487348844375517 (.cut 5 31 1209263634286386134815173463703) -- 3^6 * 1093 * 547^2 * 163^6 * 613^4 * 131^4
                  (.node 152881917404543610290104002847242638886764397 (.cut 5 31 74456077515638586287814488044114033537) -- 3^2 * 13 * 7^2 * 19^2 * 127^18
                    (.node 138915861298866198640344234900222091384744401 (.cut 5 101 825126277467915800008090461170228323) -- 3^6 * 1093^10 * 23^8
                      (.node 131009626345323266890627102670709265259390625 (.basic (.split 1866871)) -- 3^6 * 1093^2 * 398581^4 * 5^6 * 19531^2
                        (.node 129922714851260075082460994474985211040886801 (.basic (.groups [5, 14939, 732541])) .empty .empty)
                        .empty)
                      (.node 149638601861404010769206628343981243363957893 (.cut 5 7 8552005160815644846702802709080508299) -- 3^6 * 1093 * 547^10 * 23^8
                        (.node 148385536234302989400658107931509565186084293 (.basic (.groups [11, 41, 1693])) .empty .empty)
                        .empty))
                    (.node 163102952722470619590130965197280105894479973 (.basic (.groups [2801, 3541, 10837, 398581])) -- 3^6 * 1093^8 * 56773 * 28387^2 * 7^4
                      (.node 160610165519566209561001688967591503302075401 (.basic (.groups [249561007, 262209281, 171686630257])) -- 3^4 * 11^10 * 15797^2 * 1806113^2 * 19^2 * 127^4
                        (.node 154066203970370250118809730632777539776960449 (.basic (.groups [127, 17311991, 3597318971, 171686630257])) .empty .empty)
                        .empty)
                      (.node 171105309754972855695172064227366294218915849 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581^6 * 7^2
                        (.node 171068583354464484749309090653920811000299093 (.basic (.groups [31, 163, 431, 613])) .empty .empty)
                        .empty)))
                  (.node 255379982375423482790834750969226430534146525 (.basic (.groups [7, 5233, 6781, 12774841])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^2 * 31^2 * 331^2
                    (.node 211467846495495341021726547742426749454064949 (.basic (.groups [19, 617, 1621, 25646167, 32668561])) -- 3^6 * 1093^2 * 398581^5 * 17^6
                      (.node 207208687898762852822295547397469143439187269 (.basic (.groups [5, 11, 1871])) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941 * 191^4
                        (.node 198479687169321302935960467748660471929884349 (.cut 5 7 19479706183274119042854814008911) .empty .empty)
                        .empty)
                      (.node 237234387712683953950448340106798021342325025 (.cut 7 31 4629222518876813657144468359657) -- 3^12 * 797161 * 398581^4 * 5^2 * 31^6
                        (.node 229104764513032912766004261150733542859163097 (.cut 5 13 3711666255355598352498287593) .empty .empty)
                        .empty))
                    (.node 311249325900513787863405004153234545915235941 (.cut 5 7 3502327601818228254979345093531170499) -- 3^2 * 13^2 * 61^13 * 31^2 * 331^6
                      (.node 283900518291289922759670698187316438106903289 (.basic (.groups [5, 11, 72931, 67155461, 72577051])) -- 3^2 * 13^6 * 5229043^2 * 31^6 * 4051^4
                        (.node 277001499895973694139117542602720406543545373 (.cut 5 7 24677250509889386989206760957519) .empty .empty)
                        .empty)
                      (.node 321681344018908011426232827068529160758242901 (.basic (.split 281)) .empty .empty))))
                (.node 468670676043698442749485945135482240770732025 (.basic (.groups [331, 3637, 81343, 1866871])) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^8
                  (.node 417737586619464051982350632075018584822926513 (.basic (.groups [37, 43, 4933])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2 * 97 * 2801^2
                    (.node 372401050098117426366282507071214742778397309 (.cut 5 7 269506539999056538241618146533) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^6 * 307^8
                      (.node 333121611623058382810243536302311565559639009 (.basic (.groups [5, 32668561, 3158528101])) -- 3^4 * 11^12 * 1093^2 * 398581^2 * 1621^4
                        (.node 330796589619745062932023144086587333088914601 (.basic (.groups [19, 11503, 2384047, 3060947, 17177163455369])) .empty .empty)
                        .empty)
                      (.node 383030048177042775065233837719821278243452405 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2
                        (.node 373783515662540566861964348257425048774408801 (.basic (.groups [7, 883, 1693])) .empty .empty)
                        .empty))
                    (.node 437417859923751514421516077816723287796510269 (.cut 5 13 2870720949203942799509207058461) -- 3^6 * 1093^2 * 398581^2 * 1621^5 * 7^10
                      (.node 431872820127519548401687028031805782099815577 (.cut 5 101 141365251191274892381063571577) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^6 * 4733^6
                        (.node 422123250634123367392827599878365984325742025 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 441611284031018345032473360487897480690666917 (.basic (.groups [23, 211, 1597])) .empty .empty)))
                  (.node 652591276945065503200332684205123983635730717 (.basic (.groups [29, 953, 967, 1009])) -- 3^6 * 1093^5 * 547^4 * 431^6
                    (.node 615354196183211312323393240944864400493132829 (.basic (.groups [5, 461, 691])) -- 3^2 * 13^2 * 61 * 31^12 * 42407^2 * 1471^4
                      (.node 580876145500802302789905648744970819065522045 (.cut 7 101 41224098758539714439769957096836519) -- 3^2 * 13^2 * 61^4 * 5 * 131^6 * 127^10
                        (.node 544252237380384222968013720915762806272097709 (.basic (.groups [5, 67, 271])) .empty .empty)
                        .empty)
                      (.node 637579200472385065880047292798508859063920909 (.cut 5 7 3361254269060743336104931500779) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^12
                        (.node 621200847030641312721932013794127911899483677 (.cut 5 7 51883560873665344730001481) .empty .empty)
                        .empty))
                    (.node 718412255033907459472066543044666020129061669 (.basic (.groups [31, 313, 1009])) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^4 * 5419^2
                      (.node 698481671384640487162959421505350685343412173 (.basic (.groups [5, 9631, 1956611, 6294091])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13 * 2801^4
                        (.node 678171771249660132650518519665347777476875045 (.basic (.split 7)) .empty .empty)
                        .empty)
                      (.node 792062202194742908658198733032976366152035205 (.cut 7 31 162901580527903479541089896597273838227) .empty .empty)))))))))
      (.node 2047168489182073625631057332498911991266088411488033964961 (.basic (.groups [29, 239, 701, 70841])) -- 3^2 * 13^6 * 5229043^6 * 7^2 * 19^6
        (.node 59735776253027761111501255226061584164320774177381 (.basic (.groups [11, 3301, 604842197, 1478526139, 2950536931])) -- 3^2 * 13^2 * 61 * 31^2 * 331^6 * 2180921^2 * 3217^4
          (.node 138273847391912441798549415416855481445886318205 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^2
            (.node 7992044683401060359916417294666725188829518677 (.basic (.groups [29, 3541, 4733])) -- 3^6 * 1093^8 * 56773 * 28387^2 * 7^6
              (.node 2668306086181737485506340777967658804606859829 (.basic (.split 917087137)) -- 3^2 * 13^8 * 61 * 31^6 * 1609669^4
                (.node 1650802097070276056906763632128037553376809117 (.basic (.groups [11, 281, 1021, 162709])) -- 3^2 * 13 * 7^2 * 19^2 * 127^6 * 43^4 * 86353^4
                  (.node 1356705736214926934564253719405067984759049653 (.cut 5 7 4648463818759203534863266585393) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^2 * 37^10
                    (.node 1167124137782444038559149955840529927585011133 (.basic (.groups [5, 251, 631])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2 * 43^2 * 271^4
                      (.node 1155259250391902317331741296637665789264372677 (.cut 5 13 568610354953870303252118881) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^2 * 127^2 * 5419^4
                        (.node 1057134756771797446893380678022260733728180049 (.basic (.groups [131, 443, 26339])) .empty .empty)
                        .empty)
                      (.node 1346190415280357717581388673394393609973839593 (.cut 5 7 96787640124372291411173327505307) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^6 * 433^5
                        (.node 1216807395052846872914171970077418040907372781 (.basic (.groups [11, 131, 5581])) .empty .empty)
                        .empty))
                    (.node 1405280042770794929357509517503723029414452169 (.basic (.split 947)) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^10
                      (.node 1370243838233333443935012120048174384522747645 (.basic (.split 197)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^6
                        (.node 1360441100517334796984820514368465909146257881 (.basic (.groups [11, 31, 433, 8269])) .empty .empty)
                        .empty)
                      (.node 1555067558964351179794781212313781374759000853 (.basic (.groups [11, 128341, 492103, 57344741, 3706509671])) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^2 * 39103^4
                        (.node 1510398222385551176295818276121079471311508881 (.basic (.groups [18041, 48271, 246247])) .empty .empty)
                        .empty)))
                  (.node 2231044512780936467987028594142584104274439653 (.cut 5 13 1192592432217491052707090171977459) -- 3^6 * 1093 * 547^6 * 7^4 * 29^4 * 2801^4
                    (.node 1943379837334109055191308662896533843435208133 (.basic (.split 547)) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093
                      (.node 1859498355745776641668770637178134571062845693 (.basic (.groups [37, 127, 1621, 1693])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^8
                        (.node 1698637292435475586367159456552545840551836481 (.basic (.groups [7, 113, 1093, 47251, 518323723])) .empty .empty)
                        .empty)
                      (.node 2152670902084988912573584578909018376551195525 (.basic (.groups [6781, 12774841, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^2 * 31^6
                        (.node 2061836032097138251251535096896641991578968413 (.basic (.groups [37, 379, 22406023])) .empty .empty)
                        .empty))
                    (.node 2531685741248149694948731037882244324175070721 (.basic (.groups [11, 31, 61, 271, 10711])) -- 3^6 * 1093^14
                      (.node 2336794135838705214918416641456751347231210197 (.basic (.groups [292561, 1372537, 10196539, 45437789])) -- 3^2 * 13 * 7^4 * 2801^10 * 23^4
                        (.node 2311876684303777683145447460463718755352559277 (.cut 5 31 42612327480509667453583781490349361) .empty .empty)
                        .empty)
                      (.node 2539303778194563560364203754910338139770527409 (.basic (.split 52379047267)) .empty .empty))))
                (.node 4504836516564085506502553618698220738954438877 (.cut 5 31 168904425598774902678802586940100831) -- 3^6 * 1093^5 * 547^2 * 163^10
                  (.node 3211267186115974053183159261737881107249438441 (.basic (.groups [13, 139, 28411, 238639])) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^4 * 3500201^2
                    (.node 2722773274514230002613833013144932517162959681 (.basic (.groups [73, 12157, 26403131021])) -- 3^8 * 13^2 * 61^6 * 757^2 * 14713^4 * 1774921
                      (.node 2691557120753059132310119500842596512055998909 (.cut 5 7 7679926311431008201256050291) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2 * 127^2 * 617^6
                        (.node 2679075211848588450862072389452549830614862401 (.basic (.split 5229043)) .empty .empty)
                        .empty)
                      (.node 3182344092614633502076696819902560604428602557 (.cut 5 31 2292674787845104118064683105739199) -- 3^6 * 1093 * 547^8 * 163^8
                        (.node 2727103378481643256582660674869055747392257653 (.basic (.groups [23, 10847, 398581, 1193557])) .empty .empty)
                        .empty))
                    (.node 3738493973781313894423898266696439383426242357 (.basic (.groups [43, 67, 73])) -- 3^2 * 13 * 7^4 * 2801^8 * 37^8
                      (.node 3717811477577691308113475781113379133750000341 (.cut 5 101 862625735997684844049477) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^6 * 73^4
                        (.node 3326935245077322611666879102097599971129727637 (.cut 5 101 8460675771378699814015767804983) .empty .empty)
                        .empty)
                      (.node 4201506551929941362049289627987285924355760933 (.basic (.groups [127, 1499, 2683])) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^8
                        (.node 3797692204322223441928745285768451498593348973 (.basic (.groups [70841, 223939, 62966051321959646638153131367])) .empty .empty)
                        .empty)))
                  (.node 5327268394136719308179113746284458634833593753 (.cut 5 7 809760948706703286861512042749) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^9
                    (.node 4728853441776395731306580582507220102140145249 (.basic (.split 911)) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^2 * 19^4
                      (.node 4713725333482594020183300953935451646854230353 (.cut 5 101 388196429001955763381) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2 * 97^5
                        (.node 4670132716267552518948632065987295390967072921 (.basic (.groups [181, 631, 5113])) .empty .empty)
                        .empty)
                      (.node 4949894246927014502289135412847733235894682481 (.basic (.split 12601)) -- 3^2 * 13^2 * 61^12 * 187123^4
                        (.node 4920490513645975119013078241263784041997766693 (.cut 5 31 29891401431950940454630885030364023) .empty .empty)
                        .empty))
                    (.node 6360305114288455401314876068874236961206963737 (.basic (.groups [5, 1361, 1597])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^6 * 71^2 * 211^4
                      (.node 6338837133136136907217649846839319975491058025 (.basic (.split 37861)) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2 * 331^4
                        (.node 5578799857303185941193062611385260117690508769 (.basic (.split 4051)) .empty .empty)
                        .empty)
                      (.node 6595764727510254175879793597992363639620344841 (.basic (.groups [7, 13, 19, 9631, 761203, 32668561])) .empty .empty)))))
              (.node 41971151610684426935781250000464207130147248381 (.basic (.groups [31, 37, 73, 97, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^8
                (.node 14337362751697479535829267267557050746178665133 (.cut 5 13 101778305486758828638462035227648597) -- 3^2 * 13 * 7^10 * 1123^2 * 127^4 * 3313^6
                  (.node 11375527819748060562952516978576345771842523773 (.basic (.groups [199, 11299, 7960598843])) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^6 * 1499^2
                    (.node 9210794097871552312841130227314902778575637077 (.basic (.groups [67, 4933, 5839])) -- 3^2 * 13 * 7^4 * 2801^8 * 37^2 * 43^6
                      (.node 8384160177993669929063431147140948416726876601 (.basic (.split 113)) -- 3^6 * 1093^2 * 398581^6 * 7^4
                        (.node 8147208216748400209970466045480322844966399241 (.basic (.split 1806113)) .empty .empty)
                        .empty)
                      (.node 10553081265853084184820689996959149608143550625 (.basic (.groups [11, 71, 151841, 104670301, 32607907713428723311])) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5^4
                        (.node 9486419653792860161492128012361409652601202081 (.basic (.groups [5, 1361, 292661, 398581, 5091991])) .empty .empty)
                        .empty))
                    (.node 12858987110673584421247771578782513303656828893 (.basic (.groups [11, 1811, 5479])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^10 * 433^4
                      (.node 12183345162817856532689477201969067686345626089 (.basic (.groups [101, 5209, 8269, 14083, 1706822489])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^6 * 743^4
                        (.node 11853840451557150184256813883615987364086490209 (.cut 5 101 19084101687110059734610881999980099679311) .empty .empty)
                        .empty)
                      (.node 13615486596633093425233343002870530830042642649 (.basic (.groups [5, 11, 41, 151])) -- 3^2 * 13^2 * 61^2 * 97^10 * 89^2 * 8011^4
                        (.node 13044631217910551447651722402341832545671462157 (.cut 5 31 912079722042652709315922549469) .empty .empty)
                        .empty)))
                  (.node 24530020371307408188713639822999004034532949561 (.basic (.groups [1499, 3500201, 7960598843])) -- 3^4 * 11^6 * 43^4 * 45319^4 * 151^6
                    (.node 16751267816395194139714444149105334156713403893 (.basic (.split 29)) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^6
                      (.node 15783314884031142466072397906557121381890833561 (.basic (.groups [4733, 2384047, 3060947])) -- 3^2 * 13^4 * 30941^6 * 7^6 * 29^6
                        (.node 15426102020201360469739770919951680335387659689 (.basic (.split 398581)) .empty .empty)
                        .empty)
                      (.node 20915281307206216228057052100778957673474716041 (.basic (.groups [7, 241, 24979, 292561])) -- 3^6 * 1093^10 * 23^4 * 6491^2
                        (.node 18610561655051959263418072017779806298907157557 (.cut 5 31 1857748893874355090340259622270859901) .empty .empty)
                        .empty))
                    (.node 39181753370999216247944765474420049217958365977 (.basic (.groups [23, 1372537, 10196539, 45437789])) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^10
                      (.node 33832740776079590453838094053930171194246459829 (.cut 5 7 8938486691063875564266070681) -- 3^4 * 11^12 * 1093^2 * 398581^2 * 1621 * 811^4
                        (.node 31854410353714550258717703983132746188426407853 (.cut 5 101 4091266068975969713467408551751) .empty .empty)
                        .empty)
                      (.node 40372780568967771346102111705571201539222218813 (.cut 5 101 3112651710354338688272465815279) .empty .empty))))
                (.node 72309144105881458459481315675226042807927197013 (.cut 5 31 1773359798018163608171923640097583543) -- 3^2 * 13 * 7^2 * 19^4 * 151^12 * 911^4
                  (.node 61769016821545200905957115186079232213028621489 (.basic (.split 113)) -- 3^6 * 1093^2 * 398581^6 * 7^2 * 19^2
                    (.node 55617899633303660292890312758432691859482722089 (.basic (.groups [151, 911, 17311991])) -- 3^4 * 11^10 * 15797^4 * 1806113^2 * 19^4
                      (.node 52765406329265420924103449984795748040717753125 (.basic (.groups [7, 31, 151841, 104670301])) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5^5
                        (.node 45201107341723400732369574751565606516704956573 (.basic (.split 62060021)) .empty .empty)
                        .empty)
                      (.node 61114207637198153555278972297561330592224770261 (.basic (.groups [19, 307, 617, 1621])) -- 3^6 * 1093^2 * 398581^5 * 17^8
                        (.node 59200314430703188211125668319537864306497928293 (.cut 5 7 153156253755899993310611510571258852293) .empty .empty)
                        .empty))
                    (.node 65514182728514697534918559184071418507611572117 (.basic (.split 1483)) -- 3^2 * 13 * 7^4 * 2801^12
                      (.node 64131738377264692680451836069328883560260680169 (.basic (.groups [73, 8387, 30941, 62047])) -- 3^8 * 13^4 * 757^2 * 14713^6 * 7673^2
                        (.node 62914620021352743198148051488448061001789336357 (.cut 5 101 6765659592790782030175877410767221) .empty .empty)
                        .empty)
                      (.node 67756986592344388882853233685165143398722540841 (.basic (.groups [104281, 2384047, 3060947])) .empty .empty)))
                  (.node 89799482527700610758573348113843319070070932093 (.cut 5 7 23999923099192169797400850783263147) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2 * 37^9
                    (.node 83388196357869604501330157513011720926981475053 (.basic (.groups [29, 113, 15401])) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^2 * 1499^6
                      (.node 78710508801944822140135085152987009272537475401 (.basic (.groups [11, 1811, 14083, 28447])) -- 3^2 * 13^4 * 30941^2 * 157^10 * 433^4
                        (.node 74060215095162635289269399399720412126850955253 (.cut 5 7 5126310224165455091939209471) .empty .empty)
                        .empty)
                      (.node 89152138584219651806035633368930879503235590397 (.cut 5 31 314845082400798315358865959943089) -- 3^6 * 1093 * 547^2 * 163^6 * 613^8
                        (.node 88923740643025269156378131707710649452978492093 (.cut 5 7 14215070727785607056419148083327327379) .empty .empty)
                        .empty))
                    (.node 119116044366726222743532352098646178877560787789 (.basic (.groups [307, 617, 701, 1621])) -- 3^6 * 1093^2 * 398581^5 * 17^2 * 19^6
                      (.node 116189286921476932301279326471047071526427169781 (.cut 5 7 188280509299153787831700366073) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^12
                        (.node 114322583171164893912982748177595299906124217461 (.cut 5 101 51705308409005268873241) .empty .empty)
                        .empty)
                      (.node 132960713514870366004190448568001885606993047893 (.cut 5 13 1181656934012566501098649495379760330744779) .empty .empty))))))
            (.node 3083492107062664739288202324537606862824301955025 (.cut 7 31 12154958478999353643942783073021) -- 3^12 * 797161 * 398581^4 * 5^2 * 31^2 * 331^4
              (.node 629252969720765401832204346705898649276909938821 (.cut 5 257 381183560853492219637039) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^2 * 97^6
                (.node 357752425329115286022371515996066127575265130717 (.basic (.groups [911, 1499])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13 * 19^4 * 151^6
                  (.node 248321037303574684919352489629415494671726948533 (.cut 5 13 4165301373266086349623373301839) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^4 * 2801^4
                    (.node 209182703094712347881246361281897813491590852369 (.basic (.groups [1093, 1123, 151841])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^10
                      (.node 203139799104760792489500949758236594739749397117 (.cut 5 31 896197884376771071841021046527) -- 3^2 * 13 * 7^12 * 16148168401^2 * 433^2 * 37^6
                        (.node 150214964708048756903217707367094253089796561949 (.cut 5 7 1285842612521009342808246710507) .empty .empty)
                        .empty)
                      (.node 245584626924777572620199245057983651236920110117 (.basic (.groups [7561, 67411, 128341, 16975792017452101])) -- 3^2 * 13 * 7^2 * 19^6 * 701^6 * 70841^2 * 39103^2
                        (.node 235800697689413838012345950248657992681652044009 (.basic (.groups [19, 30941, 3798019, 3381319079812669342728169])) .empty .empty)
                        .empty))
                    (.node 332074036525559556102323779213774405923079980009 (.basic (.groups [7673, 8387, 52379047267])) -- 3^8 * 13^2 * 61^6 * 757^2 * 14713^6
                      (.node 292417856828378586422120299986411762248049886209 (.basic (.groups [31, 313, 1009])) -- 3^4 * 11^10 * 15797^2 * 1806113^2 * 19^2 * 127^2 * 5419^2
                        (.node 263827031646327104620517249923978740203588765625 (.basic (.groups [19531, 151841, 104670301, 32607907713428723311])) .empty .empty)
                        .empty)
                      (.node 356391654335419154677842168519049197788994905301 (.cut 5 257 81671938142413085724071) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^4 * 97^4
                        (.node 348944139859502601143334117806012118871832100429 (.cut 5 7 9303525036216680082062513184891391) .empty .empty)
                        .empty)))
                  (.node 411053377567138998058483611403980021591869507097 (.cut 5 31 636655419214922106456351866089799) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^6 * 71^8
                    (.node 384993289508345875996954484193064912344449756481 (.basic (.split 1499)) -- 3^2 * 13^6 * 5229043^4 * 151^6
                      (.node 365087841298975571083374428862683134290558256413 (.basic (.groups [109, 337, 433])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^6 * 281^8
                        (.node 363913524298379470305973245524433576125523929601 (.cut 5 13 59006860842304131818918751623756133607) .empty .empty)
                        .empty)
                      (.node 410823848721689826524108126209906472419616953449 (.basic (.groups [29, 113, 4733, 47251, 518323723])) -- 3^6 * 1093^2 * 398581^6 * 7^6
                        (.node 391610189486651957635904447438669534252646415173 (.cut 5 13 114418975704456208715211421900909) .empty .empty)
                        .empty))
                    (.node 539990132440977638535404772346047047772174833589 (.cut 5 7 192595694487391892216845595617711) -- 3^4 * 11^12 * 1093^2 * 398581^2 * 1621^5
                      (.node 484890587376513651476783404077928319481553888293 (.cut 5 31 2067493615545075912884004391221063239) -- 3^2 * 13 * 7^2 * 19^6 * 701^10 * 89^4
                        (.node 450392519677994203482255993275198433380673476025 (.basic (.groups [23, 397, 617])) .empty .empty)
                        .empty)
                      (.node 598821845815847470535699451416452623714036750441 (.basic (.groups [43, 8269, 14083, 16183, 552793])) .empty .empty))))
                (.node 1707116092481278859001675590285106456872592434889 (.basic (.groups [701, 1093, 70841, 151841])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^2 * 19^6
                  (.node 947410100113284701984167719626927171090137055913 (.basic (.groups [19, 2801, 47251, 518323723, 189361597248713])) -- 3^6 * 1093^2 * 398581^6 * 7^4 * 113
                    (.node 806028480785840435114224288167573495491375826453 (.basic (.groups [5, 61, 71, 19743162529239426375290171925151])) -- 3^2 * 13 * 7^2 * 19^6 * 701^6 * 70841^4
                      (.node 748755915454317979789556326710207113776784215761 (.basic (.groups [5, 911, 2384047, 3060947])) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^4 * 151^4
                        (.node 743380863297532804827314840329809629253869372589 (.cut 5 7 1423032002610542767011956443153) .empty .empty)
                        .empty)
                      (.node 901094865860125728266434367121462362524902526077 (.cut 5 31 1269722815201466519008741520173528121) -- 3^6 * 1093^5 * 547^2 * 163^6 * 613^4
                        (.node 888046899553604471654200165422151558063373267769 (.basic (.split 7)) .empty .empty)
                        .empty))
                    (.node 1496700735489024774162271014088787506838449311141 (.basic (.groups [4447, 38047, 6038099])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^2 * 43^10
                      (.node 1236164097858675058691842403330621462685310194213 (.basic (.groups [29, 1372537, 5336717])) -- 3^2 * 13 * 7^4 * 2801^10 * 23^6
                        (.node 1025690911815500553936675502537276603289724429453 (.cut 5 101 160845099062864024859244051993789) .empty .empty)
                        .empty)
                      (.node 1621595655199315285599639681252455499382302463941 (.basic (.groups [5, 11, 211, 281])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^6 * 71^4
                        (.node 1534564232032055150297021849047255455699476544081 (.basic (.groups [5, 9631, 30941])) .empty .empty)
                        .empty)))
                  (.node 2545049690601743626173547404435175790833181034093 (.basic (.groups [5, 11, 421, 14621, 6579701, 477869921, 4440731591])) -- 3^2 * 13 * 7^2 * 19^2 * 127^4 * 262209281^4
                    (.node 2124114162206181197324100368545911490874682489369 (.basic (.split 2801)) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093^2
                      (.node 2068716736903674344983214780331566659865698899525 (.cut 7 31 277121826701357568956457632701) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^2 * 31^8
                        (.node 1851101945022518296537007693346315205710607287021 (.basic (.groups [307, 7580566663, 136219001651])) .empty .empty)
                        .empty)
                      (.node 2295485884828616777192950485543483388670759084901 (.cut 5 7 61818217066383792618900824880017) -- 3^8 * 13^2 * 61 * 31^2 * 331^6 * 757^2 * 14713^4
                        (.node 2226162482800363477308698210219491200161651928597 (.cut 5 13 16178484420010871361985181903701802648663) .empty .empty)
                        .empty))
                    (.node 2931056819964600097042759083412435696522858633677 (.cut 5 31 8570433220549044262910676872143010210743) -- 3^6 * 1093 * 547^4 * 431^12
                      (.node 2783147731627591149125539700031932546792693218773 (.basic (.groups [743, 5209, 1706822489])) -- 3^2 * 13 * 7^12 * 16148168401^2 * 433^6
                        (.node 2652834376364354195642022343214783887363394378901 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 3055065506691355757775291983970049577580214988349 (.basic (.groups [17, 19, 617])) .empty .empty)))))
              (.node 19812217364011516980936712437553197403753751817189 (.cut 5 7 445902457286823550573723478047) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^6 * 73^6
                (.node 6979898900834607702373154016026953240072234228257 (.basic (.split 127)) -- 3^6 * 1093^2 * 398581^6 * 7^2 * 19^2 * 113
                  (.node 4553923130891245803990159054332267655162467451321 (.basic (.groups [37, 127, 1621, 1693])) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^8
                    (.node 3418011972703446866015909063947467276908810141829 (.cut 5 7 739438149501642192458701950204728317943) -- 3^2 * 13^2 * 61 * 31^2 * 331^12 * 53^6
                      (.node 3208473107946533634994726780205014143128863806321 (.cut 5 31 100143927839752385018150312929) -- 3^12 * 797161 * 398581^2 * 1621^8
                        (.node 3190932676389708751437114551127041393518328247237 (.cut 5 7 103760866142632740015433639627178551) .empty .empty)
                        .empty)
                      (.node 4343908672882954263883042742032626185600343139509 (.cut 5 7 24946235552554662692491945466311) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^10
                        (.node 3545488542361111861660924161440371015841128611309 (.cut 5 7 532446078232026512815937809621) .empty .empty)
                        .empty))
                    (.node 5117998250106618721466316727107425515910525786733 (.cut 5 31 506261251012508826614848601588561992474019) -- 3^2 * 13 * 7^4 * 2801^8 * 37^10
                      (.node 4975410832248447306486225542091938183196640396641 (.basic (.groups [5, 1361, 292661, 4105333, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^6 * 211^4
                        (.node 4611875014823835624164507611842313193892675118809 (.basic (.groups [5, 11, 1774921, 69617111])) .empty .empty)
                        .empty)
                      (.node 6595675791158177615512931248099468505089719140625 (.basic (.groups [19, 31, 829])) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5^8
                        (.node 5615928599029681454099775401297347513214066406429 (.cut 5 13 19786541075052012959227297) .empty .empty)
                        .empty)))
                  (.node 11503576521904378426748726756827089793922705811033 (.cut 5 101 4986708902591693388557504874277873) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^8
                    (.node 7657514835817156063251784970555741171789808568845 (.basic (.groups [7673, 8387])) -- 3^8 * 13^2 * 61^4 * 5 * 131^2 * 757^2 * 14713^6
                      (.node 7559180143234767633810163864607071821804990760389 (.cut 5 7 2287254171885185971889958719477) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941 * 191^6
                        (.node 7394596173015668075546362764111954382707010478805 (.basic (.split 1247451159302262598804596798564656994853573)) .empty .empty)
                        .empty)
                      (.node 10691734623294122019101145422345621459824578987261 (.basic (.groups [5, 11, 811, 32668561, 125613804731])) -- 3^6 * 1093^2 * 398581^2 * 1621^9
                        (.node 7774664553928542707242855343292889367301932264817 (.cut 5 13 2177236088490934675169224112387) .empty .empty)
                        .empty))
                    (.node 17662006007150266377475622993995224541152958605429 (.basic (.groups [19, 617, 1621])) -- 3^6 * 1093^2 * 398581^5 * 17^10
                      (.node 16739697326022575738003049238787979178597414970889 (.basic (.groups [43, 86353, 162709, 2384047])) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^2 * 127^6
                        (.node 11841739249507540023912985288999383510159448953093 (.cut 5 7 50058149748260866457435753906226011861) .empty .empty)
                        .empty)
                      (.node 18019816953125066945532795746137599294169757643009 (.basic (.groups [11, 23, 89, 4051])) .empty .empty))))
                (.node 34081650311242107986678491871243375015008726848633 (.cut 5 101 3141624883428124630840398419630237) -- 3^2 * 13^4 * 30941^2 * 157^10 * 433^5
                  (.node 27732382568932674853638449241670142980313008806801 (.cut 5 101 259457201998148394490087279350188451941969) -- 3^2 * 13^18 * 12865927^4
                    (.node 22298615072577817527050518582174602828903332357529 (.basic (.groups [113, 151, 911, 47251, 518323723])) -- 3^6 * 1093^2 * 398581^6 * 7^2 * 19^4
                      (.node 20446260736433206273516492003851052803143895722097 (.cut 5 7 7575261190288387259624237471663147) -- 3^2 * 13^10 * 23^4 * 419^2 * 859^2 * 13537^5
                        (.node 20130368587362801499681298184285417148561230719001 (.basic (.groups [19, 37, 113, 1063])) .empty .empty)
                        .empty)
                      (.node 25400280605076995490226770258158131062631617705861 (.basic (.groups [109, 727, 5113, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^6 * 71^2 * 281^2
                        (.node 22320115978761788061124206491410612545082877887245 (.basic (.split 421)) .empty .empty)
                        .empty))
                    (.node 33332400305116945012550871136389800225881589041809 (.basic (.groups [5, 1956611, 2384047, 3060947, 6294091])) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^4
                      (.node 32978378955790888077564656240497342525448595703125 (.cut 7 101 270005856885214245060438696011543371) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5^9
                        (.node 27979686249033772198046646150939416955751627425525 (.basic (.groups [6781, 37861, 63601])) .empty .empty)
                        .empty)
                      (.node 33533512686651785410878840858668316194546110508769 (.cut 5 101 836281651542594879903697242127367938250339) .empty .empty)))
                  (.node 51185259756905964017356023705468991938588491317437 (.cut 5 31 64356424100362619689988886794173276085647841) -- 3^6 * 1093 * 547^16
                    (.node 43000892016388166410415179107611270574799444391829 (.basic (.groups [127, 307, 523])) -- 3^6 * 1093^2 * 398581^5 * 17^2 * 19^8
                      (.node 39850317909510938624086465592023200763199195437521 (.basic (.groups [19, 3798019, 5229043])) -- 3^8 * 13^6 * 757^2 * 14713^8
                        (.node 34402389899027648512002045559229764455358581911997 (.basic (.groups [23, 6491, 830833])) .empty .empty)
                        .empty)
                      (.node 49916858908480391489276338965484828801964960872005 (.basic (.groups [151, 331, 911, 184725139, 2703853428809791])) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^4
                        (.node 43514298078126619111055808105685426345105290120681 (.basic (.split 19)) .empty .empty)
                        .empty))
                    (.node 54920077081594851414078774553180357173479236315677 (.basic (.groups [23, 89, 732541])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^10
                      (.node 54740487251955285601268383722178129496208737683437 (.basic (.split 398581)) -- 3^6 * 1093^8 * 56773 * 28387^4
                        (.node 53177793117997437625673885366949599688943313354805 (.basic (.groups [19, 2053, 12342821, 85161343])) .empty .empty)
                        .empty)
                      (.node 58246739604209713413386614456014936492871058155821 (.basic (.split 31747594185191)) .empty .empty)))))))
          (.node 110117266240355714071444007689178176985115024595173717 (.basic (.split 5)) -- 3^2 * 13 * 7^12 * 16148168401^4
            (.node 3353289075641958826363816963595733901996653063977109 (.cut 5 7 262041881730361633694787728897) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^4 * 97^6
              (.node 581476737748901436294736273716608994760405190266797 (.basic (.groups [163, 613, 2801, 151841])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093 * 547^2
                (.node 239994712697667279444167440851183493592066947884525 (.basic (.groups [11, 1721, 63601, 1866871])) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2 * 331^4 * 37861
                  (.node 107057341312801171324210952317842770333185487318169 (.basic (.groups [13, 991, 2801, 47251, 518323723])) -- 3^6 * 1093^2 * 398581^6 * 7^4 * 113^2
                    (.node 84551700196678197516675757807991132699063541336933 (.cut 5 7 72914149496593115862391746813460981223639) -- 3^6 * 1093 * 547^8 * 163^10
                      (.node 72143097433580581029781995470699744886028296417489 (.basic (.groups [11, 31, 41, 2384047])) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801 * 467^4
                        (.node 62373617405527309743345395337294286505508893943081 (.basic (.split 6301)) .empty .empty)
                        .empty)
                      (.node 85714763802880472635822531906884358411770802618653 (.cut 5 31 86282133286145837817259039289497) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2 * 43^2 * 271^6
                        (.node 85319894917786663096131152399062401423965406351861 (.basic (.groups [5, 1801, 3169])) .empty .empty)
                        .empty))
                    (.node 128701448199974478116903452120452659981934208810077 (.basic (.groups [2633, 443791, 1806113])) -- 3^4 * 11^10 * 15797^9
                      (.node 121226008196592312939996999750628036324156973720637 (.cut 5 31 16879338057378245047937737444852149329929) -- 3^6 * 1093^5 * 547^4 * 431^8
                        (.node 119689001408591187822266347095193026813280486523013 (.cut 5 7 103215298725878558953281484271467562085541) .empty .empty)
                        .empty)
                      (.node 206708995579979285063730316647929837277283523075649 (.basic (.split 23)) -- 3^2 * 13^4 * 30941^10
                        (.node 142126922541607977383289269941001964234399444252213 (.cut 5 31 781310687635899994695912063953506074617) .empty .empty)
                        .empty)))
                  (.node 389630155906176203910778074185819510344753554142005 (.basic (.split 127)) -- 3^12 * 797161^4 * 5 * 2671^6
                    (.node 294673856482144843638310663186189136204738777901777 (.basic (.groups [5, 45121, 487681])) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^2 * 732541^4
                      (.node 283167143993236322921939597462349903749895232534977 (.cut 5 31 298353084040494124072944968463263) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^6 * 71^2 * 211^6
                        (.node 263474549939053570510310101927255527061886222713641 (.basic (.groups [79, 8269, 14083, 473201])) .empty .empty)
                        .empty)
                      (.node 348635487220419916769836137993891272594001876134877 (.basic (.groups [947, 14083, 39449441])) -- 3^2 * 13^4 * 30941^2 * 157 * 79^4 * 433^10
                        (.node 312224639962378005030450054547429097196003666872049 (.basic (.groups [1231, 4591, 60217])) .empty .empty)
                        .empty))
                    (.node 425034982855787090149338871478957108917475829866109 (.basic (.groups [7, 71, 617])) -- 3^2 * 13^2 * 61 * 31^12 * 42407^6
                      (.node 422344889406511927249791031238342319143458117848201 (.basic (.groups [7, 307189, 398581, 5091991])) -- 3^6 * 1093^8 * 56773^2 * 211^6
                        (.node 411526623219852868445919976008474925159808772923649 (.basic (.groups [7, 29, 211])) .empty .empty)
                        .empty)
                      (.node 531489977966861956079199427306252444952600472802893 (.cut 5 7 28934666683336652806438184492967758429219) .empty .empty))))
                (.node 1331528639223276149269163553879376329227461033836189 (.cut 5 7 237896064835800302414338542694675164161) -- 3^2 * 13^2 * 61 * 31^12 * 42407^2 * 1471^6
                  (.node 788728575794310670368166403811045716128162467793041 (.basic (.groups [13, 127, 991, 47251, 518323723])) -- 3^6 * 1093^2 * 398581^6 * 7^2 * 19^2 * 113^2
                    (.node 694489335143528295691672934869562735834775808277025 (.basic (.groups [1866871, 2180921, 604842197, 2703853428809791])) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2 * 331^6
                      (.node 653930807767239106047984631361898753760529092738677 (.cut 5 31 795856068305232647810321978663284694910809) -- 3^2 * 13 * 7^4 * 2801^10 * 23^8
                        (.node 609225045719137719662285065038405353199735954849669 (.cut 5 7 4570341980641728111509411994641) .empty .empty)
                        .empty)
                      (.node 784270160206402102699480841973626508256274893264605 (.basic (.split 366340651)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2
                        (.node 748105562845786670049284839296525934069242978515625 (.basic (.groups [19, 331, 12207031])) .empty .empty)
                        .empty))
                    (.node 875786089992891837948536014438416747680963603523597 (.basic (.groups [7, 211, 28387, 398581, 5091991])) -- 3^6 * 1093^8 * 56773^5
                      (.node 815973874772113997158841317866895301121490020096477 (.cut 5 31 26306253685426866095709994691513310752666629) -- 3^6 * 1093^5 * 547^12
                        (.node 810308766421502298738852702323808452205756570094845 (.basic (.groups [19, 31, 2593, 6367])) .empty .empty)
                        .empty)
                      (.node 1260267789877233829802178752882996346286145435228721 (.basic (.groups [7, 277, 463, 8269])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^10 * 947^2
                        (.node 986388060780777273484383611029985440279500305231049 (.basic (.groups [113, 1123, 47251])) .empty .empty)
                        .empty)))
                  (.node 2767399659919206807426039105050168100144292776299709 (.cut 5 7 266730160638739775532864731495540683) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^2 * 43^12
                    (.node 2132200605828204336441734597178585890910159215913369 (.basic (.split 29)) -- 3^2 * 13^6 * 5229043^6 * 7^4
                      (.node 1971848715675909433127738870525871894685348406421993 (.cut 5 101 581563435109225599359622374470534351) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^9
                        (.node 1866189746896144921587227362171902834860270278681173 (.cut 5 31 98171834883421549153405808418596324700765223) .empty .empty)
                        .empty)
                      (.node 2410918634393079669555323445534354636789315192319677 (.cut 5 7 892134035792988187964827114487588094869) -- 3^2 * 13^4 * 30941^2 * 157 * 79^10 * 433^6
                        (.node 2230218884584155773768803521258462060240700426328445 (.basic (.split 331)) .empty .empty)
                        .empty))
                    (.node 3277402427319253785696782101358397884105337073319313 (.cut 5 101 3874707257454688423340591) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^2 * 61^2 * 97 * 2801^4
                      (.node 3024475839096360784920806585674985299631424061771929 (.cut 8 257 4152600144877475715539930757350827985168536481201) -- 3^6 * 1093^16
                        (.node 2851826531083606042249758342168215523745956318184413 (.cut 5 31 4288418517654311304712000100212206699719) .empty .empty)
                        .empty)
                      (.node 3323885521738249300524292998411681212808255905071797 (.basic (.groups [5, 11, 61, 101])) .empty .empty)))))
              (.node 15523322017916128074159879657847668677502599425450269 (.cut 5 7 10313017623147704432808716288259843287959) -- 3^6 * 1093^2 * 398581^5 * 17^2 * 19^10
                (.node 6725803513788434881014693199869821847179416536806361 (.basic (.groups [7, 281, 3767, 5209])) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^6 * 743^6
                  (.node 4832707463174071630469347105524216768295397559960201 (.basic (.groups [26403131021, 52379047267, 1050115443721])) -- 3^8 * 13^2 * 61^6 * 757^2 * 14713^4 * 1774921^2
                    (.node 3924574777252508121721688663614974614388251485195329 (.basic (.groups [1093, 151841, 830833, 32607907713428723311])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^2 * 19^4 * 911^2
                      (.node 3486918519084248865133308497348836321627257469276293 (.cut 5 31 4703358971321786354511658272025440166785577) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^10
                        (.node 3469335665104345798675645966008505046325146523504417 (.basic (.groups [7, 11, 521])) .empty .empty)
                        .empty)
                      (.node 4658978129371560697729774719343473326513585221366689 (.basic (.groups [29, 72577051, 175421429, 917087137])) -- 3^2 * 13^6 * 5229043^2 * 31^6 * 4051^6
                        (.node 4298314413921786475981958199181362531414233799970881 (.cut 5 31 4909420696277607428069196166483) .empty .empty)
                        .empty))
                    (.node 5480008499497006790726201600321800842280959887900973 (.basic (.groups [71, 211, 1597])) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13 * 2801^6
                      (.node 5264761491804330309507978014810925642543739349876733 (.cut 5 7 7294234405121522008048914834110931461744509) -- 3^2 * 13^4 * 30941^2 * 157^17
                        (.node 5104319736066426983090455045264619892393205036968981 (.cut 5 7 61051997145430521142229528621910178667063) .empty .empty)
                        .empty)
                      (.node 6148551169313878457389347633045260699759148786501309 (.basic (.groups [17, 19, 617, 10010548486153, 10389030590500306061])) -- 3^6 * 1093^8 * 56773^4 * 398581
                        (.node 5554139478591768751561431006052303730282712819608157 (.basic (.groups [523, 1867147, 22299994021, 1437263292796553])) .empty .empty)
                        .empty)))
                  (.node 10075942946673429069806025892236866306942357864304897 (.basic (.groups [13, 17, 19, 17707])) -- 3^4 * 11^10 * 15797^2 * 1806113^5
                    (.node 8728859398492090107352559989420926848019519520757481 (.basic (.groups [19, 127, 883, 110557])) -- 3^4 * 11^6 * 43^4 * 45319^8
                      (.node 8174463697859748354707783633193628172386186720726581 (.cut 5 31 2433016071869437371879682537112117) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^6 * 71^6
                        (.node 8049800041200592127265237208165031621234102981067969 (.basic (.groups [113, 701, 47251, 70841])) .empty .empty)
                        .empty)
                      (.node 9508659083255320599415236015000774763853970617438289 (.basic (.groups [31, 37, 3529, 123127])) -- 3^4 * 11^16 * 50544702849929377^2
                        (.node 8778231994079794318606559194086073066365798897523281 (.basic (.groups [7, 1093, 111187, 151841, 35537473])) .empty .empty)
                        .empty))
                    (.node 14757354584767832758231786980248381381498778725458089 (.cut 5 101 851918962428786122176691086302173799868283) -- 3^2 * 13^4 * 30941^2 * 157^10 * 433^6
                      (.node 14714778673976103348430388340800602334490798232360233 (.basic (.groups [17, 17707, 249561007])) -- 3^4 * 11^10 * 15797^8 * 1806113
                        (.node 11847853452447809306331371772223369847694413018844933 (.basic (.groups [6301, 492103, 732541])) .empty .empty)
                        .empty)
                      (.node 15122379195481803924604032928374926498157120308859645 (.cut 11 257 4152600144877475715539930757350827985168536481201) .empty .empty))))
                (.node 46187784825621270039240249399224680382896037741484357 (.cut 5 31 938709158488361274491799849870786244404331) -- 3^2 * 13 * 7^6 * 29^6 * 4733^10
                  (.node 24821091218540384307286912513876741885009659119386005 (.basic (.groups [10378063, 22939801, 1431873631, 45548808606973099])) -- 3^4 * 11^4 * 5 * 3221^8 * 24517^4
                    (.node 17331301824359771792962956729622252386375642538350081 (.basic (.split 12893)) -- 3^6 * 1093^2 * 398581^2 * 1621^10
                      (.node 17072383628273904257181673805319432401224456903566561 (.basic (.groups [911, 1499, 2384047])) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^4 * 151^6
                        (.node 15708661606203709499091146726152438910583009733565841 (.basic (.split 29)) .empty .empty)
                        .empty)
                      (.node 21096578898345766569481997865837265738727188313781309 (.cut 5 7 11110310100546079298382450669041) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^4 * 5419^4
                        (.node 18019986065961421327628758366540023197509350874793805 (.basic (.groups [331, 701, 70841, 184725139])) .empty .empty)
                        .empty))
                    (.node 28827701036808410068314328277426322966716770484626893 (.cut 5 7 16458235778946715964823722864910115003649) -- 3^2 * 13^4 * 30941^2 * 157 * 79^6 * 281^10
                      (.node 27605307808530971968628979531555318777847578352399701 (.basic (.groups [23, 32668561, 620453153, 8635898822607632819])) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^10
                        (.node 25560822386501711833014868603378027525675922760454773 (.cut 5 31 298908738266284412078237907115799130703) .empty .empty)
                        .empty)
                      (.node 33500609963653634339502203915409787660051334567890293 (.cut 5 7 141615899057092701850410597960402055773779) .empty .empty)))
                  (.node 91551458517059520509728814483461561072631980895060169 (.basic (.groups [5471551, 37680901, 249561007, 69710210289691])) -- 3^4 * 11^10 * 15797^2 * 1806113^4 * 4051^2
                    (.node 61833817569017925756810303318178990836394617261487701 (.basic (.groups [5, 239, 2801, 108263, 3891879327005091062913468854183])) -- 3^2 * 13^6 * 5229043^6 * 7^4 * 29
                      (.node 49974926956311585920491205850311752168185802696265625 (.basic (.groups [191, 1866871, 4760281, 32009891])) -- 3^6 * 1093^2 * 398581^4 * 5^6 * 19531^4
                        (.node 46226840130713080559221628379534220839204320219633157 (.basic (.split 88009573)) .empty .empty)
                        .empty)
                      (.node 86660941497353562870538728526956845032608543644636721 (.basic (.groups [19, 37, 61, 151, 1657])) -- 3^12 * 797161^8
                        (.node 75611895977409019623020164641874632490785601544298225 (.basic (.split 31)) .empty .empty)
                        .empty))
                    (.node 104477829685582012485644995261750708654597801579755081 (.basic (.groups [29, 239, 4733, 108263, 3891879327005091062913468854183])) -- 3^2 * 13^6 * 5229043^6 * 7^6
                      (.node 93364053254632562980154990053027830432694330906107009 (.basic (.groups [19, 37, 43, 467])) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^5
                        (.node 92596113030558938666402675713896446031166804622785629 (.basic (.groups [11, 281, 38047, 3500201])) .empty .empty)
                        .empty)
                      (.node 109349058661809041798713337506754883919682983707018321 (.basic (.split 7)) .empty .empty))))))
            (.node 8430715485837737587191178871464683568065270820905118761 (.cut 5 7 4094757185470268611782911477377900285271) -- 3^12 * 797161 * 398581^2 * 1621^10
              (.node 1367015191223158156638849650146534334384445487565699961 (.basic (.groups [11, 251, 2801, 47251])) -- 3^6 * 1093^2 * 398581^6 * 7^4 * 113^4
                (.node 404284762146605044889972166585284915127200707137736929 (.basic (.groups [5, 11, 72931, 2180921])) -- 3^2 * 13^6 * 5229043^2 * 31^2 * 331^6 * 4051^4
                  (.node 148199316115721678461119522698074279681939779026824521 (.basic (.split 19)) -- 3^6 * 1093^16 * 7^2
                    (.node 119618382402861289487965277033822439877563576963632397 (.cut 5 31 179982614657077907144353038559617843396311) -- 3^2 * 13 * 7^4 * 2801^6 * 71^2 * 211^10
                      (.node 114084480123610196030964274134501643217796734435006553 (.cut 5 101 722615385080892059889956663459944449991) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^13
                        (.node 112578789371561387631576601124498728809125065867557153 (.basic (.groups [5419, 47251, 518323723, 189361597248713])) .empty .empty)
                        .empty)
                      (.node 144084621418812360626873503109377245938186546829624813 (.basic (.groups [733591, 8932457, 22867937, 770146437854801511784879])) -- 3^2 * 13 * 7^4 * 2801^12 * 1483^2
                        (.node 142696024833664298047274030018013012532233260851069269 (.basic (.groups [61, 157, 191])) .empty .empty)
                        .empty))
                    (.node 221510265662533122532073247359475179854097627098853961 (.basic (.groups [7, 307189, 4105333, 32668561])) -- 3^6 * 1093^2 * 398581^2 * 1621^6 * 211^6
                      (.node 202808580198612127086891099890715640252859844973307781 (.cut 5 7 2281486702512879669534227181923814808490872549) -- 3^2 * 13^2 * 61 * 31^2 * 331^18
                        (.node 187373360604329359184093365261894849934648301425566053 (.cut 5 31 8879913974172246180494369935660826063801) .empty .empty)
                        .empty)
                      (.node 338603516649393584784949775698864790503620097321428213 (.cut 5 7 477122472545445384598876681188481550415583) -- 3^6 * 1093^5 * 547^2 * 163^6 * 613^6
                        (.node 307404403429264821994091699950875412564463374067517177 (.basic (.groups [1483, 8932457, 22867937])) .empty .empty)
                        .empty)))
                  (.node 853810493887668784544310930937702530398755859980722969 (.cut 5 101 49289142297520747780369389302978536182114803) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^10
                    (.node 554754190696743413435523619906622828116979108216959761 (.basic (.split 1621)) -- 3^6 * 1093^2 * 398581^8
                      (.node 544476045933444078626759970093777467421782742650473197 (.cut 5 7 318410449096482202264510049289231561931184123) -- 3^6 * 1093 * 547^4 * 431^14
                        (.node 513998137529017639494654582853109905114735857812707317 (.basic (.groups [5, 37, 43, 61])) .empty .empty)
                        .empty)
                      (.node 785969952927049630075895326645245304255917572576763681 (.basic (.split 52932601)) -- 3^2 * 13^2 * 61^12 * 187123^4 * 12601^2
                        (.node 586317727402634439976184168255437352828949762472246473 (.cut 5 7 84475904587744122683561521444521695420434211) .empty .empty)
                        .empty))
                    (.node 881225241454305392040242248783339986752081762407452321 (.cut 5 101 1694803976220585728983611609476887071070548991) -- 3^6 * 1093^10 * 23^4 * 6491^4
                      (.node 873789115299403596262079473786722533883047069801984529 (.basic (.split 29)) -- 3^2 * 13^2 * 61^2 * 97^10 * 89^2 * 8011^6
                        (.node 865080306518542691711032722936301051102890947262563481 (.basic (.groups [199, 11299, 151841, 7960598843, 32607907713428723311])) .empty .empty)
                        .empty)
                      (.node 1217691064722547269289833654262766330681499670271132769 (.basic (.groups [7, 113, 47251])) .empty .empty))))
                (.node 2627859229135032632444718953579233285533775110757471437 (.basic (.groups [5, 61, 181])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^6 * 70001^4
                  (.node 1974269165201335459619518634742581516268532817125709049 (.basic (.groups [53, 4051, 37181])) -- 3^2 * 13^6 * 5229043^2 * 31^2 * 331^12
                    (.node 1699702888453664012824250230510490155515946117929014025 (.basic (.groups [19, 331, 184725139, 917087137])) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^6 * 1866871^2
                      (.node 1392162776359893712060884518708220515588442608076437721 (.basic (.groups [4051, 17311991, 37680901, 3597318971])) -- 3^4 * 11^10 * 15797^4 * 1806113^4
                        (.node 1391917873086650592745428190282696908259897721782449861 (.basic (.groups [7908811, 5889307277311, 3234152111453204401])) .empty .empty)
                        .empty)
                      (.node 1946468500981206914886088042159319905722804883632746805 (.basic (.groups [7, 42337, 77797, 104670301, 32607907713428723311])) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5 * 151841^2
                        (.node 1793180709501519846947498796227190734255443900583143329 (.basic (.groups [67, 239, 2801, 108263, 3891879327005091062913468854183])) .empty .empty)
                        .empty))
                    (.node 2063776973116362556814777817205947014328201047986627245 (.basic (.groups [661, 991, 2311])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^6 * 197^4
                      (.node 2033096777214996830812723833146790669734614696572786369 (.basic (.groups [463, 1806113, 116880853])) -- 3^4 * 11^10 * 15797^10
                        (.node 2005631556857484640903796006354424186836455165672490421 (.cut 5 31 2984734141902993398565353391422891) .empty .empty)
                        .empty)
                      (.node 2537570859765452161202039181183004616661948561242186481 (.basic (.groups [11, 31, 2801, 151841])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093^4
                        (.node 2377767667665230794647999939022871827479858928506051477 (.basic (.groups [43, 7547, 128341, 492103])) .empty .empty)
                        .empty)))
                  (.node 5358103874428643048136953537830989312064466201643897729 (.basic (.split 19)) -- 3^2 * 13^4 * 30941^10 * 23^2 * 7^2
                    (.node 3775751543608033995768421536501377097259614766441583001 (.basic (.groups [31, 71, 281])) -- 3^8 * 13^4 * 757^2 * 14713^6 * 7673^4
                      (.node 3065482405130389115790188598943073461089104052367944525 (.cut 7 31 3733028187992217559510787949544897) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^2 * 31^2 * 331^6
                        (.node 2905977814873413757942750632147576415265511176165536809 (.basic (.groups [113, 127, 523])) .empty .empty)
                        .empty)
                      (.node 5119413654593518611796604767825784724075292277407998969 (.basic (.groups [19, 29, 37, 239])) -- 3^2 * 13^6 * 5229043^6 * 7^8
                        (.node 4619633454830776920092002719352578005959982252548731813 (.cut 5 31 5395003549223466926867664662383092186441619) .empty .empty)
                        .empty))
                    (.node 6505214969812073099273981770320948374300875665800563605 (.basic (.groups [127, 331, 523])) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^8
                      (.node 6284344784610715992876939558543082882350530074756398645 (.cut 7 13 468664664302158135192510656946354045796219) -- 3^12 * 797161^4 * 5 * 2671^6 * 127^2
                        (.node 5670826839839539129171903968141030446720466513817268601 (.basic (.groups [29, 151, 239, 911, 108263])) .empty .empty)
                        .empty)
                      (.node 7402371179931888439736473336529392288544477679594119013 (.cut 5 7 39005468915354729187018842405749735834326917) .empty .empty)))))
              (.node 154472716608216871700190010466558379785442340094924095593 (.basic (.groups [13, 19, 991])) -- 3^6 * 1093^2 * 398581^6 * 7^4 * 113^5
                (.node 35971200389457848475117031994377734569622257176251489405 (.basic (.groups [331, 184725139, 262209281, 2703853428809791])) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^2 * 127^4
                  (.node 15733615976192155336204125610209436662449025137393758521 (.basic (.groups [449, 104707, 2384047])) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801 * 467^6
                    (.node 10071275184317552949931116810263242749240506551249340529 (.basic (.groups [11, 127, 251, 47251])) -- 3^6 * 1093^2 * 398581^6 * 7^2 * 19^2 * 113^4
                      (.node 9347733007087624595475225187993675762411073885316243021 (.cut 5 7 245950649320298811787166572933) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^2 * 97^2 * 331^6
                        (.node 9086439817446380867035623478066658250889246713856001025 (.basic (.groups [37, 1201, 10753, 63601])) .empty .empty)
                        .empty)
                      (.node 13878014785375831139238209778648811103335103894822672397 (.basic (.groups [5, 198031, 1806113])) -- 3^4 * 11^10 * 15797 * 2633^4 * 1717451^4
                        (.node 13210984410817319688735654396694201123800311185928872281 (.basic (.groups [67, 127, 239, 108263, 3891879327005091062913468854183])) .empty .empty)
                        .empty))
                    (.node 18803216821267317513087946501762238390585898864719756721 (.cut 5 31 685486702488443681571281564601960828370591) -- 3^6 * 1093^8 * 56773^2 * 211^8
                      (.node 16664952195118977407907159175564171738717899813275915769 (.basic (.groups [37, 43, 4933, 151841])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093^2 * 2801^2
                        (.node 16248240940198390010172568026609023643469708408742703321 (.basic (.groups [8269, 14083, 552793, 1706822489])) .empty .empty)
                        .empty)
                      (.node 33700063890892994544738777779497252552534513586628668277 (.basic (.split 22406023)) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^6
                        (.node 22519064508607184644046782670676414655611723595319249757 (.cut 5 7 21948659018136481248449777085593630727635499247) .empty .empty)
                        .empty)))
                  (.node 58093664039562902897342231015210398892632567402824424245 (.basic (.groups [46574123, 539314889, 647251721])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^4 * 541^6
                    (.node 49721003687166448315852235147712234016091346662845172481 (.basic (.split 29)) -- 3^6 * 1093^8 * 56773^6
                      (.node 49398579893523214881407530700239211513305986010357837449 (.cut 5 101 778515396204913827805473425696181627055621) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^14
                        (.node 41207471500910991456081937294929079616998767259182694821 (.cut 5 7 85853838128066274218593615636231502363) .empty .empty)
                        .empty)
                      (.node 57845652032096983111519355541073333593512298381012691809 (.basic (.split 4027)) -- 3^2 * 13^4 * 30941^10 * 23^4
                        (.node 51044335640680239735914779097883134746581880800320487321 (.basic (.groups [23, 67, 30941])) .empty .empty)
                        .empty))
                    (.node 76860822921256829410972524228348797003917493831573101245 (.basic (.split 29)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^6
                      (.node 76088946047660103604275378417244162900793872330639136025 (.basic (.groups [7, 5233, 1866871])) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2 * 331^8
                        (.node 65365318863469309775259807676336680807376817754651953853 (.cut 5 7 306173675234063025364822186975536938992937) .empty .empty)
                        .empty)
                      (.node 84065354426491269251917086356504022781354809663080664933 (.basic (.groups [39103, 128341, 285139, 367597])) .empty .empty))))
                (.node 415573971759567442281894943140560611423485458101443634605 (.basic (.split 7)) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4 * 21491^2 * 421^6
                  (.node 250851269075082411978033633623463451479689321592991949481 (.basic (.groups [29, 239, 1123])) -- 3^2 * 13^6 * 5229043^6 * 7^10
                    (.node 200152467697013390258548156184356551986206580662428330081 (.basic (.split 23)) -- 3^2 * 13^6 * 5229043^4 * 151^10
                      (.node 173983073225111049852311745722472860713266076574538063573 (.basic (.groups [431, 2801, 151841])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093 * 547^4
                        (.node 173320631842887968410485486191463865923674904712231217049 (.basic (.groups [1499, 66179, 14421466756460791, 432756417615425605965733])) .empty .empty)
                        .empty)
                      (.node 244345011213924690729883882592598361782031379408970762645 (.basic (.groups [7, 5233, 5419, 184725139])) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^2 * 127^2 * 331^2
                        (.node 223452474421470537726671401115019700017541159246947594333 (.basic (.groups [7, 307, 32668561, 122556524179])) .empty .empty)
                        .empty))
                    (.node 269857094045108535601758674677291379850854639583185318841 (.basic (.groups [1621, 3691, 8731, 32668561])) -- 3^12 * 797161 * 398581^8
                      (.node 262547089847003509358710723353718476291158843880550988721 (.basic (.groups [79, 2801, 4027, 8682564712362839769429759610849611323291])) -- 3^2 * 13^4 * 30941^10 * 23^2 * 7^4
                        (.node 261512713166225808907414127138530953041976820868005732209 (.basic (.groups [71, 211, 1597, 2384047])) .empty .empty)
                        .empty)
                      (.node 375509849852607395939021660161779794333948876138085209253 (.basic (.groups [11, 128341, 57344741])) .empty .empty)))
                  (.node 1130219496372012193671062125194247070316531801622034051289 (.cut 5 101 22990057839945197728998247161989760422959063) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^10 * 947^4
                    (.node 589845951458019646779049579630364870032032816376793970201 (.basic (.split 297134095231)) -- 3^2 * 13^2 * 61^6 * 52379047267^4
                      (.node 479185002419786020884506672898909690104848411047857634045 (.basic (.groups [947, 6733, 46685826619])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^10
                        (.node 456595710123258931474112100601510480392867196614550640625 (.basic (.groups [19, 331, 127159831, 184725139])) .empty .empty)
                        .empty)
                      (.node 899256543119421073178983787868635604377623134419691772581 (.basic (.groups [811, 3691, 8731, 32668561, 7875862993, 5265894013256197])) -- 3^6 * 1093^2 * 398581^8 * 1621
                        (.node 618210864926670819213665413946226453997546316510617755909 (.basic (.groups [43, 2017, 1130417, 604842197])) .empty .empty)
                        .empty))
                    (.node 1508064976690778191282846487627067407508828320390423539689 (.basic (.groups [239, 2801, 108263, 732541])) -- 3^2 * 13^6 * 5229043^6 * 7^4 * 29^4
                      (.node 1441909106927827001159714819283654786466649053222510001949 (.basic (.split 5)) -- 3^6 * 1093^8 * 56773^6 * 29
                        (.node 1138054095827883483342216199559746430664177240291175479777 (.basic (.groups [13, 127, 991])) .empty .empty)
                        .empty)
                      (.node 1815783293773913621109698999537039996962378187377829320737 (.basic (.groups [47251, 262209281, 518323723])) .empty .empty))))))))
        (.node 3912785843949384703513908467451876734503394183793798714513422474808715005 (.basic (.groups [13, 67, 8387, 430570659106944883310029331646560742422358013])) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^6 * 29^2
          (.node 283371322215967081096282750592172133250093261205672138326485245 (.cut 7 101 1999246066474622591584273140339404696603805439) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^12
            (.node 227702196285312675569164882919906724413942398675563725944605 (.cut 11 257 10759551865586282085333861297328743336478181653) -- 3^6 * 1093^2 * 398581^2 * 1621^12 * 5
              (.node 26576553055191001946943653977368398284154179067842837504329 (.basic (.groups [19, 249561007, 171686630257])) -- 3^4 * 11^10 * 15797^8 * 1806113^2
                (.node 8440010009407404448513313075647511625054318406857620794641 (.basic (.groups [5, 11, 31])) -- 3^8 * 13^6 * 757^2 * 14713^4 * 1774921^4
                  (.node 3257087023712178792887385577396003346947712060844792639009 (.basic (.groups [5, 11, 701])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^2 * 19^4 * 911^4
                    (.node 2476394844778305973343454636263855476707903918173461653681 (.cut 5 257 1428692323295990997469700337413652535127) -- 3^2 * 13^2 * 61^12 * 187123^4 * 12601 * 6301^2
                      (.node 2450695673616294989424703568926813054970701282472478242529 (.basic (.split 1621)) -- 3^6 * 1093^8 * 56773^4 * 398581^2
                        (.node 2348382604102158388837907419085862363122616115354003461405 (.cut 7 31 1069927245126290510481239305663873937219) .empty .empty)
                        .empty)
                      (.node 2779715433102234427164633278757515169301464940855611893205 (.cut 7 13 1243809893587503714106721486655534507311437633) -- 3^12 * 797161^4 * 5 * 2671^8
                        (.node 2773564949723639212193828825033024046011509777437709823733 (.basic (.groups [547, 2801, 151841])) .empty .empty)
                        .empty))
                    (.node 4415157704378407045880705762787340620759829323992934252129 (.basic (.groups [7, 1774921, 2384047])) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941^6
                      (.node 4321798998407080035454476845257585792861262593155454986645 (.basic (.groups [11, 21491, 261581, 2279749583])) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^10
                        (.node 3712973103983391687629280366294935280913549719727414783689 (.cut 5 101 96291134521088024667577186746898022094127127) .empty .empty)
                        .empty)
                      (.node 6913672564341190624891524212002196872228981570940124945069 (.basic (.split 29)) -- 3^2 * 13^8 * 61 * 31^6 * 1609669^6
                        (.node 6579423160913914117860723414519556547234610804744593077449 (.basic (.split 29)) .empty .empty)
                        .empty)))
                  (.node 15921436923918829129471775057591311331993255799896817734805 (.basic (.groups [7, 1009, 3571, 149381])) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4 * 21491^6
                    (.node 11394271429856387366843993847958191983925840813103870285245 (.cut 7 31 27589061956276144962421743520395285679481485667) -- 3^10 * 23^4 * 3851^4 * 5 * 292561^6
                      (.node 11110437889497365858226685347619823145116061707366181588321 (.basic (.groups [127, 239, 108263, 732541])) -- 3^2 * 13^6 * 5229043^6 * 7^2 * 19^2 * 29^4
                        (.node 9861858537561637148250433045691194482284280456068077197681 (.cut 5 31 94831054575633767396108470885040173571989) .empty .empty)
                        .empty)
                      (.node 13639578861997538120421353364136192019414489521735942315605 (.cut 7 101 148000086635619354542934324619350333701115281) -- 3^2 * 13^2 * 61^4 * 5 * 131^6 * 127^4 * 21491^6
                        (.node 12864807402503171958576825444332205338266783350146998447329 (.basic (.groups [29, 79, 4027])) .empty .empty)
                        .empty))
                    (.node 18156590657134799414178621046474095821884687081518683741421 (.cut 5 31 2647988476168757762182480458310740546580873) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^12
                      (.node 17455416976728506502121471182721096915754984430726422802009 (.basic (.groups [2801, 44983, 47251])) -- 3^6 * 1093^2 * 398581^6 * 7^4 * 113^6
                        (.node 16845169594190879082524330981461433839620078490923445172001 (.basic (.groups [79, 17881, 353461951])) .empty .empty)
                        .empty)
                      (.node 18198291543245186997554570842305603316230582789373310435361 (.basic (.groups [7, 249561007, 339147187, 14621215991505054747928028827])) .empty .empty))))
                (.node 80093120549672914467424712307945597679063154471313016751205 (.cut 7 257 14202129196688623250745270006101412793) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^6 * 197^6
                  (.node 42993960163662215974328278001686321010000341177475761669773 (.cut 5 31 1192508095041497330386917469277771051719) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13 * 2801^8
                    (.node 36047727673195675028992870482091369661666226330562750048725 (.basic (.groups [31, 127, 36277007914872163096693185049500538726334453])) -- 3^6 * 1093^8 * 56773^6 * 29 * 5^2
                      (.node 30600349924979304065993739081227793470968005843555713966961 (.basic (.split 29)) -- 3^2 * 13^4 * 30941^10 * 23^6
                        (.node 28971341594104444849531098449575066467273024102906266366673 (.cut 5 7 4650212656081524147041944883095831204041961) .empty .empty)
                        .empty)
                      (.node 41815364100906983033631729759225988807532822543452790056521 (.basic (.groups [13, 67, 127, 36277007914872163096693185049500538726334453])) -- 3^6 * 1093^8 * 56773^6 * 29^2
                        (.node 39342541412589952913257997384023126095995655476121049454841 (.basic (.groups [5, 689261, 5390701])) .empty .empty)
                        .empty))
                    (.node 45540439257062535113832976583981344882788479735112745188921 (.cut 8 257 10759551865586282085333861297328743336478181653) -- 3^6 * 1093^2 * 398581^2 * 1621^12
                      (.node 44111076273292556952114317614776384843746003793324165340053 (.basic (.groups [29, 337, 2647, 80709547373732627341381599878068429811])) -- 3^6 * 1093^8 * 56773 * 28387^6
                        (.node 43733884324032567547202548141184954817756021291322282650981 (.basic (.groups [5, 67, 239])) .empty .empty)
                        .empty)
                      (.node 73253660683534457756820475460760440366188162079200276873449 (.basic (.groups [31, 4051, 72577051])) -- 3^8 * 13^6 * 757^2 * 14713^4 * 1774921^2 * 5229043^2
                        (.node 69082722784971863531441523371277445543039259260302253149081 (.basic (.groups [5, 11, 31, 2671])) .empty .empty)
                        .empty)))
                  (.node 158366673361023844730404636457751688216793336336665516132581 (.cut 5 7 1178387962894683899947057071981759183397) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^6 * 71^2 * 281^6
                    (.node 105880655411720083446771974621524616000703281170424586612849 (.basic (.groups [7, 79, 1335485920015252423594158474143553560213111057])) -- 3^2 * 13^6 * 5229043^4 * 151^10 * 23^2
                      (.node 103740046247571170456806185642315813867096189333830496676005 (.basic (.split 7)) -- 3^4 * 11^4 * 5 * 3221^10 * 381510691^2
                        (.node 84637087057493413562988906850606404158833711101140741599089 (.cut 5 101 25131659619966425431087390074767504881) .empty .empty)
                        .empty)
                      (.node 128600112828550833617670430550251346665052028152902829214801 (.basic (.groups [127, 44983, 47251])) -- 3^6 * 1093^2 * 398581^6 * 7^2 * 19^2 * 113^6
                        (.node 121228929261988912978976659476437711241384301340171044074813 (.cut 5 31 4044050088514190392293678104801304238219961) .empty .empty)
                        .empty))
                    (.node 216904700951369433051449099471511259871518566452478526245417 (.cut 5 101 22181404570435282050988768795677362453) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^6 * 4733^2 * 22406023^4
                      (.node 197891922800542142629373015645594697722472724772231791292169 (.basic (.split 53)) -- 3^2 * 13^4 * 30941^12
                        (.node 190022284028193409290118460148450846395976808333652047661637 (.basic (.groups [967, 67411, 128341])) .empty .empty)
                        .empty)
                      (.node 221114480082098686470544439946001633453693649932224038499141 (.basic (.groups [5, 11, 17, 19, 151, 617])) .empty .empty)))))
              (.node 5814398626610941315533771862293847569544573501160645078803029 (.cut 5 7 36855911639846081441634654623810371810510485941) -- 3^2 * 13^8 * 61 * 31^6 * 1609669^6 * 29^2
                (.node 1943836313827471946817382239470591398129247061389927404370481 (.basic (.groups [11, 131, 151841, 3506165161])) -- 3^2 * 13^6 * 5229043^4 * 151^6 * 1499^4
                  (.node 901193191829891875724821762052284241541655658264068751218125 (.cut 7 101 4607180005188764713280034501286568418244475531) -- 3^6 * 1093^8 * 56773^6 * 29 * 5^4
                    (.node 580179491081565638055162609037318480873437385995760272613245 (.basic (.groups [7, 43, 331])) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^2 * 127^6
                      (.node 516690144424938514807462215443015747664194001220006806606777 (.basic (.split 5)) -- 3^2 * 13^2 * 61^2 * 97 * 7^12 * 16148168401^4
                        (.node 316883722955558417790715999779919173842148352390378725357957 (.basic (.groups [11, 64661, 6804911])) .empty .empty)
                        .empty)
                      (.node 887410147824399817913818433355606010658072169463115705041869 (.basic (.groups [5, 4027, 46336390704066877165791878421134505192399575647])) -- 3^2 * 13^4 * 30941^10 * 23^6 * 29
                        (.node 764363212371357154337155514461724543536233098509020301581741 (.cut 5 7 200749216057924045816556307775990948442729341993079) .empty .empty)
                        .empty))
                    (.node 1457694856396581559623132720135058314696127100894320363353801 (.basic (.groups [7, 13, 3691, 8731, 9631, 32668561])) -- 3^6 * 1093^2 * 398581^8 * 1621^2
                      (.node 1268282645396944458868873896094363689714924617448346196878449 (.basic (.groups [239, 2801, 108263])) -- 3^2 * 13^6 * 5229043^6 * 7^4 * 29^6
                        (.node 1138510981426563377845824414599533622069711993377818629723025 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 1831163045434744734309494032006954762491162775360525647048861 (.basic (.groups [71, 127, 38047])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^2 * 43^4 * 4447^6
                        (.node 1502414456691515484336476192691108777600095458308455304451569 (.basic (.groups [5, 72931, 37680901])) .empty .empty)
                        .empty)))
                  (.node 3431328574631770965117421550204965832276845443189067402086369 (.cut 5 13 284176446734180407880218166303613592893643665301) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801 * 467^8
                    (.node 2514403288499696711971420320737660280070988844200759161588473 (.basic (.groups [13, 17, 19])) -- 3^4 * 11^10 * 15797^4 * 1806113^5
                      (.node 2411772294949043516701667835226288087691166412047486831388377 (.cut 5 31 6001209134842417547172219272996530392015893423) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^14
                        (.node 2231481523596064220577815852615085899256635507020524514257129 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 3031506490047937658927854905761095282290580186739416837340169 (.basic (.groups [29, 2801, 14939])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093^6
                        (.node 2880972752716019642909974374575948992326158166170895333735369 (.basic (.groups [19, 43, 67, 3037])) .empty .empty)
                        .empty))
                    (.node 4563676415959602311285156509159513741837496245684028354176881 (.cut 5 101 700359532632158721738520122070816686146718332208863) -- 3^2 * 13^6 * 5229043^4 * 151^12
                      (.node 4032624301795798321436901489886941924678076760791234338962517 (.cut 12 257 14360343178806285814906132763634459811239737063891580817) -- 3^2 * 13 * 7^4 * 2801^16
                        (.node 3972577686932014177857444485230363962107506778887887231139509 (.basic (.split 811)) .empty .empty)
                        .empty)
                      (.node 5533294878328601773120868391610947056224307686790202778134609 (.basic (.split 67)) .empty .empty))))
                (.node 25734894286907594719500734567312574309084092914430355446214201 (.basic (.groups [67, 4027, 46336390704066877165791878421134505192399575647])) -- 3^2 * 13^4 * 30941^10 * 23^6 * 29^2
                  (.node 16187585110314051850910687973969502746142075091240972688522369 (.basic (.groups [7, 19, 79])) -- 3^2 * 13^4 * 30941^10 * 23^8
                    (.node 9343878265067284686768642377348271265042607895894958715777961 (.basic (.groups [127, 239, 108263])) -- 3^2 * 13^6 * 5229043^6 * 7^2 * 19^2 * 29^6
                      (.node 8696446782494677590325212101915080119505908385893740916689157 (.basic (.split 1621)) -- 3^6 * 1093^8 * 56773 * 28387^4 * 398581^2
                        (.node 6634555921967838896276422126936643213471355051755252784784329 (.basic (.groups [29, 2180921, 72577051])) .empty .empty)
                        .empty)
                      (.node 14919543146209271978748004040496290152845665700249383545970445 (.basic (.split 113)) -- 3^4 * 11^4 * 5 * 3221^8 * 24517^6
                        (.node 12617984956085194767179166528719132934744035799234263452923141 (.basic (.groups [7, 43, 72377887, 604842197, 4939322796502677327122750821])) .empty .empty)
                        .empty))
                    (.node 19063433687732466269078724484502892819917821737271180158140625 (.basic (.groups [7, 631, 63436494018485783312061813518073519935339221])) -- 3^6 * 1093^2 * 398581^4 * 5^6 * 19531^6
                      (.node 17927434092738440327952440279730735139983148749300798106534041 (.basic (.groups [23, 38677, 3500201])) -- 3^4 * 11^6 * 43^4 * 45319^10
                        (.node 17002911684763309982897021515762794758294592460026055312450845 (.cut 7 101 185586226936868313280461464243350264583) .empty .empty)
                        .empty)
                      (.node 24281769307281803179425031157223224524294167816388537413790881 (.basic (.split 31)) .empty .empty)))
                  (.node 106255370497779210365194398384600570309660470843146970842585761 (.cut 5 7 14882256857132191352221780783788910711) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^4 * 3500201 * 583367^4
                    (.node 41603433916276300176004967043077438237302086758094373797664281 (.cut 5 257 37137158926926271004278556193855576686651) -- 3^2 * 13^2 * 61^12 * 187123^4 * 12601^2 * 52932601
                      (.node 35166721208862772731284284727509056587135103759043796437534161 (.cut 5 101 3374948248180982891830869753606964115669226349954271) -- 3^6 * 1093^8 * 56773^6 * 29^4
                        (.node 29286768745279452794878335163532918111006197784217009114167073 (.cut 5 31 2801956962240712201893711837334865391839) .empty .empty)
                        .empty)
                      (.node 73821052035698369419523255042633760055000125650617759951240941 (.cut 5 31 8720616787057681630163094581484946474215582564037) -- 3^6 * 1093^2 * 398581^2 * 1621^13
                        (.node 52057301356612252115260345125875382181155629505790959463613757 (.cut 5 13 53167433790440306500340773419760337769530221) .empty .empty)
                        .empty))
                    (.node 158126799487634182035926943060179197979203946495420891344642137 (.cut 5 101 3462238585852413578933245597000102015636981) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^2 * 732541^6
                      (.node 130746565606977644270453815934965441357456893492937338033182169 (.basic (.groups [5, 151841, 398581])) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^4 * 1093^2 * 2801^4
                        (.node 124800396955482113848576684696325931330582027201033509017084881 (.cut 5 257 7076197360057495459146307985759994762678674880551) .empty .empty)
                        .empty)
                      (.node 174089633401803846758136288467305901632131736435636056341808693 (.basic (.split 31)) .empty .empty))))))
            (.node 18084004157045368192503949399343583664700296131984626583283930628637 (.basic (.groups [43, 271, 6247])) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^8
              (.node 160259422919786293228601555403589477590118988609645047766198455449 (.basic (.split 199)) -- 3^6 * 1093^8 * 56773^8
                (.node 10317953639230350793460764418712152723002017153705518474049957225 (.basic (.split 11)) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^4 * 5^2
                  (.node 938067262832816076837086167064234620012585101012021568627072761 (.basic (.groups [7, 229, 3373, 2540179814813584765784139901509773138353338251])) -- 3^2 * 13^4 * 30941^10 * 23^4 * 4027^2
                    (.node 487947540517291596893865080276319972886047288055739355014464557 (.basic (.groups [19, 14360343178806285814906132763634459811239737063891580817])) -- 3^2 * 13 * 7^4 * 2801^16 * 11^2
                      (.node 440874586482483191249609215784808759263364801125842122989654601 (.cut 5 101 313624909555141956554709808415452675258645487) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^6 * 743^2 * 5209^6
                        (.node 412718145569214031738430576748486108920080686148220738961998289 (.basic (.split 5)) .empty .empty)
                        .empty)
                      (.node 795934557251533610351468562686276440400088972465013187643419205 (.cut 7 101 134272306822569594817892446964890129056583204072725669937) -- 3^4 * 11^4 * 5 * 3221^16
                        (.node 555878411146722878645908800948475505902425883885199101739702721 (.basic (.groups [7, 79, 409, 2393, 5910676280174070976604828251164496731606578851])) .empty .empty)
                        .empty))
                    (.node 2115295017852991970835357530414126277346486463196289452568865769 (.basic (.groups [5, 689261, 20241187])) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^4 * 967^4 * 3500201^4
                      (.node 2051724403929654372589817183292185583717086387778846640624662609 (.basic (.groups [37, 43, 4933])) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^8
                        (.node 1019834915057020409207244257097762641026918009012270096688490669 (.cut 5 7 1087483375604761211687332623718182896010844248812771) .empty .empty)
                        .empty)
                      (.node 9357715011654572176191717721162909778007671598725617436979028605 (.cut 7 31 1253018766273722926001100602578703937976951) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^2 * 127^8
                        (.node 6439548430516794982306917510558419982576268488577265201677144089 (.basic (.groups [7, 13, 9631, 3397526895844168594277762829213027983813])) .empty .empty)
                        .empty)))
                  (.node 88132030585602976552116073418117277063606668683635789489026118921 (.basic (.split 89)) -- 3^6 * 1093^2 * 398581^10
                    (.node 14980351005907399711159698157541356981053035881018135158444998361 (.cut 5 7 405342159860620756968378069532343729034294828803) -- 3^8 * 13^6 * 757^2 * 14713^4 * 1774921^5
                      (.node 12876878125681598032682697765636463145354706056760891198058651437 (.cut 5 31 9742627082365008042550475659732469074048812151621) -- 3^2 * 13 * 7^6 * 29^4 * 4733^6 * 70001^6
                        (.node 11941970963601357405492976813307988778065818271943550189091161541 (.cut 5 7 116109175235612768273361548634706572204283016131) .empty .empty)
                        .empty)
                      (.node 55070052377990955704587456212170899766534718951201804422574559041 (.basic (.groups [23, 67, 9791, 75252409])) -- 3^12 * 797161^10
                        (.node 15505418959349967052253911191167300652223843488688260842430796689 (.basic (.groups [5, 61, 72577051, 917087137])) .empty .empty)
                        .empty))
                    (.node 124276502355085388784832334390161955500318154328016342723367214645 (.cut 7 31 23395151671311173939906095264189130781713368399) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^6 * 21491^2 * 421^6
                      (.node 119663925349867056829047196424109325049155203679651388880961565361 (.cut 5 31 1882933041867532723608974534343935828798329584101) -- 3^6 * 1093^2 * 398581^2 * 1621^14
                        (.node 98319316440690015515571815385183984713398702809577596824896924281 (.cut 5 7 442437849857721713073844950144699727543515317951) .empty .empty)
                        .empty)
                      (.node 137706802794888765776938555701555129984330089293174373422883923041 (.cut 5 7 41255879063581548212696053753277100930555278827) .empty .empty))))
                (.node 3830298770156769965909688083868404765086446111521052853883345013441 (.basic (.groups [5, 11, 3691, 8731, 32668561])) -- 3^6 * 1093^2 * 398581^8 * 1621^4
                  (.node 696918886175207117104526000439978659920124607780283636513775892573 (.cut 5 13 1674599996216873420427542213697681179346183993460116604123) -- 3^2 * 13 * 7^4 * 2801^12 * 1483^6
                    (.node 190507646433946193896633263593097128961686305326484378498496612205 (.cut 7 257 900347602278701774895789803352986925762392834996153) -- 3^4 * 11^4 * 5 * 3221^8 * 24517^6 * 113^2
                      (.node 174981600836331614395242044553689341990548114338802311904153611373 (.basic (.groups [43, 197, 11593, 589331, 2393847653, 2345859770241123348845770103])) -- 3^2 * 13 * 7^2 * 19^2 * 127^4 * 262209281^6
                        (.node 167300137699133496734568973217080971468478598714646250144478153973 (.cut 5 101 7554876878341040018126071397275720133702919283) .empty .empty)
                        .empty)
                      (.node 421877549347926424547522206063239809792652102049959689016685897173 (.basic (.groups [11, 67, 2003])) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^10
                        (.node 257948840980758769836519110467803818075050428842637961851248930625 (.basic (.split 11)) .empty .empty)
                        .empty))
                    (.node 1572609802036030116605914803858403060696664124760223247124286585481 (.cut 5 7 5715843777825929505191234887734203971583398620405527) -- 3^2 * 13^2 * 61^12 * 187123^4 * 12601^5
                      (.node 1561462456911144566116357821864267696079914307833524276786824943289 (.basic (.groups [11, 79, 131, 2393])) -- 3^2 * 13^4 * 30941^12 * 53^4
                        (.node 1292424694283991710973505037994586882288120133907300936372510976605 (.basic (.groups [53, 8737, 21491])) .empty .empty)
                        .empty)
                      (.node 2933022884920354069981224947941384155930552095094698908002593607045 (.cut 7 31 3570346080480540914045588008241528829547747) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^2 * 127^2 * 331^6
                        (.node 2612847768826611297074576244270200215521311466116920077552308998989 (.cut 5 31 745794526433649292298505996403380985754775443) .empty .empty)
                        .empty)))
                  (.node 5923816966750391734351089537349694329654239531776965561195301240025 (.basic (.groups [41, 2019041, 13306091])) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^6 * 1866871^4
                    (.node 4761271465087102501767076837184532774921908029465917765538487684445 (.basic (.groups [7, 1009, 3571])) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^6 * 21491^6
                      (.node 4541296466602052727548837869748457821419853874365965731614041735449 (.basic (.groups [7, 17311991, 339147187])) -- 3^4 * 11^10 * 15797^4 * 1806113^6
                        (.node 4367802141006643291970604709472658342187816276190228267547875177481 (.cut 5 101 2204252318591608812419379436336900507366042006900931) .empty .empty)
                        .empty)
                      (.node 5746880055406961897624077930401411819991558972168549440389679967809 (.cut 5 13 4032563252986128295634063226802509983176741720079537437) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^9
                        (.node 5345272164541578710067970915013209127736245709485737884899510209533 (.cut 5 31 857976256553506808159782314363316750150361823341728585421) .empty .empty)
                        .empty))
                    (.node 7843750722118664913138330534212437658660993512843585264523324583969 (.basic (.split 5)) -- 3^6 * 1093^2 * 398581^10 * 89
                      (.node 7353523911628313015650381930638075490624618994961463721092478234205 (.basic (.split 421)) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4 * 21491^8
                        (.node 6448721024518969245912977761695095451876260721065949046281223265625 (.basic (.split 11)) .empty .empty)
                        .empty)
                      (.node 8197428681496085017989170015178977860032305802600739324317782227581 (.cut 5 7 28617928571967028858579339643807731739291369419201) .empty .empty)))))
              (.node 4386148041463405086220849121616727958288479290704369693494191265698801 (.basic (.groups [29, 79, 2393])) -- 3^2 * 13^4 * 30941^12 * 53^6
                (.node 189450938019499884596287714391652381422170255206452859678093142838289 (.basic (.groups [5, 11, 157, 433, 661])) -- 3^2 * 13^4 * 30941^14
                  (.node 35545665515038535697686007710566966974212193363417189304769995013757 (.cut 5 31 26705775750945548310656728335032548633953365861867251) -- 3^6 * 1093^8 * 56773 * 28387^8
                    (.node 22851140120001097118119730652688243040298624617018215276070013188637 (.cut 5 31 2045278964135734063382768080042813951530383) -- 3^6 * 1093^8 * 56773 * 28387^4 * 398581^2 * 1621^2
                      (.node 22424723872430198154065784199349949535900674155958958460921568212001 (.basic (.split 5)) -- 3^2 * 13^6 * 5229043^8 * 31^4
                        (.node 20299676651682771401732568487531386395454053592678645646145221497333 (.cut 5 31 566708909301668638956731601536676658142564718457299871) .empty .empty)
                        .empty)
                      (.node 31638361254793417106463675765958481451196243712540468920998662337717 (.cut 5 13 112665522803985774795713370116503281529522292348204850349438819) -- 3^2 * 13 * 7^4 * 2801^18
                        (.node 23207254387699108244384428837329011056298059316609583931735162072053 (.basic (.groups [211, 449, 88009573])) .empty .empty)
                        .empty))
                    (.node 48988351429540520746450346191809942539537957382684855634008954602349 (.basic (.split 7)) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^6
                      (.node 42871336647777501049454326313671701483238156013173752798825487602801 (.cut 5 31 101196854578795486272313906782844902277541871040090707911) -- 3^12 * 797161 * 398581^10
                        (.node 40935118906756548260138661129901427951582222924442789051737816620197 (.cut 5 7 117962148213822898577481651743658612324689820991961) .empty .empty)
                        .empty)
                      (.node 161218025612974231147824444042377386296906518026648726157030581640625 (.basic (.groups [11, 19, 31])) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^4 * 5^8
                        (.node 105253347477052561760157094348891750037958215664867508135903634263605 (.basic (.split 3229)) .empty .empty)
                        .empty)))
                  (.node 698093814268561177269311417544906951620828422643079088542575887973241 (.basic (.split 8011)) -- 3^6 * 1093^2 * 398581^10 * 89^2
                    (.node 389334212675149242736512848532387322457931244959978798069483584135769 (.basic (.split 5)) -- 3^6 * 1093^8 * 56773^4 * 398581^4
                      (.node 358058539407717939412177466824937459524722680406370988082279169102653 (.basic (.groups [8059, 320374117039, 304018940824561])) -- 3^2 * 13 * 7^6 * 29^6 * 4733^2 * 22406023^4 * 88009573^2
                        (.node 196093768052966622828458263355310941466524837821089631613083114599225 (.basic (.split 31)) .empty .empty)
                        .empty)
                      (.node 493139733434829959992942474597117748621501081607000113464080342090525 (.cut 7 31 54061899040849756679606934888021725530486461743) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2 * 331^4 * 37861^5
                        (.node 478902513267997198714101796889879609646482500249438371163501500681681 (.cut 5 31 8776549113824147273826528524479703618974006091899447) .empty .empty)
                        .empty))
                    (.node 1946671063375746213682564242661936612289656224799893990347417920678845 (.cut 11 257 524965004879661300487606740508924841185961717473762013) -- 3^6 * 1093^8 * 56773^4 * 398581^4 * 5
                      (.node 1591330716060815081650552173332987591822610251289410950392372741890625 (.basic (.groups [41, 2019041, 13306091])) -- 3^6 * 1093^2 * 398581^4 * 5^6 * 19531^2 * 1866871^4
                        (.node 947222978740543863080776683972396102154330829769871658570331607312605 (.basic (.split 43)) .empty .empty)
                        .empty)
                      (.node 2400429220047485516576066963398687184437359911751557926066438775515101 (.basic (.split 19)) .empty .empty))))
                (.node 21550159641405420426057218615575301504000547863876559080945627051732961 (.basic (.split 4051)) -- 3^2 * 13^6 * 5229043^8 * 31^6
                  (.node 8967888064700877083281388370846799277370785448500387582034397777393605 (.cut 7 101 360872297911418516343042843483138553461097915476512780407) -- 3^4 * 11^4 * 5 * 3221^8 * 24517^8
                    (.node 6208914306424124114739604383950684124205129146775626676144902266787861 (.basic (.groups [7, 13, 811, 3691])) -- 3^6 * 1093^2 * 398581^8 * 1621^5
                      (.node 4902344201324165570711456583882773536663120945527240790327077864980625 (.basic (.groups [11, 71, 1137043309874106587329369739133088789635301921798771999])) -- 3^6 * 1093^2 * 398581^10 * 89 * 5^4
                        (.node 4652539647977865283607501150358949743761467519374314761609301396918805 (.basic (.split 29)) .empty .empty)
                        .empty)
                      (.node 8278232800901880915657559471265101611195518397645805786199239015701405 (.basic (.split 19)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^8
                        (.node 6346433407046456998145850195537546902046302067930553536589225034235849 (.cut 5 31 3190024434137687285264697271414943096243371569963856173361) .empty .empty)
                        .empty))
                    (.node 15212382585131550624910203520929418425162069172549579520580141028418769 (.cut 6 257 668188255796452491946298593323346594011875048959344109196131) -- 3^2 * 13^4 * 30941^10 * 23^4 * 4027^4
                      (.node 9733355316878731068412821213309683061448281123999469951737089603394225 (.basic (.split 31)) -- 3^6 * 1093^8 * 56773^4 * 398581^4 * 5^2
                        (.node 9098408217425027225467396104927985411223825340335378296830384911206077 (.cut 5 31 1111312064945642181767412619206790090401398240278516694024521) .empty .empty)
                        .empty)
                      (.node 16920821477511581684103931034361237241436688707593653711800132571164049 (.cut 5 31 426776280062889969206649664004295399559924810819303) .empty .empty)))
                  (.node 122558605033104139267786414597069338416578023638181019758176946624515625 (.cut 7 31 22207592885151175757129920375008357150367081834651815912469) -- 3^6 * 1093^2 * 398581^10 * 89 * 5^6
                    (.node 66212635856145946381715960719802483571416810689333424825714645952453189 (.cut 5 7 106198093185426742059971217739289384359742030294512141) -- 3^2 * 13^2 * 61 * 31^2 * 331^6 * 2180921^2 * 3217^10
                      (.node 59363630810201168236197866879005305949164441281497697845550966749440609 (.basic (.groups [19, 271, 3511])) -- 3^4 * 11^10 * 15797^2 * 1806113^8
                        (.node 33527364132515155440490911357748790893268330722055477608291205812149321 (.basic (.groups [151, 3061, 963550486823208498642839329761819197633918596633])) .empty .empty)
                        .empty)
                      (.node 117621031782326790312227281206535672037430635675826338377255500000239949 (.basic (.split 2801)) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^6 * 7^4
                        (.node 76061912925657753124551017604647092125810345862747897602900705142093845 (.cut 7 101 668188255796452491946298593323346594011875048959344109196131) .empty .empty)
                        .empty))
                    (.node 1381576789637740263217000208352723964399922746979727380568493538509258077 (.cut 5 31 32813202512116685051085704872446686704478156801153993) -- 3^6 * 1093^8 * 56773 * 28387^4 * 398581^4
                      (.node 846641920832469307007991917921271799945456376250137014656664682865800013 (.basic (.split 11)) -- 3^2 * 13 * 7^2 * 19^2 * 127^12 * 12346432697^4
                        (.node 188446111098900924538148391084453814749330369146067135980172873129855225 (.basic (.split 331)) .empty .empty)
                        .empty)
                      (.node 1718524847360407608923187361957640355952892498805886790327782227124044069 (.cut 5 7 294314833584038115593012377186965570663165740058473) .empty .empty)))))))
          (.node 3233777438843749629560809685679430016100108390954237763020505882688911411566661954245 (.basic (.groups [3541, 194406513029296671576581892788971698035494756470088124301265641215687851])) -- 3^2 * 13^6 * 5229043^10 * 23^4 * 5 * 59^2
            (.node 9704171701597577755272943881221356225342232630115541751639020739155107799393797 (.cut 5 31 996976083421838087614808215007360667607783697077748531593517871353) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^10
              (.node 18082923228186677007656669255303399612091541542411060315517176306458519341329 (.basic (.split 113)) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^6
                (.node 492134498151093304578369200715215508777183792282268821970771181168607734529 (.cut 5 31 3397602525364747515918651705612800011575614578432676006527897) -- 3^6 * 1093^2 * 398581^10 * 89^5
                  (.node 27428651615046273909932472206699565568368872395009312666828014897856923429 (.cut 5 7 6341539874834493100357624439745258437587987620270490463) -- 3^6 * 1093^8 * 56773^4 * 398581^2 * 1621^5
                    (.node 5763430557334012725299136779120247929834101148115490580485519500011757501 (.basic (.groups [29, 4733, 84989558479232242640144815482521415474498435681558241])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^6 * 7^6
                      (.node 5559167108238078298268253469233160881975957789907458733369764276699225237 (.cut 5 31 22951204439831354286068594921712998119338614488822119973) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^2 * 39103^10
                        (.node 5529601102821273085150215738373207963788581935755829460345743608636041961 (.basic (.groups [131, 691, 701, 1137043309874106587329369739133088789635301921798771999])) .empty .empty)
                        .empty)
                      (.node 10064650090713505189992898706384058965336514346923290842030886574463122681 (.basic (.groups [211, 3691, 8731, 4105333])) -- 3^6 * 1093^2 * 398581^8 * 1621^6
                        (.node 6174490103564287883020914467301217807172098875716008919411024848288913133 (.cut 5 7 6286447095807485044542390424573689482135602822618933351) .empty .empty)
                        .empty))
                    (.node 60044592676059802832553247171960387630653318287286360206227885525003315317 (.cut 5 7 293434533966882832414929942486173388858924339791513) -- 3^6 * 1093^8 * 56773 * 28387^4 * 398581^2 * 1621^4
                      (.node 60016390684061714210903259491854266247771036192890557150893820907452004981 (.basic (.groups [19, 3217, 9883, 12583])) -- 3^2 * 13^2 * 61 * 31^2 * 331^6 * 2180921^8
                        (.node 28714546434597883587649116885219305061827804480561512543737343276102579317 (.basic (.groups [113, 911, 3938257, 445646455759])) .empty .empty)
                        .empty)
                      (.node 181096712766043788481160603832160115974106484749370517676946131077790871225 (.cut 7 101 19728838469625623396751894343698223588962123645130492954649) -- 3^6 * 1093^2 * 398581^10 * 89 * 5^2 * 31^4
                        (.node 155181219822273660319162027680887471372604693547393309313332836448418943789 (.cut 5 31 539837658952374305494455062589235683732734304986519300821) .empty .empty)
                        .empty)))
                  (.node 2117170240440044688258564470305187537504892115311554727505392904298887436613 (.cut 5 31 7861009852408947846629745468937817655834372286491375382127170699) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^12
                    (.node 931414171506305349080578757972393049916581626481786173516191591495818240717 (.cut 5 7 31070847409558719433815731031426538074938119821092645551937) -- 3^6 * 1093 * 547^4 * 431^10 * 87653303^4
                      (.node 663933764070827434039404350778255839335701320250624356632315913035060752969 (.basic (.split 23)) -- 3^2 * 13^6 * 5229043^10
                        (.node 516543929727871070671460479065076515751410236046860432045951442563902609521 (.cut 5 31 2623885514157838863668410143412090857565007203216066231309924811) .empty .empty)
                        .empty)
                      (.node 1097417817521987389091134094960153247157519096095016846396019224335055979805 (.basic (.groups [7, 31, 37, 433])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^2 * 3229^2
                        (.node 1034674155434274686995773848710880937527839853692267615916674668616613959605 (.cut 20 257 41829589073881927685021094107858482669917387242444104961317) .empty .empty)
                        .empty))
                    (.node 3396321210031824376240686617311229842010473143464025110493496683175360885605 (.cut 7 31 81726912966227839353554334536856448509146605582446475665007) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4 * 21491^10
                      (.node 3290652894761432535655197021127028333717354508570584718905788301314129319205 (.basic (.split 8387)) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^6 * 29^4
                        (.node 2199055508342513094828950052385783672970911976887767563684241546018323475045 (.cut 7 31 1217083474015743715744443511519241274837938019033543287384707) .empty .empty)
                        .empty)
                      (.node 14001254871795337726671678835747425454896982171999464260380155890081921487681 (.basic (.split 13)) .empty .empty))))
                (.node 373517370111773162005474359384628018447550187182908609345919555370597639417405 (.basic (.groups [127, 41829589073881927685021094107858482669917387242444104961317])) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5 * 151841^6 * 19^2
                  (.node 44800953093850708608337779119043471460959430971781383398878063838253159178161 (.basic (.split 13)) -- 3^6 * 1093^2 * 398581^10 * 89^2 * 8011^2
                    (.node 28643471065610648939078987939876713320124247037478899370577637520106845076133 (.cut 5 7 1355766013863087445229207081857366239805935857295316715767556681) -- 3^6 * 1093^8 * 56773 * 28387^10
                      (.node 27440850008744116459579253606604204069602944385057389315758082228119036816741 (.cut 5 7 76000610719859084393553619794105379719226783936014532295161613669) -- 3^2 * 13^8 * 61^6 * 1609669^9
                        (.node 20646344378106684193324075875603844397751384574012261485123720152980068306225 (.cut 7 101 5950147640571199771494591844883453636161534956772973870767) .empty .empty)
                        .empty)
                      (.node 43799970335447304107474858863654180281169357513121925155398635124006088373081 (.cut 5 31 571510720792741222962550509988458459686267217027795732979856326369) -- 3^6 * 1093^2 * 398581^10 * 89^6
                        (.node 38133022644584754405719809226649529684223243988568876589984061155102949578349 (.basic (.groups [7, 19, 606883597718553434112627160618183222883563297])) .empty .empty)
                        .empty))
                    (.node 181369999384179304398277552748667071477403047034514367252349584993323487922009 (.basic (.split 17)) -- 3^2 * 13^4 * 30941^16
                      (.node 107217425333504862566584037942440910143763236536249651548921593208732426642817 (.cut 5 7 8506090259604178206889434393863092474235771512828043485151759113) -- 3^4 * 11^10 * 15797^2 * 1806113^9
                        (.node 58707455969234121699745468862537838683282096577323521581282588825963645575901 (.basic (.split 2671)) .empty .empty)
                        .empty)
                      (.node 351220961193467712606844901561697339008585998412580284658495117995547138320601 (.basic (.split 7)) -- 3^2 * 13^6 * 5229043^10 * 23^2
                        (.node 182016313333339390446731824864716530913660768235993035384942026571064979339853 (.basic (.groups [7, 10687, 5557579, 17956667])) .empty .empty)
                        .empty)))
                  (.node 1618280467507867160659578271417916148397420445336823634514846581044797041357089 (.basic (.split 7)) -- 3^2 * 13^2 * 61^6 * 52379047267^6
                    (.node 670496858159911682050097603658978077988696134738550725436760194631256015993613 (.cut 5 31 3815161819309959512367505044536894491745933108007932122198967) -- 3^2 * 13 * 7^2 * 19^10 * 104281^6 * 62060021^4
                      (.node 582412390220059211908391128547565128992472602633157984185414829897291069316093 (.basic (.split 7)) -- 3^6 * 1093^2 * 398581^10 * 89^2 * 8011^2 * 13
                        (.node 464199222459242895884968763458715756755802909973908157160935310676638196515089 (.basic (.groups [7, 43, 873349])) .empty .empty)
                        .empty)
                      (.node 1040987445685718790175050934067579509403661555566126359976090107292882601136605 (.cut 102 257 5156079357350148056297841503257506041993836370052856956181) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^8
                        (.node 922807684572454848400400669661277475072537832688898796198934128057382544114349 (.basic (.groups [37, 43, 4933])) .empty .empty)
                        .empty))
                    (.node 3083289989531048174770718396727340215115851799586744243289942944886499294674153 (.cut 6 257 41506359939867181866123584459143160099548242350457362691640785245991521) -- 3^2 * 13^4 * 30941^16 * 17
                      (.node 2767439084494364762486020694767830828656295141707861748599767961405182757451405 (.cut 7 31 317819828358272256176373811398545302444730589482066611763) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^6 * 29^6
                        (.node 2366212073333412075807513723241314901877589987067909460004246345423844731418089 (.basic (.split 61)) .empty .empty)
                        .empty)
                      (.node 7571361072860769754809084671118346676902143834231053794410392788664783901109209 (.basic (.split 61)) .empty .empty)))))
              (.node 8245661557276578536976578448749297293986403181639286897370609739866923083603048205 (.basic (.groups [8011, 5156079357350148056297841503257506041993836370052856956181])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^8 * 89^2
                (.node 399889840393346640811469819227782218417312707814476698740717632376629759609657041 (.basic (.groups [10687, 30941, 5557579])) -- 3^6 * 1093^2 * 398581^12 * 13^4
                  (.node 61852285777981657803671920155075809227164151358813572619417515284447271034363409 (.cut 5 31 54502364106826955342694692487131594685147042490750049149454621) -- 3^6 * 1093^8 * 56773^4 * 398581^6
                    (.node 28538207120782901383511165298830691320631157529024741225085326664967262396488557 (.cut 5 31 1871285616095381293777548260069063476275929231894563621038253) -- 3^6 * 1093^2 * 398581^10 * 89^2 * 8011^2 * 13 * 7^2
                      (.node 26446287229012525490938130349741715083735803895063862871444880829408854144625521 (.cut 5 31 133845237022339804408500667560405921043846891922630375099984989) -- 3^6 * 1093^2 * 398581^8 * 1621^8
                        (.node 17209827098479917917735400176523169611420713922216433948266260781781809777709449 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 52415929822027818971102212744364783656969480592974652135929030063070488009460601 (.basic (.split 307)) -- 3^2 * 13^4 * 30941^16 * 17^2
                        (.node 52076714882788118480957893942310916872056684720912959705250646494921196698785561 (.basic (.split 18457)) .empty .empty)
                        .empty))
                    (.node 144338936473338136624258337117720209014532989211142477060259027070854528616503429 (.basic (.split 31)) -- 3^6 * 1093^2 * 398581^12 * 13^2 * 61
                      (.node 134733849204037932010179020915605204044312249455405598488986031110606276722220377 (.cut 5 31 2533037263815926782774622528148270034260864758236590557305201) -- 3^2 * 13^2 * 61^2 * 97 * 7^12 * 16148168401^6
                        (.node 79295742907885490872319335299477891271473601821504358091227482471195055026497361 (.basic (.split 19)) .empty .empty)
                        .empty)
                      (.node 230900846700715678710768009720969109646796893955046829168838824257168833469430001 (.basic (.split 991)) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^6 * 113^2
                        (.node 185795888471344419969020952926137892335541993160254970584343917419644436171597929 (.cut 11 257 194406513029296671576581892788971698035494756470088124301265641215687851) .empty .empty)
                        .empty)))
                  (.node 5198567925113506330549107649961168839425065201588197083629329220896186874925541533 (.cut 5 7 82905696816645820010899015810363239803322922923120315322727455038365959) -- 3^6 * 1093^2 * 398581^12 * 13^5
                    (.node 928979442356722099845104764630689461677709965801274852921719587098222180857989645 (.cut 69 257 194406513029296671576581892788971698035494756470088124301265641215687851) -- 3^2 * 13^6 * 5229043^10 * 23^4 * 5
                      (.node 843281527825515977969034608649635310959614982188605263465046778307308679107763001 (.basic (.groups [79, 2801, 664499072088544514055468407576442854773858294407279590585435656891])) -- 3^2 * 13^6 * 5229043^10 * 23^2 * 7^4
                        (.node 461853025444506955043354164938219147291030773888094281459033960108551817967661749 (.cut 5 7 58009854098956820107103996062140967764553806188731472252185843) .empty .empty)
                        .empty)
                      (.node 3885491402486389052743647429674416672302206489253713546470146641088557696298370689 (.basic (.split 29)) -- 3^2 * 13^2 * 61^6 * 52379047267^6 * 7^4
                        (.node 1887461297760524881353647282251394218168940242671882151960491466802107620033049269 (.cut 5 7 4748855988590929389006442395524216230110273326297146612462081) .empty .empty)
                        .empty))
                    (.node 6496802648524570969482492879515763718188251768288194612610778359614880313693551805 (.basic (.groups [7, 43])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^8 * 79^2
                      (.node 5580634168055057506434524422031044585238294051097718464366582914824742348481380661 (.basic (.groups [7, 17, 19, 29])) -- 3^6 * 1093^2 * 398581^13
                        (.node 5547422098059195432842846427646131205612112429611887372312584181763771381456968045 (.basic (.groups [1801, 5156079357350148056297841503257506041993836370052856956181])) .empty .empty)
                        .empty)
                      (.node 7171362513328916745515925884791555240281824456295044493875284749140668239230071845 (.basic (.groups [19, 367])) .empty .empty))))
                (.node 190389078721833063584438724054046416942808117973431963777037185413339327118620163761 (.basic (.groups [29, 3319, 4733, 30650832715386945983110738674706459882548133096065184443881])) -- 3^2 * 13^2 * 61^6 * 52379047267^6 * 7^6
                  (.node 16215065287230353678535203499006852015439175155831379500806875586912220796265604005 (.basic (.split 19)) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^8
                    (.node 9794650876456928096757054238641855603979051576321682921015031819518732394094316445 (.basic (.groups [3169, 5156079357350148056297841503257506041993836370052856956181])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^8 * 97^2
                      (.node 9103998535095876578482026693380756724441557664852493558632851953562577372408298521 (.basic (.split 19)) -- 3^2 * 13^6 * 5229043^10 * 23^4 * 7^2
                        (.node 8804675124873626334079758564180932749886512341879691100675800651322126245606709169 (.basic (.split 97)) .empty .empty)
                        .empty)
                      (.node 11442162126741767715102753264190435182446290561808023542954157077395225405134024005 (.cut 105 257 47925158781154998637979945452523136351923013320699) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^2 * 3229^4
                        (.node 10619112933440017378575694578423378575426751528330054998116095184494695414194507605 (.basic (.groups [10303, 5156079357350148056297841503257506041993836370052856956181])) .empty .empty)
                        .empty))
                    (.node 112679250672105282529565775460558083496763988188357692847634252591568173192652749981 (.basic (.groups [5, 2801, 3319, 30650832715386945983110738674706459882548133096065184443881])) -- 3^2 * 13^2 * 61^6 * 52379047267^6 * 7^4 * 29
                      (.node 98286025001341198163612084097926945045501714381774879439117932314991906734775304441 (.basic (.split 29)) -- 3^2 * 13^6 * 5229043^10 * 23^6
                        (.node 42869431598229303820810709296931320150735738113898521714612151824471752568437969541 (.cut 5 7 337616325368680473786550047734168193751764566604196310203075400744191) .empty .empty)
                        .empty)
                      (.node 138709717950877949295912261970129120862966202631907920454908925015091202000459795269 (.cut 5 7 409340617346764814863103182225722823653394106229997827709583788805011) .empty .empty)))
                  (.node 961179926591620302803039848493232592707550229893890497279811182356760527469485099377 (.basic (.split 11)) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457
                    (.node 418833139381404809629313813523340812785657147967901137929571077788331704777061526141 (.basic (.groups [7, 19, 577, 22280841470107301759731, 377352952657283842305463])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^2 * 2671^2
                      (.node 231470345782489997532142132509605546706801062132980590492200893453940881007645373645 (.cut 7 31 22189189534391544281754885108695895326933037006692780112181) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^6 * 29^4 * 8387^2
                        (.node 219486702259583799125838238186070352978819328287231325615381757172983476791192382197 (.cut 5 7 23846884381664127390156397242092675079347433116336072826715967) .empty .empty)
                        .empty)
                      (.node 891600371962387659352397456274187717062544851969678382987530239900303004602156216445 (.basic (.split 23)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^10
                        (.node 854053487112741754405736580725550476738991697162330036765552663178246245823850789393 (.cut 5 7 60597251510548265644386875918611535827843840499304814373926301061769) .empty .empty)
                        .empty))
                    (.node 2875151386666287431584426921615007228738579218136189646553789889129459172049920893481 (.cut 5 31 85156040597252413664950658665771248449933748991802880586353918133889) -- 3^6 * 1093^2 * 398581^10 * 89^2 * 8011^4
                      (.node 2850294725038894746744750438839881406319549717071471503734420037134765295308483828789 (.cut 5 7 3546243494499161013416557193676131382600180715354333914830334422536366847) -- 3^2 * 13^6 * 5229043^10 * 23^6 * 29
                        (.node 2773408636200690207224237574285774769945761817214393756618202123315755783453704998837 (.cut 5 31 1374630907896148379340988300585591698801883964577984961298711) .empty .empty)
                        .empty)
                      (.node 2948372911521438501457796716127054561079949538911992961656902946939788834571151682769 (.basic (.groups [11, 251, 1933, 3169780419549724275388949137180362318346933902869291057])) .empty .empty))))))
            (.node 1357780637507547378149354416829946137467484357085838815112844019179921861365386475787134006900837461 (.cut 5 7 7003602565797830439179515080365610311671245584028325937508606407660554376580310034081) -- 3^2 * 13^2 * 61 * 31^2 * 331^6 * 2180921^12
              (.node 2748134244641975735613579697707551098402576907925855770860951786455756175995607919286609 (.basic (.groups [2801, 3319, 22452991648162268797413923619508144828821691966324686277705031621])) -- 3^2 * 13^2 * 61^6 * 52379047267^6 * 7^4 * 29^4
                (.node 90633366205921542071328908605652437080157067540081354483739878210047580434066604143605 (.basic (.groups [8011, 47925158781154998637979945452523136351923013320699])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^2 * 3229^4 * 89^2
                  (.node 8493561465764539031179153654593431533811969303357434400370774847102573636361723919957 (.cut 5 31 38944967333321441736142530046477365617544497643391923177262711667) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^6 * 22406023^4
                    (.node 4170188716739325506204675288427164993471240036481922814765599226483919369871515516405 (.basic (.groups [7, 31])) -- 3^2 * 13^6 * 5229043^10 * 23^4 * 5 * 67^2
                      (.node 3456732505009362933523634829190795486902758782746543727721718583592484734972579469045 (.basic (.groups [97, 194406513029296671576581892788971698035494756470088124301265641215687851])) -- 3^2 * 13^6 * 5229043^10 * 23^4 * 5 * 61^2
                        (.node 3267698269491053193357407488356184421406155657462373092581393325155477022586929749449 (.basic (.groups [67, 2801, 3319, 30650832715386945983110738674706459882548133096065184443881])) .empty .empty)
                        .empty)
                      (.node 7239980892889336331065031894295188219706577892681857084357153794021128545486080628749 (.cut 5 31 1046653865032259044238597881592123850563759487513896035193978587841) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^6 * 7^4 * 2801^4
                        (.node 5853638568690157677951208463141473577573542231255127999791282086875311707451883045805 (.basic (.groups [127, 331, 7048127460409027779498076057093420544664560356370027865192439])) .empty .empty)
                        .empty))
                    (.node 24292408308814102841455977933622520317290467163609590302992503837046419741491472251281 (.cut 6 257 6526834353714373775270515615065695833990342213228387761584505523781) -- 3^4 * 11^16 * 50544702849929377^4
                      (.node 23855125834773734800978093216023573299427847953857422744873501146388293566979965494005 (.cut 7 31 137772858348476325312451140525920725325141055138590109098595023390077) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5 * 151841^8
                        (.node 10333900511498545055971528095563258268389711262980269450806856743128610766108162582881 (.basic (.groups [29, 151, 911, 3319])) .empty .empty)
                        .empty)
                      (.node 78825054891124037789342867237007907971872495680295474187411188106175707815968291370445 (.basic (.groups [19, 367])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^2 * 3229^4 * 83^2
                        (.node 71410533832995372309956283121812505973647299396243874931576894320023601753441443815205 (.basic (.groups [7, 43])) .empty .empty)
                        .empty)))
                  (.node 173633749299416839959414439307675549652395800694122780518611261825583656333293396591329 (.cut 5 101 675510744060251731095555529681203068707154339246953965752345137919204751892363159) -- 3^2 * 13^4 * 30941^18
                    (.node 116721495854892772461763186048006629296134610021003648161675356346508694357772178875005 (.basic (.groups [10303, 47925158781154998637979945452523136351923013320699])) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^2 * 3229^4 * 101^2
                      (.node 116302771117586056639167821667681143717613577817160750170857153065168023823807697024617 (.basic (.groups [7, 19, 839, 21613, 73774717787791])) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457 * 11^2
                        (.node 107659303450513292431401805462767804631637147896051693515655663941211675836906031863045 (.basic (.groups [3169, 47925158781154998637979945452523136351923013320699])) .empty .empty)
                        .empty)
                      (.node 121462041544070514207279889668112601586452335818047951514962519185232098707457361256405 (.cut 7 101 6526834353714373775270515615065695833990342213228387761584505523781) -- 3^4 * 11^16 * 50544702849929377^4 * 5
                        (.node 121389898002603413689525109379796326850572696570221321767200652434085946323066860669045 (.basic (.groups [3571, 47925158781154998637979945452523136351923013320699])) .empty .empty)
                        .empty))
                    (.node 2113163523297146921740386255194071961504048745483101207924652833361987526390129779535605 (.cut 7 31 320920209783418995494302032202133075793263125357446360447196980523349) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^8 * 19^4
                      (.node 1144033544790200716037649806144859258011698237961412084564617655681766405656878766160605 (.cut 7 101 2217315705963295988959530782303349453655243979579748279655713112267) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^10
                        (.node 285462945413073431712205909072565059863235628140739318703259725903383576802822061448421 (.basic (.groups [727, 29833, 254827])) .empty .empty)
                        .empty)
                      (.node 2224334747337552875972179178657555781828864481180579723245696984773760630000057185242041 (.basic (.groups [5, 31, 1621, 3388421399525642776912775349522942939112247256620164819904201017946977111])) .empty .empty))))
                (.node 206037453503841872085740785321418874645519227531347115733433868941282129453328587548627517137 (.cut 5 13 1141559591858754146527270709074820832339319553465114399958469) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457 * 11^8
                  (.node 119301028326907563317223665846638985194100484211548210797222484472193751368330998380716205 (.cut 7 101 11620670708077779222732198330858642485254994170005018703) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^2 * 3229^6
                    (.node 18153868340272232532842887977736741891512301818376022209794892393607628081282530302725681 (.basic (.split 53)) -- 3^2 * 13^6 * 5229043^12
                      (.node 14072635305227912853339306421789418389831242915876450770673715520885330882680731339978657 (.basic (.groups [5, 839, 3221, 21613])) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457 * 11^4
                        (.node 3730538084650974765205721642498336234888685765935877271741275284269428486565046692420041 (.basic (.groups [29, 701, 3319])) .empty .empty)
                        .empty)
                      (.node 37647773707217248225114606268226359690429875662367238127396993729474163628639035837277361 (.basic (.groups [7, 1933, 15964467311628307355709367231742535166170741189747270313375253])) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^6 * 113^6
                        (.node 19113711987705524311893912494396820785393845081598571438725787094900652982958486274665089 (.cut 5 257 50533219639974068817976432285102777132225507731702840434934348444901) .empty .empty)
                        .empty))
                    (.node 50994216167824701184755672329462507973258055807818246387313852733643827280322627620356437929 (.basic (.groups [7, 409, 1171, 517953204373017526357542369403663062966586835752887290757375653954434566179])) -- 3^2 * 13^6 * 5229043^12 * 53^2
                      (.node 2988056555133532830454645410304572483548759436975666982163801095571705369820408199317693981 (.basic (.groups [5, 11, 571, 147389551])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^2 * 2671^4
                        (.node 1702788871932577455254056077036519625169580392821050543251519578027125036804368492137417497 (.basic (.groups [43, 839, 21613])) .empty .empty)
                        .empty)
                      (.node 129057353506116094800293385876455379535480639750900759412357134021134329860328148877991219517 (.cut 5 31 5090791308233417432671649211757062950685675167570044441897833725774770133591) .empty .empty)))
                  (.node 6043493078034610660721175352231468689656359808866152148834090332193457492209058355143931952634361 (.basic (.groups [421, 21613, 73774717787791, 275667700616081, 25332490598403837286469216576711])) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457^4
                    (.node 7487701112602689216444462718336674368317257227617389268915696465022411566455617882471352064917 (.basic (.groups [127, 199, 379])) -- 3^2 * 13 * 7^12 * 16148168401^8
                      (.node 2197724692482894408634355081580340865738145490062273206988074384487550976052805657747664762805 (.cut 7 101 971797249456899091549913773693930042639299797111001418973579711973080103299137) -- 3^4 * 11^4 * 5 * 3221^10 * 381510691^6
                        (.node 222699962239057938013510242045571178120155147396018944400245072095239731564562983479533320561 (.basic (.groups [5, 1933, 10272696651169673512025094858698975323497873289977112575960257])) .empty .empty)
                        .empty)
                      (.node 143242753215419585627978683573460184896881878764161454101964612328805510830426260985581234142561 (.basic (.groups [11, 131, 1171])) -- 3^2 * 13^6 * 5229043^12 * 53^4
                        (.node 56512864405877640888038011605721393807297278564153927355111777969921731236934053235509608817205 (.basic (.groups [463, 727, 881])) .empty .empty)
                        .empty))
                    (.node 353372973602529053881051546198676024655763805140050152066771120675552885771060988267185768206118001 (.cut 5 31 405757511589360442996933655519046683168033019977438159147208480345557286593781596033198897) -- 3^6 * 1093^2 * 398581^16
                      (.node 96029097320971840747631718631744530292500427046908374324285785594744553945099101663249682945530205 (.basic (.split 131)) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^12
                        (.node 21317515585952410393875579926656703499605385074408719386499258491872578889292918812308464424703421 (.basic (.groups [127, 22280841470107301759731, 1079319407727069602574578824577953188139513])) .empty .empty)
                        .empty)
                      (.node 827150666440253865851023208650983631284511380816919883477663437094233309456627021055397040362420333 (.basic (.groups [23, 67, 947, 1052756618474976278162998182950257362835133824350283768160599538602376228767093])) .empty .empty)))))
              (.node 254417273455232217876639725885667824894599732098248656814977460439503631080980320457545664180319705947119331424274460605 (.cut 7 101 60347700699719734300926199775507958180522768576429686957316457207119268899477330308109799) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^4 * 33151^2 * 366340651^8
                (.node 2873614952217127862579839687267478614883321318391147360810866576392911172930711955222241836909113506575625 (.basic (.groups [11, 71, 2311, 25332490598403837286469216576711])) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^4 * 5^4
                  (.node 22988919617737022900638717498139828919066570547129178886486932611143289383445695641777934695272908052605 (.basic (.split 2311)) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^4 * 5
                    (.node 1647955339125197759070107923439367884349599828551994611779068366591411290251845683643027809028243848005 (.cut 7 257 206060486419159677562191211783529114343259952971352905385746916042256828810721579422863) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^12 * 131^2
                      (.node 1339162043182050002557053701036622534087883607320127696773320478910603989102490838354572149804981231641 (.basic (.groups [31, 67, 139])) -- 3^2 * 13^2 * 61^2 * 97^16 * 62065212901958868055012327674641^2
                        (.node 496379237734897354910037209003768938918146910733599261935115343943816154986893677721462424379452398169 (.basic (.groups [31, 151, 4051, 5281])) .empty .empty)
                        .empty)
                      (.node 4597783923547404580127743499627965783813314109425835777297386522228657876689139128355586939054581610521 (.basic (.split 5)) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^4
                        (.node 1895729500247135799475311172440439417897480191829885819941835009491660058447211027614972691648764861605 (.basic (.split 29)) .empty .empty)
                        .empty))
                    (.node 59171816479329028713427959621364657494784966276226417436660826794660962555676554063015816428093011114381 (.basic (.split 5)) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^4
                      (.node 34713530750660549260478600456872429152865544874454214901738128984349448705291204121282771483966698014609 (.basic (.split 2311)) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^10
                        (.node 34652552734930706057082568772898794273739505455949557076394151324594649496036297147424523674360487978989 (.basic (.split 23)) .empty .empty)
                        .empty)
                      (.node 2058781482888893719065726547769046168335253050737821118384995572707715261541348704753875376182649204832489 (.basic (.groups [21613, 215447, 445279031, 412114133551])) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457^6
                        (.node 114944598088685114503193587490699144595332852735645894432434663055716446917228478208889673476364540263025 (.basic (.split 31)) .empty .empty)
                        .empty)))
                  (.node 1952517971313611295715446760276091028909576136811265296177778263123062746213883729980618638943829853712827687630517 (.cut 5 13 1205681780003306664674160705174341421591813212001936614450862773535709710283079659932397166602831662011) -- 3^2 * 13 * 7^12 * 16148168401^10
                    (.node 196959049302885595190265355176117637074276496171318698425945748984730386911972358785883033059117155364478405 (.cut 7 13 4845684022434050353510684331845006621441139895792901165791821002787790218477804227694076943) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^12
                      (.node 71840373805428196564495992181686965372083032959778684020271664409822779323267798880556045922727837664390625 (.basic (.groups [2311, 25332490598403837286469216576711, 13175420496922694647857902273274723865166871481])) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^4 * 5^6
                        (.node 18331200396778343504196678880863462170808198386197315693412506050710569583403201190987573023736698140885181 (.basic (.groups [7, 79, 18296928269900459971988699477237282979477642133512118795105419584254956007342982168289229])) .empty .empty)
                        .empty)
                      (.node 10342736300102952046341762646611741145813710926662987888130010603625979670837878171597395711677066676992933123645 (.cut 7 101 164343543440194073083478414256742839739115877091589959531627727992084927106364398044144124854831) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^14
                        (.node 9697205009895743713720043127976771488357536946298380001815215700825891309620293430032426129556713316528260749 (.cut 5 13 5352967631570348469864985907760016745758958460222438986814836658989214184464270206136865125469) .empty .empty)
                        .empty))
                    (.node 1520946239661326737830362930588778054893611711346680829985576497503943781181078336990223363173020892027623541807152849 (.cut 5 257 7461147352711754519228150235242094118398462745716820670797996454051148550942350172997473098587) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^12
                      (.node 56869674600472422937831642859593799883613082450439570820962882222203762342824619023183073667924624131336130570428013 (.basic (.groups [53, 79, 6397])) -- 3^2 * 13 * 7^2 * 19^2 * 127^4 * 262209281^12
                        (.node 13572443241074143735186696818491545530319222361282233610237358805056008273990112903108376457742591725388740223500481 (.cut 5 101 312431989210056179916062523639983061177558325593810739220978626478435279463829489707799201365248373363752801) .empty .empty)
                        .empty)
                      (.node 12944747696870320270841080003069294767151870865043995036684734891878879317244840505150592413842954904708037546140982577 (.cut 5 7 5020466175993732408217445142988079942535979860498423815185920796695192437465144062176277) .empty .empty))))
                (.node 50157113815285103802858957658189987178814026719001282078778642244040357674427601279656762116685891018773768932676288790099830724742501 (.basic (.groups [67, 22280841470107301759731, 35307496424266551241253715808286617328416524666519791808607875106787941047411293])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^6 * 29^2
                  (.node 81866868136318273962257002442726429934035197068867628935904532059592423912976456701525140969795331242867223694682586478153669 (.cut 5 7 19119331538751529553850996495625789610812569864423340005847170691359021666239902368100185441374569157743821431) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^12 * 53^2
                    (.node 3502016876195001002866872967856076458266851195087167777715534456200530788435579338518418272024187143866032038670928020115405 (.cut 7 31 12829493037613820015973189659054962787295125612767054350796308410388425578042021807585208479) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^4 * 5 * 2311^6
                      (.node 29144488478575391228998576875303107844085153815901612294732834481876975405117998113750495183266404856841304270089920426541 (.basic (.split 53)) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^12
                        (.node 12181034438213967541135440700350670455497587186577758910866556137121083248974468789196914934472316982110633554923322128369 (.basic (.split 23)) .empty .empty)
                        .empty)
                      (.node 21545486862193084973202618145493258844677217206822847798019580269188164634723122677012110483443175871500083542732580295621741 (.cut 5 7 319234751382317624862356726630630002958215839141307972482264048250574830707884462576832548435461) -- 3^2 * 13^2 * 61 * 31^16 * 751670559138758105956097^4
                        (.node 6443767217815188829260648130485504670958223621699634463848408196537053038707493989485168000335855683536525150554437405907201 (.basic (.groups [7, 67, 79, 100872621660213627140633959039687613804667219578019505044319975535451022633798600576274371862100889143097])) .empty .empty)
                        .empty))
                    (.node 59639849958721883237644420521034467513453063875150157049677339172461780825716529464514580400339941758351687196999154328299442003261 (.basic (.split 29)) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^6
                      (.node 3408752858224234890678882861026831970936900295879106631375807935968101057476264320437653872177667656590821804643297387724909329 (.basic (.split 67)) -- 3^2 * 13^2 * 61^6 * 52379047267^10 * 23^4
                        (.node 405932230080392865448963304769390409609777359533437173657255889498555216528036277139615591579990519401431796038856655178701081 (.basic (.groups [7, 29, 127, 211, 5237])) .empty .empty)
                        .empty)
                      (.node 11506985440815628095111439798663190930884595193377370251642803777226707121673879966133809848507096115191348358779003580320267642656845 (.basic (.split 1483)) .empty .empty)))
                  (.node 60111585459632179362813988576918609837928997980776551968440997241648478086556310006164256924959174345479305447149721333037183225443427171621024885842888834541 (.basic (.groups [19, 37, 181])) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^8
                    (.node 33419454785908265963215282842076630028485231016262253384926182722570866915062517633641926572082153148749382381689850909578510082346530569459641 (.basic (.split 131)) -- 3^2 * 13^2 * 61^6 * 52379047267^12
                      (.node 25307186503145961897669543323362170519194250478247723243365250276413147478919025796838460527913322908083065340630716005158981103551129983205 (.cut 7 101 256589387918277104289073961823878304573126230038696189546679067311607144051404255735977) -- 3^4 * 11^4 * 5 * 3221^12 * 1247451159302262598804596798564656994853573^2 * 1483^2
                        (.node 42182132718654772298204383390537779217382596470680078228252838127237940804193612676191336940132834346788739672380758872473957639508443341 (.cut 5 7 576275889027178927997053569617771822898704493667980012980551844989147969008731727895293267259939327802777003) .empty .empty)
                        .empty)
                      (.node 2867556317904858760973687344264385239594175247350382651693591108510193235646939325554645509517509150928440755260897657296384057615744055512484496005 (.cut 7 31 4330587617946686583618167190634801445120157817703588945530452597435005238087577294424324047745763958897801806499470360837624801251) -- 3^2 * 13^2 * 61^6 * 52379047267^12 * 131^2 * 5
                        (.node 573511263580971752194737468852877047918835049470076530338718221702038647129387865110929101903501830185688151052179531459276811523148811102496899201 (.cut 6 257 4330587617946686583618167190634801445120157817703588945530452597435005238087577294424324047745763958897801806499470360837624801251) .empty .empty)
                        .empty))
                    (.node 60587052264074813499887042889926483026148220839762496596280103665679912518622586714112835208637605637082983965614358241775908977538410456360515318546418686530747112021690240053538360221 (.cut 5 7 23176069867770495804059280257875057769311107547907814748097302131628152586581927293873530240798909382800218441712548939470634366594177685699408183144695662491) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^10
                      (.node 3164196815965109792310651550684929227813678904243844747967218797690574910226301688375185204817497142836372561229589741951615210181387615096276571357679842712373412299103001 (.cut 5 257 5908468716654489485899139189593722969846071857865738933396117134916820383251129784679026521909197515017055176551896784704404669355614934957808977) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^10
                        (.node 91688432854568418738282711901310939158511960531119744456206805084672714461063714120029831239697808860218040563392883761239966471426003881545741080483215868673165249 (.cut 5 257 390018377222516525785260337142367441356147931833639018311770192382474072968734861990861040938491939985721856528069424520889845202864635740195339635079) .empty .empty)
                        .empty)
                      (.node 17906415825428777712179792786741375888328185508031680869533205362284853872669017528082976674434327478191394681140586058217871367282179072969577058881680915296839362148184660264332810207384027535977880595193870211872005 (.cut 7 101 220141295892567423975069417577122730152568851347169564807045940168089744834507610533648150929156872439101021295741678890748019774210992246370146056734650495250067518151) .empty .empty)))))))))))

private def seed5Tree : ChoiceTree :=
  (.node 1216601012828248662450725535363025 (.basic (.groups [37, 43, 4933, 17351])) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^6 * 701^2 * 2801^2
    (.node 16805019541827014430625 (.basic (.groups [71, 2801, 5839, 45319, 158341])) -- 5^4 * 11^6 * 43^6 * 7^4
      (.node 478573784584575625 (.basic (.split 5113)) -- 5^4 * 11^4 * 71^2 * 3221^2
        (.node 6707556111025 (.basic (.split 19)) -- 5^2 * 31^4 * 11^2 * 7^4
          (.node 244140625 (.basic (.split 305175781)) -- 5^12
            (.node 390625 (.basic (.split 19)) -- 5^8
              (.node 625 (.basic (.split 11)) -- 5^4
                (.node 25 (.basic (.split 31)) -- 5^2
                  (.node 1 (.basic (.split 5)) .empty .empty)
                  .empty)
                (.node 75625 (.basic (.split 7)) -- 5^4 * 11^2
                  (.node 15625 (.basic (.split 19531)) .empty .empty)
                  .empty))
              (.node 23088025 (.basic (.split 11)) -- 5^2 * 31^4
                (.node 9765625 (.basic (.split 12207031)) -- 5^10
                  (.node 9150625 (.basic (.split 71)) .empty .empty)
                  .empty)
                (.node 181575625 (.basic (.split 19)) .empty .empty)))
            (.node 46128300625 (.basic (.split 3221)) -- 5^4 * 11^4 * 71^2
              (.node 6103515625 (.basic (.split 11)) -- 5^14
                (.node 2793651025 (.basic (.split 7)) -- 5^2 * 31^4 * 11^2
                  (.node 1107225625 (.basic (.split 43)) .empty .empty)
                  .empty)
                (.node 22187592025 (.basic (.split 917087137)) -- 5^2 * 31^6
                  (.node 8897205625 (.basic (.split 19)) .empty .empty)
                  .empty))
              (.node 338031774025 (.basic (.split 3221)) -- 5^2 * 31^4 * 11^4
                (.node 133974300625 (.basic (.split 7)) -- 5^4 * 11^8
                  (.node 50906640625 (.basic (.split 31)) .empty .empty)
                  .empty)
                (.node 738525390625 (.basic (.split 7)) .empty .empty))))
          (.node 1961517735450625 (.basic (.split 71)) -- 5^4 * 11^12
            (.node 232532763450625 (.basic (.split 211)) -- 5^4 * 11^4 * 71^4
              (.node 21362190705625 (.basic (.split 19)) -- 5^4 * 11^2 * 7^10
                (.node 18377297265625 (.basic (.split 31)) -- 5^8 * 19^6
                  (.node 16210890375625 (.basic (.split 71)) .empty .empty)
                  .empty)
                (.node 40901844657025 (.basic (.split 43)) -- 5^2 * 31^4 * 11^6
                  (.node 23663117025625 (.basic (.split 71)) .empty .empty)
                  .empty))
              (.node 1046747344575625 (.basic (.split 19)) -- 5^4 * 11^2 * 7^12
                (.node 328670249440225 (.basic (.split 19)) -- 5^2 * 31^4 * 11^2 * 7^6
                  (.node 321672295800625 (.basic (.split 19)) .empty .empty)
                  .empty)
                (.node 1159492734255625 (.basic (.split 29)) .empty .empty)))
            (.node 47013351656640625 (.basic (.split 11)) -- 5^8 * 19^4 * 31^4
              (.node 8542385246250625 (.basic (.split 71)) -- 5^4 * 11^2 * 7^4 * 19^6
                (.node 4949123203500025 (.basic (.split 7)) -- 5^2 * 31^4 * 11^8
                  (.node 3785384073975625 (.basic (.split 71)) .empty .empty)
                  .empty)
                (.node 20490707174520025 (.basic (.split 23)) -- 5^2 * 31^10
                  (.node 15761942494230625 (.basic (.split 19)) .empty .empty)
                  .empty))
              (.node 119285772926175625 (.basic (.split 151)) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^2
                (.node 81719098383525625 (.basic (.split 5113)) -- 5^4 * 11^10 * 71^2
                  (.node 74505805908203125 (.basic (.split 3499)) .empty .empty)
                  .empty)
                (.node 418576877066280625 (.basic (.split 29)) .empty .empty)))))
        (.node 72460112822443866025 (.basic (.split 1093)) -- 5^2 * 31^4 * 11^12
          (.node 10839584095321093225 (.basic (.split 7)) -- 5^2 * 31^10 * 23^2
            (.node 2783942054947755625 (.basic (.groups [71, 151, 911, 1123, 293459])) -- 5^4 * 11^2 * 7^10 * 19^4
              (.node 874135419944889025 (.basic (.split 151)) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^4
                (.node 789137268905980225 (.basic (.split 19)) -- 5^2 * 31^4 * 11^2 * 7^10
                  (.node 598843907623503025 (.basic (.split 15797)) .empty .empty)
                  .empty)
                (.node 1172197660554600625 (.basic (.split 7)) -- 5^4 * 11^4 * 71^6
                  (.node 975133389508980625 (.basic (.groups [13, 67, 71, 151, 911, 4733])) .empty .empty)
                  .empty))
              (.node 6999175152780930625 (.basic (.split 7)) -- 5^4 * 11^6 * 43^6
                (.node 5688615550453515625 (.basic (.split 7)) -- 5^8 * 19^4 * 31^4 * 11^2
                  (.node 3507025908457305025 (.basic (.split 17351)) .empty .empty)
                  .empty)
                (.node 9888010904406600625 (.basic (.split 1093)) .empty .empty)))
            (.node 38667726176393031025 (.basic (.split 19)) -- 5^2 * 31^4 * 11^2 * 7^12
              (.node 19082121116911125625 (.basic (.split 5113)) -- 5^4 * 11^6 * 43^4 * 71^2
                (.node 16971819948047265625 (.basic (.split 11)) -- 5^8 * 19^6 * 31^4
                  (.node 11882844811603560025 (.basic (.split 19)) .empty .empty)
                  .empty)
                (.node 20347955247131282425 (.basic (.split 11)) -- 5^2 * 31^6 * 917087137
                  (.node 19691569594713744025 (.basic (.split 42407)) .empty .empty)
                  .empty))
              (.node 43062164026349400625 (.basic (.split 701)) -- 5^4 * 11^2 * 7^4 * 19^6 * 71^2
                (.node 42832635577299562225 (.basic (.split 29)) -- 5^2 * 31^4 * 11^2 * 7^6 * 19^4
                  (.node 41920655261033250625 (.basic (.groups [71, 151, 911, 2801, 1772893])) .empty .empty)
                  .empty)
                (.node 45179830942031640625 (.basic (.split 151)) .empty .empty))))
          (.node 2053590213713719140625 (.basic (.groups [7, 701, 829, 17351, 70841])) -- 5^8 * 19^6 * 31^4 * 11^2
            (.node 582259395768574441225 (.basic (.groups [19, 29, 4733, 17351, 1772893])) -- 5^2 * 31^4 * 11^8 * 7^6
              (.node 352023153612742005625 (.basic (.groups [13, 67, 71, 701, 4733])) -- 5^4 * 11^2 * 7^6 * 19^6 * 29^2
                (.node 315562886600104938025 (.basic (.split 701)) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^6
                  (.node 139835267415281727025 (.basic (.split 17351)) .empty .empty)
                  .empty)
                (.node 417829750034966520625 (.basic (.split 2557)) -- 5^4 * 11^10 * 71^2 * 5113
                  (.node 411945974951352675625 (.basic (.split 211)) .empty .empty)
                  .empty))
              (.node 820087180577052705625 (.basic (.groups [71, 151, 911, 4733, 732541])) -- 5^4 * 11^2 * 7^6 * 19^4 * 29^4
                (.node 688322481604875390625 (.basic (.groups [151, 829, 911, 3221, 17351])) -- 5^8 * 19^4 * 31^4 * 11^4
                  (.node 601319581320851325625 (.basic (.split 151)) .empty .empty)
                  .empty)
                (.node 1113252187676627700625 (.basic (.split 71)) .empty .empty)))
            (.node 5734139986424858316025 (.basic (.split 397)) -- 5^2 * 31^10 * 23^4
              (.node 2462102584902885173425 (.basic (.split 7)) -- 5^2 * 31^6 * 917087137 * 11^2
                (.node 2446947760580935170625 (.basic (.split 2557)) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113
                  (.node 2273620341345648765625 (.basic (.split 191)) .empty .empty)
                  .empty)
                (.node 2814446582991596100625 (.basic (.split 883)) .empty .empty))
              (.node 13658365936638891015625 (.basic (.groups [151, 829, 911, 2801])) -- 5^8 * 19^4 * 31^4 * 11^2 * 7^4
                (.node 10807595918516414483125 (.basic (.split 547)) -- 5^4 * 11^12 * 71^2 * 1093
                  (.node 5909048406855741750625 (.basic (.split 37)) .empty .empty)
                  .empty)
                (.node 15462581443405141963225 (.basic (.groups [29, 701, 4733, 17351, 70841])) .empty .empty))))))
      (.node 15757594387029731113232430625 (.basic (.split 7)) -- 5^4 * 11^4 * 71^10 * 23^2
        (.node 5911508306351827301393425 (.basic (.split 19)) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^4
          (.node 296051472188316026730625 (.basic (.groups [71, 701, 4733, 70841])) -- 5^4 * 11^2 * 7^6 * 19^6 * 29^4
            (.node 102841158021096248902225 (.basic (.groups [151, 911, 1123, 17351])) -- 5^2 * 31^4 * 11^2 * 7^10 * 19^4
              (.node 79198903314931145565325 (.basic (.split 547)) -- 5^2 * 31^4 * 11^12 * 1093
                (.node 36022246520508931831225 (.basic (.groups [13, 67, 151, 911, 4733])) -- 5^2 * 31^4 * 11^2 * 7^6 * 19^4 * 29^2
                  (.node 26025841412865944833225 (.basic (.split 79)) .empty .empty)
                  .empty)
                (.node 97566885270766585320625 (.basic (.split 2557)) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113
                  (.node 96192972550348984275625 (.basic (.split 211)) .empty .empty)
                  .empty))
              (.node 218634791053662444773125 (.basic (.split 19)) -- 5^4 * 11^4 * 71^8 * 37
                (.node 217076368856827328550625 (.basic (.groups [211, 701, 2221, 2801, 70841])) -- 5^4 * 11^2 * 7^4 * 19^6 * 71^4
                  (.node 137907882566588208930625 (.basic (.groups [29, 883, 3221, 4733, 21020917])) .empty .empty)
                  .empty)
                (.node 258555409450855913269225 (.basic (.split 7)) .empty .empty)))
            (.node 2276453574610668751461925 (.basic (.split 199)) -- 5^2 * 31^10 * 23^4 * 397
              (.node 689693318865301325430625 (.basic (.groups [71, 151, 911, 4733])) -- 5^4 * 11^2 * 7^6 * 19^4 * 29^6
                (.node 460907711104938056100625 (.basic (.split 1361)) -- 5^4 * 11^4 * 71^4 * 211^4
                  (.node 297914412773249105984425 (.basic (.split 1451)) .empty .empty)
                  .empty)
                (.node 1548584218692987546018025 (.basic (.groups [151, 911, 2801, 17351])) -- 5^2 * 31^4 * 11^8 * 7^4 * 19^4
                  (.node 1275266229230431296828025 (.basic (.groups [29, 79, 397, 617, 4733])) .empty .empty)
                  .empty))
              (.node 4965126921833223161850625 (.basic (.split 5113)) -- 5^4 * 11^4 * 71^2 * 3221^4
                (.node 3033360052818750049177225 (.basic (.split 29)) -- 5^2 * 31^10 * 23^6
                  (.node 3031252009438411532475625 (.basic (.groups [151, 883, 911, 2801, 21020917])) .empty .empty)
                  .empty)
                (.node 5611904278077880238850625 (.basic (.groups [2801, 5113, 104281, 62060021])) .empty .empty))))
          (.node 454450418153436017640429025 (.basic (.split 911)) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^4 * 151^4
            (.node 62014955748474343434675625 (.basic (.split 911)) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^2 * 151^4
              (.node 30294709323748011670060225 (.basic (.groups [151, 911, 4733, 17351])) -- 5^2 * 31^4 * 11^2 * 7^6 * 19^4 * 29^4
                (.node 29787513018959794164900625 (.basic (.split 23)) -- 5^4 * 11^4 * 71^10
                  (.node 21160790464712121816525625 (.basic (.split 2801)) .empty .empty)
                  .empty)
                (.node 41124470944612275628356025 (.basic (.groups [2801, 17351, 104281, 62060021])) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^10
                  (.node 36047643945563141824115425 (.basic (.split 43)) .empty .empty)
                  .empty))
              (.node 155067918038178166650423025 (.basic (.split 2801)) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^6 * 701^2
                (.node 149438628086283755685757225 (.basic (.split 17351)) -- 5^2 * 31^4 * 11^10 * 15797^2
                  (.node 82943943672630612618765625 (.basic (.split 7)) .empty .empty)
                  .empty)
                (.node 289663907011239537768277825 (.basic (.split 19)) .empty .empty)))
            (.node 2551055804420568791358046225 (.basic (.groups [13, 67, 397, 617, 5336717])) -- 5^2 * 31^10 * 23^6 * 29^2
              (.node 1055815403834638478829735025 (.basic (.split 13)) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2
                (.node 620791538091505047759409225 (.cut 13 101 2036337670901142530731) -- 5^2 * 31^4 * 11^6 * 43^6 * 7^4
                  (.node 484908774626309229733425625 (.basic (.groups [7, 883, 45319, 3500201, 21020917])) .empty .empty)
                  .empty)
                (.node 1094281975407266563223700625 (.basic (.groups [701, 883, 2801, 70841])) .empty .empty))
              (.node 13725600249850300224786555325 (.basic (.split 7)) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13
                (.node 11074508071241163815093100625 (.basic (.groups [41, 3221, 4271, 5113, 3462179509])) -- 5^4 * 11^4 * 71^8 * 37^4
                  (.node 4361764917413140160717966425 (.basic (.split 7)) .empty .empty)
                  .empty)
                (.node 15280541379579032535209625625 (.basic (.groups [37, 151, 911, 2801])) .empty .empty)))))
        (.node 10472597566708949525883837386425 (.cut 13 31 207006296634000247) -- 5^2 * 31^6 * 917087137 * 11^8 * 7^4
          (.node 627229302567211440988714379425 (.basic (.split 7)) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^2
            (.node 42098414209131221364592557025 (.basic (.split 13)) -- 5^2 * 31^4 * 11^6 * 43^4 * 17351^2
              (.node 25477850541272077814520649225 (.cut 13 101 994228601205281887199) -- 5^2 * 31^4 * 11^2 * 7^6 * 19^4 * 29^6
                (.node 25386693951333270026542245625 (.basic (.split 2557)) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113
                  (.node 20520072206102947195655925625 (.basic (.split 7)) .empty .empty)
                  .empty)
                (.node 35412406035190912677810697225 (.basic (.split 1471)) -- 5^2 * 31^12 * 42407^2
                  (.node 28492704604904343465278423125 (.basic (.groups [151, 911, 3221, 5113])) .empty .empty)
                  .empty))
              (.node 527773555006989959446873937425 (.basic (.split 1451)) -- 5^2 * 31^6 * 917087137 * 11^10
                (.node 312617391928059165254199825625 (.basic (.groups [211, 911, 2221, 2801])) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^4 * 151^4
                  (.node 199148408757986100897656265625 (.basic (.split 13)) .empty .empty)
                  .empty)
                (.node 547279384718705877739703241325 (.basic (.groups [7, 1063, 21787, 45319, 3500201])) .empty .empty)))
            (.node 1414003006020963504654038925625 (.basic (.groups [911, 1499, 2801, 5113])) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^2 * 151^6
              (.node 853749032341609965014365800625 (.basic (.split 13)) -- 5^4 * 11^4 * 71^4 * 211^4 * 1361^2
                (.node 770393673992076485744892539425 (.basic (.groups [151, 911, 1451, 2801, 28729])) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^4 * 19^4
                  (.node 695483040733986130181635057825 (.cut 13 31 13737734262967003) .empty .empty)
                  .empty)
                (.node 1013708631124282993395645241225 (.cut 11 31 4068960780926179499149687) -- 5^2 * 31^10 * 23^2 * 7^4 * 79^4
                  (.node 867295126738517865655010640625 (.basic (.split 7)) .empty .empty)
                  .empty))
              (.node 10361923984316494638219422199025 (.basic (.groups [911, 1499, 2801, 17351])) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^4 * 151^6
                (.node 9758272029141318943985157015625 (.basic (.groups [13, 29, 31, 4733, 4760281, 32009891])) -- 5^6 * 19531^4 * 191^2 * 7^6
                  (.node 3025878009121237378945188765625 (.basic (.split 11)) .empty .empty)
                  .empty)
                (.node 10398433595150001372762508650625 (.basic (.groups [101, 2801, 5113, 70841])) .empty .empty))))
          (.node 123239721168735214831427639105425 (.basic (.split 1451)) -- 5^2 * 31^6 * 917087137 * 11^6 * 43^4
            (.node 49268693366853176216769877425625 (.cut 13 31 253812054489386603927971) -- 5^4 * 11^4 * 71^4 * 211^6 * 7^4
              (.node 30155143748921109593856062049025 (.basic (.split 1063)) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13^4
                (.node 11167755228520202085395751953125 (.basic (.split 43609)) -- 5^12 * 305175781 * 3499^4
                  (.node 11098737420440929545186755408125 (.basic (.groups [7, 2221, 3221, 142591, 292661])) .empty .empty)
                  .empty)
                (.node 37749290025611747801499734431825 (.basic (.groups [29, 151, 911, 1451])) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^6 * 19^4
                  (.node 32955166199890570839712519335325 (.basic (.split 1063)) .empty .empty)
                  .empty))
              (.node 55850457792382939856037494625625 (.basic (.split 4751)) -- 5^4 * 11^10 * 71^2 * 5113^4
                (.node 51512402358839118821717500125625 (.basic (.split 7)) -- 5^4 * 11^4 * 71^2 * 3221^6
                  (.node 51467514089729575577649429375625 (.basic (.groups [2801, 5113, 830833, 104670301])) .empty .empty)
                  .empty)
                (.node 76200529991878789270184524908025 (.basic (.groups [101, 2801, 17351, 70841])) .empty .empty)))
            (.node 327078559176446090266692423675625 (.basic (.split 4751)) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4
              (.node 190665960979626073067319614925625 (.cut 7 101 140328162594169124887679) -- 5^4 * 11^6 * 43^4 * 71^4 * 211^4
                (.node 166019118830735887635855260025625 (.basic (.groups [37, 43, 4933, 5113])) -- 5^4 * 11^2 * 7^4 * 19^6 * 71^2 * 701^2 * 2801^2
                  (.node 142439459862002717825917527318025 (.basic (.split 617)) .empty .empty)
                  .empty)
                (.node 278112116311139611353906206732425 (.basic (.groups [701, 1451, 2801, 28729])) .empty .empty))
              (.node 377486890210969742934746022087025 (.basic (.split 7)) -- 5^2 * 31^4 * 11^4 * 3221^6
                (.node 377157945484317773196162496857025 (.basic (.groups [2801, 17351, 830833, 104670301])) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^4 * 151^4 * 911^2
                  (.node 366131239103669722852367840640625 (.basic (.split 7)) .empty .empty)
                  .empty)
                (.node 1202372808226996813394128021191025 (.basic (.groups [1063, 21787, 30941, 45319])) .empty .empty)))))))
    (.node 15694684149828551485052600870871982542996696025 (.basic (.split 31747594185191)) -- 5^2 * 31^6 * 917087137^4
      (.node 85812616071519966124591377708327015625 (.basic (.groups [13, 67, 631, 4733, 12567292335484050831661])) -- 5^6 * 19531^6 * 7^6 * 29^2
        (.node 216840416733533038495799526572265625 (.basic (.split 131)) -- 5^10 * 12207031^4
          (.node 17861678629470574629502441177770625 (.cut 7 31 110922498204102770206051) -- 5^4 * 11^10 * 71^2 * 5113 * 2557^4
            (.node 5096219293567667521361674486285225 (.basic (.split 1063)) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13^6
              (.node 1710944116403970818386237223550625 (.cut 13 31 10492953267991749012036547) -- 5^4 * 11^4 * 71^6 * 7^4 * 883^4
                (.node 1614803143794637971145913447430925 (.basic (.groups [29, 1063, 4733, 21787])) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13 * 7^6
                  (.node 1505977555463874669813903224999425 (.basic (.groups [19, 73, 2801, 3221, 28729])) .empty .empty)
                  .empty)
                (.node 3570023734961029048868316843921925 (.cut 7 13 42771615915623930408293091) -- 5^2 * 31^10 * 23^4 * 397 * 199^4
                  (.node 2082375599299181395437680548140625 (.basic (.split 631)) .empty .empty)
                  .empty))
              (.node 13041568263851962786883467158225625 (.basic (.split 4751)) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113^4
                (.node 7127989153351677026961010224075625 (.cut 13 31 14269536662804642994875137) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^4 * 151^6
                  (.node 5687877702536841027737960602515625 (.basic (.groups [31, 2801, 30941, 4760281, 32009891])) .empty .empty)
                  .empty)
                (.node 13627493699245840956341404129888825 (.cut 13 31 9797767450922088787) .empty .empty)))
            (.node 102036404365659888376446346858890625 (.basic (.split 29)) -- 5^6 * 19531^6 * 7^6
              (.node 44301879931544036465136508717515625 (.basic (.split 1871)) -- 5^6 * 19531^4 * 191^4 * 11^4
                (.node 37291693678464949845907225035885025 (.basic (.split 17351)) -- 5^2 * 31^4 * 11^10 * 15797^4
                  (.node 24383926112708722210775301631650625 (.basic (.groups [2221, 3221, 30941, 142591])) .empty .empty)
                  .empty)
                (.node 73792900217729858820881258024971825 (.cut 13 31 31972058484481) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^2 * 7^6
                  (.node 44989575092936573978521905724027225 (.basic (.groups [13, 1063, 21787, 1806113, 249561007])) .empty .empty)
                  .empty))
              (.node 123681278063572724290943717801625625 (.basic (.groups [673, 2801, 5113, 10333, 248879])) -- 5^4 * 11^4 * 71^2 * 3221^6 * 7^4
                (.node 110387055650751860821299431358765625 (.basic (.split 127)) -- 5^6 * 19531^4 * 191^6
                  (.node 104603835698491401628124426046420625 (.basic (.split 12011)) .empty .empty)
                  .empty)
                (.node 203201004590362461463607635581283225 (.cut 7 13 19209949089804820108053977) .empty .empty))))
          (.node 5109800667090305824576869513425775625 (.cut 13 31 17222794925345736283641261733) -- 5^4 * 11^2 * 7^4 * 19^6 * 71^2 * 701^6
            (.node 1320569200854309535069080243155774425 (.basic (.split 41)) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^4
              (.node 906346023396538352786325199030947025 (.basic (.groups [673, 2801, 10333, 17351, 248879])) -- 5^2 * 31^4 * 11^4 * 3221^6 * 7^4
                (.node 879081105087911004568535185378140625 (.basic (.groups [19, 1871, 2801, 13001, 4760281])) -- 5^6 * 19531^4 * 191^4 * 11^2 * 7^4
                  (.node 227870244440991412223309704705930825 (.cut 7 101 1746626715595179084599) .empty .empty)
                  .empty)
                (.node 1111174970485271667609407834728532425 (.cut 7 31 59836048590169237) -- 5^2 * 31^6 * 917087137 * 11^10 * 1451^2
                  (.node 961251331728726133687715341825140625 (.cut 11 31 69185295635465920676430943) .empty .empty)
                  .empty))
              (.node 4120883513047774053621025975748955625 (.cut 7 13 1561055930511738395222113) -- 5^4 * 11^4 * 71^4 * 211^4 * 1361^2 * 13^6
                (.node 3877142348250925768721338187281650925 (.cut 17 13 79208937952866391984571) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13 * 7^10
                  (.node 1581417261336043312005375074179500625 (.basic (.groups [2221, 3221, 11831, 292661, 58044391])) .empty .empty)
                  .empty)
                (.node 4170857507008580698990340509596570625 (.cut 7 101 616699232982945713256329) .empty .empty)))
            (.node 42713970760862459092978392076848075625 (.cut 13 31 18793175856254473424414243) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^2 * 151^4 * 911^4
              (.node 11196393787968165544431598846368639325 (.cut 7 13 17929928464964834967853) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13^9
                (.node 6060382625115063490256242172279655625 (.cut 13 31 3861832732158238425647045969) -- 5^4 * 11^4 * 71^2 * 3221^6 * 7^6
                  (.node 5360527471716828412281517554819390625 (.basic (.groups [43, 1871, 13001, 45319, 4760281])) .empty .empty)
                  .empty)
                (.node 37445016638539228926157945724328393025 (.cut 13 31 58445670790078988902299928091) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^6 * 701^6
                  (.node 12674030748339674145735635723379387025 (.basic (.split 45319)) .empty .empty)
                  .empty))
              (.node 54225135535405952646430717557171619225 (.cut 7 13 417640328230875026066444629621) -- 5^2 * 31^10 * 23^4 * 397^4 * 617^2
                (.node 44410955146430379286529934752516404225 (.cut 13 31 13105155434319889482378622063) -- 5^2 * 31^4 * 11^4 * 3221^6 * 7^6
                  (.node 43074974149307639223858224083528890625 (.cut 13 31 17542998873237072273935353) .empty .empty)
                  .empty)
                (.node 63684029613255200225781228685812924025 (.basic (.split 2426789)) .empty .empty)))))
        (.node 2780327716047864149443976613020410630169425 (.basic (.groups [2381, 3221, 28729, 52584967, 74590391])) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^6
          (.node 7382817564809300325945871653898631175625 (.basic (.split 10378063)) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4 * 4751^2
            (.node 2219876826636094328451123888744856808425 (.basic (.split 1723)) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^4 * 41^2
              (.node 534432984000980802355426410720839400625 (.basic (.split 5113)) -- 5^4 * 11^4 * 71^2 * 3221^8
                (.node 259469032188376290041302582800200900425 (.cut 7 101 4557155124379751) -- 5^2 * 31^6 * 917087137 * 11^6 * 43^4 * 1451^2
                  (.node 145553119243586152077610785002792311225 (.cut 7 13 35895716787099951196313309) .empty .empty)
                  .empty)
                (.node 1302519764717540310771753663912303525625 (.cut 13 31 2195098418740371404216823799) -- 5^4 * 11^2 * 7^4 * 19^6 * 71^2 * 701^2 * 2801^4
                  (.node 1260656589140125510813418184727102125625 (.cut 7 31 8425417322380515832847207573) .empty .empty)
                  .empty))
              (.node 3916366465523267538758863354535372538025 (.basic (.split 17351)) -- 5^2 * 31^4 * 11^4 * 3221^8
                (.node 3721198391564160473626415675506650390625 (.basic (.split 17293)) -- 5^10 * 12207031^4 * 131^2
                  (.node 3393388045964719131588581491539244950625 (.basic (.split 4751)) .empty .empty)
                  .empty)
                (.node 4027030177195078634621824555399128765625 (.basic (.groups [7, 13, 31, 4760281, 32009891, 48551233240513])) .empty .empty)))
            (.node 340942706519612913334090711836578964255625 (.cut 7 101 2834738530048088984539445873559617) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113^6
              (.node 155084977265440247355351933013392615015625 (.basic (.groups [7, 157, 3187, 3221, 13001])) -- 5^6 * 19531^4 * 191^4 * 11^4 * 1871^2
                (.node 9544966122846320534372074710969684303025 (.cut 13 31 7449081295435983617165286473) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^6 * 701^2 * 2801^4
                  (.node 8550739217402660378795288426201995305625 (.basic (.split 113)) .empty .empty)
                  .empty)
                (.node 294374291893234767877496407578935965725625 (.cut 7 101 46843052441106145997299619167) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113^4 * 4751^2
                  (.node 165808246349794492493989405412979058345225 (.basic (.groups [461, 691, 1222567, 2426789, 2941691])) .empty .empty)
                  .empty))
              (.node 2117582361196856952290090698515996337890625 (.basic (.split 11)) -- 5^12 * 305175781^4
                (.node 1085248163361972231758932048447872603495625 (.basic (.split 12011)) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113 * 2557^4
                  (.node 683925924151825708203682900473583604985625 (.basic (.split 743)) .empty .empty)
                  .empty)
                (.node 2732555847197014842443295238015651855395625 (.basic (.split 2557)) .empty .empty))))
          (.node 95694291862944614624478248934167189762595025 (.basic (.split 10378063)) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^6
            (.node 28716600963311864213438905724330225718765625 (.basic (.groups [197, 10627, 183569, 4760281, 32009891])) -- 5^6 * 19531^4 * 191^6 * 127^4
              (.node 13544435551658799832503239054461514806297225 (.cut 7 31 742817331656750777964483086681) -- 5^2 * 31^4 * 11^10 * 15797^2 * 17351^4
                (.node 11226932919388051777214210474980670184315025 (.cut 7 31 2604963138458266432601364061433) -- 5^2 * 31^4 * 11^10 * 15797^4 * 17351^2
                  (.node 2929292402935241083737108362779246777200625 (.cut 7 31 13315948401885606820032381814867) .empty .empty)
                  .empty)
                (.node 27270104924341345746592894846529268292335625 (.cut 7 7 44353464576866630500041586233533) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113 * 2557^6
                  (.node 15090580410271283081939339202216376661895625 (.basic (.split 1459)) .empty .empty)
                  .empty))
              (.node 63859485597632557887902919407369627353515625 (.basic (.split 61)) -- 5^10 * 12207031^4 * 131^4
                (.node 42078142913366220289930724257135590711747325 (.cut 17 31 809410158778927780690549621) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13 * 7^4 * 1063^4
                  (.node 38502990412605408570169846394388543437613025 (.basic (.groups [1291, 21787, 30941, 10378063])) .empty .empty)
                  .empty)
                (.node 64350683785319027070421606276536505205078125 (.basic (.split 8647)) .empty .empty)))
            (.node 3815608222483077695567236576836208518842217025 (.cut 7 101 4328579438852746089217673195376108983) -- 5^2 * 31^4 * 11^6 * 43^4 * 17351^6
              (.node 330123547335949225087905012076112560790640625 (.cut 11 101 2478646123662105166366606131407171) -- 5^6 * 19531^6 * 7^4 * 631^4
                (.node 256227465704819691227100974520435556884765625 (.basic (.split 7)) -- 5^12 * 305175781^4 * 11^2
                  (.node 109184389067014570376837037914173278057525625 (.basic (.groups [13, 991, 10378063, 14686393, 10768274427527])) .empty .empty)
                  .empty)
                (.node 546286359838439629429248499130125775955695425 (.cut 7 7 4042898775006710584859737651) .empty .empty))
              (.node 6272841361512036545658376290983555319831836425 (.cut 7 7 9748851134581722493413008903) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^4 * 41^6
                (.node 5544657234165719668489974498429404168019675625 (.basic (.split 5113)) -- 5^4 * 11^4 * 71^2 * 3221^10
                  (.node 3895428621455586031162078083849547268564453125 (.basic (.split 31)) .empty .empty)
                  .empty)
                (.node 6507005379730314048358704040651663840956601225 (.cut 7 13 1511046242374809303507837794303) .empty .empty))))))
      (.node 115064657344835134018906389931697797292306474864627148795625 (.cut 7 7 657960052724662338132445210480614949023491) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^6 * 743^6
        (.node 2177029318267606025358149745328586830933286534370625 (.cut 7 31 13983634512808228018962674981863) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^4 * 12011^4
          (.node 6644616810988387073765616789368150197294773225625 (.cut 7 7 211468285310711997532371897462679139) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113^4 * 4751^4
            (.node 377560622502091230388134941523541355548709295625 (.cut 7 31 2158958382312826827200586856691) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^6 * 743^2
              (.node 88712559813017034407000888970985935178605780625 (.basic (.split 113)) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^6
                (.node 76595558366903686202936593015605328564752450625 (.basic (.split 22576753)) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^4 * 4751^2
                  (.node 40631679377535882515084544644031118957775829025 (.basic (.split 17351)) .empty .empty)
                  .empty)
                (.node 166644965455693091766550540917671556794838675625 (.basic (.split 31)) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4 * 4751^4
                  (.node 126201589894569388642232583264134717641809390625 (.basic (.split 23)) .empty .empty)
                  .empty))
              (.node 1394175463996709049141832137126078587516544705625 (.cut 7 31 24544775986561991008720303241851183) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^6 * 113^4
                (.node 1179050326200697925592902415457889911790072568025 (.basic (.groups [13, 1063, 21787, 24517, 10378063])) -- 5^2 * 31^4 * 11^4 * 3221^8 * 17351^2
                  (.node 542896829899468012942286546135935737220912515625 (.cut 7 31 15647378751025652922739869445874131) .empty .empty)
                  .empty)
                (.node 5853704753694889228103497805029785561169337564425 (.cut 7 31 63043246408362392378642686721) .empty .empty)))
            (.node 66760641054227206591741036546727265632517167640625 (.basic (.split 7)) -- 5^6 * 19531^10 * 23^2
              (.node 32311738707385906583033352568264717773883603515625 (.basic (.split 37871)) -- 5^10 * 12207031^6
                (.node 28349832438289324664989239610469543511084601470625 (.cut 7 31 307448819151627043261998329798965394827) -- 5^4 * 11^4 * 71^2 * 3221^10 * 5113
                  (.node 7095622718853251582325605706832254601932666660625 (.cut 7 31 547380484441992121294045927692817) .empty .empty)
                  .empty)
                (.node 47546997069673514574792730558111246300962413082925 (.cut 17 13 914608387705266919277250446737133) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13 * 7^4 * 1063^6
                  (.node 43507185573541320916626251160420828039656152246225 (.cut 7 13 10103141065329762138292540547123753) .empty .empty)
                  .empty))
              (.node 1132770676252414512342994351270519406295617212800625 (.cut 7 31 306810330040542698311411453048813931) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^6 * 113^2
                (.node 375054664502066854405920444455949199798422554667025 (.basic (.split 7908811)) -- 5^2 * 31^12 * 42407^4 * 2426789^2
                  (.node 156562372354279328841110615868061755463277867970625 (.cut 7 31 91421953057107410675990449763) .empty .empty)
                  .empty)
                (.node 1142960020714789885261806260841308224169580259770625 (.cut 7 31 1126835975942307563290402533471164098141) .empty .empty))))
          (.node 12232459665330375067056193288891550030326028271721059025 (.cut 7 31 2784663993154656937902524263137994828976491) -- 5^2 * 31^4 * 11^4 * 3221^10 * 17351^2
            (.node 365255214585448689364091325350921506347069442690500625 (.cut 7 31 720204921866523174171595048815454076834599) -- 5^4 * 11^4 * 71^2 * 3221^8 * 5113^4
              (.node 28809455659935181296869087709501607415962712723025025 (.basic (.groups [13, 19, 1063, 21787, 10378063])) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^8
                (.node 19564555593281237572878096169573720784075471399390425 (.cut 7 7 17657112056170859645416180926289) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^4 * 41^2 * 1723^4
                  (.node 17802226499773977848492054558962897483998759346125625 (.cut 7 7 3447534690483614411776973553402059602199) .empty .empty)
                  .empty)
                (.node 208431964091656961644539506333129481789309417940485625 (.cut 7 7 1191850818903139816223498486980144187) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^6 * 743^4
                  (.node 153900125142607139801336522098828953802726208551875625 (.cut 7 7 7743745293133922879791787140780763) .empty .empty)
                  .empty))
              (.node 3761510326910869923047670576144223297644655381046175625 (.cut 7 31 53843131584498659661001143519084141499) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4 * 4751^6
                (.node 1729279002146667898193207335174846648490260583905320625 (.cut 7 31 12567506976794029340098460389) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^4 * 4751^2 * 22576753
                  (.node 1728915020053308371876370980484836491968920880259950625 (.cut 7 31 2609798660866469861907774587285312911) .empty .empty)
                  .empty)
                (.node 5843954585914720683343615411681608950179063868207205625 (.cut 7 31 126753271589846408564284219380037364753866589) .empty .empty)))
            (.node 116813210106817979090244684361996006433769844113816645625 (.cut 7 7 45056842838896039747620359474700729088639) -- 5^4 * 11^4 * 71^2 * 3221^8 * 5113 * 2557^4
              (.node 53460870909594287697453420130968755094300186011880855025 (.cut 7 7 24332359311864175864229181161628614620351) -- 5^2 * 31^4 * 11^6 * 43^4 * 17351^4 * 45319^4
                (.node 29236944144214872640085371118331726530719290551306235625 (.cut 7 7 124049055390789210016962546833690920849841) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^10
                  (.node 14464348765067080908107694871373262298988736190251180625 (.cut 7 7 4629966331796709587821537489212358313371) .empty .empty)
                  .empty)
                (.node 68379687451472559645067881713785287377039346935556945625 (.cut 7 7 1506244167934701664129222309310341) .empty .empty))
              (.node 46341904106821867286631550378015073665601243824741416015625 (.basic (.split 1434250513)) -- 5^10 * 12207031^6 * 37871^2
                (.node 22586333029364807963732771661974581125626729401536269445625 (.cut 7 7 2637781539578894984513497958004964531) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113 * 2557^4 * 12011^4
                  (.node 332785343185870056028585428355969478204556475416806640625 (.cut 8 257 3031833909459797478788537007222325302502531) .empty .empty)
                  .empty)
                (.node 58081863561886215138492817563402422529587590132040937019825 (.cut 7 7 52419180617404063436220358791713213957) .empty .empty)))))
        (.node 97421574236955161208925344264141707491135009289093592664936768455873602825004416884233025 (.basic (.groups [7, 19, 571, 147389551, 22280841470107301759731])) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^2 * 2671^4 * 11^2
          (.node 66465899738606069955469219171653463326621374409073458012756572265625 (.cut 7 257 2724085471229500305099398456202351274736421673) -- 5^10 * 12207031^6 * 37871^2 * 1434250513
            (.node 145558541463888059737822743514382179319043494074128294569970625 (.cut 7 7 3206313341643409158086364927207780039281) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^4 * 12011^2 * 1459^6
              (.node 8673294083313693522662957609246055033650577012761002279455025 (.cut 7 31 1115985611578566957283218686282585971156739931041) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^10
                (.node 359761762284627943440557560776678976188376657768409892578125 (.cut 7 13 189544413632508478018538099506943711495791) -- 5^10 * 12207031^4 * 131^2 * 17293 * 8647^4
                  (.node 314067220991105426022597183196202435336766191522114503845625 (.cut 7 7 10086683706877711283656459028919393177551) .empty .empty)
                  .empty)
                (.node 84904814860542482813901943292397984418658458905629657253675625 (.cut 7 7 35245069379084624580636547347967905706138580927) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4 * 4751^8
                  (.node 39025071561558296623301817647874709781558974078148485767450625 (.cut 7 7 294541889914383093068941505031370121938793627) .empty .empty)
                  .empty))
              (.node 31693189279681936579748892878535387643329624512515045746773450383225 (.basic (.split 2801)) -- 5^2 * 31^6 * 917087137^6 * 7^4
                (.node 3258397481094581209221708182708472070431730691217485961192247920625 (.cut 7 7 1902686175986879975468353496544117359075430587) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113 * 2557^4 * 12011^6
                  (.node 13199995535061198075697164880689457577396761562896728757506643225 (.basic (.split 7)) .empty .empty)
                  .empty)
                (.node 45308631571194573103480508770876114871917913602455500958640210320625 (.cut 7 7 1455146558777734672828480727819920675196401938107) .empty .empty)))
            (.node 19899836717951751831642533436983675176091801582366356677821146084220132250625 (.cut 7 7 6652600001535581671757128205802779858127261198826231) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^4 * 4751^2 * 22576753^4
              (.node 1110072244569763626279447986209332453988937128999068054808356217944219025 (.cut 7 31 28776943033939210872818079768185158721484428487737467) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^6 * 10378063^4
                (.node 1552966274704414892407695751048233994523151601113237241591899068778025 (.cut 11 257 402255580282206204415805411678773859440801096080815154653) -- 5^2 * 31^6 * 917087137^6 * 7^6
                  (.node 85642107861090068465648042882758493527834481899890793528687619775625 (.cut 7 31 311418531339421319020169399505539305557706883) .empty .empty)
                  .empty)
                (.node 248652117505861881312014493716730115829894545405012555425931529100080443225 (.cut 11 257 419253491978052652943834374775278142535700783217126802853) -- 5^2 * 31^6 * 917087137^6 * 7^4 * 2801^2
                  (.node 15818824966651071259133192373044545403499126054182300681519543016879438025 (.basic (.split 2671)) .empty .empty)
                  .empty))
              (.node 119559433754471780758163234417451773003648818043641873073489706022683863912423928010225 (.cut 7 7 34093371258206085786958847604588010507763954048491055263838594772601) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^6 * 10378063^6
                (.node 9224013996836603465092463227587939406368151251223910597147420275180478526356955625 (.cut 7 7 368951892948401151457893103582130810823720563790833302170449) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4 * 4751^2 * 10378063^6
                  (.node 1950825301756107481883422223918471513485136475324111909862243830639120225446503225 (.cut 11 13 1046653865032259044238597881592123850563759487513896035193978587841) .empty .empty)
                  .empty)
                (.node 805136977164918687677068960860675268521776936273500765825923706246889279545491048630025 (.basic (.split 11)) .empty .empty))))
          (.node 4632051631096654689767787655112167809153388944809706464716951763079643866372885656260823337888686714403025 (.cut 13 31 1152723877104824561420394342047560645942737995062845561232560608178283941602501) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^4 * 11^2 * 7^4
            (.node 15943947704629457732032409550814460259855187558936209309196071069146959656523575425737978796330340025 (.basic (.split 11)) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^4
              (.node 1426349268403260515259875965371298739377707671001619290207339226962445418960889667602055719025 (.cut 7 7 1378894118156072308970618060802964525511857968297687163609728421) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^2 * 2671^4 * 11^6
                (.node 11788010482671574506279966655961146606427336123980324712457348983160705941825534442992196025 (.cut 7 31 2279149796805133278559360222057050221593845856472155964148173) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^2 * 2671^4 * 11^4
                  (.node 10181355236228960538447446609652362386769922856823810242030414927501918347460734469723058425 (.basic (.groups [11, 71, 1451, 28729, 31747594185191, 22280841470107301759731])) .empty .empty)
                  .empty)
                (.node 9337189924373176096690747236206441586569315230475409048294950292784796859280536194755532833866979225 (.basic (.split 23)) -- 5^2 * 31^6 * 917087137^10
                  (.node 5744041233106026663291940140399624788374070411616796377086703767978513620593903604269318186025 (.basic (.split 127)) .empty .empty)
                  .empty))
              (.node 4939373469993410155149405287953207599295167756921491386548028704883157538559403647025676869115632010025 (.basic (.split 7)) -- 5^2 * 31^6 * 917087137^10 * 23^2
                (.node 1929217672260164385575921555648549691442477694631281326412724599366782118439352626514295434355971143025 (.basic (.split 7)) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^4 * 11^2
                  (.node 1494281544475564621258509646017749987106273520938773723087321177594117721543011259921247846818244842025 (.cut 7 7 6305646709978405223125319207433606232831903574747379386359701189317258843) .empty .empty)
                  .empty)
                (.node 233435338343479890654686508233474512664539801050385040495939676523380636331161667808229747557072508306025 (.basic (.split 3221)) .empty .empty)))
            (.node 13514920569751647374693891437414445624323413931462606050478719307843297031296170896966178990495330676208967604540878194377035903025 (.basic (.split 13)) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^6 * 29^2
              (.node 2421854519094807252239758427767488946447086774069377783923935289521506884414625648805202122374765699146188717025 (.cut 7 31 4270989296036460871962949648915791995685265728402677684306273346302229909974679163) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^4 * 11^4 * 3221^2
                (.node 226970529923736079798621595100496222648516058295675616771130636390902549452271397156780343556545649005748225 (.cut 13 13 1073248483682885109500429224534815637280644552223662574353393022683972745618762983) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^4 * 11^2 * 7^6
                  (.node 28245675939561066769217067496250416032409315927096589900008700859329056996070561804795799454405773505029025 (.cut 7 31 801975228711204000306128740111351745547873815610454556782731813883384843922813617) .empty .empty)
                  .empty)
                (.node 16070060130501364298090239521301362216793595637886570809130462910634122510459180614704136730672212456847761717646704155026202025 (.basic (.split 29)) .empty .empty))
              (.node 385999646392676800668632233343993981476301025296503491407722702151312406510849936988251038147537139443204323753292022109602522426297025 (.cut 7 7 1630826128394350889776146197053015495575934527193597303044190100757798170627506559111577402238803621481341601) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^6 * 29^2 * 13^4
                (.node 11366048199161135442117562698865548770055991116360051688452602937896212803320079724348556531006573098691741755418878561471087194444025 (.cut 7 13 576275889027178927997053569617771822898704493667980012980551844989147969008731727895293267259939327802777003) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^6 * 29^4
                  (.node 175693967406771415871020588686387793116204381109013878656223351001962861406850221660560326876439298790716578859031416526901466739325 (.cut 7 101 786680730535463445728025557092056039045875239294428588953453588248504819537379788838158229041022042183) .empty .empty)
                  .empty)
                (.node 16197170072437293024114309119571520526273967186378825397560113935409318202691367307467115283559989207240519461729697172114221453057044861453590952307824025 (.basic (.groups [19, 37, 181, 199, 397])) .empty .empty))))))))

private theorem seed3Check : replayPlan (prepareChoices splitPrimes (fun n => seed3Tree.lookup n) 3 1 27 5) 27 5 28 root = true := by
  decide +kernel

theorem exclude_3_budget_27 {N : ℕ} (H : Conditions N 27 5) (hseed : 3 ∣ N) : False :=
  exclude_of_choice_certificate H hseed (Nat.coprime_one_left N) splitPrimes prime_proofs (fun n => seed3Tree.lookup n) seed3Check

private theorem seed5Check : replayPlan (prepareChoices splitPrimes (fun n => seed5Tree.lookup n) 5 3 27 8) 27 8 28 root = true := by
  decide +kernel

theorem exclude_5_budget_27 {N : ℕ} (H : Conditions N 27 8) (h3 : ¬ 3 ∣ N) (hseed : 5 ∣ N) : False :=
  exclude_of_choice_certificate H hseed (Nat.prime_three.coprime_iff_not_dvd.mpr h3) splitPrimes prime_proofs (fun n => seed5Tree.lookup n) seed5Check

end OddPerfect.FactorBudget
