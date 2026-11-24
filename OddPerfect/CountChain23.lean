module

public import OddPerfect.CountChain
import Mathlib.Tactic.Primality

/-! Replay data for the exact-exponent factor-count certificates. -/

public section

namespace OddPerfect.FactorBudget

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def splitPrimes : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 43, 53, 61, 67, 71, 73, 79, 89, 97, 103, 113, 127, 131, 151, 157, 163, 191, 199, 211, 307, 331, 379, 419, 431, 433, 541, 547, 599, 613, 617, 631, 701, 757, 769, 787, 811, 859, 911, 967, 1093, 1123, 1361, 1451, 1499, 1621, 1871, 2557, 2633, 2671, 2801, 3217, 3221, 3313, 3851, 4027, 4051, 4733, 4751, 5113, 5419, 8011, 12011, 14009, 14713, 15797, 17293, 17351, 18457, 19531, 21491, 24517, 28387, 30941, 33151, 37861, 39103, 42407, 45319, 56773, 70841, 86353, 104281, 151841, 187123, 398581, 732541, 797161, 1609669, 1806113, 1866871, 2180921, 5229043, 5471551, 6619231, 10378063, 12207031, 22406023, 127159831, 262209281, 366340651, 381510691, 917087137, 12346432697, 16148168401, 52379047267, 297134095231, 31747594185191, 751670559138758105956097, 1247451159302262598804596798564656994853573]

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
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 11, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 47] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 61] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 3, 71] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 43] }]),
    by primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 89] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1201] }, .lucas { root := 11, primeFactors := [2, 3, 5] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 103] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 613] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 359] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 131] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 347] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 769] }]),
    by primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 307] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 227] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 13, 17] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 631] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 13, 233] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 11, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 5, 11, 79] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 2399] }, .lucas { root := 11, primeFactors := [2, 11, 109] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 29, 421] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 13, 73] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 61, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 733] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20743] }, .lucas { root := 5, primeFactors := [2, 3, 3457] }, .lucas { root := 7, primeFactors := [2, 3] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 7789] }, .lucas { root := 2, primeFactors := [2, 3, 11, 59] }]),
    by primality (cert := .witnesses [.lucas { root := 26, primeFactors := [2, 3, 7, 13, 61, 157] }]),
    by primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7, 193] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 73547] }, .lucas { root := 2, primeFactors := [2, 11, 3343] }, .lucas { root := 5, primeFactors := [2, 3, 557] }]),
    by primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 71, 521] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 263, 4733] }, .lucas { root := 5, primeFactors := [2, 7, 13] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 17, 31, 383] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 127, 1613] }, .lucas { root := 3, primeFactors := [2, 13, 31] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 17, 43, 257] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 19, 71, 857] }]),
    by primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 19, 31, 331] }]),
    by primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 13, 61, 1123, 1733] }, .lucas { root := 2, primeFactors := [2, 3, 11, 17] }, .lucas { root := 2, primeFactors := [2, 433] }]),
    by primality (cert := .witnesses [.lucas { root := 22, primeFactors := [2, 3, 5, 7, 13, 19, 43, 181] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 31, 61, 97, 523] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 7, 17, 557, 16603] }, .lucas { root := 2, primeFactors := [2, 3, 2767] }, .lucas { root := 3, primeFactors := [2, 3, 461] }]),
    by primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 5, 13, 244212262963] }, .lucas { root := 3, primeFactors := [2, 3, 19, 3001, 713833] }, .lucas { root := 14, primeFactors := [2, 3, 5] }, .lucas { root := 5, primeFactors := [2, 3, 7, 607] }]),
    by primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 31, 37, 409, 1129, 25085030513] }, .lucas { root := 11, primeFactors := [2, 3, 47] }, .lucas { root := 3, primeFactors := [2, 1229, 1275683] }, .lucas { root := 2, primeFactors := [2, 307] }, .lucas { root := 2, primeFactors := [2, 637841] }, .lucas { root := 21, primeFactors := [2, 5, 7, 17, 67] }]),
    by primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 73, 179, 857, 3221, 3643, 6053, 10378063, 107637315400441] }, .lucas { root := 10, primeFactors := [2, 5, 7, 23] }, .lucas { root := 2, primeFactors := [2, 3, 607] }, .lucas { root := 2, primeFactors := [2, 17, 89] }, .lucas { root := 11, primeFactors := [2, 3, 179, 3221] }, .lucas { root := 19, primeFactors := [2, 3, 5, 7, 23, 179, 3221] }]), by simp⟩

private def seed3Tree : HintTree :=
  (.node 2259052652260785207216681837 (.split 23) -- 3^2 * 13 * 7^2 * 19^2 * 127^10
    (.node 76045932094365697581 (.split 23) -- 3^2 * 13^2 * 61 * 31^10
      (.node 490585775987241 (.split 45319) -- 3^4 * 11^6 * 43^4
        (.node 238408833573 (.split 163) -- 3^6 * 1093 * 547^2
          (.node 143496441 (.split 43) -- 3^4 * 11^6
            (.node 796797 (.split 547) -- 3^6 * 1093
              (.node 9801 (.split 7) -- 3^4 * 11^2
                (.node 729 (.split 1093) -- 3^6
                  (.node 81 (.split 11) -- 3^4
                    (.node 9 (.split 13) -- 3^2
                      (.node 1 (.split 3) .empty .empty)
                      .empty)
                    (.node 117 (.split 7) .empty .empty))
                  (.node 5733 (.split 19) -- 3^2 * 13 * 7^2
                    (.node 1521 (.split 61) .empty .empty)
                    (.node 6561 (.split 13) .empty .empty)))
                (.node 257049 (.split 30941) -- 3^2 * 13^4
                  (.node 85293 (.split 7) -- 3^8 * 13
                    (.node 59049 (.split 23) .empty .empty)
                    (.node 92781 (.split 31) .empty .empty))
                  (.node 480249 (.split 19) -- 3^4 * 11^2 * 7^2
                    (.node 280917 (.split 2801) .empty .empty)
                    (.node 531441 (.split 797161) .empty .empty))))
              (.node 5929605 (.split 3221) -- 3^4 * 11^4 * 5
                (.node 3341637 (.split 7) -- 3^2 * 13^5
                  (.node 1185921 (.split 5) -- 3^4 * 11^4
                    (.node 1108809 (.split 61) .empty .empty)
                    (.node 2069613 (.split 127) .empty .empty))
                  (.node 4782969 (.split 11) -- 3^14
                    (.node 4179357 (.split 19) .empty .empty)
                    (.node 5659641 (.split 97) .empty .empty)))
                (.node 43046721 (.split 1871) -- 3^16
                  (.node 23532201 (.split 19) -- 3^4 * 11^2 * 7^4
                    (.node 13764933 (.split 29) .empty .empty)
                    (.node 31236921 (.split 7) .empty .empty))
                  (.node 67637349 (.split 31) -- 3^8 * 13^2 * 61
                    (.node 43441281 (.split 5229043) .empty .empty)
                    (.node 89162541 (.split 331) .empty .empty)))))
            (.node 10034636157 (.split 29) -- 3^8 * 13 * 7^6
              (.node 870899121 (.split 398581) -- 3^6 * 1093^2
                (.node 548985177 (.split 7) -- 3^2 * 13^2 * 61^2 * 97
                  (.node 187388721 (.split 757) -- 3^8 * 13^4
                    (.node 163740213 (.split 19) .empty .empty)
                    (.node 204788493 (.split 757) .empty .empty))
                  (.node 674481717 (.split 19) -- 3^2 * 13 * 7^8
                    (.node 578739249 (.split 7) .empty .empty)
                    (.node 747130293 (.split 151) .empty .empty)))
                (.node 2436053373 (.split 7) -- 3^8 * 13^5
                  (.node 1508747877 (.split 127) -- 3^8 * 13 * 7^2 * 19^2
                    (.node 1153077849 (.split 19) .empty .empty)
                    (.node 1530609129 (.split 19) .empty .empty))
                  (.node 7341576489 (.split 61) -- 3^2 * 13^8
                    (.node 4125878289 (.split 97) .empty .empty)
                    (.node 8023270437 (.split 61) .empty .empty))))
              (.node 64999492389 (.split 331) -- 3^8 * 13^2 * 61 * 31^2
                (.node 28358223201 (.split 13) -- 3^14 * 11^2 * 7^2
                  (.node 17363069361 (.split 7) -- 3^4 * 11^8
                    (.node 16524331209 (.split 3851) .empty .empty)
                    (.node 21059524161 (.split 5) .empty .empty))
                  (.node 33049604133 (.split 1123) -- 3^2 * 13 * 7^10
                    (.node 31668693849 (.split 757) .empty .empty)
                    (.node 56500814601 (.split 19) .empty .empty)))
                (.node 95440494357 (.split 7) -- 3^2 * 13^9
                  (.node 74999847321 (.split 79) -- 3^10 * 23^2 * 7^4
                    (.node 70027449129 (.groups [5, 13, 3221, 4561]) .empty .empty)
                    (.node 85685201901 (.split 5) .empty .empty))
                  (.node 119366615277 (.split 19) -- 3^8 * 13^5 * 7^2
                    (.node 105297620805 (.split 131) .empty .empty)
                    (.node 141853261797 (.split 379) .empty .empty))))))
          (.node 24093161412957 (.groups [757, 1123, 293459]) -- 3^8 * 13 * 7^10
            (.node 1619430602517 (.split 16148168401) -- 3^2 * 13 * 7^12
              (.node 526488104025 (.split 31) -- 3^2 * 13^2 * 61^4 * 5^2
                (.node 400210194033 (.split 7) -- 3^8 * 13^2 * 61^2 * 97
                  (.node 269714035773 (.split 701) -- 3^2 * 13 * 7^2 * 19^6
                    (.node 265324919409 (.split 631) .empty .empty)
                    (.node 393140251413 (.split 29) .empty .empty))
                  (.node 447836165829 (.split 31) -- 3^2 * 13^8 * 61
                    (.node 423644039001 (.split 398581) .empty .empty)
                    (.node 491697171693 (.groups [19, 37, 757, 1063]) .empty .empty)))
                (.node 1240726426641 (.split 23) -- 3^2 * 13^10
                  (.node 552549895569 (.split 79) -- 3^10 * 23^2 * 7^2 * 19^2
                    (.node 544657983597 (.split 151) .empty .empty)
                    (.node 850790398689 (.split 19) .empty .empty))
                  (.node 1318113409977 (.split 2801) -- 3^2 * 13^2 * 61^2 * 97 * 7^4
                    (.node 1284630973821 (.split 7) .empty .empty)
                    (.node 1389552936849 (.groups [13, 19, 2801]) .empty .empty))))
              (.node 8741371209561 (.split 29) -- 3^10 * 23^6
                (.node 3674992518729 (.groups [29, 79, 3851, 4733]) -- 3^10 * 23^2 * 7^6
                  (.node 2203962696117 (.split 37) -- 3^2 * 13 * 7^4 * 2801^2
                    (.node 2100931392681 (.split 15797) .empty .empty)
                    (.node 2768539915449 (.split 19) .empty .empty))
                  (.node 5352009260481 (.split 61) -- 3^8 * 13^8
                    (.node 4676584223493 (.split 11) .empty .empty)
                    (.node 5848964148573 (.groups [61, 157, 757, 2801]) .empty .empty)))
                (.node 17035317810693 (.split 911) -- 3^2 * 13 * 7^2 * 19^4 * 151^2
                  (.node 13162202600625 (.split 11) -- 3^2 * 13^2 * 61^4 * 5^4
                    (.node 9735675577173 (.split 4733) .empty .empty)
                    (.node 15352393113369 (.split 5) .empty .empty))
                  (.node 21338788298373 (.split 61) -- 3^2 * 13^5 * 7^2 * 19^4
                    (.node 19610299507617 (.split 19) .empty .empty)
                    (.node 23973201243693 (.split 379) .empty .empty)))))
            (.node 135658455857001 (.split 19) -- 3^4 * 11^2 * 7^12
              (.node 64587557088873 (.split 29) -- 3^2 * 13^2 * 61^2 * 97 * 7^6
                (.node 41688729535761 (.split 19) -- 3^4 * 11^8 * 7^4
                  (.node 29854589296077 (.split 97) -- 3^2 * 13^5 * 7^4 * 61^2
                    (.node 24334594508133 (.split 757) .empty .empty)
                    (.node 38820388821201 (.split 757) .empty .empty))
                  (.node 61518709067805 (.split 10378063) -- 3^4 * 11^4 * 5 * 3221^2
                    (.node 43091348114997 (.groups [61, 127, 157, 757]) .empty .empty)
                    (.node 62464512185829 (.split 5) .empty .empty)))
                (.node 79352099523333 (.groups [19, 31, 2801, 159871]) -- 3^2 * 13 * 7^14
                  (.node 76761965566845 (.split 131) -- 3^8 * 13^2 * 61^4 * 5
                    (.node 69576120386253 (.groups [7, 11, 757, 2411]) .empty .empty)
                    (.node 78362489403081 (.split 52379047267) .empty .empty))
                  (.node 87899131841157 (.split 37) -- 3^2 * 13 * 7^8 * 19^4
                    (.node 82343479026861 (.split 917087137) .empty .empty)
                    (.node 107382919180329 (.split 14713) .empty .empty))))
              (.node 253499765077269 (.split 5) -- 3^10 * 23^6 * 29
                (.node 199470512300409 (.groups [79, 151, 911, 3851]) -- 3^10 * 23^2 * 7^2 * 19^4
                  (.node 180074633417721 (.groups [19, 37, 79]) -- 3^10 * 23^2 * 7^8
                    (.node 150691116448161 (.groups [7, 157, 3187, 34511]) .empty .empty)
                    (.node 196621532078517 (.split 701) .empty .empty))
                  (.node 229152626951157 (.split 11) -- 3^2 * 13^9 * 7^4
                    (.node 209682766102329 (.split 53) .empty .empty)
                    (.node 246084698545569 (.split 157) .empty .empty)))
                (.node 329055065015625 (.split 131) -- 3^2 * 13^2 * 61^4 * 5^6
                  (.node 286599243280077 (.groups [29, 61, 157]) -- 3^8 * 13^5 * 7^6
                    (.node 254212698514401 (.split 1093) .empty .empty)
                    (.node 326472564889341 (.split 31) .empty .empty))
                  (.node 347123842547301 (.split 17) -- 3^6 * 1093^2 * 398581
                    (.node 330630951438333 (.split 61) .empty .empty)
                    (.node 468074047130361 (.split 43) .empty .empty)))))))
        (.node 347206123957644081 (.split 419) -- 3^2 * 13^10 * 23^4
          (.node 32160869704961361 (.groups [19, 79, 419, 859, 18041]) -- 3^2 * 13^10 * 23^2 * 7^2
            (.node 6647264336993049 (.groups [19, 31, 2801]) -- 3^4 * 11^2 * 7^14
              (.node 1807012470634605 (.split 17293) -- 3^2 * 13^2 * 61^4 * 5 * 131^2
                (.node 936495979915509 (.groups [7, 31, 97, 523, 757]) -- 3^8 * 13^2 * 61^5
                  (.node 656344279693089 (.split 7) -- 3^2 * 13^10 * 23^2
                    (.node 538398730893933 (.split 262209281) -- 3^2 * 13 * 7^2 * 19^2 * 127^4
                      (.node 501043948448121 (.split 11) .empty .empty)
                      .empty)
                    (.node 904489565021289 (.groups [23, 419, 757, 859]) .empty .empty))
                  (.node 960904675873233 (.split 757) -- 3^8 * 13^2 * 61^2 * 97 * 7^4
                    (.node 943929743642613 (.groups [61, 157, 1123, 293459]) .empty .empty)
                    (.node 1040418764003529 (.split 11) .empty .empty)))
                (.node 3084398968144221 (.split 31) -- 3^2 * 13^2 * 61^5 * 7^4
                  (.node 2725875959330277 (.split 7) -- 3^2 * 13^13
                    (.node 2042747747252289 (.groups [19, 29, 4733, 1772893]) .empty .empty)
                    (.node 3017224930984173 (.split 43) .empty .empty))
                  (.node 4624185369857769 (.groups [7, 19, 79, 3851]) -- 3^10 * 23^8
                    (.node 3888252876643317 (.split 14009) .empty .empty)
                    (.node 6334284299201037 (.split 7) .empty .empty))))
              (.node 12418746683995197 (.split 757) -- 3^8 * 13 * 7^2 * 19^4 * 151^2
                (.node 7703302575712653 (.split 61) -- 3^2 * 13^5 * 7^2 * 19^6
                  (.node 7121409385631229 (.split 7) -- 3^8 * 13^2 * 61 * 31^2 * 331^2
                    (.node 7097307495759117 (.groups [757, 4733, 732541]) .empty .empty)
                    (.node 7351493187240801 (.groups [13, 67, 3851, 5336717]) .empty .empty))
                  (.node 8226376625390625 (.groups [19, 31, 131, 829, 21491]) -- 3^2 * 13^2 * 61^4 * 5^8
                    (.node 8187703160402493 (.split 4733) .empty .empty)
                    (.node 11228478720606693 (.groups [11, 29, 2411, 4733]) .empty .empty)))
                (.node 20375944377782877 (.split 61) -- 3^8 * 13^4 * 757 * 379^2
                  (.node 18147713341475601 (.split 14713) -- 3^8 * 13^6 * 757^2
                    (.node 15555976669513917 (.groups [61, 151, 157]) .empty .empty)
                    (.node 19914826458249801 (.split 97) .empty .empty))
                  (.node 30759736520242521 (.groups [5, 7, 19, 3221]) -- 3^4 * 11^14
                    (.node 29387034337649157 (.split 379) .empty .empty)
                    (.node 31731586594657677 (.groups [37, 701, 1063, 70841]) .empty .empty)))))
            (.node 100318790496169989 (.split 19) -- 3^6 * 1093^2 * 398581 * 17^2
              (.node 47084329117788417 (.groups [29, 757, 4733]) -- 3^8 * 13^2 * 61^2 * 97 * 7^6
                (.node 38635297671654333 (.split 79) -- 3^2 * 13^4 * 30941^2 * 157
                  (.node 35149402855973133 (.split 104281) -- 3^2 * 13 * 7^2 * 19^10
                    (.node 33188413210181757 (.split 2633) .empty .empty)
                    (.node 35436387471293601 (.split 61) .empty .empty))
                  (.node 41679814210646157 (.split 127) -- 3^2 * 13 * 7^10 * 1123^2
                    (.node 41131883126953125 (.groups [11, 71, 131, 521]) .empty .empty)
                    (.node 46252557438488037 (.groups [61, 157, 16148168401]) .empty .empty)))
                (.node 70980373080344637 (.groups [127, 523, 757]) -- 3^8 * 13 * 7^2 * 19^8
                  (.node 60028396210581669 (.split 757) -- 3^8 * 13^2 * 61 * 31^6
                    (.node 57126254774846049 (.split 757) .empty .empty)
                    (.node 60626317762222641 (.split 7) .empty .empty))
                  (.node 72008854940447649 (.groups [79, 701, 3851]) -- 3^10 * 23^2 * 7^2 * 19^6
                    (.node 71334068684543757 (.split 431) .empty .empty)
                    (.node 100094639615362161 (.groups [19, 37, 1063]) .empty .empty))))
              (.node 155074724570384073 (.split 1123) -- 3^2 * 13^2 * 61^2 * 97 * 7^10
                (.node 125890670444427009 (.split 7) -- 3^6 * 1093^4 * 11^2
                  (.node 105642035236806849 (.split 307) -- 3^4 * 11^6 * 43^2 * 631^2
                    (.node 101650300756032249 (.split 5) .empty .empty)
                    (.node 111088926770702517 (.groups [5, 131, 157, 2801, 21491]) .empty .empty))
                  (.node 133567922007183573 (.groups [19, 29, 22079, 5229043]) -- 3^2 * 13^13 * 7^2
                    (.node 132537746892887973 (.split 70841) .empty .empty)
                    (.node 151135549439066829 (.groups [29, 31, 97, 523, 4733]) .empty .empty)))
                (.node 278060630159638053 (.groups [61, 157, 4733, 732541]) -- 3^2 * 13^5 * 7^6 * 29^4
                  (.node 245059153220043009 (.split 13) -- 3^10 * 23^4 * 3851^2
                    (.node 205659415634765625 (.split 131) .empty .empty)
                    (.node 277854479476240293 (.split 547) .empty .empty))
                  (.node 313740134858656701 (.groups [331, 757, 1609669]) -- 3^8 * 13^8 * 61 * 31^2
                    (.node 310379930660850813 (.split 19) .empty .empty)
                    (.node 337712505774076161 (.split 61) .empty .empty))))))
          (.node 6182605770469513641 (.groups [3851, 732541, 5336717]) -- 3^10 * 23^6 * 29^4
            (.node 1931738166450230697 (.groups [7, 757, 1609669]) -- 3^8 * 13^8 * 61^2 * 97
              (.node 865468913144037489 (.groups [631, 2801, 3851]) -- 3^10 * 23^2 * 7^4 * 79^2 * 43^2
                (.node 392492674821677157 (.split 757) -- 3^8 * 13 * 7^2 * 19^2 * 127^4
                  (.node 365261038418680209 (.split 11) -- 3^8 * 13^2 * 61^2 * 97^4
                    (.node 348949059895930221 (.split 19) .empty .empty)
                    (.node 388422281401611093 (.split 5) .empty .empty))
                  (.node 550195457309727957 (.groups [11, 19, 37]) -- 3^2 * 13^9 * 7^8
                    (.node 413586103702563909 (.split 5) .empty .empty)
                    (.node 588998889981442161 (.split 7) .empty .empty)))
                (.node 1230277770302037093 (.groups [67, 97, 157, 4733]) -- 3^2 * 13^5 * 7^6 * 29^2 * 61^2
                  (.node 1070272611384284061 (.split 5) -- 3^2 * 13^2 * 61 * 31^2 * 331^4
                    (.node 907093099800408609 (.split 7) .empty .empty)
                    (.node 1137177709055857197 (.split 547) .empty .empty))
                  (.node 1575882615543106689 (.groups [79, 419, 859, 2801]) -- 3^2 * 13^10 * 23^2 * 7^4
                    (.node 1317312091092627045 (.split 757) .empty .empty)
                    (.node 1579924889900180577 (.split 7) .empty .empty))))
              (.node 4714322510948370489 (.split 43) -- 3^2 * 13^2 * 61^2 * 97^6
                (.node 2921250128140583001 (.groups [2801, 3851, 39449441]) -- 3^10 * 23^2 * 7^4 * 79^4
                  (.node 2307132126771632433 (.groups [19, 37]) -- 3^8 * 13^2 * 61^2 * 97 * 7^8
                    (.node 2161619635748909661 (.groups [31, 4651, 30941, 161971]) .empty .empty)
                    (.node 2541257518900806225 (.split 31) .empty .empty))
                  (.node 3443534599845306213 (.split 61) -- 3^8 * 13^6 * 757 * 379^2
                    (.node 3185768991860559117 (.split 7) .empty .empty)
                    (.node 4130580930517332837 (.split 11) .empty .empty)))
                (.node 5968835603933417397 (.groups [757, 4733]) -- 3^8 * 13 * 7^6 * 29^6
                  (.node 5578848897389735877 (.split 67) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2
                    (.node 5141485390869140625 (.groups [131, 21491, 305175781]) .empty .empty)
                    (.node 5615707577694524037 (.groups [61, 157]) .empty .empty))
                  (.node 6065741734449730281 (.split 433) -- 3^2 * 13^4 * 30941^2 * 157^2
                    (.node 5988749482648618569 (.split 103) .empty .empty)
                    (.node 6168642851776923441 (.split 19) .empty .empty)))))
            (.node 25707426954345703125 (.groups [29, 131]) -- 3^2 * 13^2 * 61^4 * 5^13
              (.node 15208616602381689837 (.split 19) -- 3^6 * 1093 * 547^2 * 163^2 * 7^4
                (.node 8683833130588245357 (.split 43) -- 3^2 * 13 * 7^2 * 19^2 * 127^6
                  (.node 7335784449228939561 (.split 5) -- 3^2 * 13^2 * 61^2 * 97^4 * 11^4
                    (.node 6544828178351995077 (.groups [29, 2801, 22079]) .empty .empty)
                    (.node 7598661503948819577 (.split 16148168401) .empty .empty))
                  (.node 12688934431006301013 (.split 599) -- 3^2 * 13 * 7^2 * 19^12
                    (.node 10341391887428961177 (.split 37) .empty .empty)
                    (.node 14137967992768145253 (.split 1093) .empty .empty)))
                (.node 17786796207200728461 (.groups [5, 11, 31, 131, 21491, 1238411]) -- 3^2 * 13^2 * 61^9
                  (.node 17098503934900580829 (.groups [757, 2801, 5233]) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^4
                    (.node 15232771123775668089 (.split 5) .empty .empty)
                    (.node 17291411932618231317 (.split 5) .empty .empty))
                  (.node 21521863188954091089 (.groups [127, 3851, 39449441]) -- 3^10 * 23^2 * 7^2 * 19^2 * 79^4
                    (.node 20600462852218645821 (.split 31) .empty .empty)
                    (.node 25623914682004413957 (.groups [757, 104281]) .empty .empty))))
              (.node 44447561890220021841 (.groups [19, 5839, 45319, 158341]) -- 3^4 * 11^6 * 43^6 * 7^2
                (.node 36215083369117366029 (.split 127) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2
                  (.node 28992130453393126821 (.split 19) -- 3^6 * 1093^2 * 398581 * 17^4
                    (.node 28860945609090665889 (.groups [19, 409, 264031, 1803647]) .empty .empty)
                    (.node 35430320726611980273 (.groups [7, 67, 139, 757]) .empty .empty))
                  (.node 43244574864558459093 (.split 379) -- 3^8 * 13^2 * 61^6 * 757
                    (.node 41414996894187268521 (.split 61) .empty .empty)
                    (.node 44196585648660305289 (.groups [7, 19, 31, 757]) .empty .empty)))
                (.node 63531437972520155625 (.groups [11, 71, 131, 21491]) -- 3^2 * 13^8 * 61^4 * 5^4
                  (.node 57687288758368983909 (.groups [331, 757, 3637]) -- 3^8 * 13^2 * 61 * 31^8
                    (.node 45681551965375184313 (.split 4733) .empty .empty)
                    (.node 61535674453368353121 (.groups [11, 191, 2521, 30941, 62081]) .empty .empty))
                  (.node 74103069251147509521 (.groups [5, 131, 757]) -- 3^8 * 13^8 * 61^4
                    (.node 67249501302930093693 (.groups [11, 191, 2521, 2801]) .empty .empty)
                    (.node 75818889029730085317 (.split 97) .empty .empty))))))))
      (.node 763077718495487255992677 (.groups [223, 125731]) -- 3^2 * 13 * 7^16 * 14009^2
        (.node 10315291611273621636573 (.split 67) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4
          (.node 1003902094969448651613 (.groups [61, 157, 104281]) -- 3^2 * 13^5 * 7^2 * 19^10
            (.node 267007306393130517513 (.split 7) -- 3^8 * 13^6 * 757^2 * 14713
              (.node 164737124830554644277 (.groups [11, 41, 151]) -- 3^2 * 13 * 7^8 * 19^4 * 37^4
                (.node 112047154968567143493 (.split 67) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^2
                  (.node 77416319605108848273 (.split 19) -- 3^8 * 13^4 * 757^2 * 14713 * 7^2
                    (.node 77218248161612227761 (.groups [29, 79, 419]) -- 3^2 * 13^10 * 23^2 * 7^6
                      (.node 76163855618878340445 (.split 31) .empty .empty)
                      .empty)
                    (.node 96620017484915332317 (.groups [757, 70841, 492103]) .empty .empty))
                  (.node 138356968286345779881 (.split 1621) -- 3^6 * 1093^2 * 398581^2
                    (.node 131858797780683489321 (.groups [97, 4651, 30941, 161971]) .empty .empty)
                    (.node 156102680601167396733 (.groups [19, 292561, 1141081]) .empty .empty)))
                (.node 212566794017202148329 (.groups [19, 97, 757, 903870199]) -- 3^8 * 13^2 * 61^8
                  (.node 183672039573593718849 (.groups [29, 419, 859, 18041]) -- 3^2 * 13^10 * 23^6
                    (.node 168295599545472352053 (.split 11) .empty .empty)
                    (.node 187378602145672377609 (.groups [757, 3169, 1609669]) .empty .empty))
                  (.node 233848989964255602573 (.groups [61, 157, 4733]) -- 3^2 * 13^5 * 7^6 * 29^6
                    (.node 218091682214494175997 (.split 732541) .empty .empty)
                    (.node 241122892768794692253 (.split 7) .empty .empty))))
              (.node 397456245658163916549 (.split 1609669) -- 3^2 * 13^8 * 61 * 31^6
                (.node 302263499737069248609 (.split 19) -- 3^6 * 1093^4 * 11^2 * 7^4
                  (.node 295453469911933116693 (.groups [5, 131, 151, 157]) -- 3^2 * 13^5 * 7^2 * 19^4 * 61^4
                    (.node 283159843141774486797 (.groups [5, 757, 911]) .empty .empty)
                    (.node 301504269599169089661 (.groups [5, 11]) .empty .empty))
                  (.node 362876454203199456429 (.groups [31, 97, 523]) -- 3^2 * 13^2 * 61^5 * 7^10
                    (.node 303694946067530640249 (.split 398581) .empty .empty)
                    (.node 378240769113195998529 (.split 1609669) .empty .empty)))
                (.node 745222213516702802013 (.groups [19, 29, 67, 613]) -- 3^6 * 1093 * 547^2 * 163^2 * 7^6
                  (.node 524277363481241215329 (.split 1806113) -- 3^4 * 11^10 * 15797^2
                    (.node 413361896513784065757 (.split 157) .empty .empty)
                    (.node 672253723403511866253 (.split 3313) .empty .empty))
                  (.node 837826692810128460621 (.groups [29, 757]) -- 3^8 * 13^2 * 61 * 31^2 * 331^2 * 7^6
                    (.node 780228733699143080469 (.groups [5, 757, 37861, 63601]) .empty .empty)
                    (.node 887629918356701686881 (.split 31) .empty .empty)))))
            (.node 3436741110481362086481 (.groups [43, 757, 967, 20241187]) -- 3^8 * 13^2 * 61^2 * 97^6
              (.node 1677215141530955518041 (.groups [19, 181, 199, 631]) -- 3^4 * 11^6 * 43^8
                (.node 1256628233985337395081 (.split 13) -- 3^12 * 797161^2 * 61^2
                  (.node 1187810198070661942569 (.split 31) -- 3^2 * 13^6 * 5229043^2
                    (.node 1084994568639244436121 (.split 199) .empty .empty)
                    (.node 1242935235998051916321 (.split 7) .empty .empty))
                  (.node 1588285949313003890625 (.groups [131, 19531, 21491]) -- 3^2 * 13^8 * 61^4 * 5^6
                    (.node 1414186334845442628561 (.groups [409, 2801, 264031]) .empty .empty)
                    (.node 1654497881957871030249 (.groups [11, 131, 5581, 264031]) .empty .empty)))
                (.node 2626466171016733211673 (.split 7) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433
                  (.node 2177930532620781070209 (.groups [2801, 5839, 45319]) -- 3^4 * 11^6 * 43^6 * 7^4
                    (.node 1843165305976855838769 (.split 31) .empty .empty)
                    (.node 2526314810545423379781 (.groups [31, 292561, 1141081]) .empty .empty))
                  (.node 2848507219459519122141 (.groups [5, 11, 97, 523]) -- 3^2 * 13^2 * 61^5 * 7^4 * 31^4
                    (.node 2643005324931992930637 (.groups [11, 31, 157, 2801]) .empty .empty)
                    (.node 2926821026369110235157 (.groups [11, 41, 30941, 45869891]) .empty .empty))))
              (.node 5654765293878228653853 (.split 43) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6
                (.node 4577863583293880023053 (.groups [5, 67, 131]) -- 3^2 * 13^5 * 7^6 * 29^2 * 61^4
                  (.node 4135292096602383124317 (.groups [37, 1063]) -- 3^2 * 13 * 7^8 * 19^10
                    (.node 3793399660650333565377 (.groups [1051, 2801, 30941]) .empty .empty)
                    (.node 4221182999294262560637 (.split 787) .empty .empty))
                  (.node 5347786863487896939969 (.groups [5, 31, 757]) -- 3^8 * 13^2 * 61^2 * 97^4 * 11^4
                    (.node 4580705329593274665693 (.groups [31, 127, 151]) .empty .empty)
                    (.node 5490310593459790031157 (.groups [67, 127, 613, 2801]) .empty .empty)))
                (.node 7649031349457202439917 (.groups [2801, 292561]) -- 3^10 * 23^4 * 3851^2 * 13 * 7^4
                  (.node 6330514352198830865253 (.groups [43, 757, 86353]) -- 3^8 * 13 * 7^2 * 19^2 * 127^6
                    (.node 5791006878992635651533 (.groups [23, 4733, 18944890940537]) .empty .empty)
                    (.node 6999134475117648380049 (.groups [30941, 292561, 1141081]) .empty .empty))
                  (.node 8856416438238134531493 (.split 911) -- 3^2 * 13 * 7^2 * 19^4 * 151^6
                    (.node 8378725701030613651269 (.split 19) .empty .empty)
                    (.node 9956656179033808711401 (.split 433) .empty .empty))))))
          (.node 73080140742685435375341 (.split 42407) -- 3^2 * 13^2 * 61 * 31^12
            (.node 27947291377444294226553 (.groups [127, 1051, 30941]) -- 3^8 * 13^4 * 757^2 * 14713 * 7^2 * 19^2
              (.node 13251087932909532844077 (.split 7) -- 3^6 * 1093 * 547^4 * 431^2
                (.node 12813392246024384418573 (.groups [97, 787, 5229043]) -- 3^8 * 13^6 * 757 * 379^2 * 61^2
                  (.node 10466159093674918782381 (.split 127) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2
                    (.node 10399528982619251677449 (.groups [11, 191, 2521, 62081]) .empty .empty)
                    (.node 11815021745670939920397 (.split 19) .empty .empty))
                  (.node 13073645096251369136469 (.split 151) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4
                    (.node 12966574435049331048069 (.groups [5, 11, 31]) .empty .empty)
                    (.node 13083358013263395358137 (.groups [19, 1051, 5229043]) .empty .empty)))
                (.node 19797044800982118633981 (.split 151) -- 3^12 * 797161^2 * 61 * 31^2
                  (.node 16336167041809386136053 (.groups [7, 97, 151, 22996651]) -- 3^12 * 797161^2 * 61^2 * 13
                    (.node 14810911487116393181841 (.groups [19, 29, 31, 4733]) .empty .empty)
                    (.node 17780946255956773365021 (.groups [31, 97]) .empty .empty))
                  (.node 21343795357033652988213 (.split 7) -- 3^6 * 1093 * 547^6
                    (.node 20363767545002154598413 (.groups [7, 19, 31, 613, 1301]) .empty .empty)
                    (.node 23245434905101356829401 (.split 19) .empty .empty))))
              (.node 46582505561199843312597 (.groups [163, 379, 3511, 14713]) -- 3^8 * 13^4 * 757^5
                (.node 38418185202880530007233 (.split 4733) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^6
                  (.node 34399212420077614838781 (.split 14713) -- 3^8 * 13^2 * 61 * 31^6 * 757^2
                    (.node 32736143172470753533401 (.split 14713) .empty .empty)
                    (.node 36515888462318437298637 (.groups [19, 37, 67]) .empty .empty))
                  (.node 40449022943652738800973 (.groups [67, 151, 613, 911]) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^4
                    (.node 40228298077919454020349 (.groups [7, 79, 397, 617]) .empty .empty)
                    (.node 42062538391922251804689 (.groups [5, 41, 1511, 45319, 46601]) .empty .empty)))
                (.node 60955854328127952504441 (.groups [859, 13537, 18041, 292561]) -- 3^2 * 13^10 * 23^4 * 419^2
                  (.node 55437484496792593536549 (.groups [23, 397]) -- 3^8 * 13^2 * 61 * 31^10
                    (.node 52563622415657977331253 (.groups [41, 19571, 293459, 1983851]) .empty .empty)
                    (.node 60903826563904543899729 (.split 19) .empty .empty))
                  (.node 65129181360912042820173 (.split 5) -- 3^2 * 13 * 7^2 * 19^6 * 701^4
                    (.node 63534643261419194398521 (.groups [443, 3571, 15798461357509]) .empty .empty)
                    (.node 67302978560200879692561 (.split 1621) .empty .empty)))))
            (.node 225525123893029308015213 (.groups [71, 151]) -- 3^2 * 13 * 7^8 * 19^4 * 37^6
              (.node 149514468012451401696369 (.split 11) -- 3^2 * 13^4 * 30941^2 * 157^4
                (.node 106658702638207855126173 (.groups [5, 131, 157]) -- 3^2 * 13^5 * 7^2 * 19^6 * 61^4
                  (.node 90988748176529428940637 (.groups [7, 61]) -- 3^10 * 23^4 * 3851^2 * 13^5
                    (.node 83136560949606381828237 (.groups [163, 613, 3158528101]) .empty .empty)
                    (.node 97162508934431077271121 (.groups [7, 19, 79]) .empty .empty))
                  (.node 117260137575873546007221 (.split 2180921) -- 3^2 * 13^2 * 61 * 31^2 * 331^6
                    (.node 107403220121160904112601 (.groups [7, 19, 31, 262321]) .empty .empty)
                    (.node 128696842379819927371977 (.split 19) .empty .empty)))
                (.node 196667000559938961763893 (.groups [61, 67]) -- 3^2 * 13^5 * 7^6 * 29^8
                  (.node 183415104742389602013477 (.split 22406023) -- 3^2 * 13 * 7^6 * 29^6 * 4733^2
                    (.node 154105203443270826166641 (.groups [97, 292561, 1141081]) .empty .empty)
                    (.node 185876583371866344703473 (.groups [29, 1051]) .empty .empty))
                  (.node 223023002023199556491049 (.groups [7, 19, 31, 1772893]) -- 3^6 * 1093^4 * 11^8
                    (.node 212370171543522019768689 (.split 97) .empty .empty)
                    (.node 224276645592166509187101 (.split 811) .empty .empty))))
              (.node 532165029847905992366205 (.split 127) -- 3^2 * 13^2 * 61^4 * 5 * 131^6
                (.node 340253805148893976057173 (.split 163) -- 3^6 * 1093^5 * 547^2
                  (.node 235588074095847754723689 (.split 5) -- 3^2 * 13^4 * 30941^4
                    (.node 230084947189681754754573 (.split 19) .empty .empty)
                    (.node 282122086079625647464557 (.groups [5, 131, 787]) .empty .empty))
                  (.node 490646586541923263763441 (.groups [5, 131, 4651]) -- 3^2 * 13^14 * 61^4
                    (.node 362408656283970963232293 (.groups [61, 157]) .empty .empty)
                    (.node 494632753456379629741533 (.groups [11, 41, 5229043]) .empty .empty)))
                (.node 649303308712567109359773 (.split 19) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2
                  (.node 584113079660493996681741 (.split 307) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2
                    (.node 578936065537876056099453 (.split 43) .empty .empty)
                    (.node 641084542649906372548713 (.groups [1051, 2801]) .empty .empty))
                  (.node 725734662868703265910209 (.groups [19, 31, 37]) -- 3^6 * 1093^4 * 11^2 * 7^8
                    (.node 713379926880730372747653 (.groups [787, 3169, 30941]) .empty .empty)
                    (.node 754884376488538835510205 (.groups [14713, 17293, 21491]) .empty .empty)))))))
        (.node 42078614525859082784213133 (.split 19) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37
          (.node 6306145276611176441226873 (.split 31) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4
            (.node 3024719978072051528108109 (.split 127) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^2
              (.node 1653634623983172154315173 (.groups [3044803, 99995282631947]) -- 3^2 * 13 * 7^2 * 19^16
                (.node 1137259852050245480654409 (.split 37) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2
                  (.node 1045845972494648996422437 (.split 19) -- 3^6 * 1093 * 547^6 * 7^2
                    (.node 1007570836501906951741401 (.split 127) -- 3^4 * 11^6 * 43^4 * 45319^2
                      (.node 790961040538009193932209 (.groups [199, 757, 859]) .empty .empty)
                      .empty)
                    (.node 1099382361542303127214653 (.groups [151, 157, 911]) .empty .empty))
                  (.node 1177940370479238773618445 (.split 11) -- 3^2 * 13^4 * 30941^4 * 5
                    (.node 1141485600345906126808809 (.split 331) .empty .empty)
                    (.node 1504847973770047674350973 (.split 433) .empty .empty)))
                (.node 2421451727597847345216741 (.groups [19, 307, 617, 1270657]) -- 3^6 * 1093^2 * 398581 * 17^8
                  (.node 1789278534653603427633213 (.groups [19, 67]) -- 3^6 * 1093 * 547^2 * 163^2 * 7^10
                    (.node 1771281859043758461057009 (.groups [43, 331, 45319, 4189129561]) .empty .empty)
                    (.node 1982002124238984201247677 (.groups [67, 151, 613]) .empty .empty))
                  (.node 2737415437900597876377501 (.groups [97, 523, 2801]) -- 3^2 * 13^2 * 61^5 * 7^4 * 31^6
                    (.node 2464015872945260706407973 (.groups [5, 31, 613, 1301]) .empty .empty)
                    (.node 2984287501631322651086721 (.split 29) .empty .empty))))
              (.node 4471445784323654921696157 (.split 613) -- 3^6 * 1093 * 547^2 * 163^6
                (.node 3928478498962129304168769 (.split 19) -- 3^8 * 13^6 * 757^2 * 14713^2
                  (.node 3634276499143035052114809 (.groups [5, 292561, 2289401, 19218301]) -- 3^10 * 23^4 * 3851^4
                    (.node 3101170796690736752857809 (.groups [45319, 6038099, 3664405207]) .empty .empty)
                    (.node 3778283432816645680439541 (.groups [151, 617, 911, 88741]) .empty .empty))
                  (.node 4302634869034782139307097 (.groups [7, 11, 31, 3931, 22291]) -- 3^2 * 13^2 * 61^2 * 97^9
                    (.node 4037264789906628546806241 (.split 187123) .empty .empty)
                    (.node 4311232125521639172036633 (.groups [7, 31, 733, 45319]) .empty .empty)))
                (.node 4719585879746744258265309 (.groups [307, 617, 701, 70841]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^6
                  (.node 4647484550419659723969441 (.groups [29, 264031, 1803647]) -- 3^2 * 13^12 * 53^6
                    (.node 4552802362779491809765413 (.groups [29251, 51343, 133338869]) .empty .empty)
                    (.node 4675913658659440447096401 (.groups [5, 131, 151, 21491]) .empty .empty))
                  (.node 5889701852396193868092225 (.split 11) -- 3^2 * 13^4 * 30941^4 * 5^2
                    (.node 4870236785232806582939253 (.groups [521, 4733]) .empty .empty)
                    (.node 6211693978120041622577613 (.split 787) .empty .empty)))))
            (.node 19024960053743816007255741 (.groups [5, 11, 151]) -- 3^12 * 797161^2 * 61 * 31^4
              (.node 10842780304775242890794637 (.groups [3313, 293459, 262209281]) -- 3^2 * 13 * 7^10 * 1123^2 * 127^4
                (.node 8391602000741589815413761 (.split 127) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2
                  (.node 7741373687319295027124757 (.groups [43, 67, 73, 127]) -- 3^2 * 13 * 7^4 * 2801^2 * 37^8
                    (.node 6456327583475600073458397 (.groups [757, 911]) .empty .empty)
                    (.node 7872443439842773519828893 (.groups [163, 379, 3511]) .empty .empty))
                  (.node 10188957387168263436844293 (.groups [2801, 8269, 52379047267]) -- 3^2 * 13^5 * 7^4 * 61^6 * 157^2
                    (.node 10088972187257390215785633 (.groups [151, 911]) .empty .empty)
                    (.node 10455661028380844780974197 (.groups [71, 631, 4933, 37140797]) .empty .empty)))
                (.node 14602097282658638707151253 (.groups [67, 613, 701]) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^6
                  (.node 12748039454597722409657601 (.groups [11, 191, 2521, 3169]) -- 3^8 * 13^2 * 61^2 * 97^2 * 757^4
                    (.node 11733396534526131876515013 (.groups [5, 11, 701, 1093, 17884211]) .empty .empty)
                    (.node 12995789634660469397624721 (.groups [31, 15797, 262321]) .empty .empty))
                  (.node 17034230393436527565780213 (.groups [67, 157]) -- 3^2 * 13^5 * 7^6 * 29^2 * 61^6
                    (.node 16117330514752799976163689 (.split 967) .empty .empty)
                    (.node 18091250629506619605260649 (.groups [7, 19, 31, 433, 14083, 1793161]) .empty .empty))))
              (.node 26985783244807146335416929 (.groups [31, 15797, 1806113]) -- 3^6 * 1093^4 * 11^10
                (.node 21280769683219391176764621 (.groups [397, 617, 292561]) -- 3^2 * 13^2 * 61 * 31^10 * 23^4
                  (.node 19381433361135749308447497 (.groups [11, 41, 43, 4271]) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^2 * 37^4
                    (.node 19072974189244926406023477 (.groups [67, 4933, 5839, 158341]) .empty .empty)
                    (.node 20599906639721635917562833 (.groups [7, 151, 22996651]) .empty .empty))
                  (.node 23473771477954870066329933 (.groups [7, 79, 433, 3499, 8269, 14083]) -- 3^2 * 13^4 * 30941^2 * 157^5
                    (.node 21986281389569540347802169 (.split 29) .empty .empty)
                    (.node 24868037102285121484363533 (.groups [43, 157, 967]) .empty .empty)))
                (.node 32336297108519135871699729 (.groups [757, 1153, 3169]) -- 3^8 * 13^2 * 61^2 * 97^8
                  (.node 29688297390688223814756957 (.split 86353) -- 3^2 * 13 * 7^2 * 19^2 * 127^6 * 43^4
                    (.node 28367867211355926748873197 (.groups [29, 43, 433, 4733]) .empty .empty)
                    (.node 31815862126915788358628877 (.groups [67, 397, 2801, 208097431]) .empty .empty))
                  (.node 35890558990855221340908441 (.groups [97, 151, 30941]) -- 3^12 * 797161^2 * 61^2 * 13^4
                    (.node 35262956709828281387635929 (.groups [7, 30941, 878837, 30629717273]) .empty .empty)
                    (.node 38537259472142787260679957 (.groups [2801, 878837, 30629717273]) .empty .empty))))))
          (.node 396877032516771428924489733 (.groups [157, 701]) -- 3^2 * 13^5 * 7^2 * 19^6 * 61^6
            (.node 146230087579934809903249329 (.groups [29, 4733, 14939, 562731116179]) -- 3^6 * 1093^6 * 7^6
              (.node 83060665935475113466400853 (.groups [127, 365017, 1806113]) -- 3^4 * 11^10 * 15797 * 2633^2 * 19^2
                (.node 47678632547456734421510133 (.groups [5, 131]) -- 3^8 * 13^6 * 757 * 379^2 * 61^4
                  (.node 46305344043007287526576197 (.split 31) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^2
                    (.node 42966869912682718914827721 (.split 859) .empty .empty)
                    (.node 47479173212104879215906117 (.groups [5, 101]) .empty .empty))
                  (.node 70230015253720703395702701 (.groups [5, 11, 331]) -- 3^2 * 13^2 * 61 * 31^14
                    (.node 51246452652237800824699413 (.split 29) .empty .empty)
                    (.node 81134434533404545239232377 (.split 5) .empty .empty)))
                (.node 102104865986614943025665637 (.groups [37, 757]) -- 3^8 * 13 * 7^2 * 19^2 * 127^8
                  (.node 85853468014082340942110949 (.groups [5, 11, 31]) -- 3^2 * 13^8 * 61^9
                    (.node 85482640292811815039264109 (.groups [757, 2180921, 604842197]) .empty .empty)
                    (.node 86544337547308356881514909 (.groups [5, 2801, 14939, 562731116179]) .empty .empty))
                  (.node 121047035298542430121086669 (.groups [17, 19, 617]) -- 3^4 * 11^12 * 1093^2 * 398581
                    (.node 112420059172017151815468117 (.groups [631, 761, 4933, 26881]) .empty .empty)
                    (.node 135661518749961528238886517 (.split 71) .empty .empty))))
              (.node 309001118553947645620116777 (.groups [29, 31, 4733, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^6
                (.node 246273152184304341355180701 (.split 31) -- 3^2 * 13^2 * 61^13
                  (.node 168808680021882765041023149 (.split 617) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2
                    (.node 147242546309904846702305625 (.split 11) .empty .empty)
                    (.node 234398494445236726478878053 (.groups [67, 127, 397, 208097431]) .empty .empty))
                  (.node 298092181839627467680629669 (.groups [7, 307, 617, 911]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^4 * 151^2
                    (.node 285230733178225867272880461 (.groups [7, 13, 31]) .empty .empty)
                    (.node 298145920626376545475364733 (.groups [31, 43, 613]) .empty .empty)))
                (.node 367059189446473198375249029 (.groups [23, 397]) -- 3^2 * 13^8 * 61 * 31^10
                  (.node 362808863624629411842827601 (.groups [31, 3158528101, 4189129561]) -- 3^4 * 11^12 * 1093^4
                    (.node 315546832273083829954514433 (.groups [11, 191]) .empty .empty)
                    (.node 363552442504901911392290721 (.split 7) .empty .empty))
                  (.node 382233129020330234700138813 (.groups [43, 67, 179743, 62060021]) -- 3^2 * 13 * 7^2 * 19^10 * 104281^2
                    (.node 377550396070568287708499757 (.split 29) .empty .empty)
                    (.node 387948306759123468434963445 (.groups [127, 757]) .empty .empty)))))
            (.node 1023325647544887497223779457 (.split 732541) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^2
              (.node 637602160297516670086262901 (.groups [5, 127, 14939, 562731116179]) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29
                (.node 466577266881117877431809733 (.groups [7, 97]) -- 3^12 * 797161^2 * 61^2 * 13^5
                  (.node 420411499048685363288186637 (.groups [7, 43, 30941]) -- 3^8 * 13^4 * 757 * 379^6
                    (.node 417355582296373867512788409 (.split 89) .empty .empty)
                    (.node 451392418507193286973400781 (.groups [7, 331, 1093]) .empty .empty))
                  (.node 606334947201627168472459317 (.groups [11, 41, 3169]) -- 3^8 * 13^2 * 61^2 * 97^2 * 757 * 379^4
                    (.node 481646874496562196736928913 (.groups [7, 1051, 52379047267]) .empty .empty)
                    (.node 608842440577669089756176901 (.split 5) .empty .empty)))
                (.node 736212731549524233511528125 (.groups [7, 11, 31, 69617111, 239371661]) -- 3^2 * 13^4 * 30941^4 * 5^5
                  (.node 699799549275777882767638149 (.groups [19, 617, 2141993519227]) -- 3^6 * 1093^2 * 398581 * 17^10
                    (.node 665133695524479846339451413 (.split 39103) .empty .empty)
                    (.node 715502766850273296650411397 (.groups [67, 613]) .empty .empty))
                  (.node 938404888217757437240832849 (.groups [433, 1051, 1621, 5231]) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^4
                    (.node 819744869830699498570028001 (.groups [5, 43, 17351]) .empty .empty)
                    (.node 946904161789195015141506177 (.split 17) .empty .empty))))
              (.node 1539745448917582561366057437 (.groups [43, 151, 433, 911]) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^2 * 19^4
                (.node 1096967661932415787863265449 (.split 5) -- 3^2 * 13^6 * 5229043^2 * 31^4
                  (.node 1070452785179532827727888597 (.groups [433, 631, 2801, 14083]) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4 * 43^2
                    (.node 1049776282302287034215616597 (.groups [787, 30941]) .empty .empty)
                    (.node 1091923912084010601647027349 (.groups [151, 617, 911]) .empty .empty))
                  (.node 1418180738125328678804925609 (.groups [127, 3798019, 5229043]) -- 3^8 * 13^6 * 757^2 * 14713^2 * 19^2
                    (.node 1363960319246809090638674301 (.groups [617, 701, 70841]) .empty .empty)
                    (.node 1484871336749836723780966329 (.split 56773) .empty .empty)))
                (.node 1866763510350869761491862089 (.groups [37, 733, 1693, 45319]) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^2
                  (.node 1702201866541051881075785649 (.groups [5, 43, 17351]) -- 3^6 * 1093^4 * 11^6 * 31^4
                    (.node 1558977244218873629572814973 (.groups [29, 67, 397]) .empty .empty)
                    (.node 1703770502588574677233776549 (.groups [127, 307, 523]) .empty .empty))
                  (.node 2189041326170300972236538529 (.groups [5, 31, 433, 3221, 14083]) -- 3^2 * 13^4 * 30941^2 * 157^4 * 11^4
                    (.node 1998190944052998684003594801 (.groups [151, 3169, 22996651]) .empty .empty)
                    (.node 2257875777477347705151805653 (.groups [127, 613, 761]) .empty .empty)))))))))
    (.node 541519566649680374245776882786381009 (.split 2801) -- 3^2 * 13^4 * 30941^6 * 7^4
      (.node 20177513284715072032572299144853 (.groups [11, 31, 830833, 4189129561]) -- 3^2 * 13 * 7^2 * 19^4 * 151^2 * 911^2 * 1093^4
        (.node 147511459615525348589049256821 (.split 31) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2
          (.node 16251110021939257224637056729 (.split 5419) -- 3^4 * 11^6 * 43^4 * 45319^2 * 127^2
            (.node 6386255664982682276950223517 (.split 163) -- 3^6 * 1093 * 547^8
              (.node 4078132072128162890377805997 (.groups [11, 191]) -- 3^8 * 13 * 7^2 * 19^4 * 151^2 * 757^4
                (.node 3029368322267713923364367721 (.groups [151, 911, 30941]) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^4
                  (.node 2511076179959652240410271237 (.groups [29, 4733, 132197305635599]) -- 3^6 * 1093 * 547^6 * 7^6
                    (.node 2509785788871942349563932361 (.groups [13, 67, 2801, 14939]) -- 3^6 * 1093^6 * 7^4 * 29^2
                      (.node 2461535345505207730648587597 (.groups [5, 71, 191, 510101, 208097431]) .empty .empty)
                      .empty)
                    (.node 2614469893089888107919178053 (.groups [37, 151, 3169]) .empty .empty))
                  (.node 3681063657747621167557640625 (.split 11) -- 3^2 * 13^4 * 30941^4 * 5^6
                    (.node 3136620819526356179554873713 (.groups [7, 11]) .empty .empty)
                    (.node 3685382122038914600413799481 (.split 433) .empty .empty)))
                (.node 5484838309662078939316327245 (.split 11) -- 3^2 * 13^6 * 5229043^2 * 31^4 * 5
                  (.node 5237061548859022797468767889 (.groups [199, 859, 1609669]) -- 3^2 * 13^8 * 61^10
                    (.node 4885534801783044025325660133 (.groups [11, 41, 101, 732541]) .empty .empty)
                    (.node 5271357119039768573281602333 (.groups [67, 127]) .empty .empty))
                  (.node 5959439683960979554510472001 (.groups [7, 878837, 5229043]) -- 3^8 * 13^6 * 757^6
                    (.node 5723343094588308482804966637 (.groups [157, 199]) .empty .empty)
                    (.node 6060205610823340560019024953 (.groups [331, 2801, 8269, 14083]) .empty .empty))))
              (.node 9132484077219914734996444005 (.groups [19, 17293, 21491, 395533]) -- 3^2 * 13^2 * 61^4 * 5 * 131^8
                (.node 7165274291416805685259217121 (.groups [19, 29, 37]) -- 3^6 * 1093^6 * 7^8
                  (.node 6625822830390218721626658045 (.split 769) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2
                    (.node 6621709329206060106421928205 (.groups [7, 673, 10333, 248879, 92204351]) .empty .empty)
                    (.node 6712191732020792077182667077 (.groups [11, 31]) .empty .empty))
                  (.node 7937047581634604065556583009 (.groups [29, 151, 911, 14939]) -- 3^6 * 1093^6 * 7^2 * 19^4
                    (.node 7350125986839030848511202053 (.split 1499) .empty .empty)
                    (.node 9040203349000964049863029437 (.groups [7, 19, 67, 613, 398581]) .empty .empty)))
                (.node 10701470741700471469632166401 (.groups [31, 859, 18041]) -- 3^2 * 13^10 * 23^4 * 419^4
                  (.node 9421159861844107672479800589 (.split 307) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^4
                    (.node 9391756204298867535624422493 (.groups [281, 337, 433, 1289, 2017]) .empty .empty)
                    (.node 10597940577940114892133792333 (.groups [43, 2663, 4933]) .empty .empty))
                  (.node 15022662283242564822666022761 (.groups [5, 97, 131, 21491]) -- 3^2 * 13^2 * 61^14
                    (.node 11257527162423057932508484509 (.groups [29, 397]) .empty .empty)
                    (.node 15221061014441727243904422525 (.groups [31, 160967, 52379047267]) .empty .empty)))))
            (.node 43098266680531990493572206333 (.groups [13, 67, 2801]) -- 3^6 * 1093 * 547^6 * 7^4 * 29^2
              (.node 19332517241476182000021290253 (.groups [71, 4933, 3500201]) -- 3^2 * 13 * 7^4 * 2801^2 * 37^6 * 43^4
                (.node 17814069682740193658222245329 (.split 13) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2
                  (.node 16771901195780512755043414617 (.groups [31, 151, 911, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^2 * 19^4
                    (.node 16747662348666155700806776929 (.groups [7, 45319, 6032531, 1497157061]) .empty .empty)
                    (.node 17399074723871777903645708121 (.groups [151, 22996651, 52379047267]) .empty .empty))
                  (.node 18490462648627983432501624129 (.groups [13, 67, 127, 14939]) -- 3^6 * 1093^6 * 7^2 * 19^2 * 29^2
                    (.node 18282986611647807182972767101 (.groups [151, 22996651]) .empty .empty)
                    (.node 18759414108841192841561909649 (.groups [11, 191, 2521]) .empty .empty)))
                (.node 29800944121777927155926660961 (.groups [7, 967, 5839, 158341]) -- 3^2 * 13^2 * 61^2 * 97^6 * 43^6
                  (.node 24875207265170775900444964533 (.groups [431, 208097431]) -- 3^4 * 11^12 * 1093 * 547^4
                    (.node 19712434278113057105748613269 (.groups [11, 191]) .empty .empty)
                    (.node 26533182271394840803264623393 (.groups [43, 71, 4933]) .empty .empty))
                  (.node 32004544849933538753875832373 (.split 70841) -- 3^2 * 13 * 7^2 * 19^6 * 701^6
                    (.node 29984900402706515961370707933 (.groups [151, 911]) .empty .empty)
                    (.node 36075656395791562002519132693 (.groups [7, 19]) .empty .empty))))
              (.node 84617856494730458258874977133 (.groups [67, 151, 397]) -- 3^6 * 1093 * 547^4 * 431^2 * 7^2 * 19^4
                (.node 67491044658825595963270295661 (.split 751670559138758105956097) -- 3^2 * 13^2 * 61 * 31^16
                  (.node 55052073644921898693257407509 (.groups [43, 617, 733, 5419]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^2
                    (.node 48785708526324119096855690061 (.groups [617, 5419, 25646167]) .empty .empty)
                    (.node 66289508573436329293785764637 (.groups [113, 3823, 293147]) .empty .empty))
                  (.node 71049543339227826395703541653 (.groups [7, 43]) -- 3^8 * 13^6 * 757 * 379^6
                    (.node 68111249174465580124044545997 (.groups [43, 433]) .empty .empty)
                    (.node 76389884966724807849067933677 (.groups [19, 37]) .empty .empty)))
                (.node 123042732818022959780103290613 (.groups [19, 29]) -- 3^6 * 1093 * 547^6 * 7^8
                  (.node 101807000784795417682090676157 (.split 431) -- 3^6 * 1093^5 * 547^4
                    (.node 92026591443690529188941015625 (.groups [11, 19, 31, 829]) .empty .empty)
                    (.node 118801843043695187614545195333 (.groups [7, 19, 67, 613]) .empty .empty))
                  (.node 135348148669961102132808551169 (.groups [5419, 30941, 3798019]) -- 3^8 * 13^4 * 757^2 * 14713^2 * 19^2 * 127^2
                    (.node 130830904243895306658689308761 (.split 1806113) .empty .empty)
                    (.node 136295692981475151862768412277 (.groups [29, 151, 911]) .empty .empty))))))
          (.node 1622964371067571539092596197597 (.groups [11, 31, 547, 4189129561, 1425881675401]) -- 3^6 * 1093^9
            (.node 394184532262327827194576872989 (.groups [617, 701]) -- 3^6 * 1093^2 * 398581 * 17^6 * 19^6
              (.node 236668499249116472042328653661 (.groups [331, 50689400581, 52379047267]) -- 3^2 * 13^2 * 61^13 * 31^2
                (.node 207864689409059713706800548333 (.groups [761, 4933, 26881]) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^4
                  (.node 176848065886904799716240678601 (.groups [7, 13, 9631, 32668561]) -- 3^12 * 797161 * 398581^2 * 1621^2
                    (.node 174883203535719892585626700173 (.groups [43, 3313]) .empty .empty)
                    (.node 202242069740699808119847425061 (.groups [19, 617]) .empty .empty))
                  (.node 214604700345297830583979243281 (.split 5) -- 3^12 * 797161^4
                    (.node 213223712401048474922414489001 (.split 11) .empty .empty)
                    (.node 231582905875622517556889189277 (.split 19) .empty .empty)))
                (.node 273655302757077359375895285153 (.groups [307, 17707, 249561007]) -- 3^4 * 11^10 * 15797^2 * 1806113 * 17^2
                  (.node 251147610636310525454774978157 (.groups [11, 31]) -- 3^2 * 13^5 * 7^4 * 61^6 * 157^4
                    (.node 246638030389924463732136032793 (.groups [41, 19571]) .empty .empty)
                    (.node 264874000466606417640621162009 (.groups [31, 43, 433, 14083]) .empty .empty))
                  (.node 317519883095347929962848295637 (.groups [13, 67, 127]) -- 3^6 * 1093 * 547^6 * 7^2 * 19^2 * 29^2
                    (.node 282142441754172468416389576797 (.split 37) .empty .empty)
                    (.node 380526525361043181097610563125 (.groups [11, 71]) .empty .empty))))
              (.node 741911685648028297133900381577 (.groups [31, 1123]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^10
                (.node 504653645623184994499636377213 (.groups [631, 4933, 175897]) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^2 * 67^6
                  (.node 460132957218452645944705078125 (.groups [11, 71, 521]) -- 3^2 * 13^4 * 30941^4 * 5^9
                    (.node 432585737062380691150287465045 (.groups [11, 191]) .empty .empty)
                    (.node 492389675248098081720561422661 (.groups [127, 523]) .empty .empty))
                  (.node 615061151434475458481393334189 (.groups [307, 617]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^10
                    (.node 555848107059247304653146734757 (.groups [43, 433, 701]) .empty .empty)
                    (.node 683869716018556063852226932197 (.split 211) .empty .empty)))
                (.node 1054185923117051572136598096489 (.split 4051) -- 3^2 * 13^6 * 5229043^2 * 31^6
                  (.node 872889414454269489252890021121 (.split 13) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4
                    (.node 860616869585250385165198523337 (.groups [22406023, 88009573]) .empty .empty)
                    (.node 892253934711140898708670908933 (.groups [11, 41]) .empty .empty))
                  (.node 1595107382447487614687725936797 (.groups [1717451, 1806113, 2545021]) -- 3^4 * 11^10 * 15797 * 2633^4
                    (.node 1073023501726489152919896216405 (.split 2671) .empty .empty)
                    (.node 1595770458842850021979175175273 (.groups [7, 31, 12503, 14083, 1205476469]) .empty .empty)))))
            (.node 5031994362342580897974763320969 (.split 30941) -- 3^8 * 13^4 * 757^2 * 14713^4
              (.node 2722715200072947117346662370221 (.groups [617, 88741, 262209281]) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^4
                (.node 1979267199796956198468866015853 (.groups [433, 2801, 14083]) -- 3^2 * 13^4 * 30941^2 * 157 * 79^2 * 7^4 * 43^4
                  (.node 1680230710929515486270843219733 (.split 7) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2
                    (.node 1633550040567644440835639949813 (.groups [11, 2221]) .empty .empty)
                    (.node 1701531015412148351746092579321 (.groups [71, 859, 22199431, 4242586390571]) .empty .empty))
                  (.node 2131408061578340120268747825849 (.groups [11, 41, 1693, 4271, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^4
                    (.node 2110729848441303515983267115601 (.groups [2801, 14939, 732541]) .empty .empty)
                    (.node 2300664786092263229723525390625 (.groups [11, 12207031, 69617111]) .empty .empty)))
                (.node 3847330687534232059734273586197 (.groups [37, 151]) -- 3^8 * 13^2 * 61^6 * 757 * 379^2 * 787^2
                  (.node 3010577776383092728239559460601 (.split 19) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^2
                    (.node 2865274176970092067665926466249 (.groups [29, 701, 14939]) .empty .empty)
                    (.node 3305873567369577404568796987689 (.split 8011) .empty .empty))
                  (.node 4108734768299540025298880171853 (.groups [11, 41, 101]) -- 3^2 * 13 * 7^6 * 29^6 * 4733^4
                    (.node 3926898673826581719427826140281 (.groups [53, 79, 20359, 8224356155341457]) .empty .empty)
                    (.node 4604323382699711952024091732293 (.groups [23, 911, 14864609]) .empty .empty))))
              (.node 7446479004308424448020476142189 (.groups [19, 3798019]) -- 3^8 * 13^2 * 61 * 31^6 * 757^2 * 14713^2
                (.node 6054656331676765104570672676737 (.groups [31, 701, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^2 * 19^6
                  (.node 5483727123624481527521439705693 (.groups [151, 911, 1693, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37 * 19^4
                    (.node 5365117508632445764599481082025 (.groups [31, 2671, 178601, 169299992707751]) .empty .empty)
                    (.node 5823857592001230278178282979833 (.groups [5, 11, 2801]) .empty .empty))
                  (.node 7086470464467919600590435096969 (.groups [19, 3798019, 52379047267]) -- 3^8 * 13^2 * 61^6 * 757^2 * 14713^2
                    (.node 6796799838125345890586037082869 (.groups [5, 307, 617]) .empty .empty)
                    (.node 7305251261417770229131878595449 (.groups [7, 3169, 878837]) .empty .empty)))
                (.node 11347562387905503360287570274573 (.split 2801) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13
                  (.node 10135604365095813848426455576317 (.groups [127, 613]) -- 3^6 * 1093 * 547^2 * 163^2 * 7^2 * 19^2 * 67^6
                    (.node 9365563553120755267516815046149 (.groups [7, 757]) .empty .empty)
                    (.node 10292198534382514136280511207581 (.groups [5, 331]) .empty .empty))
                  (.node 14508580651200017287331161703877 (.groups [43, 4933]) -- 3^2 * 13 * 7^4 * 2801^2 * 37^12
                    (.node 14200876480392782981062365604293 (.groups [163, 379]) .empty .empty)
                    (.node 15550479087496134066733865892489 (.groups [127, 14939, 732541]) .empty .empty)))))))
        (.node 1910825171263803381403999428298053 (.split 23) -- 3^6 * 1093 * 547^10
          (.node 141758512690519859994076335804981 (.split 73) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2
            (.node 64263607588850527940702061569661 (.groups [97, 3931, 5419]) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^2
              (.node 42771581308259204973391611034929 (.groups [13, 29, 4733, 9631]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^6
                (.node 32049754056459376534515160603089 (.groups [7, 19, 31]) -- 3^2 * 13^4 * 30941^2 * 157^4 * 11^8
                  (.node 25800069200526865465612153169121 (.groups [7, 19, 1811, 8269, 14083]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^4 * 11^2
                    (.node 21980330685612084674333971766241 (.split 5) -- 3^6 * 1093^2 * 398581^4
                      (.node 20207402079610386820903381477521 (.groups [19, 14713, 30941]) .empty .empty)
                      .empty)
                    (.node 30547046194597695431453866745013 (.groups [67, 397]) .empty .empty))
                  (.node 36245642278327404005094225526053 (.groups [2801, 732541]) -- 3^6 * 1093 * 547^6 * 7^4 * 29^4
                    (.node 35745824379489460518039365677797 (.groups [71, 4933]) .empty .empty)
                    (.node 36436260228314204607197861348973 (.split 12346432697) .empty .empty)))
                (.node 55899326355945583705140270693681 (.split 103) -- 3^2 * 13^2 * 61^16
                  (.node 49202745166312529822459396831997 (.groups [29, 701]) -- 3^6 * 1093 * 547^6 * 7^2 * 19^6
                    (.node 48247048376328340340092845616689 (.groups [1621, 32668561, 3158528101]) .empty .empty)
                    (.node 53897050971867537572908092546609 (.groups [7, 29, 1373]) .empty .empty))
                  (.node 60388328134852214268078416725317 (.groups [37, 61]) -- 3^8 * 13^4 * 757 * 379^8
                    (.node 58613950471029232289832020778813 (.groups [7, 43, 397, 433]) .empty .empty)
                    (.node 61211165604797801963514746352429 (.groups [5, 13]) .empty .empty))))
              (.node 88443722309635420702511255185401 (.groups [433, 659, 45319]) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^6
                (.node 82331304835546258827271317766917 (.groups [19, 17923, 18871143464293]) -- 3^6 * 1093 * 547^2 * 163^6 * 613^2 * 7^2
                  (.node 69254885610924782759590214672109 (.split 43) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^2
                    (.node 65206703231164743641839469191077 (.groups [67, 4933]) .empty .empty)
                    (.node 79086382496795356859633737409217 (.groups [17707, 88741]) .empty .empty))
                  (.node 84300600401298480319216801396317 (.split 28387) -- 3^6 * 1093^8 * 56773
                    (.node 83601429021099728838036997328997 (.split 127) .empty .empty)
                    (.node 87094558150988928106552528753197 (.groups [7, 43]) .empty .empty)))
                (.node 117031555208705022115036300905957 (.groups [43, 271, 15349897, 22406023]) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^2
                  (.node 92325867469653989641405473737433 (.groups [7, 31, 37, 1693, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^5
                    (.node 90840983926137205985599743407169 (.groups [19, 37, 433, 2593, 8269]) .empty .empty)
                    (.node 109901653428060423371669858831205 (.split 1866871) .empty .empty))
                  (.node 134127937715811144114987027050625 (.groups [11, 71, 2671]) -- 3^12 * 797161^4 * 5^4
                    (.node 131423937774041922766398171969309 (.groups [1471, 1222567, 2426789]) .empty .empty)
                    (.node 138439880642537788985855140257405 (.groups [21491, 189967, 211093]) .empty .empty)))))
            (.node 457257267316392893253012280606317 (.groups [29, 953, 967, 1009]) -- 3^6 * 1093 * 547^4 * 431^6
              (.node 240189162779606613840810829111653 (.groups [11, 31, 613, 1301]) -- 3^6 * 1093^5 * 547^2 * 163^4
                (.node 161600431340752825202511335548605 (.split 21491) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4
                  (.node 151953887411683612649426703699981 (.groups [7, 43, 307]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^6
                    (.node 147518311042771543683738413569449 (.groups [61, 2801, 9631, 32668561]) .empty .empty)
                    (.node 156722559249170956767273975569805 (.groups [23, 67, 353]) .empty .empty))
                  (.node 225539178113153008848720067799409 (.split 7) -- 3^2 * 13^4 * 30941^6
                    (.node 169676426762924885416290488623173 (.groups [7, 19, 67, 613]) .empty .empty)
                    (.node 227438427778400929632677836168221 (.groups [5, 11]) .empty .empty)))
                (.node 380909171361178426784499135607257 (.groups [7, 43, 71]) -- 3^2 * 13^2 * 61^2 * 97^13
                  (.node 267034221683187609098755416630717 (.groups [127, 732541]) -- 3^6 * 1093 * 547^6 * 7^2 * 19^2 * 29^4
                    (.node 262114153543858279776171087982041 (.groups [3500201, 5390701, 262209281]) .empty .empty)
                    (.node 349997623792174220712347731204521 (.groups [733, 1811, 45319]) .empty .empty))
                  (.node 422288137194432869353038685848117 (.split 433) -- 3^2 * 13 * 7^12 * 16148168401^2
                    (.node 386253002761462109262037330635093 (.groups [7, 67, 1693, 14083]) .empty .empty)
                    (.node 450963893537387887935282110882181 (.groups [5, 13]) .empty .empty))))
              (.node 933104590757269054829827661466837 (.groups [4933, 175897]) -- 3^2 * 13 * 7^4 * 2801^2 * 37^2 * 43^4 * 67^6
                (.node 690968608678954059516982850893209 (.groups [37, 1693, 12503, 14083, 1205476469]) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^2
                  (.node 549508267140302116858349294156025 (.split 31) -- 3^6 * 1093^2 * 398581^4 * 5^2
                    (.node 508787644208742671072485548841569 (.groups [19, 9631, 30941, 32668561]) .empty .empty)
                    (.node 636548400709713233533466776223577 (.groups [71, 211, 1597, 2884629032993]) .empty .empty))
                  (.node 850407047235896171757735001243761 (.groups [1774921, 5229043, 26403131021]) -- 3^8 * 13^6 * 757^2 * 14713^4
                    (.node 786864692821081716913185424993869 (.groups [617, 25646167]) .empty .empty)
                    (.node 887934895818945304023548725712661 (.groups [43, 617, 733]) .empty .empty)))
                (.node 1407545279071965799539656753458341 (.groups [11, 23, 89, 703207451121161180833]) -- 3^2 * 13^2 * 61 * 31^2 * 331^10
                  (.node 1064346147166216915912536296661717 (.groups [37, 43, 4933, 143879023, 3356457657661]) -- 3^2 * 13 * 7^4 * 2801^8
                    (.node 955285303576022963352750182419161 (.split 5) .empty .empty)
                    (.node 1086818577274296474894480965276961 (.groups [61, 127, 9631, 32668561]) .empty .empty))
                  (.node 1710215916361568376382271145860001 (.split 19) -- 3^4 * 11^10 * 15797^2 * 1806113^2
                    (.node 1619321603213190907513793391508557 (.groups [3169, 570821]) .empty .empty)
                    (.node 1773900057576855692228207643973521 (.split 23) .empty .empty))))))
          (.node 32478164413260860240122526484696081 (.split 151) -- 3^2 * 13^6 * 5229043^4
            (.node 6614239374713654723942312134940397 (.groups [19, 61, 157]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^5
              (.node 3447387238449541117879075965205077 (.groups [5, 11, 211, 1597]) -- 3^2 * 13 * 7^4 * 2801^6 * 71^4
                (.node 2095807484104701043696188940711521 (.groups [13, 19, 37]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^8
                  (.node 2066735794340814159287315010497517 (.groups [7, 19, 2633]) -- 3^4 * 11^10 * 15797^5
                    (.node 1979625491628437831435239733755173 (.groups [701, 1693, 8269]) .empty .empty)
                    (.node 2069360834048224596414148804417161 (.split 151) .empty .empty))
                  (.node 3121808373263750721339070533463641 (.groups [5, 1811, 3221, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^4 * 11^4
                    (.node 2917897636300747624647915773587281 (.groups [71, 1693, 8269, 14083]) .empty .empty)
                    (.node 3156446167827937439730851294802477 (.groups [23, 613, 579189657172292026411]) .empty .empty)))
                (.node 4776426517880114816763750912095805 (.split 11) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5
                  (.node 3918253214802390133439862128149245 (.split 31) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^2
                    (.node 3659665052424572010968933263312197 (.groups [433, 2801]) .empty .empty)
                    (.node 4034233936941766682536294570578933 (.groups [2801, 17923]) .empty .empty))
                  (.node 5596727145913182297329329943619513 (.groups [2801, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433 * 7^4 * 31^6
                    (.node 5188602888960244029940817400315741 (.groups [617, 1051, 1621]) .empty .empty)
                    (.node 6100023909123435320827265319027813 (.groups [5, 11, 701]) .empty .empty))))
              (.node 16515740442553289155635519524293053 (.groups [199, 11299, 830833]) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^2 * 1499^2
                (.node 13701951073150440784034058847259289 (.groups [5, 4051, 37861, 63601, 72577051]) -- 3^2 * 13^6 * 5229043^2 * 31^2 * 331^4
                  (.node 10692209747023413368826279385619721 (.split 5) -- 3^12 * 797161 * 398581^4
                    (.node 6668265988407265219988927108827569 (.groups [19, 307, 433]) .empty .empty)
                    (.node 11051419727544497433587283322171041 (.split 19) .empty .empty))
                  (.node 14262034476403541339739159714925533 (.groups [11, 31, 79, 433]) -- 3^2 * 13^4 * 30941^2 * 157^9
                    (.node 13737706678507552921458732353900625 (.split 11) .empty .empty)
                    (.node 15727065343802190877193337903924573 (.groups [397, 59023, 70841]) .empty .empty)))
                (.node 24930594566228390882551791893236881 (.groups [2801, 9631, 30941]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13^4
                  (.node 22923813571765165297796581288520073 (.groups [11, 41]) -- 3^2 * 13^2 * 61^2 * 97 * 7^6 * 29^4 * 4733^4
                    (.node 18911770272784381584042846093600477 (.groups [7, 67, 397, 398581]) .empty .empty)
                    (.node 23882132589400574083818754560479025 (.split 11) .empty .empty))
                  (.node 30180115876617002110531356035767917 (.groups [151, 911, 9631]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13 * 19^4
                    (.node 26185824527134422621589440939484569 (.groups [131, 691, 701]) .empty .empty)
                    (.node 30461570897817852129240669122259813 (.groups [7, 29, 398581, 1193557]) .empty .empty)))))
            (.node 151548971102011437568446567611557593 (.groups [7, 13]) -- 3^4 * 11^6 * 43^2 * 631^2 * 307^2 * 433^5
              (.node 80987680307932777031590025069933133 (.groups [5419, 257611]) -- 3^2 * 13 * 7^10 * 1123^2 * 127^2 * 3313^4
                (.node 67382329741336486877497012233690921 (.groups [29, 211, 859]) -- 3^2 * 13^2 * 61^10 * 199^6
                  (.node 43914673461976564055684317369294509 (.groups [7, 43]) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^6
                    (.node 39977100614360177514728570128308489 (.groups [743, 5209, 8269, 14083, 1706822489]) .empty .empty)
                    (.node 52898604262048041930920465364092733 (.groups [11, 1811, 14083, 1768661]) .empty .empty))
                  (.node 68699181438729529840570584040290405 (.split 24517) -- 3^4 * 11^4 * 5 * 3221^8
                    (.node 68688533392537764607293661769503125 (.groups [7, 31, 1866871, 2703853428809791]) .empty .empty)
                    (.node 74035733053146392751902692741416897 (.groups [7, 19, 43]) .empty .empty)))
                (.node 104983177448936132218101315588012693 (.groups [911, 141451988078598368963321713]) -- 3^2 * 13 * 7^2 * 19^4 * 151^12
                  (.node 85985111871277511411250057754225161 (.groups [19, 9631, 5229043]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13^6
                    (.node 83599621657709184525942747570895173 (.groups [127, 577]) .empty .empty)
                    (.node 97021384729782947799338066245564941 (.split 5) .empty .empty))
                  (.node 136229930695589585454307358708586741 (.groups [5, 11, 73, 97]) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^4
                    (.node 109442277014299684511043431755111437 (.groups [70001, 732541, 69655517]) .empty .empty)
                    (.node 141364895772889184877060906859102089 (.groups [19, 4729, 129901, 14421466756460791]) .empty .empty))))
              (.node 343442666962688823036468308847515625 (.split 19531) -- 3^6 * 1093^2 * 398581^4 * 5^6
                (.node 214992551314177613980331816778179409 (.split 6619231) -- 3^2 * 13^2 * 61^6 * 52379047267^2
                  (.node 155694937565241795564237151914101829 (.groups [191, 1774921, 26403131021]) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941
                    (.node 154973833109096011651252231526496069 (.groups [307, 617]) .empty .empty)
                    (.node 171074497531957963926155477553125241 (.groups [61, 151, 691, 398581]) .empty .empty))
                  (.node 267305243675585334220656984640493025 (.groups [31, 1866871, 2703853428809791]) -- 3^12 * 797161 * 398581^4 * 5^2
                    (.node 236295396956654483995245323514255993 (.groups [17, 17707, 17311991]) .empty .empty)
                    (.node 324097729360969081473173294612079453 (.groups [61, 157]) .empty .empty)))
                (.node 464693228695132414831182372959810241 (.groups [5, 11, 32668561]) -- 3^12 * 797161 * 398581^2 * 1621^4
                  (.node 377738813164913837282027534549100561 (.groups [43, 1811, 8269]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^4 * 11^6
                    (.node 365809664889693438720841641680571933 (.groups [433, 5479, 14083]) .empty .empty)
                    (.node 392341506396021027436907628464982921 (.groups [61, 151, 911]) .empty .empty))
                  (.node 528077444721830334300873671683940025 (.split 331) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^2
                    (.node 477222962666968596324770192235909969 (.groups [31, 313, 1009]) .empty .empty)
                    (.node 528780360780441627579729105639442317 (.groups [11, 41, 1693]) .empty .empty))))))))
      (.node 283900518291289922759670698187316438106903289 (.groups [5, 11, 72931]) -- 3^2 * 13^6 * 5229043^2 * 31^6 * 4051^4
        (.node 1440232070313326450042528349828652234161 (.groups [151, 911, 2384047, 3060947]) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^4
          (.node 14926332868375358802386721600299390625 (.groups [11, 19531, 32668561]) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^6
            (.node 2985266573675071760477344320059878125 (.groups [7, 11, 31]) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^5
              (.node 1010826515598551988762715697569670037 (.groups [7, 79, 10847]) -- 3^6 * 1093 * 547^10 * 23^2
                (.node 631378614015273104760508485835849677 (.groups [131, 20161, 53551]) -- 3^6 * 1093 * 547^2 * 163^6 * 613^4
                  (.node 597053314735014352095468864011975625 (.groups [11, 71, 32668561, 125613804731]) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5^4
                    (.node 577947608663493892828413860363592405 (.groups [7, 19, 32668561, 125613804731]) -- 3^6 * 1093^2 * 398581^2 * 1621^4 * 5 * 11^2
                      (.node 557738042398481972317674375469908261 (.split 3217) .empty .empty)
                      .empty)
                    (.node 617387945806526183873999883655460361 (.groups [127, 249561007, 171686630257]) .empty .empty))
                  (.node 938393130458156661188721843661992609 (.groups [7, 79, 6491, 2608387]) -- 3^6 * 1093^10 * 23^2
                    (.node 755431114127780333908432793504743749 (.groups [97, 331, 1801, 32668561]) .empty .empty)
                    (.node 973562837902982584951163210667617769 (.groups [23, 397, 617]) .empty .empty)))
                (.node 2239139412795355990339048075243308681 (.groups [433, 14083, 28447, 321910472390668481]) -- 3^2 * 13^4 * 30941^2 * 157^10
                  (.node 1548517477096733223594808045701459981 (.groups [7, 13, 811, 9631, 2626021]) -- 3^6 * 1093^2 * 398581^2 * 1621^5
                    (.node 1017019091405953336574486567065082517 (.groups [7561, 67411, 128341, 492103]) .empty .empty)
                    (.node 2232896834883491998552857557211685245 (.groups [7, 43]) .empty .empty))
                  (.node 2450864250063044988422603303976993549 (.groups [37, 307]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^8
                    (.node 2425534618244573694983451656139123525 (.groups [31, 6781, 12774841, 32668561]) .empty .empty)
                    (.node 2689515839275022789083188694753423605 (.groups [79, 21491]) .empty .empty))))
              (.node 7655208259980689700816393302821423605 (.groups [7, 19, 31]) -- 3^12 * 797161^4 * 5 * 2671^2
                (.node 4508132982664151280625421992229083437 (.groups [11, 31, 613]) -- 3^6 * 1093 * 547^8 * 163^4
                  (.node 3989562521643563573525009279303745801 (.split 127) -- 3^2 * 13^4 * 30941^6 * 7^2 * 19^2
                    (.node 3337938385806307753801517746601458053 (.groups [5, 61, 71, 492103]) .empty .empty)
                    (.node 4156604466918972654370117272411037293 (.groups [5, 41, 3181]) .empty .empty))
                  (.node 6381585865891368123136502918667508557 (.groups [613, 398581, 1193557]) -- 3^6 * 1093^5 * 547^2 * 163^6
                    (.node 4785997986582918623162895465673105041 (.split 211) .empty .empty)
                    (.node 6682631091889633355516424616012325625 (.groups [11, 71]) .empty .empty)))
                (.node 10895021831458737761901819528912218037 (.groups [701, 9631]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^2 * 13 * 19^6
                  (.node 8586066674067220575911707721187890625 (.groups [19, 31, 829]) -- 3^6 * 1093^2 * 398581^4 * 5^8
                    (.node 8081598228241642264774495318225376133 (.groups [127, 1093, 2683]) .empty .empty)
                    (.node 8760942185001950321580708800560104021 (.groups [17, 19, 617, 1621, 32668561, 158866414981]) .empty .empty))
                  (.node 12512038885981740375071555073299455593 (.groups [7, 19]) -- 3^8 * 13^6 * 757^2 * 14713^5
                    (.node 11058383404112490463981836037047257133 (.groups [7, 29]) .empty .empty)
                    (.node 14092855804242711875018662549977850569 (.groups [3500201, 20241187, 875296605041]) .empty .empty)))))
            (.node 129549013472608417664779597731116862201 (.groups [11, 1811, 12503, 14083]) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^4
              (.node 47183496377133569022839006889515687961 (.groups [7, 1093, 3500201]) -- 3^4 * 11^6 * 43^4 * 45319^4 * 151^2
                (.node 24464448509391918631217927116892676429 (.groups [5419, 88741]) -- 3^6 * 1093^2 * 398581 * 17^4 * 19^2 * 127^2 * 617^4
                  (.node 17378279069024136775228421940598793157 (.groups [211, 883, 1597]) -- 3^2 * 13 * 7^4 * 2801^6 * 71^6
                    (.node 17299824564090609646756428858840479889 (.split 5471551) .empty .empty)
                    (.node 23394101632278068350666335828972033081 (.groups [181, 631, 13267]) .empty .empty))
                  (.node 32648225343201841274261715220829276049 (.groups [43, 337, 1806113]) -- 3^4 * 11^10 * 15797^6
                    (.node 26534458765834338338043067256532669441 (.groups [29, 4733, 2384047, 3060947]) .empty .empty)
                    (.node 42930333370336102879558538605939453125 (.groups [11, 71]) .empty .empty)))
                (.node 83863618233020469836208988051607011413 (.groups [613, 10865297]) -- 3^6 * 1093 * 547^2 * 163^12
                  (.node 79174380554447024242131870170977608213 (.groups [37, 1693, 200741603328100897]) -- 3^2 * 13 * 7^12 * 16148168401^2 * 433^2
                    (.node 60638365456114342374586291403478088125 (.groups [11, 71, 6781]) .empty .empty)
                    (.node 83686975996039775958915443849692586589 (.groups [617, 1051]) .empty .empty))
                  (.node 89028446818113805068975521633760203373 (.groups [37, 43, 4933]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13 * 2801^2
                    (.node 84940567233960460243572814257710052237 (.groups [7, 67, 397]) .empty .empty)
                    (.node 92040954969026034673787526106048718517 (.groups [70001, 69655517]) .empty .empty))))
              (.node 507482424377678951263139598488266364025 (.groups [11, 17351, 1866871, 2703853428809791]) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^4
                (.node 160613121081791520590096299183893627813 (.groups [39103, 128341, 16975792017452101]) -- 3^2 * 13 * 7^2 * 19^6 * 701^6 * 70841^2
                  (.node 147800268971541769431290877679516544493 (.groups [11, 19]) -- 3^2 * 13^4 * 30941^2 * 157^2 * 433^2 * 37^9
                    (.node 130916963398461591621589371718951858101 (.groups [73, 97, 32668561]) .empty .empty)
                    (.node 154212068320403644963364333565649298301 (.groups [53, 37181, 10999171]) .empty .empty))
                  (.node 489020633681614039577892099162358273509 (.groups [617, 659]) -- 3^6 * 1093^2 * 398581 * 17^2 * 19^2 * 127^2 * 307^6
                    (.node 236768672181515258223269785511220921309 (.groups [4447, 38047, 3500201, 38533987]) .empty .empty)
                    (.node 496409966012364873768833855297194090161 (.groups [6491, 292561, 2608387]) .empty .empty)))
                (.node 740534626786760874335033726377555342881 (.split 7) -- 3^2 * 13^6 * 5229043^4 * 151^2
                  (.node 571736088668671345946509264941632140077 (.groups [13, 313, 82889]) -- 3^6 * 1093 * 547^12
                    (.node 534727226751634002055476604014355449573 (.groups [10847, 292561]) .empty .empty)
                    (.node 723900313908424588156649145620396531973 (.groups [71, 1693]) .empty .empty))
                  (.node 1300188479525882578564110295570100802609 (.groups [19, 37, 1063]) -- 3^2 * 13^4 * 30941^6 * 7^8
                    (.node 1089287740410942876558744318304466805561 (.groups [7673, 8387, 30941]) .empty .empty)
                    (.node 1355511459231529090909936353451462541877 (.groups [5, 1361, 1597]) .empty .empty))))))
          (.node 213077416360658120021835269027232309530361 (.groups [13, 31, 37, 398581]) -- 3^6 * 1093^8 * 56773^2 * 211^2
            (.node 9114376166765181717737971367402236387917 (.groups [163, 613, 1747]) -- 3^6 * 1093^5 * 547^8
              (.node 3513069357642699507433383133193318207997 (.groups [5, 71, 191]) -- 3^6 * 1093^5 * 547^4 * 431^4
                (.node 2119187929884133075864736033665322889129 (.groups [13, 131, 937, 58782569]) -- 3^6 * 1093^12
                  (.node 1515959136402858559364657285086952203125 (.groups [6781, 19531]) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^4 * 5^6
                    (.node 1501199461525435442739555521364574962129 (.groups [4051, 2180921, 72577051, 604842197]) .empty .empty)
                    (.node 1516796306185754728262421048684653206209 (.groups [467, 2384047, 3060947, 17177163455369]) .empty .empty))
                  (.node 2317102139358756231701130307964465672445 (.split 541) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^4
                    (.node 2283018118576576751056772685728449433853 (.groups [433, 14083]) .empty .empty)
                    (.node 2510146830373804555447183842082066629201 (.split 211) .empty .empty)))
                (.node 5062537942683630564896284860832881592773 (.groups [1499, 7960598843]) -- 3^2 * 13 * 7^2 * 19^4 * 151^6 * 911^6
                  (.node 4817357063206146396553061717374224691089 (.groups [157, 433, 14083]) -- 3^8 * 13^4 * 757^2 * 14713^4 * 30941^2
                    (.node 4025692407186941399398038356586779438421 (.groups [97, 331, 28792661]) .empty .empty)
                    (.node 4994104769156526854723400473006471934777 (.groups [37, 43, 4933]) .empty .empty))
                  (.node 8350435196553418601700310681625463556917 (.groups [23, 1372537, 10196539, 45437789]) -- 3^2 * 13 * 7^4 * 2801^10
                    (.node 7728295637009740399243683439326439096773 (.groups [89, 70841]) .empty .empty)
                    (.node 8461730938442214084900807329583356401605 (.groups [43, 45319]) .empty .empty))))
              (.node 63813002185857570209528432269099218559461 (.groups [71, 281, 32668561, 14278950628867]) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^6
                (.node 48326261389924318417484004293927560200645 (.split 21491) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^6
                  (.node 36286196712551282842416652592500211801169 (.split 19) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^2
                    (.node 9917906414487125333586347130648382417437 (.groups [743, 5209, 14083]) .empty .empty)
                    (.node 37110885290157683286002168006606014384053 (.groups [11, 131]) .empty .empty))
                  (.node 56094722833639444848849565817573601333033 (.groups [7, 31, 37]) -- 3^2 * 13^4 * 30941^2 * 157^6 * 433^5
                    (.node 55192547385992729805867196006672315677969 (.groups [433, 14083, 245753]) .empty .empty)
                    (.node 57856692921168453256338020343364153079025 (.groups [7, 5233, 1866871, 2703853428809791]) .empty .empty)))
                (.node 119776585216403835374936836911534517837653 (.groups [613, 1747]) -- 3^6 * 1093 * 547^8 * 163^6
                  (.node 74637273109969060707486334373903530552005 (.groups [421, 384481, 1097113, 232611722621]) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^4 * 21491^2
                    (.node 67931258943136451307842967595701835024773 (.groups [7, 3541, 10837, 398581]) .empty .empty)
                    (.node 87603904786950673483926475002558516304437 (.groups [37, 211]) .empty .empty))
                  (.node 136373917527073142481338026641726870240801 (.groups [7, 547, 78919, 95957]) -- 3^12 * 797161^6
                    (.node 125811201825921589548347386221912735635061 (.groups [73, 97]) .empty .empty)
                    (.node 169552354870867759663613746046077034850933 (.groups [7, 19]) .empty .empty)))))
            (.node 4250077618721012917284857241316054012030521 (.groups [7, 953, 4327]) -- 3^4 * 11^6 * 43^4 * 45319^6
              (.node 712743084256970114100675158695150545700605 (.split 381510691) -- 3^4 * 11^4 * 5 * 3221^10
                (.node 426776188283574100052104516988303434285209 (.groups [19, 17311991, 3597318971]) -- 3^4 * 11^10 * 15797^4 * 1806113^2
                  (.node 236346718061897229285928327147936356158541 (.groups [2426789, 7908811]) -- 3^2 * 13^2 * 61 * 31^12 * 42407^4
                    (.node 215918912955081139682875169541777820620729 (.groups [19, 37, 157, 433, 14083, 115201]) .empty .empty)
                    (.node 237252510409905159302751513214051397276613 (.groups [43, 71]) .empty .empty))
                  (.node 487690609826949472163877154147223975828025 (.groups [1866871, 917087137, 2703853428809791]) -- 3^6 * 1093^2 * 398581^4 * 5^2 * 31^6
                    (.node 437785274863621712454825833410247483500341 (.groups [7, 4447, 5839]) .empty .empty)
                    (.node 519923777383110848465352734288143456532121 (.groups [701, 70841, 2384047]) .empty .empty)))
                (.node 2451648076215384365340707606298028527442293 (.groups [37, 379]) -- 3^2 * 13 * 7^6 * 29^4 * 4733^8
                  (.node 1221046980141706433639422881666488741471481 (.groups [211, 4105333]) -- 3^12 * 797161 * 398581^2 * 1621^6
                    (.node 713628891843823350024729544058044053040605 (.split 33151) .empty .empty)
                    (.node 1778023638915012859278415977032510378257281 (.groups [1093, 2801, 151841, 32607907713428723311]) .empty .empty))
                  (.node 3491945097040262361125960494436046820794201 (.split 7) -- 3^6 * 1093^2 * 398581^6
                    (.node 3245450445198140714451523135112524317354393 (.groups [7, 11, 31]) .empty .empty)
                    (.node 4248546453626298993863041357365713630591409 (.groups [37, 43, 4933, 2384047]) .empty .empty))))
              (.node 41293929930799297777993812291588665152542045 (.groups [19, 463, 22777]) -- 3^4 * 11^4 * 5 * 3221^8 * 24517^2
                (.node 15778644709947729055306329549326477013597357 (.groups [87653303, 208097431]) -- 3^6 * 1093 * 547^4 * 431^10
                  (.node 8665229939600858579521149773047553561441133 (.groups [79, 433]) -- 3^2 * 13^4 * 30941^2 * 157^13
                    (.node 6707088083180531990023913928996922385675493 (.groups [67, 1093]) .empty .empty)
                    (.node 14844325435772718128133062206486420786247157 (.groups [11, 1811]) .empty .empty))
                  (.node 21452914837899210717392146402250947627345509 (.groups [97, 331]) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^2 * 31^2 * 73^6
                    (.node 16884930025364934695713103995134639373029681 (.split 5) .empty .empty)
                    (.node 24289014986965879619551861999009369377203289 (.groups [743, 5209, 12503]) .empty .empty)))
                (.node 87123158306835630104642382874593008534606769 (.groups [29, 1093, 4733]) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^6
                  (.node 62801042091544389195197428058761828711368717 (.groups [5, 45121, 487681]) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^4
                    (.node 60348725676446906656401276392012563826905917 (.groups [1597, 5113]) .empty .empty)
                    (.node 84424650126824673478565519975673196865148405 (.split 151841) .empty .empty))
                  (.node 131009626345323266890627102670709265259390625 (.groups [1866871, 127159831, 2703853428809791]) -- 3^6 * 1093^2 * 398581^4 * 5^6 * 19531^2
                    (.node 111754247035072152613064071833335688398657721 (.groups [13, 31, 37, 4105333]) .empty .empty)
                    (.node 171105309754972855695172064227366294218915849 (.groups [19, 113, 47251, 518323723, 189361597248713]) .empty .empty)))))))
        (.node 513998137529017639494654582853109905114735857812707317 (.groups [5, 37]) -- 3^2 * 13 * 7^4 * 2801^14
          (.node 806028480785840435114224288167573495491375826453 (.groups [5, 61]) -- 3^2 * 13 * 7^2 * 19^6 * 701^6 * 70841^4
            (.node 5578799857303185941193062611385260117690508769 (.groups [4051, 37680901, 249561007]) -- 3^4 * 11^10 * 15797^2 * 1806113^4
              (.node 1555067558964351179794781212313781374759000853 (.groups [11, 128341, 492103]) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^2 * 39103^4
                (.node 698481671384640487162959421505350685343412173 (.groups [5, 9631]) -- 3^6 * 1093^2 * 398581^2 * 1621^2 * 7^4 * 13 * 2801^4
                  (.node 652591276945065503200332684205123983635730717 (.groups [29, 953]) -- 3^6 * 1093^5 * 547^4 * 431^6
                    (.node 422123250634123367392827599878365984325742025 (.groups [31, 151841, 104670301, 32607907713428723311]) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5^2
                      (.node 383030048177042775065233837719821278243452405 (.split 19) .empty .empty)
                      .empty)
                    (.node 678171771249660132650518519665347777476875045 (.groups [7, 13963, 647251721]) .empty .empty))
                  (.node 1370243838233333443935012120048174384522747645 (.groups [197, 12342821, 85161343]) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^6
                    (.node 1037863309940019575795340643486141681356402441 (.groups [2384047, 3060947, 262209281]) .empty .empty)
                    (.node 1405280042770794929357509517503723029414452169 (.groups [947, 8269, 14083]) .empty .empty)))
                (.node 2539303778194563560364203754910338139770527409 (.split 52379047267) -- 3^2 * 13^8 * 61^6 * 1609669^4
                  (.node 1698637292435475586367159456552545840551836481 (.groups [7, 113, 1093]) -- 3^12 * 797161 * 398581^6
                    (.node 1650802097070276056906763632128037553376809117 (.groups [11, 281]) .empty .empty)
                    (.node 1859498355745776641668770637178134571062845693 (.groups [37, 127]) .empty .empty))
                  (.node 4728853441776395731306580582507220102140145249 (.groups [911, 1093, 151841]) -- 3^2 * 13^6 * 5229043^4 * 151^2 * 7^2 * 19^4
                    (.node 2668306086181737485506340777967658804606859829 (.groups [917087137, 6713462860391040872837261]) .empty .empty)
                    (.node 4949894246927014502289135412847733235894682481 (.groups [12601, 14421466756460791, 97298466526008161]) .empty .empty))))
              (.node 39181753370999216247944765474420049217958365977 (.groups [23, 1372537]) -- 3^2 * 13^2 * 61^2 * 97 * 7^4 * 2801^10
                (.node 9486419653792860161492128012361409652601202081 (.groups [5, 1361, 292661]) -- 3^6 * 1093^8 * 56773^2 * 211^4
                  (.node 6595764727510254175879793597992363639620344841 (.groups [7, 13, 19, 9631]) -- 3^6 * 1093^2 * 398581^2 * 1621^8
                    (.node 6338837133136136907217649846839319975491058025 (.groups [37861, 63601, 1866871]) .empty .empty)
                    (.node 8384160177993669929063431147140948416726876601 (.groups [113, 2801, 47251, 518323723]) .empty .empty))
                  (.node 15426102020201360469739770919951680335387659689 (.split 398581) -- 3^6 * 1093^8 * 56773^4
                    (.node 10553081265853084184820689996959149608143550625 (.groups [11, 71, 151841]) .empty .empty)
                    (.node 16751267816395194139714444149105334156713403893 (.groups [29, 6301, 492103]) .empty .empty)))
                (.node 65514182728514697534918559184071418507611572117 (.groups [1483, 8932457, 22867937]) -- 3^2 * 13 * 7^4 * 2801^12
                  (.node 45201107341723400732369574751565606516704956573 (.groups [62060021, 1285983178319318482443211013887]) -- 3^2 * 13 * 7^2 * 19^10 * 104281^6
                    (.node 41971151610684426935781250000464207130147248381 (.groups [31, 37, 73]) .empty .empty)
                    (.node 52765406329265420924103449984795748040717753125 (.groups [7, 31]) .empty .empty))
                  (.node 384993289508345875996954484193064912344449756481 (.groups [1499, 151841, 7960598843, 32607907713428723311]) -- 3^2 * 13^6 * 5229043^4 * 151^6
                    (.node 138273847391912441798549415416855481445886318205 (.groups [127, 331, 184725139, 2703853428809791]) .empty .empty)
                    (.node 410823848721689826524108126209906472419616953449 (.groups [29, 113, 4733]) .empty .empty)))))
            (.node 810308766421502298738852702323808452205756570094845 (.groups [19, 31]) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^2 * 769^8
              (.node 33332400305116945012550871136389800225881589041809 (.groups [5, 1956611, 2384047]) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^4
                (.node 4975410832248447306486225542091938183196640396641 (.groups [5, 1361, 292661]) -- 3^6 * 1093^2 * 398581^2 * 1621^6 * 211^4
                  (.node 2545049690601743626173547404435175790833181034093 (.groups [5, 11, 421, 14621, 6579701]) -- 3^2 * 13 * 7^2 * 19^2 * 127^4 * 262209281^4
                    (.node 888046899553604471654200165422151558063373267769 (.split 7) .empty .empty)
                    (.node 2652834376364354195642022343214783887363394378901 (.groups [5, 4666801, 604842197, 969550980294955841]) .empty .empty))
                  (.node 10691734623294122019101145422345621459824578987261 (.groups [5, 11, 811]) -- 3^6 * 1093^2 * 398581^2 * 1621^9
                    (.node 7394596173015668075546362764111954382707010478805 (.split 1247451159302262598804596798564656994853573) .empty .empty)
                    (.node 22320115978761788061124206491410612545082877887245 (.groups [421, 1097113, 591694601]) .empty .empty)))
                (.node 58246739604209713413386614456014936492871058155821 (.split 31747594185191) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4
                  (.node 49916858908480391489276338965484828801964960872005 (.groups [151, 331, 911]) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^4
                    (.node 43514298078126619111055808105685426345105290120681 (.groups [19, 29, 239, 108263, 3891879327005091062913468854183]) .empty .empty)
                    (.node 54740487251955285601268383722178129496208737683437 (.groups [398581, 10010548486153, 649371599062696121]) .empty .empty))
                  (.node 206708995579979285063730316647929837277283523075649 (.split 23) -- 3^2 * 13^4 * 30941^10
                    (.node 59735776253027761111501255226061584164320774177381 (.groups [11, 3301, 604842197]) .empty .empty)
                    (.node 784270160206402102699480841973626508256274893264605 (.split 366340651) .empty .empty))))
              (.node 18019986065961421327628758366540023197509350874793805 (.groups [331, 701]) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^2 * 19^6
                (.node 6148551169313878457389347633045260699759148786501309 (.groups [17, 19, 617]) -- 3^6 * 1093^8 * 56773^4 * 398581
                  (.node 2132200605828204336441734597178585890910159215913369 (.groups [29, 239, 2801, 108263]) -- 3^2 * 13^6 * 5229043^6 * 7^4
                    (.node 875786089992891837948536014438416747680963603523597 (.groups [7, 211, 28387]) .empty .empty)
                    (.node 5554139478591768751561431006052303730282712819608157 (.groups [523, 1867147]) .empty .empty))
                  (.node 10075942946673429069806025892236866306942357864304897 (.groups [13, 17]) -- 3^4 * 11^10 * 15797^2 * 1806113^5
                    (.node 8778231994079794318606559194086073066365798897523281 (.groups [7, 1093, 111187]) .empty .empty)
                    (.node 17331301824359771792962956729622252386375642538350081 (.groups [12893, 32668561, 122556524179]) .empty .empty)))
                (.node 93364053254632562980154990053027830432694330906107009 (.groups [19, 37]) -- 3^2 * 13^4 * 30941^6 * 7^4 * 2801^5
                  (.node 27605307808530971968628979531555318777847578352399701 (.groups [23, 32668561]) -- 3^6 * 1093^2 * 398581^2 * 1621 * 811^10
                    (.node 24821091218540384307286912513876741885009659119386005 (.groups [10378063, 22939801]) .empty .empty)
                    (.node 46226840130713080559221628379534220839204320219633157 (.groups [88009573, 304018940824561]) .empty .empty))
                  (.node 109349058661809041798713337506754883919682983707018321 (.groups [7, 79, 4027, 8682564712362839769429759610849611323291]) -- 3^2 * 13^4 * 30941^10 * 23^2
                    (.node 104477829685582012485644995261750708654597801579755081 (.groups [29, 239, 4733]) .empty .empty)
                    (.node 110117266240355714071444007689178176985115024595173717 (.groups [5, 61, 222942691488419051165955167217344876341]) .empty .empty))))))
          (.node 698093814268561177269311417544906951620828422643079088542575887973241 (.split 8011) -- 3^6 * 1093^2 * 398581^10 * 89^2
            (.node 197891922800542142629373015645594697722472724772231791292169 (.groups [53, 79, 2393, 5910676280174070976604828251164496731606578851]) -- 3^2 * 13^4 * 30941^12
              (.node 84065354426491269251917086356504022781354809663080664933 (.groups [39103, 128341]) -- 3^2 * 13 * 7^2 * 19^6 * 701^2 * 70841^8
                (.node 33700063890892994544738777779497252552534513586628668277 (.groups [22406023, 154522673919080310634923725508989347]) -- 3^2 * 13 * 7^6 * 29^4 * 4733^2 * 732541^6
                  (.node 1946468500981206914886088042159319905722804883632746805 (.groups [7, 42337, 77797]) -- 3^2 * 13^6 * 5229043^4 * 151^4 * 5 * 151841^2
                    (.node 554754190696743413435523619906622828116979108216959761 (.groups [1621, 3691, 8731, 32668561, 7875862993]) .empty .empty)
                    (.node 2377767667665230794647999939022871827479858928506051477 (.groups [43, 7547]) .empty .empty))
                  (.node 57845652032096983111519355541073333593512298381012691809 (.split 4027) -- 3^2 * 13^4 * 30941^10 * 23^4
                    (.node 49721003687166448315852235147712234016091346662845172481 (.groups [29, 127, 36277007914872163096693185049500538726334453]) .empty .empty)
                    (.node 76860822921256829410972524228348797003917493831573101245 (.groups [29, 113, 127, 3002048442926621678671594508574964267]) .empty .empty)))
                (.node 4321798998407080035454476845257585792861262593155454986645 (.groups [11, 21491]) -- 3^2 * 13^2 * 61^4 * 5 * 131^2 * 17293^10
                  (.node 618210864926670819213665413946226453997546316510617755909 (.groups [43, 2017]) -- 3^2 * 13^2 * 61 * 31^2 * 331^6 * 2180921^2 * 3217^6
                    (.node 589845951458019646779049579630364870032032816376793970201 (.split 297134095231) .empty .empty)
                    (.node 2450695673616294989424703568926813054970701282472478242529 (.split 1621) .empty .empty))
                  (.node 44111076273292556952114317614776384843746003793324165340053 (.groups [29, 337]) -- 3^6 * 1093^8 * 56773 * 28387^6
                    (.node 15921436923918829129471775057591311331993255799896817734805 (.groups [7, 1009]) .empty .empty)
                    (.node 103740046247571170456806185642315813867096189333830496676005 (.groups [7, 13]) .empty .empty))))
              (.node 174981600836331614395242044553689341990548114338802311904153611373 (.groups [43, 197, 11593, 589331]) -- 3^2 * 13 * 7^2 * 19^2 * 127^4 * 262209281^6
                (.node 24281769307281803179425031157223224524294167816388537413790881 (.split 31) -- 3^2 * 13^6 * 5229043^8
                  (.node 3972577686932014177857444485230363962107506778887887231139509 (.groups [811, 3397526895844168594277762829213027983813]) -- 3^6 * 1093^8 * 56773^4 * 398581^2 * 1621
                    (.node 221114480082098686470544439946001633453693649932224038499141 (.groups [5, 11, 17, 19]) .empty .empty)
                    (.node 12617984956085194767179166528719132934744035799234263452923141 (.groups [7, 43, 72377887]) .empty .empty))
                  (.node 10317953639230350793460764418712152723002017153705518474049957225 (.groups [11, 31, 101, 47745511409800938588770747187274669099]) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^4 * 5^2
                    (.node 412718145569214031738430576748486108920080686148220738961998289 (.split 5) .empty .empty)
                    (.node 88132030585602976552116073418117277063606668683635789489026118921 (.split 89) .empty .empty)))
                (.node 48988351429540520746450346191809942539537957382684855634008954602349 (.split 7) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^6
                  (.node 7843750722118664913138330534212437658660993512843585264523324583969 (.split 5) -- 3^6 * 1093^2 * 398581^10 * 89
                    (.node 257948840980758769836519110467803818075050428842637961851248930625 (.groups [11, 71, 101]) .empty .empty)
                    (.node 22424723872430198154065784199349949535900674155958958460921568212001 (.groups [5, 11, 4051]) .empty .empty))
                  (.node 189450938019499884596287714391652381422170255206452859678093142838289 (.groups [5, 11, 157]) -- 3^2 * 13^4 * 30941^14
                    (.node 105253347477052561760157094348891750037958215664867508135903634263605 (.groups [3229, 202519, 68409301]) .empty .empty)
                    (.node 196093768052966622828458263355310941466524837821089631613083114599225 (.groups [31, 1137043309874106587329369739133088789635301921798771999]) .empty .empty)))))
            (.node 230900846700715678710768009720969109646796893955046829168838824257168833469430001 (.groups [991, 1933, 53201195339952741232757911703065781345511721905797]) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^6 * 113^2
              (.node 663933764070827434039404350778255839335701320250624356632315913035060752969 (.split 23) -- 3^2 * 13^6 * 5229043^10
                (.node 8278232800901880915657559471265101611195518397645805786199239015701405 (.groups [19, 37, 769]) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^8
                  (.node 2400429220047485516576066963398687184437359911751557926066438775515101 (.split 19) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^6 * 7^2
                    (.node 947222978740543863080776683972396102154330829769871658570331607312605 (.groups [43, 127]) .empty .empty)
                    (.node 4652539647977865283607501150358949743761467519374314761609301396918805 (.groups [29, 8387, 430570659106944883310029331646560742422358013]) .empty .empty))
                  (.node 28714546434597883587649116885219305061827804480561512543737343276102579317 (.groups [113, 911]) -- 3^2 * 13 * 7^12 * 16148168401^6
                    (.node 117621031782326790312227281206535672037430635675826338377255500000239949 (.groups [2801, 84989558479232242640144815482521415474498435681558241]) .empty .empty)
                    (.node 60016390684061714210903259491854266247771036192890557150893820907452004981 (.groups [19, 3217]) .empty .empty)))
                (.node 351220961193467712606844901561697339008585998412580284658495117995547138320601 (.groups [7, 79, 664499072088544514055468407576442854773858294407279590585435656891]) -- 3^2 * 13^6 * 5229043^10 * 23^2
                  (.node 18082923228186677007656669255303399612091541542411060315517176306458519341329 (.split 113) -- 3^2 * 13^2 * 61^6 * 52379047267^2 * 6619231^6
                    (.node 14001254871795337726671678835747425454896982171999464260380155890081921487681 (.groups [13, 10687, 5557579]) .empty .empty)
                    (.node 58707455969234121699745468862537838683282096577323521581282588825963645575901 (.split 2671) .empty .empty))
                  (.node 52076714882788118480957893942310916872056684720912959705250646494921196698785561 (.split 18457) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2
                    (.node 1618280467507867160659578271417916148397420445336823634514846581044797041357089 (.split 7) .empty .empty)
                    (.node 79295742907885490872319335299477891271473601821504358091227482471195055026497361 (.groups [19, 29, 3319, 30650832715386945983110738674706459882548133096065184443881]) .empty .empty))))
              (.node 6043493078034610660721175352231468689656359808866152148834090332193457492209058355143931952634361 (.groups [421, 21613, 73774717787791]) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^2 * 18457^4
                (.node 891600371962387659352397456274187717062544851969678382987530239900303004602156216445 (.groups [23, 630137366116724786143582781440557531291758335352729974049244986288311]) -- 3^4 * 11^4 * 5 * 3221^2 * 10378063^10
                  (.node 16215065287230353678535203499006852015439175155831379500806875586912220796265604005 (.groups [19, 331]) -- 3^6 * 1093^2 * 398581^4 * 5 * 1866871^8
                    (.node 3885491402486389052743647429674416672302206489253713546470146641088557696298370689 (.groups [29, 2801, 3319]) .empty .empty)
                    (.node 418833139381404809629313813523340812785657147967901137929571077788331704777061526141 (.groups [7, 19, 577]) .empty .empty))
                  (.node 18153868340272232532842887977736741891512301818376022209794892393607628081282530302725681 (.groups [53, 1171, 517953204373017526357542369403663062966586835752887290757375653954434566179]) -- 3^2 * 13^6 * 5229043^12
                    (.node 961179926591620302803039848493232592707550229893890497279811182356760527469485099377 (.groups [11, 839, 21613, 73774717787791]) .empty .empty)
                    (.node 2988056555133532830454645410304572483548759436975666982163801095571705369820408199317693981 (.groups [5, 11]) .empty .empty)))
                (.node 59171816479329028713427959621364657494784966276226417436660826794660962555676554063015816428093011114381 (.groups [5, 11, 22280841470107301759731]) -- 3^2 * 13^2 * 61 * 31^6 * 917087137^4 * 31747594185191^4
                  (.node 4597783923547404580127743499627965783813314109425835777297386522228657876689139128355586939054581610521 (.groups [5, 2311, 25332490598403837286469216576711, 674590164196543681729450733361052883373451]) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^4
                    (.node 827150666440253865851023208650983631284511380816919883477663437094233309456627021055397040362420333 (.groups [23, 67]) .empty .empty)
                    (.node 34652552734930706057082568772898794273739505455949557076394151324594649496036297147424523674360487978989 (.groups [23, 18296928269900459971988699477237282979477642133512118795105419584254956007342982168289229]) .empty .empty))
                  (.node 405932230080392865448963304769390409609777359533437173657255889498555216528036277139615591579990519401431796038856655178701081 (.groups [7, 29, 127]) -- 3^2 * 13^2 * 61^6 * 52379047267^4 * 297134095231^6
                    (.node 12181034438213967541135440700350670455497587186577758910866556137121083248974468789196914934472316982110633554923322128369 (.groups [23, 67, 100872621660213627140633959039687613804667219578019505044319975535451022633798600576274371862100889143097]) .empty .empty)
                    (.node 59639849958721883237644420521034467513453063875150157049677339172461780825716529464514580400339941758351687196999154328299442003261 (.groups [29, 22280841470107301759731]) .empty .empty))))))))))

private def seed5Tree : HintTree :=
  (.node 251155806815228220740025 (.split 37861) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093^2
    (.node 148579256313125 (.split 3) -- 5^4 * 11^4 * 71^2 * 3221
      (.node 217206405 (.split 5229043) -- 5 * 3^2 * 13^6
        (.node 390625 (.split 19) -- 5^8
          (.node 15625 (.split 19531) -- 5^6
            (.node 405 (.split 11) -- 5 * 3^4
              (.node 25 (.split 31) -- 5^2
                (.node 5 (.split 3) -- 5
                  (.node 1 (.split 5) .empty .empty)
                  .empty)
                (.node 45 (.split 13) .empty .empty))
              (.node 3645 (.split 1093) -- 5 * 3^6
                (.node 3125 (.split 3) -- 5^5
                  (.node 625 (.split 11) .empty .empty)
                  .empty)
                (.node 7605 (.split 61) .empty .empty)))
            (.node 75625 (.split 7) -- 5^4 * 11^2
              (.node 32805 (.split 13) -- 5 * 3^8
                (.node 28125 (.split 7) -- 5^5 * 3^2
                  (.node 24025 (.split 3) .empty .empty)
                  .empty)
                (.node 49005 (.split 7) .empty .empty))
              (.node 253125 (.split 7) -- 5^5 * 3^4
                (.node 216225 (.split 13) .empty .empty)
                (.node 295245 (.split 23) .empty .empty))))
          (.node 9150625 (.split 71) -- 5^4 * 11^4
            (.node 2810925 (.split 7) -- 5^2 * 31^2 * 3^2 * 13
              (.node 1953125 (.split 3) -- 5^9
                (.node 1946025 (.split 11) -- 5^2 * 31^2 * 3^4
                  (.node 1285245 (.split 30941) .empty .empty)
                  .empty)
                (.node 2278125 (.split 7) .empty .empty))
              (.node 5544045 (.split 61) -- 5 * 3^8 * 13^2
                (.node 3705625 (.split 3) .empty .empty)
                (.node 5929605 (.split 3221) .empty .empty)))
            (.node 141015625 (.split 3) -- 5^8 * 19^2
              (.node 17578125 (.split 11) -- 5^9 * 3^2
                (.node 17514225 (.split 331) -- 5^2 * 31^2 * 3^6
                  (.node 9765625 (.split 12207031) .empty .empty)
                  .empty)
                (.node 23088025 (.split 11) .empty .empty))
              (.node 157628025 (.split 13) -- 5^2 * 31^2 * 3^8
                (.node 156184605 (.split 7) .empty .empty)
                (.node 181575625 (.split 19) .empty .empty)))))
        (.node 133974300625 (.split 7) -- 5^4 * 11^8
          (.node 8897205625 (.split 19) -- 5^4 * 11^2 * 7^6
            (.node 1418652225 (.split 23) -- 5^2 * 31^2 * 3^10
              (.node 1107225625 (.split 43) -- 5^4 * 11^6
                (.node 936943605 (.split 757) -- 5 * 3^8 * 13^4
                  (.node 717482205 (.split 43) .empty .empty)
                  .empty)
                (.node 1269140625 (.split 13) .empty .empty))
              (.node 2793651025 (.split 7) -- 5^2 * 31^4 * 11^2
                (.node 2126953125 (.split 7) .empty .empty)
                (.node 4354495605 (.split 398581) .empty .empty)))
            (.node 50906640625 (.split 31) -- 5^8 * 19^4
              (.node 22187592025 (.split 917087137) -- 5^2 * 31^6
                (.node 20629391445 (.split 97) -- 5 * 3^8 * 13^2 * 61^2
                  (.node 11422265625 (.split 11) .empty .empty)
                  .empty)
                (.node 46128300625 (.split 3221) .empty .empty))
              (.node 86815346805 (.split 7) -- 5 * 3^4 * 11^8
                (.node 65548800625 (.split 3) .empty .empty)
                (.node 105297620805 (.split 131) .empty .empty))))
          (.node 6564740730625 (.split 3) -- 5^4 * 11^8 * 7^2
            (.node 2047260180625 (.split 3) -- 5^4 * 11^6 * 43^2
              (.node 435963075625 (.split 3) -- 5^4 * 11^2 * 7^8
                (.node 338031774025 (.split 3221) -- 5^2 * 31^4 * 11^4
                  (.node 136888900225 (.split 3) .empty .empty)
                  .empty)
                (.node 1918876005225 (.split 7) .empty .empty))
              (.node 5960311890625 (.split 3) -- 5^6 * 19531^2
                (.node 3211891230625 (.split 3) .empty .empty)
                (.node 6203632133205 (.split 23) .empty .empty)))
            (.node 48921281640625 (.split 3) -- 5^8 * 19^4 * 31^2
              (.node 23663117025625 (.split 71) -- 5^4 * 11^2 * 7^4 * 19^4
                (.node 21322275936025 (.split 3) -- 5^2 * 31^8
                  (.node 6707556111025 (.split 19) .empty .empty)
                  .empty)
                (.node 40901844657025 (.split 43) .empty .empty))
              (.node 61518709067805 (.split 10378063) -- 5 * 3^4 * 11^4 * 3221^2
                (.node 53642807015625 (.split 13) .empty .empty)
                (.node 76761965566845 (.split 131) .empty .empty))))))
      (.node 1532092211173265625 (.split 30941) -- 5^6 * 19531^2 * 3^2 * 13^4
        (.node 4345067368265625 (.split 1093) -- 5^6 * 19531^2 * 3^6
          (.node 1088800344134525 (.split 3) -- 5^2 * 31^4 * 11^4 * 3221
            (.node 440291534765625 (.groups [13, 151, 331, 829, 911]) -- 5^8 * 19^4 * 31^2 * 3^2
              (.node 328670249440225 (.split 19) -- 5^2 * 31^4 * 11^2 * 7^6
                (.node 232532763450625 (.split 211) -- 5^4 * 11^4 * 71^4
                  (.node 191900483424225 (.split 13) .empty .empty)
                  .empty)
                (.node 391812447015405 (.split 52379047267) .empty .empty))
              (.node 536914595901645 (.split 14713) -- 5 * 3^8 * 13^4 * 757^2
                (.node 482785263140625 (.split 11) .empty .empty)
                (.node 697356491203125 (.split 7) .empty .empty)))
            (.node 2421427756080025 (.split 3) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^2
              (.node 1727104350818025 (.split 11) -- 5^2 * 31^8 * 3^4
                (.node 1230423492727845 (.split 157) -- 5 * 3^2 * 13^4 * 30941^2
                  (.node 1159492734255625 (.groups [29, 71, 151, 911, 4733]) .empty .empty)
                  .empty)
                (.node 1807012470634605 (.split 17293) .empty .empty))
              (.node 3281721398465445 (.groups [7, 79, 419, 859, 18041]) -- 5 * 3^2 * 13^10 * 23^2
                (.node 2494706284514925 (.split 7) .empty .empty)
                (.node 3785384073975625 (.split 71) .empty .empty))))
          (.node 119285772926175625 (.split 151) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^2
            (.node 16104842222571025 (.groups [3, 19, 37, 1063, 17351]) -- 5^2 * 31^4 * 11^2 * 7^8
              (.node 8542385246250625 (.split 71) -- 5^4 * 11^2 * 7^4 * 19^6
                (.node 5202093820017645 (.split 11) -- 5 * 3^6 * 1093^4
                  (.node 4949123203500025 (.split 7) .empty .empty)
                  .empty)
                (.node 9065634385640625 (.split 61) .empty .empty))
              (.node 75627510770839225 (.split 3) -- 5^2 * 31^4 * 11^6 * 43^2
                (.node 20490707174520025 (.split 23) .empty .empty)
                (.node 118649960047921225 (.groups [3, 29, 127, 4733, 17351]) .empty .empty)))
            (.node 629453352222135045 (.split 7) -- 5 * 3^6 * 1093^4 * 11^2
              (.node 478573784584575625 (.split 5113) -- 5^4 * 11^4 * 71^2 * 3221^2
                (.node 242507036971501225 (.split 3) -- 5^2 * 31^4 * 11^8 * 7^2
                  (.node 210233974008456225 (.split 1093) .empty .empty)
                  .empty)
                (.node 553003697524078125 (.split 31) .empty .empty))
              (.node 1172197660554600625 (.split 7) -- 5^4 * 11^4 * 71^6
                (.node 874135419944889025 (.split 151) .empty .empty)
                (.node 1317312091092627045 (.split 757) .empty .empty)))))
        (.node 601319581320851325625 (.groups [151, 211, 911, 2221]) -- 5^4 * 11^2 * 7^4 * 19^4 * 71^4
          (.node 42832635577299562225 (.groups [29, 151, 911, 4733]) -- 5^2 * 31^4 * 11^2 * 7^6 * 19^4
            (.node 19082121116911125625 (.split 5113) -- 5^4 * 11^6 * 43^4 * 71^2
              (.node 10352591161585275625 (.groups [3, 13, 31, 37, 2221, 3221]) -- 5^4 * 11^4 * 71^4 * 211^2
                (.node 4749158633514328125 (.split 547) -- 5^6 * 19531^2 * 3^6 * 1093
                  (.node 3507025908457305025 (.split 17351) .empty .empty)
                  .empty)
                (.node 10839584095321093225 (.split 7) .empty .empty))
              (.node 20347955247131282425 (.split 11) -- 5^2 * 31^6 * 917087137
                (.node 19917198745252453125 (.split 7) .empty .empty)
                (.node 30328708672248651405 (.split 433) .empty .empty)))
            (.node 229785733591242653925 (.split 547) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093
              (.node 76163855618878340445 (.split 31) -- 5 * 3^6 * 1093^4 * 11^4
                (.node 57437685367175430625 (.groups [3, 19, 883, 3221, 21020917]) -- 5^4 * 11^4 * 71^6 * 7^2
                  (.node 43062164026349400625 (.groups [701, 2801, 5113, 70841]) .empty .empty)
                  .empty)
                (.node 139835267415281727025 (.split 17351) .empty .empty))
              (.node 315562886600104938025 (.groups [701, 2801, 17351, 70841]) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^6
                (.node 258923583688281890625 (.split 5229043) .empty .empty)
                (.node 531139620670733568025 (.groups [3, 19, 79, 397, 617]) .empty .empty))))
          (.node 5939050990353309712845 (.split 31) -- 5 * 3^2 * 13^6 * 5229043^2
            (.node 2462102584902885173425 (.split 7) -- 5^2 * 31^6 * 917087137 * 11^2
              (.node 2273620341345648765625 (.split 191) -- 5^6 * 19531^4
                (.node 1455191463232041015625 (.split 3) -- 5^10 * 12207031^2
                  (.node 691784841431728899405 (.split 1621) .empty .empty)
                  .empty)
                (.node 2446947760580935170625 (.split 2557) .empty .empty))
              (.node 5190830386431160640625 (.split 398581) -- 5^6 * 19531^2 * 3^6 * 1093^2
                (.node 2719834908489730425625 (.groups [3, 911, 1093, 2801]) .empty .empty)
                (.node 5424972843196222180605 (.split 199) .empty .empty)))
            (.node 97566885270766585320625 (.split 2557) -- 5^4 * 11^6 * 43^4 * 71^2 * 5113
              (.node 19931161710163414659025 (.groups [3, 911, 1093, 2801]) -- 5^2 * 31^4 * 11^2 * 7^4 * 19^4 * 151^2
                (.node 13096723169088369140625 (.split 7) -- 5^10 * 12207031^2 * 3^2
                  (.node 6214676179990259581605 (.split 7) .empty .empty)
                  .empty)
                (.node 23033444426340472467225 (.split 1093) .empty .empty))
              (.node 120643026660241373497825 (.split 3) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^2
                (.node 116227174525506784147005 (.split 19) .empty .empty)
                (.node 125521332267712776890625 (.split 131) .empty .empty)))))))
    (.node 360020627679336956849151393923025 (.groups [37, 1201, 10753, 63601]) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093^2 * 37861^2
      (.node 18660848021395755262281667225 (.split 3) -- 5^2 * 31^6 * 917087137^2
        (.node 467064877368159242810015625 (.split 127159831) -- 5^6 * 19531^2 * 3^2 * 13^2 * 61^6
          (.node 5911508306351827301393425 (.split 19) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^4
            (.node 754884376488538835510205 (.groups [14713, 17293, 21491]) -- 5 * 3^8 * 13^2 * 61^4 * 131^2 * 757^2
              (.node 532165029847905992366205 (.split 127) -- 5 * 3^2 * 13^2 * 61^4 * 131^6
                (.node 460907711104938056100625 (.split 1361) -- 5^4 * 11^4 * 71^4 * 211^4
                  (.node 297914412773249105984425 (.split 1451) .empty .empty)
                  .empty)
                (.node 747572340062257008481845 (.split 11) .empty .empty))
              (.node 1420991005575188603953125 (.split 163) -- 5^6 * 19531^2 * 3^6 * 1093 * 547^2
                (.node 1177940370479238773618445 (.split 11) .empty .empty)
                (.node 4965126921833223161850625 (.split 5113) .empty .empty)))
            (.node 68753959562102123238245325 (.groups [163, 613, 37861, 63601]) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093 * 547^2
              (.node 36047643945563141824115425 (.split 43) -- 5^2 * 31^6 * 917087137 * 11^6
                (.node 25175554757990136406676925 (.split 547) -- 5^2 * 31^2 * 3^6 * 331^6 * 1093
                  (.node 12511243899850321527405625 (.split 3) .empty .empty)
                  .empty)
                (.node 62014955748474343434675625 (.groups [911, 2801, 5113]) .empty .empty))
              (.node 289663907011239537768277825 (.groups [19, 29, 1451, 4733]) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^6
                (.node 82943943672630612618765625 (.split 7) .empty .empty)
                (.node 454450418153436017640429025 (.groups [911, 2801, 17351]) .empty .empty))))
          (.node 5484838309662078939316327245 (.split 11) -- 5 * 3^2 * 13^6 * 5229043^2 * 31^4
            (.node 1817762212524509556961453605 (.split 7) -- 5 * 3^6 * 1093^2 * 398581^2 * 1621^2
              (.node 1055815403834638478829735025 (.split 13) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2
                (.node 627295394813820694352950625 (.groups [3, 227, 2221, 3221]) -- 5^4 * 11^4 * 71^4 * 211^4 * 1361
                  (.node 498859484389429550744355625 (.groups [3, 45319, 3500201, 8715961]) .empty .empty)
                  .empty)
                (.node 1466741554842023554106390625 (.split 157) .empty .empty))
              (.node 2134054498593009655803026425 (.groups [3, 127, 1451, 2801]) -- 5^2 * 31^6 * 917087137 * 11^2 * 7^4 * 19^2
                (.node 2068966366254118439300953125 (.groups [17, 19, 617, 127159831]) .empty .empty)
                (.node 4064253239958900018319515625 (.groups [3, 13, 19, 31, 4760281, 32009891]) .empty .empty)))
            (.node 13725600249850300224786555325 (.split 7) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13
              (.node 9132484077219914734996444005 (.groups [19, 17293, 21491, 395533]) -- 5 * 3^2 * 13^2 * 61^4 * 131^8
                (.node 6625822830390218721626658045 (.split 769) -- 5 * 3^4 * 11^4 * 3221^2 * 10378063^2
                  (.node 6621709329206060106421928205 (.groups [7, 673, 10333, 248879, 92204351]) .empty .empty)
                  .empty)
                (.node 9509010001831355665438086525 (.groups [11, 1721, 63601, 398581]) .empty .empty))
              (.node 15998753748670538798403735625 (.groups [3, 7, 13, 19, 97]) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^2
                (.node 15992673815224811804320863125 (.groups [3, 13, 73, 179, 3643]) .empty .empty)
                (.node 18426910610194573002068997405 (.split 433) .empty .empty)))))
        (.node 1066118562005242374612072445005 (.groups [11, 1811, 8269, 14083, 1768661]) -- 5 * 3^2 * 13^4 * 30941^2 * 157^2 * 433^4
          (.node 199148408757986100897656265625 (.groups [13, 31, 2801, 4760281, 32009891]) -- 5^6 * 19531^4 * 191^2 * 7^4
            (.node 66652093655346249232789420825 (.groups [3, 631, 1451, 28729]) -- 5^2 * 31^6 * 917087137 * 11^6 * 43^2
              (.node 37754310027127186018430578125 (.groups [7, 19, 67]) -- 5^6 * 19531^2 * 3^6 * 1093 * 547^2 * 163^2
                (.node 27516881350483219092497879025 (.split 398581) -- 5^2 * 31^2 * 3^6 * 331^6 * 1093^2
                  (.node 25386693951333270026542245625 (.split 2557) .empty .empty)
                  .empty)
                (.node 42098414209131221364592557025 (.groups [13, 1063, 21787, 45319]) .empty .empty))
              (.node 167947632192561797360535005025 (.split 13) -- 5^2 * 31^6 * 917087137^2 * 3^2
                (.node 117195557345845930746583676525 (.groups [3, 13, 73, 179, 3643]) .empty .empty)
                (.node 178432803248053902922225219225 (.groups [3, 61, 1063, 21787, 10378063]) .empty .empty)))
            (.node 672554412242664711014541210925 (.groups [3, 19, 1063, 21787]) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13 * 7^2
              (.node 627229302567211440988714379425 (.groups [7, 19, 73, 3221, 28729]) -- 5^2 * 31^6 * 917087137 * 11^4 * 1451^2
                (.node 300043033456005578678850126225 (.groups [11, 37861, 63601, 4189129561]) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093^4
                  (.node 230278424110197697994703328125 (.groups [79, 433, 14083, 127159831]) .empty .empty)
                  .empty)
                (.node 637916590054704355705991085625 (.groups [3, 7, 13]) .empty .empty))
              (.node 853749032341609965014365800625 (.groups [13, 2221, 3221, 142591]) -- 5^4 * 11^4 * 71^4 * 211^4 * 1361^2
                (.node 770393673992076485744892539425 (.groups [151, 911, 1451]) .empty .empty)
                (.node 867295126738517865655010640625 (.split 7) .empty .empty))))
          (.node 32955166199890570839712519335325 (.groups [1063, 2801, 21787]) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13 * 7^4
            (.node 7532752563583470724105396052325 (.groups [163, 613, 2180921]) -- 5^2 * 31^2 * 3^6 * 331^6 * 1093 * 547^2
              (.node 3025878009121237378945188765625 (.split 11) -- 5^6 * 19531^4 * 191^4
                (.node 2183319218503303365686955065325 (.split 7) -- 5^2 * 31^6 * 917087137^2 * 3^2 * 13
                  (.node 1511528689733056176244815045225 (.split 11) .empty .empty)
                  .empty)
                (.node 5270929615585257860682990482445 (.split 4051) .empty .empty))
              (.node 20571803486617014191992145447925 (.groups [431, 37861, 63601]) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093 * 547^4
                (.node 13603758207597505586203335407025 (.groups [43, 1093, 4447, 38047, 38533987]) .empty .empty)
                (.node 30155143748921109593856062049025 (.groups [1063, 21787, 30941, 10378063]) .empty .empty)))
            (.node 129802166173167009645710501880625 (.split 3) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^2
              (.node 51512402358839118821717500125625 (.groups [7, 673, 5113, 10333, 248879]) -- 5^4 * 11^4 * 71^2 * 3221^6
                (.node 42497461210187375417095521390625 (.split 3) -- 5^6 * 19531^6 * 7^2
                  (.node 36153712585301038585168422515625 (.groups [433, 8269, 14083, 127159831]) .empty .empty)
                  .empty)
                (.node 109901653428060423371669858831205 (.split 1866871) .empty .empty))
              (.node 161600431340752825202511335548605 (.split 21491) -- 5 * 3^2 * 13^2 * 61^4 * 131^2 * 17293^4
                (.node 138439880642537788985855140257405 (.groups [21491, 189967, 211093]) .empty .empty)
                (.node 327078559176446090266692423675625 (.split 4751) .empty .empty))))))
      (.node 713628891843823350024729544058044053040605 (.split 33151) -- 5 * 3^4 * 11^4 * 3221^2 * 10378063^4
        (.node 891152861515085300085816446587640625 (.groups [11, 31, 433]) -- 5^6 * 19531^2 * 3^2 * 13^4 * 30941^2 * 157^4
          (.node 4776426517880114816763750912095805 (.split 11) -- 5 * 3^6 * 1093^2 * 398581^2 * 1621^4
            (.node 1127695890565765044243600338997045 (.split 7) -- 5 * 3^2 * 13^4 * 30941^6
              (.node 392016868735974424720128806637325 (.groups [3, 7, 61]) -- 5^2 * 31^4 * 11^4 * 3221^2 * 17351^2 * 13^5
                (.node 377486890210969742934746022087025 (.groups [7, 673, 10333, 17351, 248879]) -- 5^2 * 31^4 * 11^4 * 3221^6
                  (.node 366131239103669722852367840640625 (.groups [7, 19, 1871, 13001, 4760281]) .empty .empty)
                  .empty)
                (.node 824650683227932781655013197515625 (.split 1621) .empty .empty))
              (.node 3454843043394770297584914254466045 (.groups [37, 1693, 12503, 14083]) -- 5 * 3^2 * 13^4 * 30941^2 * 157^6 * 433^2
                (.node 1614803143794637971145913447430925 (.groups [29, 1063]) .empty .empty)
                (.node 3918253214802390133439862128149245 (.split 31) .empty .empty)))
            (.node 162390822066304301200612632423480405 (.split 151) -- 5 * 3^2 * 13^6 * 5229043^4
              (.node 10967706085556951949106897119663525 (.groups [17, 19, 617]) -- 5^2 * 31^2 * 3^6 * 331^6 * 1093^2 * 398581
                (.node 7079719247366202810258671559515625 (.groups [31, 4051, 72577051, 127159831]) -- 5^6 * 19531^2 * 3^2 * 13^6 * 5229043^2
                  (.node 5096219293567667521361674486285225 (.groups [1063, 21787, 5229043]) .empty .empty)
                  .empty)
                (.node 104603835698491401628124426046420625 (.split 12011) .empty .empty))
              (.node 199885503071800887573642850641542445 (.groups [743, 5209, 8269, 14083]) -- 5 * 3^2 * 13^4 * 30941^2 * 157^2 * 433^6
                (.node 165984526340610801417769810915410625 (.groups [3, 7, 13, 19]) .empty .empty)
                (.node 577947608663493892828413860363592405 (.groups [7, 19, 32668561, 125613804731]) .empty .empty))))
          (.node 3702673133933804371675168631887776714405 (.split 7) -- 5 * 3^2 * 13^6 * 5229043^4 * 151^2
            (.node 647745067363042088323897988655584311005 (.groups [11, 1811, 12503]) -- 5 * 3^2 * 13^4 * 30941^2 * 157^6 * 433^4
              (.node 1404178399322924918419312058064515625 (.groups [11, 69617111, 127159831, 239371661]) -- 5^6 * 19531^2 * 3^2 * 13^4 * 30941^4
                (.node 1336758757512479039062776393172828125 (.groups [811, 32668561, 127159831]) -- 5^6 * 19531^2 * 3^6 * 1093^2 * 398581^2 * 1621
                  (.node 1320569200854309535069080243155774425 (.groups [41, 3221, 28729, 21637904461]) .empty .empty)
                  .empty)
                (.node 1672352673069168859533598362253470625 (.groups [3, 7, 13, 349]) .empty .empty))
              (.node 2317102139358756231701130307964465672445 (.split 541) -- 5 * 3^4 * 11^4 * 3221^2 * 10378063^2 * 769^4
                (.node 2166885945927728522320760533333154390625 (.groups [7, 13, 9631]) .empty .empty)
                (.node 3393388045964719131588581491539244950625 (.split 4751) .empty .empty)))
            (.node 48326261389924318417484004293927560200645 (.split 21491) -- 5 * 3^2 * 13^2 * 61^4 * 131^2 * 17293^6
              (.node 8550739217402660378795288426201995305625 (.groups [113, 10378063, 14686393, 10768274427527]) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^6
                (.node 7382817564809300325945871653898631175625 (.split 10378063) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113^4 * 4751^2
                  (.node 4371519259287375464826976160852607458025 (.groups [1621, 2180921, 32668561]) .empty .empty)
                  .empty)
                (.node 12550734151869022777235919210410333146005 (.groups [211, 4105333, 32668561, 20957295829]) .empty .empty))
              (.node 516073484416705442547363459953527250666025 (.groups [41, 101, 63601]) -- 5^2 * 31^2 * 3^6 * 331^4 * 1093^2 * 37861^4
                (.node 74637273109969060707486334373903530552005 (.groups [421, 384481, 1097113, 232611722621]) .empty .empty)
                (.node 683925924151825708203682900473583604985625 (.groups [743, 10378063, 112210253]) .empty .empty)))))
        (.node 2177029318267606025358149745328586830933286534370625 (.groups [9065531, 10378063]) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^4 * 12011^4
          (.node 1370243838233333443935012120048174384522747645 (.groups [197, 12342821, 85161343]) -- 5 * 3^4 * 11^4 * 3221^2 * 10378063^2 * 769^6
            (.node 84424650126824673478565519975673196865148405 (.split 151841) -- 5 * 3^2 * 13^6 * 5229043^4 * 151^4
              (.node 15090580410271283081939339202216376661895625 (.groups [1459, 98887, 10378063]) -- 5^4 * 11^4 * 71^2 * 3221^2 * 5113 * 2557^4 * 12011^2
                (.node 1085248163361972231758932048447872603495625 (.groups [12011, 323683781, 1957650063931]) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113 * 2557^4
                  (.node 1079594564775405698414375847708889103103645 (.groups [19, 37, 157, 433, 14083]) .empty .empty)
                  .empty)
                (.node 17459725485201311805629802472180234103971005 (.groups [7, 113, 47251, 518323723, 189361597248713]) .empty .empty))
              (.node 383030048177042775065233837719821278243452405 (.split 19) -- 5 * 3^6 * 1093^2 * 398581^4 * 1866871^2
                (.node 95694291862944614624478248934167189762595025 (.split 10378063) .empty .empty)
                (.node 678171771249660132650518519665347777476875045 (.groups [7, 13963, 647251721]) .empty .empty)))
            (.node 4440234497768022358271000827110757790316866338845 (.groups [7, 29, 239, 108263, 3891879327005091062913468854183]) -- 5 * 3^2 * 13^6 * 5229043^6
              (.node 138273847391912441798549415416855481445886318205 (.groups [127, 331, 184725139, 2703853428809791]) -- 5 * 3^6 * 1093^2 * 398581^4 * 1866871^2 * 19^2
                (.node 76595558366903686202936593015605328564752450625 (.groups [22576753, 13080080081, 1957650063931]) -- 5^4 * 11^4 * 71^2 * 3221^4 * 5113^4 * 4751^2
                  (.node 15694684149828551485052600870871982542996696025 (.split 31747594185191) .empty .empty)
                  .empty)
                (.node 166644965455693091766550540917671556794838675625 (.groups [31, 10378063, 13080080081]) .empty .empty))
              (.node 49916858908480391489276338965484828801964960872005 (.groups [151, 331, 911]) -- 5 * 3^6 * 1093^2 * 398581^4 * 1866871^2 * 19^4
                (.node 22320115978761788061124206491410612545082877887245 (.groups [421, 1097113, 591694601]) .empty .empty)
                (.node 784270160206402102699480841973626508256274893264605 (.split 366340651) .empty .empty))))
          (.node 646799781217998705709161079153783421292441316581939709117825518025 (.split 3) -- 5^2 * 31^6 * 917087137^6 * 7^2
            (.node 2949229757290098233895247898151824350160164081883969851005 (.split 297134095231) -- 5 * 3^2 * 13^2 * 61^6 * 52379047267^4
              (.node 14393392953085545322283988027071693163870819358026530425 (.groups [3, 11, 43, 1429, 1451, 1801]) -- 5^2 * 31^6 * 917087137^5
                (.node 1946468500981206914886088042159319905722804883632746805 (.groups [7, 42337, 77797]) -- 5 * 3^2 * 13^6 * 5229043^4 * 151^4 * 151841^2
                  (.node 795160397784087594497005133960670630020733589803555625 (.groups [3, 769, 22576753]) .empty .empty)
                  .empty)
                (.node 76860822921256829410972524228348797003917493831573101245 (.groups [29, 113, 127, 3002048442926621678671594508574964267]) .empty .empty))
              (.node 15921436923918829129471775057591311331993255799896817734805 (.groups [7, 1009]) -- 5 * 3^2 * 13^2 * 61^4 * 131^2 * 17293^4 * 21491^6
                (.node 10306676348892158530269443758167983932800483975327190354225 (.groups [3, 769, 46685826619]) .empty .empty)
                (.node 13199995535061198075697164880689457577396761562896728757506643225 (.split 7) .empty .empty)))
            (.node 805136977164918687677068960860675268521776936273500765825923706246889279545491048630025 (.groups [11, 571, 147389551, 22280841470107301759731]) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^2 * 2671^4
              (.node 8091402337539335803297891357089580741987102226684118172574232905223985206785445 (.groups [7, 29, 3319, 30650832715386945983110738674706459882548133096065184443881]) -- 5 * 3^2 * 13^2 * 61^6 * 52379047267^6
                (.node 15818824966651071259133192373044545403499126054182300681519543016879438025 (.split 2671) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^2
                  (.node 105253347477052561760157094348891750037958215664867508135903634263605 (.groups [3229, 202519, 68409301]) .empty .empty)
                  .empty)
                (.node 112855309648905705270829645488661690644005008559915590996424666092284978814914025 (.groups [3, 7, 19, 577, 22280841470107301759731]) .empty .empty))
              (.node 1929217672260164385575921555648549691442477694631281326412724599366782118439352626514295434355971143025 (.groups [7, 19, 22280841470107301759731, 18470582491407832861998377640892352778976956173094871]) -- 5^2 * 31^6 * 917087137^4 * 31747594185191^4 * 11^2
                (.node 15943947704629457732032409550814460259855187558936209309196071069146959656523575425737978796330340025 (.split 11) .empty .empty)
                (.node 22988919617737022900638717498139828919066570547129178886486932611143289383445695641777934695272908052605 (.groups [2311, 25332490598403837286469216576711, 674590164196543681729450733361052883373451]) .empty .empty))))))))

private theorem seed3Check : certify splitPrimes (fun n => seed3Tree.lookup n) 3 23 5 24 root = true := by
  decide +kernel

theorem exclude_3_budget_23 {N : ℕ} (H : Conditions N 23 5) (hseed : 3 ∣ N) : False :=
  certify_correct H hseed splitPrimes prime_proofs (fun n => seed3Tree.lookup n) 24 (root_realizes N) seed3Check

private theorem seed5Check : certify splitPrimes (fun n => seed5Tree.lookup n) 5 23 8 24 root = true := by
  decide +kernel

theorem exclude_5_budget_23 {N : ℕ} (H : Conditions N 23 8) (hseed : 5 ∣ N) : False :=
  certify_correct H hseed splitPrimes prime_proofs (fun n => seed5Tree.lookup n) 24 (root_realizes N) seed5Check

end OddPerfect.FactorBudget
