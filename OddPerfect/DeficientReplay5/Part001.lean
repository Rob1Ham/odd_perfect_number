module

public import OddPerfect.DeficientTree

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part000Tree : Tree :=
  .step (.primeLo 3 59) <|
  .step (.dropHi 4 193) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 3 78) <|
    .step (.dropHi 4 75) <|
    .step (.primeHi 3 73) <|
    .step (.xLo 93) <|
    .reject)
    (.step (.dropLo 4 97) <|
    .splitBase 3 67
      (.step (.dropLo 4 125) <|
      .splitBase 3 61
        (.step (.dropLo 4 154) <|
        .step (.xLo 157) <|
        .splitExp 2 2
          (.step (.fix 2 61 3) <|
          .step (.dropHi 4 161) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject))
          (.step (.dropLo 4 166) <|
          .step (.xLo 169) <|
          .splitBase 3 59
            (.step (.dropLo 4 183) <|
            .step (.xLo 185) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject))
            (.step (.primeLo 3 61) <|
            .step (.dropHi 4 174) <|
            .step (.xHi 173) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject))))
        (.step (.primeLo 3 67) <|
        .step (.dropHi 4 138) <|
        .step (.xHi 137) <|
        .splitExp 2 2
          (.missing 2 61)
          (.step (.dropLo 4 133) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject))))
      (.step (.primeLo 3 71) <|
      .step (.dropHi 4 123) <|
      .step (.xHi 121) <|
      .splitBase 3 73
        (.step (.dropLo 4 108) <|
        .step (.xLo 109) <|
        .splitExp 2 2
          (.missing 2 61)
          (.step (.dropLo 4 114) <|
          .step (.xLo 117) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .step (.fix 1 71 3) <|
            .step (.dropLo 4 119) <|
            .reject)
            (.step (.dropLo 4 118) <|
            .step (.xLo 121) <|
            .missing 4 61)))
        (.step (.primeLo 3 79) <|
        .step (.dropHi 4 104) <|
        .step (.xHi 101) <|
        .splitExp 2 2
          (.missing 2 61)
          (.reject))))

theorem deficientFour5Part000 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,54,79,2,0⟩, ⟨true,57,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part000Tree [] _ _ (by decide +kernel)

private def deficientFour5Part001Tree : Tree :=
  .step (.primeLo 3 167) <|
  .step (.dropHi 4 1038) <|
  .step (.xHi 1001) <|
  .splitExp 1 2
    (.missing 1 31)
    (.step (.dropLo 4 124) <|
    .step (.xLo 169) <|
    .step (.dropHi 3 936) <|
    .step (.primeHi 3 929) <|
    .splitBase 3 283
      (.step (.dropLo 4 222) <|
      .step (.xLo 273) <|
      .splitBase 3 209
        (.step (.primeHi 3 199) <|
        .step (.dropLo 4 333) <|
        .step (.xLo 377) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.step (.dropLo 4 443) <|
          .step (.xLo 481) <|
          .splitBase 3 181
            (.step (.dropLo 4 570) <|
            .step (.xLo 585) <|
            .splitBase 3 173
              (.step (.dropLo 4 668) <|
              .step (.xLo 689) <|
              .splitExp 1 4
                (.missing 1 71)
                (.step (.dropLo 4 840) <|
                .step (.xLo 845) <|
                .splitBase 3 169
                  (.step (.primeHi 3 167) <|
                  .reject)
                  (.step (.primeLo 3 173) <|
                  .step (.dropHi 4 853) <|
                  .step (.xHi 845) <|
                  .missing 4 47)))
              (.step (.primeLo 3 179) <|
              .step (.dropHi 4 731) <|
              .step (.xHi 689) <|
              .splitExp 1 4
                (.missing 1 71)
                (.reject)))
            (.step (.primeLo 3 191) <|
            .step (.dropHi 4 581) <|
            .step (.xHi 533) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 3 196) <|
              .step (.dropLo 4 513) <|
              .step (.primeLo 3 197) <|
              .step (.xLo 533) <|
              .missing 4 89))))
        (.step (.primeLo 3 211) <|
        .step (.dropHi 4 450) <|
        .step (.xHi 429) <|
        .splitBase 3 241
          (.splitExp 2 2
            (.step (.grow 2 7) <|
            .missing 2 19)
            (.step (.dropLo 4 319) <|
            .step (.xLo 325) <|
            .splitBase 3 225
              (.step (.primeHi 3 223) <|
              .step (.dropLo 4 357) <|
              .step (.xLo 377) <|
              .splitExp 1 4
                (.missing 1 71)
                (.step (.dropLo 3 215) <|
                .step (.dropLo 4 401) <|
                .step (.primeLo 3 223) <|
                .step (.xLo 429) <|
                .missing 4 43))
              (.step (.primeLo 3 227) <|
              .step (.dropHi 4 391) <|
              .step (.xHi 377) <|
              .splitExp 1 4
                (.missing 1 71)
                (.step (.dropLo 3 230) <|
                .step (.dropLo 4 353) <|
                .step (.primeLo 3 233) <|
                .step (.xLo 377) <|
                .missing 4 7))))
          (.step (.primeLo 3 251) <|
          .step (.dropHi 4 335) <|
          .step (.xHi 325) <|
          .splitExp 2 2
            (.step (.grow 2 7) <|
            .missing 2 19)
            (.splitBase 3 265
              (.step (.primeHi 3 263) <|
              .step (.dropLo 4 287) <|
              .step (.xLo 325) <|
              .missing 4 163)
              (.step (.primeLo 3 269) <|
              .step (.dropHi 4 307) <|
              .step (.xHi 273) <|
              .missing 4 137)))))
      (.step (.primeLo 3 293) <|
      .step (.dropHi 4 281) <|
      .step (.xHi 273) <|
      .splitBase 3 445
        (.step (.primeHi 3 443) <|
        .step (.dropLo 4 173) <|
        .step (.xLo 221) <|
        .step (.dropHi 3 408) <|
        .step (.primeHi 3 401) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.splitBase 3 337
            (.step (.dropLo 4 231) <|
            .step (.xLo 273) <|
            .missing 4 137)
            (.step (.primeLo 3 347) <|
            .step (.dropHi 4 244) <|
            .step (.xHi 221) <|
            .missing 4 37)))
        (.step (.primeLo 3 449) <|
        .step (.dropHi 4 210) <|
        .step (.xHi 169) <|
        .missing 4 17)))

theorem deficientFour5Part001 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,65,0,1,1⟩] : Vector Slot 5) 13 :=
  Tree.sound deficientFour5Part001Tree [] _ _ (by decide +kernel)

private def deficientFour5Part002Tree : Tree :=
  .step (.grow 0 13) <|
  .step (.dropLo 4 63) <|
  .step (.xLo 65) <|
  .splitBase 3 165
    (.step (.primeHi 3 163) <|
    .step (.dropLo 4 104) <|
    .step (.xLo 117) <|
    .splitExp 1 2
      (.step (.grow 1 31) <|
      .step (.dropHi 3 154) <|
      .step (.dropHi 4 346) <|
      .step (.primeHi 3 151) <|
      .step (.xLo 1209) <|
      .reject)
      (.step (.dropLo 3 124) <|
      .step (.dropLo 4 530) <|
      .step (.primeLo 3 127) <|
      .step (.xLo 533) <|
      .splitBase 3 141
        (.step (.primeHi 3 139) <|
        .step (.dropLo 4 1219) <|
        .step (.xLo 1261) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .step (.grow 2 19) <|
          .step (.xLo 1729) <|
          .splitBase 3 131
            (.step (.dropLo 4 2646) <|
            .step (.xLo 8645) <|
            .splitExp 1 4
              (.step (.grow 1 71) <|
              .reject)
              (.step (.dropLo 3 129) <|
              .step (.dropLo 4 14157) <|
              .step (.primeLo 3 131) <|
              .step (.xLo 15561) <|
              .step (.dropHi 4 17423) <|
              .step (.xHi 15561) <|
              .missing 4 31))
            (.step (.primeLo 3 137) <|
            .step (.dropHi 4 2536) <|
            .step (.xHi 1729) <|
            .missing 4 173))
          (.step (.dropLo 3 137) <|
          .step (.dropLo 4 13324) <|
          .step (.xLo 13325) <|
          .splitExp 1 4
            (.step (.grow 1 71) <|
            .step (.xLo 13845) <|
            .splitBase 3 137
              (.reject)
              (.step (.primeLo 3 139) <|
              .step (.dropHi 4 14603) <|
              .step (.xHi 13845) <|
              .missing 4 7))
            (.reject)))
        (.step (.primeLo 3 149) <|
        .step (.dropHi 4 4261) <|
        .step (.xHi 4225) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .step (.grow 2 19) <|
          .step (.dropHi 4 1013) <|
          .step (.xLo 1729) <|
          .reject)
          (.step (.dropLo 4 876) <|
          .step (.xLo 897) <|
          .splitBase 3 155
            (.step (.primeHi 3 151) <|
            .step (.dropLo 4 1537) <|
            .step (.xLo 1573) <|
            .splitExp 1 4
              (.step (.grow 1 71) <|
              .step (.dropHi 3 150) <|
              .step (.dropHi 4 1802) <|
              .step (.primeHi 3 149) <|
              .step (.xLo 2769) <|
              .reject)
              (.step (.dropLo 4 2912) <|
              .step (.xLo 2925) <|
              .splitBase 3 149
                (.step (.dropLo 4 3938) <|
                .step (.xLo 3965) <|
                .splitExp 1 6
                  (.step (.dropHi 4 4040) <|
                  .step (.xHi 4017) <|
                  .splitExp 2 4
                    (.reject)
                    (.reject))
                  (.step (.dropLo 4 4138) <|
                  .step (.xLo 4173) <|
                  .splitExp 2 4
                    (.reject)
                    (.reject)))
                (.step (.primeLo 3 151) <|
                .step (.dropHi 4 3084) <|
                .step (.xHi 3081) <|
                .splitExp 1 6
                  (.step (.dropHi 4 2967) <|
                  .step (.xHi 2925) <|
                  .missing 4 7)
                  (.step (.dropLo 4 3020) <|
                  .step (.xLo 3029) <|
                  .splitExp 2 4
                    (.reject)
                    (.step (.dropLo 4 3077) <|
                    .step (.xLo 3081) <|
                    .missing 4 23)))))
            (.step (.primeLo 3 157) <|
            .step (.dropHi 4 1727) <|
            .step (.xHi 1677) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 4 1199) <|
              .step (.xLo 1209) <|
              .splitBase 3 159
                (.step (.primeHi 3 157) <|
                .step (.dropLo 4 1672) <|
                .step (.xLo 1677) <|
                .missing 4 839)
                (.step (.primeLo 3 163) <|
                .step (.dropHi 4 1226) <|
                .step (.xHi 1209) <|
                .splitExp 1 6
                  (.reject)
                  (.reject))))))))
    (.use 0)

private def deficientFour5Part002Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,65,0,1,1⟩], 13, deficientFour5Part001⟩]

theorem deficientFour5Part002 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,33,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part002Tree deficientFour5Part002Refs _ _ (by decide +kernel)

private def deficientFour5Part003Tree : Tree :=
  .step (.primeLo 3 167) <|
  .step (.dropHi 4 61) <|
  .splitExp 1 2
    (.missing 1 31)
    (.step (.dropLo 4 43) <|
    .step (.xLo 45) <|
    .step (.dropHi 3 3888) <|
    .step (.primeHi 3 3881) <|
    .splitBase 3 319
      (.step (.primeHi 3 317) <|
      .step (.dropLo 4 50) <|
      .step (.xLo 53) <|
      .step (.dropHi 3 282) <|
      .step (.primeHi 3 281) <|
      .splitBase 3 209
        (.step (.primeHi 3 199) <|
        .step (.dropLo 4 56) <|
        .step (.xLo 57) <|
        .splitBase 3 181
          (.splitExp 2 2
            (.step (.grow 2 61) <|
            .step (.dropHi 4 59) <|
            .step (.xLo 61) <|
            .reject)
            (.step (.dropLo 4 59) <|
            .step (.xLo 61) <|
            .missing 4 31))
          (.step (.primeLo 3 191) <|
          .step (.dropHi 4 58) <|
          .step (.xHi 57) <|
          .missing 4 29))
        (.step (.primeLo 3 211) <|
        .step (.dropHi 4 56) <|
        .step (.xHi 53) <|
        .step (.dropLo 3 232) <|
        .step (.primeLo 3 233) <|
        .splitBase 3 253
          (.step (.primeHi 3 251) <|
          .splitExp 2 2
            (.missing 2 61)
            (.reject))
          (.step (.primeLo 3 257) <|
          .splitExp 2 2
            (.missing 2 61)
            (.step (.dropLo 3 259) <|
            .step (.primeLo 3 263) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject)))))
      (.step (.primeLo 3 331) <|
      .step (.dropHi 4 51) <|
      .step (.xHi 49) <|
      .step (.dropLo 3 356) <|
      .step (.primeLo 3 359) <|
      .splitBase 3 657
        (.step (.primeHi 3 653) <|
        .step (.dropLo 4 47) <|
        .step (.xLo 49) <|
        .step (.dropHi 3 492) <|
        .step (.primeHi 3 491) <|
        .splitBase 3 413
          (.step (.primeHi 3 409) <|
          .splitExp 2 2
            (.missing 2 61)
            (.reject))
          (.step (.primeLo 3 419) <|
          .splitExp 2 2
            (.missing 2 61)
            (.step (.dropLo 3 424) <|
            .step (.primeLo 3 431) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 3 488) <|
              .step (.primeLo 3 491) <|
              .splitExp 1 6
                (.reject)
                (.reject)))))
        (.step (.primeLo 3 659) <|
        .step (.dropHi 4 47) <|
        .step (.xHi 45) <|
        .missing 4 23)))

theorem deficientFour5Part003 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,33,97,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part003Tree [] _ _ (by decide +kernel)

private def deficientFour5Part004Tree : Tree :=
  .step (.primeLo 3 83) <|
  .splitBase 2 11
    (.use 0)
    (.step (.primeLo 2 13) <|
    .step (.dropHi 4 98) <|
    .step (.xHi 97) <|
    .splitBase 3 165
      (.step (.primeHi 3 163) <|
      .step (.dropLo 4 41) <|
      .splitExp 1 2
        (.step (.grow 1 31) <|
        .step (.dropHi 3 162) <|
        .step (.dropHi 4 54) <|
        .step (.primeHi 3 157) <|
        .step (.xLo 93) <|
        .reject)
        (.step (.dropLo 4 59) <|
        .step (.xLo 61) <|
        .splitBase 3 109
          (.step (.dropLo 4 72) <|
          .step (.xLo 73) <|
          .splitBase 3 93
            (.step (.primeHi 3 89) <|
            .step (.dropLo 4 85) <|
            .splitBase 3 85
              (.step (.primeHi 3 83) <|
              .step (.dropLo 4 92) <|
              .step (.xLo 93) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 4 96) <|
                .step (.xLo 97) <|
                .missing 4 7))
              (.step (.primeLo 3 89) <|
              .step (.dropHi 4 90) <|
              .step (.xHi 89) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 4 89) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.reject))))
            (.step (.primeLo 3 97) <|
            .step (.dropHi 4 83) <|
            .step (.xHi 81) <|
            .splitBase 3 101
              (.step (.dropLo 4 77) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 4 79) <|
                .step (.xLo 81) <|
                .missing 4 41))
              (.step (.primeLo 3 103) <|
              .step (.dropHi 4 79) <|
              .step (.xHi 77) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 3 104) <|
                .step (.dropLo 4 75) <|
                .step (.primeLo 3 107) <|
                .step (.xLo 77) <|
                .step (.dropHi 3 107) <|
                .splitExp 1 4
                  (.step (.grow 1 11) <|
                  .missing 1 71)
                  (.reject)))))
          (.step (.primeLo 3 113) <|
          .step (.dropHi 4 74) <|
          .step (.xHi 73) <|
          .splitBase 3 133
            (.step (.primeHi 3 131) <|
            .step (.dropLo 4 65) <|
            .splitBase 3 121
              (.step (.primeHi 3 113) <|
              .step (.dropLo 4 71) <|
              .step (.xLo 73) <|
              .missing 4 37)
              (.step (.primeLo 3 127) <|
              .step (.dropHi 4 69) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 4 67) <|
                .step (.xLo 69) <|
                .missing 4 7)))
            (.step (.primeLo 3 137) <|
            .step (.dropHi 4 66) <|
            .step (.xHi 65) <|
            .splitBase 3 147
              (.step (.primeHi 3 139) <|
              .step (.dropLo 4 63) <|
              .step (.xLo 65) <|
              .missing 4 11)
              (.step (.primeLo 3 149) <|
              .step (.dropHi 4 64) <|
              .step (.xHi 61) <|
              .missing 4 31)))))
      (.use 1))

private def deficientFour5Part004Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,33,0,1,1⟩], 1, deficientFour5Part002⟩,
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,33,97,1,1⟩], 1, deficientFour5Part003⟩]

theorem deficientFour5Part004 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,82,0,2,0⟩, ⟨true,33,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part004Tree deficientFour5Part004Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
