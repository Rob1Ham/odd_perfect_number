module

public import OddPerfect.DeficientTree

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart000Tree : Tree :=
  .step (.dropLo 2 12) <|
  .step (.dropLo 3 16) <|
  .step (.dropLo 4 142) <|
  .step (.primeLo 2 13) <|
  .step (.primeLo 3 17) <|
  .step (.xLo 145) <|
  .splitBase 3 17
    (.step (.dropLo 4 1766) <|
    .step (.xLo 1769) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.xLo 1793) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.xLo 1881) <|
        .splitExp 2 2
          (.step (.grow 2 61) <|
          .step (.dropHi 4 2757) <|
          .step (.xLo 12749) <|
          .reject)
          (.step (.dropLo 4 8792) <|
          .step (.xLo 9405) <|
          .splitExp 3 2
            (.step (.grow 3 307) <|
            .reject)
            (.reject)))
        (.reject))
      (.reject))
    (.step (.primeLo 3 19) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 282) <|
      .step (.xLo 165) <|
      .step (.xHi 253) <|
      .splitExp 1 2
        (.reject)
        (.step (.dropLo 4 238) <|
        .step (.xLo 253) <|
        .missing 4 127))
      (.step (.dropLo 4 294) <|
      .step (.xLo 297) <|
      .splitExp 1 2
        (.step (.dropHi 4 427) <|
        .step (.xHi 425) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 334) <|
          .step (.xLo 337) <|
          .splitExp 2 2
            (.missing 2 61)
            (.step (.dropLo 4 394) <|
            .step (.xLo 397) <|
            .splitExp 3 2
              (.missing 3 127)
              (.step (.dropLo 4 418) <|
              .step (.xLo 421) <|
              .splitExp 0 8
                (.missing 0 757)
                (.reject)))))
        (.step (.dropLo 4 1854) <|
        .step (.xLo 1857) <|
        .splitExp 0 6
          (.step (.grow 0 1093) <|
          .step (.xLo 5465) <|
          .splitExp 2 2
            (.step (.grow 2 61) <|
            .reject)
            (.step (.dropLo 4 11519) <|
            .step (.xLo 14209) <|
            .splitExp 3 2
              (.step (.grow 3 127) <|
              .step (.dropHi 4 40617) <|
              .step (.xLo 416433) <|
              .reject)
              (.reject)))
          (.step (.dropLo 4 7528) <|
          .step (.xLo 7529) <|
          .splitExp 2 2
            (.step (.grow 2 61) <|
            .step (.xLo 7625) <|
            .splitExp 3 2
              (.step (.grow 3 127) <|
              .step (.dropHi 4 44370) <|
              .step (.xLo 23241) <|
              .step (.xHi 23241) <|
              .splitExp 1 4
                (.reject)
                (.splitExp 0 8
                  (.missing 0 757)
                  (.reject)))
              (.reject))
            (.reject)))))

theorem deficientFourPowerGeneralPart000 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,25,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart000Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart001Tree : Tree :=
  .step (.primeLo 3 53) <|
  .step (.dropHi 4 314) <|
  .step (.xHi 313) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 4 89) <|
    .step (.xLo 93) <|
    .reject)
    (.step (.dropLo 4 108) <|
    .step (.xLo 109) <|
    .splitBase 3 61
      (.step (.dropLo 4 154) <|
      .step (.xLo 157) <|
      .splitBase 3 55
        (.step (.primeHi 3 53) <|
        .step (.dropLo 4 252) <|
        .step (.xLo 253) <|
        .splitExp 2 2
          (.step (.grow 2 61) <|
          .step (.dropHi 4 274) <|
          .step (.xLo 305) <|
          .reject)
          (.step (.dropLo 4 284) <|
          .step (.xLo 285) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 312) <|
            .step (.xLo 313) <|
            .missing 4 157)))
        (.step (.primeLo 3 59) <|
        .step (.dropHi 4 194) <|
        .step (.xHi 193) <|
        .splitExp 2 2
          (.step (.fix 2 61 3) <|
          .step (.dropHi 4 162) <|
          .step (.xHi 161) <|
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
            .step (.dropHi 4 175) <|
            .step (.xHi 173) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject)))))
      (.step (.primeLo 3 67) <|
      .step (.dropHi 4 139) <|
      .step (.xHi 137) <|
      .splitBase 3 69
        (.step (.primeHi 3 67) <|
        .step (.dropLo 4 125) <|
        .splitExp 2 2
          (.missing 2 61)
          (.step (.dropLo 4 133) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject)))
        (.step (.primeLo 3 71) <|
        .step (.dropHi 4 124) <|
        .step (.xHi 121) <|
        .splitExp 2 2
          (.missing 2 61)
          (.step (.dropLo 4 114) <|
          .step (.xLo 117) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .step (.fix 1 71 3) <|
            .step (.dropLo 4 119) <|
            .step (.dropHi 4 119) <|
            .reject)
            (.step (.dropLo 3 72) <|
            .step (.dropLo 4 118) <|
            .step (.primeLo 3 73) <|
            .step (.xLo 121) <|
            .missing 4 61)))))

theorem deficientFourPowerGeneralPart001 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,50,73,2,0⟩, ⟨true,61,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart001Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart002Tree : Tree :=
  .step (.dropLo 4 124) <|
  .step (.xLo 169) <|
  .step (.dropHi 3 967) <|
  .splitBase 3 277
    (.step (.dropLo 4 226) <|
    .step (.xLo 273) <|
    .splitBase 3 205
      (.step (.primeHi 3 199) <|
      .step (.dropLo 4 333) <|
      .step (.xLo 377) <|
      .splitBase 3 179
        (.step (.dropLo 4 410) <|
        .step (.xLo 429) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.step (.dropLo 4 591) <|
          .step (.xLo 637) <|
          .splitBase 3 169
            (.step (.primeHi 3 167) <|
            .step (.dropLo 4 776) <|
            .step (.xLo 793) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 4 1018) <|
              .step (.xLo 1053) <|
              .step (.dropHi 3 166) <|
              .step (.primeHi 3 163) <|
              .step (.dropLo 4 1199) <|
              .step (.xLo 1209) <|
              .splitExp 1 6
                (.reject)
                (.reject)))
            (.step (.primeLo 3 173) <|
            .step (.dropHi 4 854) <|
            .step (.xHi 845) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 4 722) <|
              .step (.xLo 741) <|
              .step (.dropHi 3 178) <|
              .step (.primeHi 3 173) <|
              .step (.dropLo 4 840) <|
              .step (.xLo 845) <|
              .missing 4 47))))
        (.step (.primeLo 3 181) <|
        .step (.dropHi 4 700) <|
        .step (.xHi 689) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.step (.dropLo 4 443) <|
          .step (.xLo 481) <|
          .splitBase 3 189
            (.step (.primeHi 3 181) <|
            .step (.dropLo 4 570) <|
            .step (.xLo 585) <|
            .splitExp 1 4
              (.missing 1 71)
              (.reject))
            (.step (.primeLo 3 191) <|
            .step (.dropHi 4 582) <|
            .step (.xHi 533) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 3 196) <|
              .step (.dropLo 4 513) <|
              .step (.primeLo 3 197) <|
              .step (.xLo 533) <|
              .missing 4 89)))))
      (.step (.primeLo 3 211) <|
      .step (.dropHi 4 451) <|
      .step (.xHi 429) <|
      .splitBase 3 239
        (.splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.step (.dropLo 4 322) <|
          .step (.xLo 325) <|
          .splitBase 3 223
            (.step (.dropLo 4 357) <|
            .step (.xLo 377) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 3 215) <|
              .step (.dropLo 4 401) <|
              .step (.primeLo 3 223) <|
              .step (.xLo 429) <|
              .missing 4 43))
            (.step (.primeLo 3 227) <|
            .step (.dropHi 4 392) <|
            .step (.xHi 377) <|
            .splitExp 1 4
              (.missing 1 71)
              (.step (.dropLo 3 231) <|
              .step (.dropLo 4 358) <|
              .step (.primeLo 3 233) <|
              .step (.xLo 377) <|
              .missing 4 7))))
        (.step (.primeLo 3 241) <|
        .step (.dropHi 4 356) <|
        .step (.xHi 325) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.splitBase 3 257
            (.step (.dropLo 4 294) <|
            .step (.xLo 325) <|
            .missing 4 163)
            (.step (.primeLo 3 263) <|
            .step (.dropHi 4 317) <|
            .step (.xHi 273) <|
            .missing 4 137)))))
    (.step (.primeLo 3 281) <|
    .step (.dropHi 4 294) <|
    .step (.xHi 273) <|
    .splitBase 3 435
      (.step (.primeHi 3 433) <|
      .step (.dropLo 4 175) <|
      .step (.xLo 221) <|
      .step (.dropHi 3 411) <|
      .step (.primeHi 3 409) <|
      .splitBase 3 333
        (.step (.primeHi 3 331) <|
        .splitExp 2 2
          (.step (.grow 2 7) <|
          .missing 2 19)
          (.step (.dropLo 4 234) <|
          .step (.xLo 273) <|
          .missing 4 137))
        (.step (.primeLo 3 337) <|
        .step (.dropHi 4 250) <|
        .step (.xHi 221) <|
        .missing 4 37))
      (.step (.primeLo 3 439) <|
      .step (.dropHi 4 213) <|
      .step (.xHi 169) <|
      .missing 4 17))

theorem deficientFourPowerGeneralPart002 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,4,0⟩, ⟨false,11,11,2,0⟩, ⟨false,163,0,2,0⟩, ⟨true,65,1209,5,0⟩] : Vector Slot 5) 13 :=
  Tree.sound deficientFourPowerGeneralPart002Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart003Tree : Tree :=
  .step (.dropLo 4 41) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 4 57) <|
    .step (.xLo 93) <|
    .reject)
    (.step (.dropLo 4 60) <|
    .step (.xLo 61) <|
    .splitBase 3 105
      (.step (.primeHi 3 103) <|
      .step (.dropLo 4 75) <|
      .step (.xLo 77) <|
      .splitBase 3 89
        (.step (.dropLo 4 85) <|
        .splitBase 3 83
          (.step (.dropLo 4 92) <|
          .step (.xLo 93) <|
          .splitBase 3 79
            (.step (.dropLo 4 97) <|
            .splitExp 2 2
              (.missing 2 61)
              (.step (.dropLo 4 102) <|
              .step (.xLo 105) <|
              .missing 4 53))
            (.step (.primeLo 3 83) <|
            .step (.dropHi 4 99) <|
            .step (.xHi 97) <|
            .splitExp 2 2
              (.missing 2 61)
              (.step (.dropLo 4 96) <|
              .step (.xLo 97) <|
              .missing 4 7)))
          (.step (.primeLo 3 89) <|
          .step (.dropHi 4 91) <|
          .step (.xHi 89) <|
          .splitExp 2 2
            (.missing 2 61)
            (.reject)))
        (.step (.primeLo 3 97) <|
        .step (.dropHi 4 84) <|
        .step (.xHi 81) <|
        .splitExp 2 2
          (.missing 2 61)
          (.step (.dropLo 3 99) <|
          .step (.dropLo 4 78) <|
          .step (.primeLo 3 101) <|
          .step (.xLo 81) <|
          .missing 4 41)))
      (.step (.primeLo 3 107) <|
      .step (.dropHi 4 78) <|
      .step (.xHi 77) <|
      .splitBase 3 127
        (.step (.dropLo 4 66) <|
        .step (.xLo 69) <|
        .splitBase 3 115
          (.step (.primeHi 3 113) <|
          .step (.dropLo 4 71) <|
          .step (.xLo 73) <|
          .splitExp 2 2
            (.missing 2 61)
            (.splitBase 3 109
              (.step (.dropLo 4 75) <|
              .step (.xLo 77) <|
              .splitExp 1 4
                (.step (.grow 1 11) <|
                .missing 1 71)
                (.reject))
              (.step (.primeLo 3 113) <|
              .step (.dropHi 4 75) <|
              .step (.xHi 73) <|
              .missing 4 37)))
          (.step (.primeLo 3 127) <|
          .step (.dropHi 4 70) <|
          .step (.xHi 69) <|
          .missing 4 7))
        (.step (.primeLo 3 131) <|
        .step (.dropHi 4 69) <|
        .splitBase 3 141
          (.step (.primeHi 3 139) <|
          .step (.dropLo 4 63) <|
          .step (.xLo 65) <|
          .splitExp 2 2
            (.missing 2 61)
            (.splitBase 3 133
              (.step (.primeHi 3 131) <|
              .step (.dropLo 4 67) <|
              .step (.xLo 69) <|
              .missing 4 7)
              (.step (.primeLo 3 137) <|
              .step (.dropHi 4 67) <|
              .step (.xHi 65) <|
              .missing 4 11)))
          (.step (.primeLo 3 149) <|
          .step (.dropHi 4 65) <|
          .splitExp 2 2
            (.step (.grow 2 61) <|
            .step (.dropHi 4 63) <|
            .step (.xHi 61) <|
            .missing 4 31)
            (.step (.dropLo 4 62) <|
            .step (.xLo 65) <|
            .missing 4 11)))))

theorem deficientFourPowerGeneralPart003 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,79,157,2,0⟩, ⟨true,33,105,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart003Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart004Tree : Tree :=
  .step (.primeLo 2 13) <|
  .step (.dropHi 4 105) <|
  .splitBase 3 157
    (.use 0)
    (.step (.primeLo 3 163) <|
    .step (.dropHi 4 62) <|
    .step (.xHi 61) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 4 43) <|
      .step (.xLo 45) <|
      .splitBase 3 325
        (.step (.primeHi 3 317) <|
        .step (.dropLo 4 50) <|
        .step (.xLo 53) <|
        .step (.dropHi 3 314) <|
        .step (.primeHi 3 313) <|
        .splitBase 3 213
          (.step (.primeHi 3 211) <|
          .step (.dropLo 4 55) <|
          .step (.xLo 57) <|
          .splitBase 3 183
            (.step (.primeHi 3 181) <|
            .splitBase 3 171
              (.step (.primeHi 3 167) <|
              .step (.dropLo 4 59) <|
              .step (.xLo 61) <|
              .missing 4 31)
              (.step (.primeLo 3 173) <|
              .splitExp 2 2
                (.step (.grow 2 61) <|
                .step (.dropHi 4 59) <|
                .step (.xLo 61) <|
                .reject)
                (.step (.dropLo 4 59) <|
                .step (.xLo 61) <|
                .missing 4 31)))
            (.step (.primeLo 3 191) <|
            .step (.dropHi 4 59) <|
            .step (.xHi 57) <|
            .missing 4 29))
          (.step (.primeLo 3 223) <|
          .step (.dropHi 4 56) <|
          .step (.xHi 53) <|
          .step (.dropLo 3 252) <|
          .step (.primeLo 3 257) <|
          .splitBase 3 281
            (.splitExp 2 2
              (.missing 2 61)
              (.reject))
            (.step (.primeLo 3 283) <|
            .splitExp 2 2
              (.missing 2 61)
              (.step (.dropLo 3 285) <|
              .step (.primeLo 3 293) <|
              .splitExp 1 4
                (.missing 1 11)
                (.step (.dropLo 3 312) <|
                .step (.primeLo 3 313) <|
                .splitExp 1 6
                  (.reject)
                  (.reject))))))
        (.step (.primeLo 3 331) <|
        .step (.dropHi 4 52) <|
        .step (.xHi 49) <|
        .step (.dropLo 3 418) <|
        .step (.primeLo 3 419) <|
        .splitBase 3 837
          (.step (.primeHi 3 829) <|
          .step (.dropLo 4 46) <|
          .step (.xLo 49) <|
          .step (.dropHi 3 618) <|
          .step (.primeHi 3 617) <|
          .splitBase 3 499
            (.splitExp 2 2
              (.missing 2 61)
              (.reject))
            (.step (.primeLo 3 503) <|
            .splitExp 2 2
              (.missing 2 61)
              (.step (.dropLo 3 516) <|
              .step (.primeLo 3 521) <|
              .splitExp 1 4
                (.missing 1 11)
                (.step (.dropLo 3 613) <|
                .splitExp 1 6
                  (.step (.dropHi 3 614) <|
                  .step (.primeHi 3 613) <|
                  .reject)
                  (.reject)))))
          (.step (.primeLo 3 839) <|
          .step (.dropHi 4 48) <|
          .step (.xHi 45) <|
          .missing 4 23))))

private def deficientFourPowerGeneralPart004Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,79,157,2,0⟩, ⟨true,33,105,5,0⟩], 1, deficientFourPowerGeneralPart003⟩]

theorem deficientFourPowerGeneralPart004 : Closed (#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,12,13,2,0⟩, ⟨false,79,0,2,0⟩, ⟨true,33,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart004Tree deficientFourPowerGeneralPart004Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
