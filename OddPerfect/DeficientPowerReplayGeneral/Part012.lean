module

public import OddPerfect.DeficientPowerReplayGeneral.Part011

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart055Tree : Tree :=
  .step (.primeLo 3 97) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 4 632) <|
    .step (.xLo 93) <|
    .step (.xHi 589) <|
    .step (.dropHi 3 881) <|
    .splitBase 3 173
      (.splitBase 2 17
        (.step (.dropLo 4 95) <|
        .step (.xLo 217) <|
        .step (.dropHi 3 136) <|
        .step (.primeHi 3 131) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .reject)
          (.splitBase 3 111
            (.step (.primeHi 3 109) <|
            .step (.dropLo 4 295) <|
            .step (.xLo 341) <|
            .splitBase 3 101
              (.step (.dropLo 4 376) <|
              .step (.xLo 465) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitBase 3 97
                  (.step (.dropLo 4 544) <|
                  .step (.xLo 589) <|
                  .missing 4 59)
                  (.step (.primeLo 3 101) <|
                  .step (.dropHi 4 501) <|
                  .step (.xHi 465) <|
                  .missing 4 233)))
              (.step (.primeLo 3 103) <|
              .step (.dropHi 4 457) <|
              .step (.xHi 341) <|
              .missing 4 19))
            (.step (.primeLo 3 113) <|
            .step (.dropHi 4 327) <|
            .step (.xHi 217) <|
            .missing 4 109)))
        (.step (.primeLo 2 19) <|
        .step (.dropHi 3 130) <|
        .step (.dropHi 4 123) <|
        .step (.primeHi 3 127) <|
        .step (.xHi 93) <|
        .missing 4 47))
      (.step (.primeLo 3 179) <|
      .step (.dropHi 2 18) <|
      .step (.dropHi 4 158) <|
      .step (.primeHi 2 17) <|
      .step (.xHi 93) <|
      .missing 4 47))
    (.step (.dropLo 4 66) <|
    .step (.xLo 69) <|
    .splitBase 3 193
      (.step (.dropLo 4 101) <|
      .splitBase 2 17
        (.step (.dropLo 3 117) <|
        .step (.dropLo 4 297) <|
        .step (.primeLo 3 127) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 7551) <|
          .step (.xHi 7513) <|
          .splitBase 3 153
            (.use 0)
            (.step (.primeLo 3 157) <|
            .step (.dropHi 4 607) <|
            .step (.xHi 605) <|
            .splitBase 3 173
              (.step (.dropLo 4 362) <|
              .step (.xLo 385) <|
              .splitBase 3 163
                (.step (.dropLo 4 415) <|
                .step (.xLo 429) <|
                .splitExp 1 4
                  (.missing 1 71)
                  (.step (.dropLo 4 476) <|
                  .step (.xLo 517) <|
                  .splitExp 2 2
                    (.missing 2 307)
                    (.step (.dropLo 4 527) <|
                    .step (.xLo 561) <|
                    .step (.dropHi 3 160) <|
                    .step (.primeHi 3 157) <|
                    .step (.dropLo 4 602) <|
                    .step (.xLo 605) <|
                    .missing 4 101)))
                (.step (.primeLo 3 167) <|
                .step (.dropHi 4 492) <|
                .step (.xHi 473) <|
                .splitExp 1 4
                  (.missing 1 71)
                  (.step (.dropLo 4 407) <|
                  .step (.xLo 429) <|
                  .splitExp 2 2
                    (.missing 2 307)
                    (.step (.dropLo 3 169) <|
                    .step (.dropLo 4 444) <|
                    .step (.primeLo 3 173) <|
                    .step (.xLo 473) <|
                    .missing 4 79))))
              (.step (.primeLo 3 179) <|
              .step (.dropHi 4 411) <|
              .step (.xHi 385) <|
              .splitExp 1 4
                (.missing 1 71)
                (.step (.dropLo 4 327) <|
                .step (.xLo 341) <|
                .splitBase 3 185
                  (.step (.primeHi 3 181) <|
                  .step (.dropLo 4 368) <|
                  .step (.xLo 385) <|
                  .missing 4 193)
                  (.step (.primeLo 3 191) <|
                  .step (.dropHi 4 359) <|
                  .step (.xHi 341) <|
                  .missing 4 19)))))
          (.reject))
        (.use 1))
      (.use 2))

private def deficientFourPowerGeneralPart055Refs : List Known := [
  ⟨#v[⟨false,3,3,4,4⟩, ⟨false,5,5,4,0⟩, ⟨false,17,17,2,0⟩, ⟨false,127,153,2,0⟩, ⟨true,297,7513,5,0⟩], 11, deficientFourPowerGeneralPart016⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,18,19,2,0⟩, ⟨false,97,193,2,0⟩, ⟨true,101,0,5,0⟩], 1, deficientFourPowerGeneralPart022⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,194,0,2,0⟩, ⟨true,69,0,5,0⟩], 1, deficientFourPowerGeneralPart054⟩]

theorem deficientFourPowerGeneralPart055 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,94,0,2,0⟩, ⟨true,45,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart055Tree deficientFourPowerGeneralPart055Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart056Tree : Tree :=
  .step (.primeHi 2 19) <|
  .step (.dropLo 3 44) <|
  .step (.dropLo 4 44) <|
  .step (.primeLo 3 47) <|
  .step (.xLo 45) <|
  .splitBase 3 93
    (.step (.primeHi 3 89) <|
    .step (.dropLo 4 87) <|
    .step (.xLo 89) <|
    .splitExp 1 2
      (.step (.grow 1 31) <|
      .step (.xLo 93) <|
      .splitBase 3 61
        (.step (.dropLo 4 160) <|
        .step (.xLo 217) <|
        .splitBase 2 17
          (.reject)
          (.step (.primeLo 2 19) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 56) <|
            .step (.dropHi 4 892) <|
            .step (.primeHi 3 53) <|
            .step (.xLo 341) <|
            .step (.xHi 341) <|
            .step (.dropLo 3 50) <|
            .step (.dropHi 3 51) <|
            .step (.primeLo 3 53) <|
            .reject)
            (.step (.dropLo 3 52) <|
            .step (.dropLo 4 387) <|
            .step (.primeLo 3 53) <|
            .step (.xLo 465) <|
            .splitBase 3 55
              (.step (.primeHi 3 53) <|
              .step (.dropLo 4 15349) <|
              .step (.xLo 15469) <|
              .splitExp 0 6
                (.step (.grow 0 1093) <|
                .step (.xLo 101649) <|
                .splitExp 2 2
                  (.step (.grow 2 127) <|
                  .reject)
                  (.reject))
                (.reject))
              (.step (.primeLo 3 59) <|
              .step (.dropHi 4 710) <|
              .step (.xHi 589) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitBase 3 59
                  (.reject)
                  (.step (.primeLo 3 61) <|
                  .step (.dropHi 4 507) <|
                  .step (.xHi 465) <|
                  .missing 4 233))))))
        (.step (.primeLo 3 67) <|
        .splitBase 2 17
          (.step (.dropLo 4 201) <|
          .step (.xLo 217) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 87) <|
            .step (.dropHi 4 969) <|
            .step (.primeHi 3 83) <|
            .step (.xLo 341) <|
            .step (.xHi 341) <|
            .missing 4 19)
            (.step (.dropLo 3 79) <|
            .step (.dropLo 4 764) <|
            .step (.xLo 837) <|
            .splitBase 3 83
              (.step (.dropLo 4 2052) <|
              .step (.xLo 2077) <|
              .splitBase 3 79
                (.reject)
                (.step (.primeLo 3 83) <|
                .splitExp 0 6
                  (.step (.grow 0 1093) <|
                  .step (.dropHi 4 3545) <|
                  .step (.xLo 101649) <|
                  .reject)
                  (.step (.dropLo 4 12372) <|
                  .step (.xLo 12493) <|
                  .splitExp 2 2
                    (.step (.grow 2 307) <|
                    .step (.dropHi 4 35370) <|
                    .step (.xLo 47585) <|
                    .reject)
                    (.reject))))
              (.step (.primeLo 3 89) <|
              .step (.dropHi 4 1547) <|
              .step (.xHi 1457) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 1108) <|
                .step (.xLo 1209) <|
                .splitExp 2 2
                  (.missing 2 307)
                  (.step (.dropLo 4 1430) <|
                  .step (.xLo 1457) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.reject))))))
          (.step (.primeLo 2 19) <|
          .step (.dropHi 4 289) <|
          .step (.xHi 217) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 69) <|
            .step (.dropLo 4 128) <|
            .step (.primeLo 3 71) <|
            .step (.xLo 217) <|
            .missing 4 109))))
      (.use 0))
    (.use 1)

private def deficientFourPowerGeneralPart056Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,17,19,2,0⟩, ⟨false,47,89,2,0⟩, ⟨true,89,0,5,0⟩], 1, deficientFourPowerGeneralPart015⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,94,0,2,0⟩, ⟨true,45,0,5,0⟩], 1, deficientFourPowerGeneralPart055⟩]

theorem deficientFourPowerGeneralPart056 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,21,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,25,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart056Tree deficientFourPowerGeneralPart056Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart057Tree : Tree :=
  .step (.primeHi 2 23) <|
  .step (.dropLo 4 75) <|
  .step (.xLo 77) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 4 292) <|
    .step (.xLo 93) <|
    .step (.xHi 217) <|
    .splitBase 3 45
      (.step (.primeHi 3 43) <|
      .step (.dropLo 4 114) <|
      .step (.xLo 217) <|
      .missing 4 109)
      (.step (.primeLo 3 47) <|
      .step (.dropHi 4 151) <|
      .step (.xHi 93) <|
      .step (.fix 4 47 3) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject)))
    (.step (.dropLo 4 179) <|
    .step (.xLo 181) <|
    .splitBase 3 45
      (.step (.primeHi 3 43) <|
      .step (.dropLo 4 913) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .splitBase 3 41
          (.reject)
          (.step (.primeLo 3 43) <|
          .step (.dropHi 4 1471) <|
          .step (.xHi 1441) <|
          .splitExp 1 4
            (.missing 1 71)
            (.step (.dropLo 4 1270) <|
            .step (.xLo 1309) <|
            .splitExp 2 2
              (.step (.grow 2 7) <|
              .missing 2 79)
              (.step (.dropLo 4 1417) <|
              .step (.xLo 1441) <|
              .missing 4 7))))
        (.reject))
      (.step (.primeLo 3 47) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 4 370) <|
        .step (.xLo 209) <|
        .step (.xHi 341) <|
        .step (.dropHi 3 52) <|
        .step (.primeHi 3 47) <|
        .step (.dropLo 4 321) <|
        .step (.xLo 341) <|
        .missing 4 19)
        (.step (.dropLo 3 48) <|
        .step (.dropLo 4 525) <|
        .step (.primeLo 3 53) <|
        .step (.dropHi 4 963) <|
        .step (.xHi 961) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 667) <|
          .step (.xLo 669) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .step (.grow 1 71) <|
            .step (.dropHi 4 736) <|
            .step (.xLo 781) <|
            .reject)
            (.step (.dropLo 4 840) <|
            .step (.xLo 841) <|
            .splitExp 2 2
              (.step (.grow 2 7) <|
              .missing 2 79)
              (.step (.dropLo 4 902) <|
              .step (.xLo 905) <|
              .splitExp 0 8
                (.step (.grow 0 13) <|
                .missing 0 757)
                (.step (.dropLo 4 940) <|
                .step (.xLo 941) <|
                .splitExp 1 6
                  (.step (.dropHi 4 951) <|
                  .step (.xHi 949) <|
                  .splitExp 3 2
                    (.step (.grow 3 7) <|
                    .missing 3 409)
                    (.step (.dropLo 4 946) <|
                    .step (.xLo 949) <|
                    .missing 4 19))
                  (.step (.dropLo 4 951) <|
                  .step (.xLo 953) <|
                  .splitExp 3 2
                    (.missing 3 7)
                    (.step (.dropLo 4 957) <|
                    .splitExp 0 10
                      (.step (.dropHi 4 958) <|
                      .step (.xHi 957) <|
                      .missing 4 479)
                      (.reject))))))))))

theorem deficientFourPowerGeneralPart057 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,25,2,0⟩, ⟨false,41,53,2,0⟩, ⟨true,41,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart057Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart058Tree : Tree :=
  .step (.dropLo 4 58) <|
  .step (.xLo 61) <|
  .splitBase 3 45
    (.step (.primeHi 3 43) <|
    .step (.dropLo 4 79) <|
    .step (.xLo 81) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 113) <|
      .step (.xLo 121) <|
      .reject)
      (.step (.dropLo 4 111) <|
      .step (.xLo 113) <|
      .splitBase 2 29
        (.step (.dropLo 4 148) <|
        .step (.xLo 149) <|
        .splitBase 3 41
          (.step (.dropLo 4 179) <|
          .step (.xLo 181) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 193) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 205) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 207) <|
                .step (.xLo 209) <|
                .missing 4 7))))
          (.step (.primeLo 3 43) <|
          .step (.dropHi 4 169) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 158) <|
            .step (.xLo 161) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 166) <|
              .step (.xLo 169) <|
              .missing 4 17))))
        (.step (.primeLo 2 31) <|
        .step (.dropHi 4 142) <|
        .step (.xHi 141) <|
        .splitBase 3 41
          (.step (.dropLo 4 127) <|
          .step (.xLo 129) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 134) <|
            .step (.xLo 137) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 140) <|
              .step (.xLo 141) <|
              .missing 4 71)))
          (.step (.primeLo 3 43) <|
          .step (.dropHi 4 122) <|
          .step (.xHi 121) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 116) <|
            .step (.xLo 117) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 120) <|
              .step (.xLo 121) <|
              .missing 4 61))))))
    (.step (.primeLo 3 47) <|
    .step (.dropHi 4 126) <|
    .step (.xHi 125) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 83) <|
      .step (.xLo 77) <|
      .step (.xHi 77) <|
      .missing 4 13)
      (.step (.dropLo 4 74) <|
      .step (.xLo 77) <|
      .splitBase 3 49
        (.step (.primeHi 3 47) <|
        .step (.dropLo 4 90) <|
        .step (.xLo 93) <|
        .splitBase 2 29
          (.step (.dropLo 4 114) <|
          .step (.xLo 117) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 120) <|
            .step (.xLo 121) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 124) <|
              .step (.xLo 125) <|
              .missing 4 7)))
          (.step (.primeLo 2 31) <|
          .step (.dropHi 4 98) <|
          .step (.xHi 97) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 94) <|
            .step (.xLo 97) <|
            .missing 4 7)))
        (.step (.primeLo 3 53) <|
        .step (.dropHi 4 96) <|
        .step (.xHi 93) <|
        .splitBase 2 29
          (.step (.dropLo 4 89) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 92) <|
            .step (.xLo 93) <|
            .missing 4 47))
          (.step (.primeLo 2 31) <|
          .step (.dropHi 4 79) <|
          .step (.xHi 77) <|
          .missing 4 13))))

theorem deficientFourPowerGeneralPart058 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,41,53,2,0⟩, ⟨true,41,209,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart058Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart059Tree : Tree :=
  .step (.primeHi 2 23) <|
  .step (.dropLo 4 51) <|
  .step (.xLo 53) <|
  .splitExp 1 2
    (.step (.grow 1 31) <|
    .step (.dropHi 4 91) <|
    .step (.xLo 93) <|
    .reject)
    (.step (.dropLo 4 84) <|
    .step (.xLo 85) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 141) <|
      .step (.xLo 121) <|
      .step (.xHi 121) <|
      .step (.fix 4 61 3) <|
      .reject)
      (.step (.dropLo 4 122) <|
      .step (.xLo 125) <|
      .splitBase 3 67
        (.step (.dropLo 4 169) <|
        .splitBase 3 61
          (.step (.dropLo 4 226) <|
          .step (.xLo 229) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 249) <|
            .splitBase 3 59
              (.step (.dropLo 4 290) <|
              .step (.xLo 293) <|
              .splitExp 1 4
                (.step (.grow 1 11) <|
                .missing 1 71)
                (.step (.dropLo 4 318) <|
                .step (.xLo 321) <|
                .splitExp 2 2
                  (.step (.grow 2 7) <|
                  .missing 2 79)
                  (.step (.dropLo 4 327) <|
                  .step (.xLo 329) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 4 332) <|
                    .step (.xLo 333) <|
                    .missing 4 167))))
              (.step (.primeLo 3 61) <|
              .step (.dropHi 4 281) <|
              .splitExp 1 4
                (.step (.grow 1 11) <|
                .missing 1 71)
                (.step (.dropLo 4 270) <|
                .step (.xLo 273) <|
                .splitExp 2 2
                  (.step (.grow 2 7) <|
                  .missing 2 79)
                  (.step (.dropLo 4 276) <|
                  .step (.xLo 277) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 4 279) <|
                    .step (.xLo 281) <|
                    .missing 4 47))))))
          (.step (.primeLo 3 67) <|
          .step (.dropHi 4 198) <|
          .step (.xHi 197) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 182) <|
            .step (.xLo 185) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 192) <|
              .step (.xLo 193) <|
              .splitExp 2 2
                (.missing 2 7)
                (.step (.dropLo 4 195) <|
                .step (.xLo 197) <|
                .missing 4 11)))))
        (.step (.primeLo 3 71) <|
        .step (.dropHi 4 169) <|
        .splitBase 3 73
          (.step (.dropLo 4 140) <|
          .step (.xLo 141) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 148) <|
            .step (.xLo 149) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .step (.fix 1 71 3) <|
              .step (.dropLo 4 157) <|
              .step (.dropHi 4 161) <|
              .step (.xLo 165) <|
              .reject)
              (.step (.dropLo 4 155) <|
              .step (.xLo 157) <|
              .splitBase 3 71
                (.step (.dropLo 4 165) <|
                .splitExp 2 2
                  (.missing 2 7)
                  (.step (.dropLo 4 168) <|
                  .step (.xLo 169) <|
                  .missing 4 17))
                (.step (.primeLo 3 73) <|
                .step (.dropHi 4 159) <|
                .step (.xHi 157) <|
                .missing 4 79))))
          (.step (.primeLo 3 79) <|
          .step (.dropHi 4 136) <|
          .step (.xHi 133) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 128) <|
            .step (.xLo 129) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject))))))

theorem deficientFourPowerGeneralPart059 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,25,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,33,333,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart059Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
