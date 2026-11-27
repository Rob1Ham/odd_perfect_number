module

public import OddPerfect.DeficientPowerReplayGeneral.Part002

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart010Tree : Tree :=
  .step (.primeLo 3 97) <|
  .step (.dropHi 4 36) <|
  .step (.xHi 33) <|
  .splitBase 2 11
    (.step (.dropLo 4 22) <|
    .step (.xLo 25) <|
    .splitBase 3 193
      (.splitExp 0 4
        (.step (.dropHi 4 31) <|
        .step (.xHi 29) <|
        .splitBase 3 129
          (.step (.primeHi 3 127) <|
          .step (.dropLo 4 26) <|
          .step (.xLo 29) <|
          .missing 4 5)
          (.step (.primeLo 3 131) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 4 26) <|
            .step (.xLo 29) <|
            .missing 4 5)))
        (.step (.dropLo 4 27) <|
        .step (.xLo 29) <|
        .splitBase 3 129
          (.step (.primeHi 3 127) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 3 115) <|
            .step (.dropLo 4 32) <|
            .step (.primeLo 3 127) <|
            .step (.xLo 33) <|
            .missing 4 17))
          (.step (.primeLo 3 131) <|
          .splitExp 1 2
            (.missing 1 19)
            (.splitBase 3 155
              (.step (.primeHi 3 151) <|
              .step (.dropLo 4 30) <|
              .step (.xLo 33) <|
              .missing 4 17)
              (.step (.primeLo 3 157) <|
              .step (.dropHi 4 31) <|
              .step (.xHi 29) <|
              .missing 4 5)))))
      (.step (.primeLo 3 197) <|
      .step (.dropHi 4 30) <|
      .step (.xHi 29) <|
      .splitExp 0 4
        (.step (.dropHi 3 657) <|
        .step (.dropHi 4 27) <|
        .step (.primeHi 3 653) <|
        .step (.xHi 25) <|
        .missing 4 13)
        (.splitBase 3 393
          (.step (.primeHi 3 389) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 3 227) <|
            .step (.dropLo 4 27) <|
            .step (.xLo 29) <|
            .missing 4 5))
          (.step (.primeLo 3 397) <|
          .step (.dropHi 4 28) <|
          .step (.xHi 25) <|
          .missing 4 13))))
    (.step (.primeLo 2 13) <|
    .step (.dropHi 4 23) <|
    .step (.xHi 21) <|
    .splitBase 3 193
      (.step (.dropLo 4 18) <|
      .step (.xLo 21) <|
      .missing 4 11)
      (.step (.primeLo 3 197) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 3 393
          (.step (.primeHi 3 389) <|
          .step (.dropLo 4 18) <|
          .step (.xLo 21) <|
          .missing 4 11)
          (.step (.primeLo 3 397) <|
          .step (.dropHi 4 20) <|
          .step (.xHi 17) <|
          .reject))))

theorem deficientFourPowerGeneralPart010 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,94,0,2,0⟩, ⟨true,17,57,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart010Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart011Tree : Tree :=
  .step (.primeLo 1 7) <|
  .splitExp 0 2
    (.step (.dropHi 4 32) <|
    .step (.xHi 29) <|
    .splitBase 3 45
      (.step (.primeHi 3 43) <|
      .step (.dropLo 4 14) <|
      .step (.xLo 17) <|
      .step (.fix 0 13 2) <|
      .step (.dropHi 3 33) <|
      .step (.dropHi 4 21) <|
      .step (.primeHi 3 31) <|
      .splitBase 3 25
        (.step (.primeHi 3 23) <|
        .step (.dropLo 4 20) <|
        .step (.xLo 21) <|
        .missing 4 11)
        (.step (.primeLo 3 29) <|
        .step (.dropHi 4 18) <|
        .step (.xHi 17) <|
        .splitExp 1 2
          (.missing 1 19)
          (.reject)))
      (.step (.primeLo 3 47) <|
      .step (.dropHi 4 18) <|
      .step (.xHi 17) <|
      .splitBase 3 93
        (.step (.primeHi 3 89) <|
        .splitBase 2 11
          (.step (.grow 0 13) <|
          .step (.dropLo 3 53) <|
          .step (.dropLo 4 15) <|
          .step (.xLo 65) <|
          .reject)
          (.step (.primeLo 2 13) <|
          .step (.dropHi 4 14) <|
          .step (.xHi 13) <|
          .step (.dropLo 3 69) <|
          .step (.primeLo 3 71) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 3 85) <|
            .step (.primeLo 3 89) <|
            .splitExp 2 2
              (.missing 2 61)
              (.reject))))
        (.step (.primeLo 3 97) <|
        .step (.dropHi 2 12) <|
        .step (.dropHi 4 15) <|
        .step (.primeHi 2 11) <|
        .step (.xHi 13) <|
        .step (.grow 0 13) <|
        .reject)))
    (.step (.dropLo 4 16) <|
    .step (.xLo 17) <|
    .splitBase 3 45
      (.use 0)
      (.step (.primeLo 3 47) <|
      .step (.dropHi 4 60) <|
      .step (.xHi 57) <|
      .splitBase 3 93
        (.step (.primeHi 3 89) <|
        .step (.dropLo 4 20) <|
        .step (.xLo 21) <|
        .splitBase 2 11
          (.use 1)
          (.step (.primeLo 2 13) <|
          .step (.dropHi 4 31) <|
          .step (.xHi 29) <|
          .splitBase 3 61
            (.step (.dropLo 4 22) <|
            .step (.xLo 25) <|
            .splitExp 0 4
              (.missing 0 11)
              (.splitBase 3 53
                (.step (.dropLo 4 26) <|
                .step (.xLo 29) <|
                .missing 4 5)
                (.step (.primeLo 3 59) <|
                .step (.dropHi 4 27) <|
                .step (.xHi 25) <|
                .reject)))
            (.step (.primeLo 3 67) <|
            .step (.dropHi 4 26) <|
            .step (.xHi 25) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 4 22) <|
              .step (.xLo 25) <|
              .step (.dropHi 3 79) <|
              .splitExp 1 2
                (.missing 1 19)
                (.step (.dropLo 3 73) <|
                .splitBase 3 75
                  (.step (.primeHi 3 73) <|
                  .reject)
                  (.step (.primeLo 3 79) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.splitExp 2 2
                      (.missing 2 61)
                      (.splitExp 1 4
                        (.splitExp 0 8
                          (.missing 0 757)
                          (.reject))
                        (.reject)))))))))
        (.use 2)))

private def deficientFourPowerGeneralPart011Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,45,2,0⟩, ⟨true,17,0,5,0⟩], 1, deficientFourPowerGeneralPart008⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,47,89,2,0⟩, ⟨true,21,57,5,0⟩], 1, deficientFourPowerGeneralPart009⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,94,0,2,0⟩, ⟨true,17,57,5,0⟩], 1, deficientFourPowerGeneralPart010⟩]

theorem deficientFourPowerGeneralPart011 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,6,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,13,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart011Tree deficientFourPowerGeneralPart011Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart012Tree : Tree :=
  .step (.primeLo 3 23) <|
  .splitBase 2 9
    (.step (.primeHi 2 7) <|
    .step (.primeHi 1 5) <|
    .reject)
    (.step (.primeLo 2 11) <|
    .splitBase 1 5
      (.step (.dropLo 3 33) <|
      .step (.dropLo 4 33) <|
      .step (.primeLo 3 37) <|
      .splitExp 0 2
        (.splitBase 3 73
          (.step (.dropLo 4 59) <|
          .step (.xLo 61) <|
          .splitBase 2 11
            (.step (.grow 0 13) <|
            .step (.dropLo 3 63) <|
            .step (.dropLo 4 510) <|
            .step (.primeLo 3 67) <|
            .step (.xLo 533) <|
            .splitExp 1 2
              (.step (.grow 1 31) <|
              .step (.xLo 1209) <|
              .step (.dropHi 3 71) <|
              .splitExp 2 2
                (.step (.grow 2 7) <|
                .step (.grow 2 19) <|
                .step (.dropHi 3 67) <|
                .step (.dropHi 4 1399) <|
                .step (.xLo 160797) <|
                .reject)
                (.step (.dropLo 4 1212) <|
                .step (.xLo 2821) <|
                .step (.dropHi 3 68) <|
                .step (.primeHi 3 67) <|
                .reject))
              (.reject))
            (.step (.primeLo 2 13) <|
            .splitBase 3 49
              (.step (.primeHi 3 47) <|
              .step (.dropLo 4 108) <|
              .step (.xLo 109) <|
              .splitExp 1 2
                (.step (.grow 1 31) <|
                .step (.dropHi 4 349) <|
                .step (.xLo 217) <|
                .step (.xHi 341) <|
                .step (.dropHi 3 39) <|
                .step (.primeHi 3 37) <|
                .step (.dropLo 4 299) <|
                .step (.xLo 341) <|
                .missing 4 19)
                (.step (.dropLo 3 43) <|
                .step (.dropLo 4 660) <|
                .step (.xLo 661) <|
                .splitBase 3 43
                  (.reject)
                  (.step (.primeLo 3 47) <|
                  .step (.dropHi 4 1370) <|
                  .step (.xHi 1369) <|
                  .splitExp 2 2
                    (.step (.grow 2 61) <|
                    .step (.dropHi 4 844) <|
                    .step (.xLo 793) <|
                    .step (.xHi 793) <|
                    .missing 4 397)
                    (.step (.dropLo 4 941) <|
                    .splitExp 1 4
                      (.step (.grow 1 11) <|
                      .missing 1 71)
                      (.step (.dropLo 4 1324) <|
                      .step (.xLo 1325) <|
                      .splitExp 1 6
                        (.step (.dropHi 4 1346) <|
                        .step (.xHi 1345) <|
                        .splitExp 3 2
                          (.missing 3 37)
                          (.step (.dropLo 4 1342) <|
                          .step (.xLo 1345) <|
                          .missing 4 673))
                        (.step (.dropLo 4 1346) <|
                        .step (.xLo 1349) <|
                        .splitExp 3 2
                          (.step (.grow 3 37) <|
                          .missing 3 61)
                          (.step (.dropLo 4 1364) <|
                          .step (.xLo 1365) <|
                          .splitExp 2 4
                            (.step (.dropHi 4 1365) <|
                            .missing 4 683)
                            (.reject))))))))
              (.use 0)))
          (.use 1))
        (.reject))
      (.use 2))

private def deficientFourPowerGeneralPart012Refs : List Known := [
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,50,73,2,0⟩, ⟨true,61,0,5,0⟩], 1, deficientFourPowerGeneralPart001⟩,
  ⟨#v[⟨false,3,3,2,2⟩, ⟨false,5,5,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,74,0,2,0⟩, ⟨true,33,0,5,0⟩], 1, deficientFourPowerGeneralPart005⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,6,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,23,0,2,0⟩, ⟨true,13,0,5,0⟩], 1, deficientFourPowerGeneralPart011⟩]

theorem deficientFourPowerGeneralPart012 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,22,0,2,0⟩, ⟨true,13,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart012Tree deficientFourPowerGeneralPart012Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart013Tree : Tree :=
  .step (.dropLo 4 113) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 4 1280) <|
    .step (.xLo 121) <|
    .step (.xHi 1265) <|
    .splitBase 3 33
      (.step (.primeHi 3 31) <|
      .step (.primeHi 2 29) <|
      .step (.dropLo 4 851) <|
      .step (.xLo 869) <|
      .splitExp 1 4
        (.missing 1 71)
        (.step (.dropLo 4 1151) <|
        .step (.xLo 1177) <|
        .splitExp 2 2
          (.missing 2 13)
          (.step (.dropLo 4 1208) <|
          .step (.xLo 1221) <|
          .splitExp 3 2
            (.missing 3 331)
            (.step (.dropLo 4 1259) <|
            .step (.xLo 1265) <|
            .missing 4 211))))
      (.step (.primeLo 3 37) <|
      .step (.dropHi 2 30) <|
      .step (.dropHi 4 162) <|
      .step (.primeHi 2 29) <|
      .step (.xHi 121) <|
      .missing 4 61))
    (.step (.dropLo 4 193) <|
    .splitBase 3 33
      (.step (.primeHi 3 31) <|
      .step (.primeHi 2 29) <|
      .reject)
      (.step (.primeLo 3 37) <|
      .step (.dropHi 4 488) <|
      .step (.xHi 485) <|
      .splitBase 2 29
        (.step (.dropLo 4 346) <|
        .step (.xLo 349) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 403) <|
          .step (.xLo 405) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 460) <|
            .step (.xLo 461) <|
            .splitExp 0 8
              (.step (.grow 0 13) <|
              .missing 0 757)
              (.step (.dropLo 4 470) <|
              .step (.xLo 473) <|
              .splitExp 2 2
                (.step (.grow 2 13) <|
                .missing 2 67)
                (.step (.dropLo 4 479) <|
                .step (.xLo 481) <|
                .splitExp 3 2
                  (.missing 3 7)
                  (.step (.dropLo 4 484) <|
                  .step (.xLo 485) <|
                  .splitExp 1 6
                    (.splitExp 0 10
                      (.missing 0 23)
                      (.reject))
                    (.reject)))))))
        (.step (.primeLo 2 31) <|
        .step (.dropHi 4 230) <|
        .step (.xHi 229) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 209) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 224) <|
            .step (.xLo 225) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 4 226) <|
              .step (.xLo 229) <|
              .missing 4 23))))))

theorem deficientFourPowerGeneralPart013 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,31,37,2,0⟩, ⟨true,61,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart013Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart014Tree : Tree :=
  .step (.dropLo 4 20) <|
  .step (.xLo 21) <|
  .splitExp 0 2
    (.step (.grow 0 13) <|
    .step (.xLo 65) <|
    .splitBase 2 21
      (.step (.primeHi 2 19) <|
      .splitBase 3 25
        (.step (.primeHi 3 23) <|
        .step (.dropLo 4 83) <|
        .step (.xLo 117) <|
        .splitExp 1 2
          (.step (.grow 1 31) <|
          .step (.xLo 1209) <|
          .step (.dropHi 2 18) <|
          .step (.dropHi 3 20) <|
          .step (.primeHi 3 19) <|
          .step (.primeHi 2 17) <|
          .reject)
          (.step (.dropLo 3 21) <|
          .step (.dropLo 4 232) <|
          .step (.primeLo 3 23) <|
          .step (.xLo 273) <|
          .step (.dropHi 2 18) <|
          .step (.primeHi 2 17) <|
          .reject))
        (.step (.primeLo 3 29) <|
        .step (.dropHi 4 152) <|
        .step (.xHi 117) <|
        .splitExp 1 2
          (.step (.fix 1 31 3) <|
          .reject)
          (.splitBase 3 31
            (.splitBase 2 17
              (.step (.dropLo 3 30) <|
              .step (.dropLo 4 106) <|
              .step (.primeLo 3 31) <|
              .step (.xLo 117) <|
              .missing 4 59)
              (.step (.primeLo 2 19) <|
              .step (.dropHi 4 76) <|
              .step (.xHi 65) <|
              .missing 4 11))
            (.step (.primeLo 3 37) <|
            .step (.dropHi 2 17) <|
            .step (.dropHi 4 70) <|
            .step (.xHi 65) <|
            .missing 4 11))))
      (.step (.primeLo 2 23) <|
      .step (.primeLo 3 29) <|
      .reject))
    (.step (.dropLo 2 20) <|
    .step (.dropLo 3 23) <|
    .step (.dropLo 4 60) <|
    .step (.primeLo 2 23) <|
    .step (.primeLo 3 29) <|
    .step (.xLo 61) <|
    .splitBase 2 25
      (.step (.primeHi 2 23) <|
      .step (.dropLo 3 31) <|
      .step (.dropLo 4 202) <|
      .step (.xLo 205) <|
      .splitExp 1 2
        (.splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.xLo 209) <|
          .step (.dropHi 3 36) <|
          .step (.primeHi 3 31) <|
          .reject)
          (.step (.dropLo 3 35) <|
          .step (.dropLo 4 782) <|
          .step (.primeLo 3 37) <|
          .step (.xLo 785) <|
          .step (.grow 1 31) <|
          .step (.dropHi 4 1389) <|
          .step (.xLo 837) <|
          .step (.xHi 1333) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 1146) <|
            .step (.xLo 1209) <|
            .splitExp 2 2
              (.missing 2 7)
              (.step (.dropLo 4 1265) <|
              .step (.xLo 1333) <|
              .missing 4 29))))
        (.reject))
      (.step (.primeLo 2 29) <|
      .step (.primeLo 3 31) <|
      .splitExp 1 2
        (.step (.dropHi 4 213) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 113) <|
          .step (.xLo 77) <|
          .step (.xHi 77) <|
          .missing 4 13)
          (.step (.dropLo 4 78) <|
          .step (.xLo 81) <|
          .splitBase 3 33
            (.step (.primeHi 3 31) <|
            .step (.primeHi 2 29) <|
            .step (.dropLo 4 192) <|
            .step (.xLo 193) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 4 208) <|
              .step (.xLo 209) <|
              .splitExp 0 8
                (.missing 0 13)
                (.step (.dropLo 4 210) <|
                .step (.xLo 213) <|
                .missing 4 107)))
            (.step (.primeLo 3 37) <|
            .step (.dropHi 4 99) <|
            .step (.xHi 97) <|
            .splitBase 2 29
              (.step (.grow 1 31) <|
              .step (.dropLo 4 94) <|
              .step (.xLo 217) <|
              .reject)
              (.step (.primeLo 2 31) <|
              .step (.dropHi 4 81) <|
              .missing 4 41))))
        (.use 0)))

private def deficientFourPowerGeneralPart014Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,31,37,2,0⟩, ⟨true,61,0,5,0⟩], 1, deficientFourPowerGeneralPart013⟩]

theorem deficientFourPowerGeneralPart014 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,31,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,13,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart014Tree deficientFourPowerGeneralPart014Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
