module

public import OddPerfect.DeficientPowerReplayGeneral.Part012

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart060Tree : Tree :=
  .step (.primeLo 3 59) <|
  .step (.dropHi 4 334) <|
  .step (.xHi 333) <|
  .splitBase 2 25
    (.use 0)
    (.step (.primeLo 2 29) <|
    .step (.dropHi 4 81) <|
    .splitExp 1 2
      (.step (.fix 1 31 2) <|
      .step (.dropHi 4 44) <|
      .step (.xHi 41) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 3 76) <|
        .step (.dropHi 4 37) <|
        .step (.primeHi 3 73) <|
        .step (.xHi 33) <|
        .missing 4 17)
        (.step (.dropLo 3 64) <|
        .step (.dropLo 4 36) <|
        .step (.primeLo 3 67) <|
        .step (.xLo 37) <|
        .step (.dropHi 4 40) <|
        .step (.xHi 37) <|
        .missing 4 19))
      (.step (.dropLo 4 43) <|
      .step (.xLo 45) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 4 61) <|
        .step (.xLo 77) <|
        .reject)
        (.step (.dropLo 4 50) <|
        .step (.xLo 53) <|
        .splitBase 3 67
          (.step (.dropLo 4 57) <|
          .splitBase 2 29
            (.step (.dropLo 4 66) <|
            .step (.xLo 69) <|
            .splitBase 3 61
              (.step (.dropLo 4 73) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 75) <|
                .step (.xLo 77) <|
                .splitBase 3 59
                  (.step (.dropLo 4 78) <|
                  .step (.xLo 81) <|
                  .missing 4 41)
                  (.step (.primeLo 3 61) <|
                  .step (.dropHi 4 77) <|
                  .missing 4 13)))
              (.step (.primeLo 3 67) <|
              .step (.dropHi 4 69) <|
              .missing 4 7))
            (.step (.primeLo 2 31) <|
            .step (.dropHi 4 68) <|
            .step (.xHi 65) <|
            .splitBase 3 61
              (.step (.dropLo 4 62) <|
              .step (.xLo 65) <|
              .missing 4 11)
              (.step (.primeLo 3 67) <|
              .step (.dropHi 4 60) <|
              .step (.xHi 57) <|
              .missing 4 29)))
          (.step (.primeLo 3 71) <|
          .step (.dropHi 4 66) <|
          .step (.xHi 65) <|
          .splitBase 2 29
            (.step (.dropLo 4 57) <|
            .splitBase 3 73
              (.step (.dropLo 4 61) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 62) <|
                .step (.xLo 65) <|
                .missing 4 11))
              (.step (.primeLo 3 79) <|
              .step (.dropHi 4 60) <|
              .step (.xHi 57) <|
              .reject))
            (.step (.primeLo 2 31) <|
            .step (.dropHi 4 57) <|
            .splitBase 3 73
              (.splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 4 54) <|
                .step (.xLo 57) <|
                .missing 4 29))
              (.step (.primeLo 3 79) <|
              .step (.dropHi 4 53) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 4
                  (.missing 1 11)
                  (.splitExp 0 8
                    (.missing 0 13)
                    (.splitExp 2 2
                      (.missing 2 331)
                      (.reject))))))))))

private def deficientFourPowerGeneralPart060Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,25,2,0⟩, ⟨false,59,79,2,0⟩, ⟨true,33,333,5,0⟩], 1, deficientFourPowerGeneralPart059⟩]

theorem deficientFourPowerGeneralPart060 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,31,2,0⟩, ⟨false,54,79,2,0⟩, ⟨true,33,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart060Tree deficientFourPowerGeneralPart060Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart061Tree : Tree :=
  .step (.dropLo 4 65) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 4 83) <|
    .step (.xLo 77) <|
    .step (.xHi 77) <|
    .missing 4 13)
    (.step (.dropLo 4 85) <|
    .splitBase 3 93
      (.step (.primeHi 3 89) <|
      .step (.dropLo 4 104) <|
      .step (.xLo 105) <|
      .splitBase 3 85
        (.step (.primeHi 3 83) <|
        .step (.dropLo 4 113) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 119) <|
          .step (.xLo 121) <|
          .splitExp 1 4
            (.step (.grow 1 11) <|
            .missing 1 71)
            (.step (.dropLo 4 123) <|
            .step (.xLo 125) <|
            .missing 4 7)))
        (.step (.primeLo 3 89) <|
        .step (.dropHi 4 114) <|
        .step (.xHi 113) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 108) <|
          .step (.xLo 109) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 4 112) <|
            .step (.xLo 113) <|
            .missing 4 19))))
      (.step (.primeLo 3 97) <|
      .step (.dropHi 4 103) <|
      .step (.xHi 101) <|
      .splitBase 3 101
        (.step (.dropLo 4 91) <|
        .step (.xLo 93) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 94) <|
          .step (.xLo 97) <|
          .splitExp 1 4
            (.missing 1 11)
            (.splitBase 3 97
              (.reject)
              (.step (.primeLo 3 101) <|
              .step (.dropHi 4 99) <|
              .step (.xHi 97) <|
              .missing 4 7))))
        (.step (.primeLo 3 103) <|
        .step (.dropHi 4 97) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 88) <|
          .step (.xLo 89) <|
          .splitBase 3 105
            (.step (.primeHi 3 103) <|
            .step (.dropLo 4 93) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 95) <|
              .step (.xLo 97) <|
              .missing 4 7))
            (.step (.primeLo 3 107) <|
            .step (.dropHi 4 93) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 91) <|
              .step (.xLo 93) <|
              .missing 4 47))))))

theorem deficientFourPowerGeneralPart061 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,83,109,2,0⟩, ⟨true,57,125,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart061Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart062Tree : Tree :=
  .step (.dropLo 4 33) <|
  .splitBase 3 109
    (.step (.dropLo 4 37) <|
    .splitExp 0 4
      (.missing 0 11)
      (.step (.dropLo 4 43) <|
      .step (.xLo 45) <|
      .splitBase 3 93
        (.step (.primeHi 3 89) <|
        .step (.dropLo 4 47) <|
        .step (.xLo 49) <|
        .splitBase 2 29
          (.step (.dropLo 4 53) <|
          .splitBase 3 85
            (.step (.primeHi 3 83) <|
            .step (.dropLo 4 55) <|
            .step (.xLo 57) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 4
                (.missing 1 11)
                (.reject)))
            (.step (.primeLo 3 89) <|
            .step (.dropHi 4 55) <|
            .step (.xHi 53) <|
            .reject))
          (.step (.primeLo 2 31) <|
          .step (.dropHi 4 51) <|
          .step (.xHi 49) <|
          .step (.dropLo 3 84) <|
          .step (.primeLo 3 89) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.splitExp 1 4
              (.missing 1 11)
              (.reject))))
        (.step (.primeLo 3 97) <|
        .step (.dropHi 4 52) <|
        .step (.xHi 49) <|
        .splitBase 2 29
          (.step (.dropLo 3 104) <|
          .step (.dropLo 4 48) <|
          .step (.primeLo 3 107) <|
          .step (.xLo 49) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 108) <|
            .step (.primeLo 3 109) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject)))
          (.step (.primeLo 2 31) <|
          .step (.dropHi 3 108) <|
          .step (.dropHi 4 47) <|
          .step (.primeHi 3 107) <|
          .step (.xHi 45) <|
          .missing 4 23))))
    (.step (.primeLo 3 113) <|
    .step (.dropHi 4 49) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 41) <|
      .step (.xHi 33) <|
      .missing 4 17)
      (.step (.dropLo 4 38) <|
      .step (.xLo 41) <|
      .splitBase 3 133
        (.step (.primeHi 3 131) <|
        .splitBase 2 29
          (.step (.dropLo 4 44) <|
          .step (.xLo 45) <|
          .splitBase 3 121
            (.step (.primeHi 3 113) <|
            .step (.dropLo 4 47) <|
            .step (.xLo 49) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 4
                (.missing 1 11)
                (.splitExp 0 8
                  (.missing 0 13)
                  (.reject))))
            (.step (.primeLo 3 127) <|
            .step (.dropHi 4 46) <|
            .step (.xHi 45) <|
            .missing 4 23))
          (.step (.primeLo 2 31) <|
          .step (.dropHi 4 44) <|
          .step (.xHi 41) <|
          .missing 4 7))
        (.step (.primeLo 3 137) <|
        .step (.dropHi 4 45) <|
        .splitBase 2 29
          (.splitBase 3 147
            (.step (.primeHi 3 139) <|
            .step (.dropLo 4 43) <|
            .step (.xLo 45) <|
            .missing 4 23)
            (.step (.primeLo 3 149) <|
            .step (.dropHi 4 44) <|
            .step (.xHi 41) <|
            .missing 4 7))
          (.step (.primeLo 2 31) <|
          .step (.dropHi 3 142) <|
          .step (.dropHi 4 41) <|
          .step (.primeHi 3 139) <|
          .missing 4 7))))

theorem deficientFourPowerGeneralPart062 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,83,163,2,0⟩, ⟨true,29,57,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart062Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart063Tree : Tree :=
  .step (.primeLo 3 337) <|
  .step (.dropHi 4 58) <|
  .step (.xHi 57) <|
  .splitExp 0 4
    (.missing 0 11)
    (.step (.dropLo 4 48) <|
    .step (.xLo 49) <|
    .splitBase 3 673
      (.step (.dropLo 4 51) <|
      .step (.xLo 53) <|
      .splitBase 3 449
        (.splitBase 3 385
          (.step (.primeHi 3 383) <|
          .step (.dropLo 4 55) <|
          .step (.xLo 57) <|
          .missing 4 29)
          (.step (.primeLo 3 389) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 55) <|
            .step (.xLo 57) <|
            .missing 4 29)))
        (.step (.primeLo 3 457) <|
        .step (.dropHi 4 56) <|
        .step (.xHi 53) <|
        .step (.dropLo 3 527) <|
        .step (.primeLo 3 541) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 670) <|
          .step (.primeLo 3 673) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject))))
      (.step (.primeLo 3 677) <|
      .step (.dropHi 4 54) <|
      .step (.xHi 53) <|
      .splitBase 3 1353
        (.step (.primeHi 3 1327) <|
        .step (.dropLo 4 50) <|
        .step (.xLo 53) <|
        .step (.dropHi 3 963) <|
        .step (.primeHi 3 953) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.splitBase 3 791
            (.step (.primeHi 3 787) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject))
            (.step (.primeLo 3 797) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 3 844) <|
              .step (.primeLo 3 853) <|
              .splitBase 3 899
                (.step (.primeHi 3 887) <|
                .splitExp 2 2
                  (.missing 2 7)
                  (.reject))
                (.step (.primeLo 3 907) <|
                .splitExp 2 2
                  (.missing 2 7)
                  (.splitExp 0 8
                    (.missing 0 13)
                    (.step (.dropLo 3 946) <|
                    .step (.primeLo 3 947) <|
                    .splitExp 1 6
                      (.step (.dropHi 3 951) <|
                      .step (.primeHi 3 947) <|
                      .splitExp 0 10
                        (.reject)
                        (.reject))
                      (.reject))))))))
        (.step (.primeLo 3 1361) <|
        .step (.dropHi 4 52) <|
        .step (.xHi 49) <|
        .step (.dropLo 3 3057) <|
        .step (.primeLo 3 3061) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))))

theorem deficientFourPowerGeneralPart063 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,334,0,2,0⟩, ⟨true,41,69,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart063Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart064Tree : Tree :=
  .step (.primeLo 3 167) <|
  .step (.dropHi 4 71) <|
  .step (.xHi 69) <|
  .splitBase 2 25
    (.step (.primeHi 2 23) <|
    .step (.dropLo 4 31) <|
    .step (.xLo 33) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 4 41) <|
      .splitBase 3 333
        (.step (.primeHi 3 331) <|
        .step (.dropLo 4 46) <|
        .step (.xLo 49) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 4 56) <|
          .step (.xLo 57) <|
          .splitBase 3 221
            (.step (.primeHi 3 211) <|
            .step (.dropLo 4 62) <|
            .step (.xLo 65) <|
            .splitBase 3 185
              (.step (.primeHi 3 181) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 3 168) <|
                .step (.dropLo 4 67) <|
                .step (.primeLo 3 173) <|
                .step (.xLo 69) <|
                .missing 4 7))
              (.step (.primeLo 3 191) <|
              .step (.dropHi 4 67) <|
              .step (.xHi 65) <|
              .missing 4 11))
            (.step (.primeLo 3 223) <|
            .step (.dropHi 4 64) <|
            .step (.xHi 61) <|
            .step (.dropLo 3 226) <|
            .step (.primeLo 3 227) <|
            .splitBase 3 269
              (.step (.dropLo 4 58) <|
              .step (.xLo 61) <|
              .missing 4 31)
              (.step (.primeLo 3 271) <|
              .splitBase 3 297
                (.step (.primeHi 3 293) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 58) <|
                  .step (.xLo 61) <|
                  .missing 4 31))
                (.step (.primeLo 3 307) <|
                .step (.dropHi 4 59) <|
                .step (.xHi 57) <|
                .missing 4 29)))))
        (.use 0)))
    (.step (.primeLo 2 29) <|
    .step (.dropHi 4 43) <|
    .step (.xHi 41) <|
    .splitExp 1 2
      (.step (.fix 1 31 2) <|
      .step (.dropHi 4 30) <|
      .step (.xHi 29) <|
      .splitBase 3 333
        (.step (.primeHi 3 331) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 3 193) <|
          .step (.dropLo 4 27) <|
          .step (.xLo 29) <|
          .step (.dropHi 3 213) <|
          .step (.primeHi 3 211) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 209) <|
            .step (.primeLo 3 211) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))
        (.step (.primeLo 3 337) <|
        .step (.dropHi 4 27) <|
        .step (.xHi 25) <|
        .missing 4 13))
      (.step (.dropLo 4 28) <|
      .step (.xLo 29) <|
      .splitBase 3 333
        (.step (.primeHi 3 331) <|
        .step (.dropLo 4 30) <|
        .step (.xLo 33) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 36) <|
          .step (.xHi 33) <|
          .missing 4 17)
          (.step (.dropLo 4 34) <|
          .step (.xLo 37) <|
          .splitBase 3 221
            (.step (.primeHi 3 211) <|
            .splitBase 2 29
              (.step (.dropLo 3 179) <|
              .step (.dropLo 4 39) <|
              .step (.xLo 41) <|
              .missing 4 7)
              (.step (.primeLo 2 31) <|
              .step (.dropHi 4 39) <|
              .step (.xHi 37) <|
              .missing 4 19))
            (.step (.primeLo 3 223) <|
            .step (.dropHi 4 40) <|
            .step (.xHi 37) <|
            .missing 4 19)))
        (.step (.primeLo 3 337) <|
        .step (.dropHi 4 38) <|
        .step (.xHi 37) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 33) <|
          .step (.xLo 33) <|
          .missing 4 17)
          (.step (.dropLo 4 31) <|
          .step (.xLo 33) <|
          .splitBase 3 673
            (.splitBase 2 29
              (.step (.dropLo 3 349) <|
              .step (.dropLo 4 35) <|
              .step (.xLo 37) <|
              .missing 4 19)
              (.step (.primeLo 2 31) <|
              .step (.dropHi 4 35) <|
              .step (.xHi 33) <|
              .missing 4 17))
            (.step (.primeLo 3 677) <|
            .step (.dropHi 4 36) <|
            .step (.xHi 33) <|
            .missing 4 17)))))

private def deficientFourPowerGeneralPart064Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,334,0,2,0⟩, ⟨true,41,69,5,0⟩], 1, deficientFourPowerGeneralPart063⟩]

theorem deficientFourPowerGeneralPart064 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,31,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,25,125,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart064Tree deficientFourPowerGeneralPart064Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
