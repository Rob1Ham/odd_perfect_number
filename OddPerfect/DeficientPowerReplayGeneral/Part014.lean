module

public import OddPerfect.DeficientPowerReplayGeneral.Part013

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart065Tree : Tree :=
  .step (.primeLo 3 83) <|
  .step (.dropHi 4 126) <|
  .step (.xHi 125) <|
  .splitBase 3 165
    (.step (.primeHi 3 163) <|
    .step (.dropLo 4 26) <|
    .step (.xLo 29) <|
    .splitBase 2 25
      (.step (.primeHi 2 23) <|
      .step (.dropLo 4 38) <|
      .step (.xLo 41) <|
      .splitExp 1 2
        (.step (.grow 1 31) <|
        .step (.dropHi 4 63) <|
        .step (.xLo 93) <|
        .reject)
        (.step (.dropLo 4 54) <|
        .step (.xLo 57) <|
        .splitBase 3 109
          (.use 0)
          (.step (.primeLo 3 113) <|
          .step (.dropHi 4 89) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 154) <|
            .step (.dropHi 4 65) <|
            .step (.primeHi 3 151) <|
            .step (.xLo 77) <|
            .reject)
            (.step (.dropLo 4 68) <|
            .step (.xLo 69) <|
            .splitBase 3 133
              (.step (.primeHi 3 131) <|
              .step (.dropLo 4 75) <|
              .step (.xLo 77) <|
              .splitBase 3 121
                (.step (.primeHi 3 113) <|
                .step (.dropLo 4 83) <|
                .step (.xLo 85) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 86) <|
                  .step (.xLo 89) <|
                  .splitExp 1 4
                    (.missing 1 11)
                    (.splitExp 2 2
                      (.missing 2 7)
                      (.reject))))
                (.step (.primeLo 3 127) <|
                .step (.dropHi 4 82) <|
                .step (.xHi 81) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 78) <|
                  .step (.xLo 81) <|
                  .missing 4 41)))
              (.step (.primeLo 3 137) <|
              .step (.dropHi 4 78) <|
              .step (.xHi 77) <|
              .splitBase 3 147
                (.step (.primeHi 3 139) <|
                .step (.dropLo 4 73) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 75) <|
                  .step (.xLo 77) <|
                  .missing 4 13))
                (.step (.primeLo 3 149) <|
                .step (.dropHi 4 75) <|
                .step (.xHi 73) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 70) <|
                  .step (.xLo 73) <|
                  .missing 4 37)))))))
      (.step (.primeLo 2 29) <|
      .step (.dropHi 4 58) <|
      .step (.xHi 57) <|
      .splitExp 1 2
        (.step (.fix 1 31 2) <|
        .step (.dropHi 4 36) <|
        .step (.xHi 33) <|
        .splitBase 3 109
          (.splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 4 31) <|
            .step (.xLo 33) <|
            .reject)
            (.step (.dropLo 3 105) <|
            .step (.dropLo 4 32) <|
            .step (.primeLo 3 107) <|
            .step (.xLo 33) <|
            .missing 4 17))
          (.step (.primeLo 3 113) <|
          .step (.dropHi 4 32) <|
          .step (.xHi 29) <|
          .splitExp 0 4
            (.missing 0 11)
            (.reject)))
        (.use 1)))
    (.use 2)

private def deficientFourPowerGeneralPart065Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,83,109,2,0⟩, ⟨true,57,125,5,0⟩], 1, deficientFourPowerGeneralPart061⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,29,31,2,0⟩, ⟨false,83,163,2,0⟩, ⟨true,29,57,5,0⟩], 1, deficientFourPowerGeneralPart062⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,31,2,0⟩, ⟨false,166,0,2,0⟩, ⟨true,25,125,5,0⟩], 1, deficientFourPowerGeneralPart064⟩]

theorem deficientFourPowerGeneralPart065 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,31,2,0⟩, ⟨false,82,0,2,0⟩, ⟨true,25,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart065Tree deficientFourPowerGeneralPart065Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart066Tree : Tree :=
  .step (.primeLo 3 59) <|
  .step (.dropHi 4 50) <|
  .step (.xHi 49) <|
  .splitExp 1 2
    (.missing 1 31)
    (.step (.dropLo 4 29) <|
    .splitBase 2 41
      (.step (.dropLo 4 32) <|
      .step (.xLo 33) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 4 41) <|
        .step (.xHi 33) <|
        .missing 4 17)
        (.step (.dropLo 4 36) <|
        .step (.xLo 37) <|
        .splitBase 3 67
          (.step (.dropLo 4 39) <|
          .step (.xLo 41) <|
          .splitBase 2 37
            (.step (.dropLo 4 44) <|
            .step (.xLo 45) <|
            .splitBase 3 61
              (.step (.dropLo 4 47) <|
              .step (.xLo 49) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitBase 3 59
                  (.reject)
                  (.step (.primeLo 3 61) <|
                  .splitExp 1 4
                    (.missing 1 11)
                    (.splitExp 0 8
                      (.missing 0 13)
                      (.splitExp 2 2
                        (.step (.grow 2 7) <|
                        .missing 2 67)
                        (.splitExp 1 6
                          (.reject)
                          (.splitExp 0 10
                            (.missing 0 23)
                            (.reject))))))))
              (.step (.primeLo 3 67) <|
              .step (.dropHi 4 45) <|
              .missing 4 23))
            (.step (.primeLo 2 41) <|
            .step (.dropHi 3 66) <|
            .step (.dropHi 4 44) <|
            .step (.primeHi 3 61) <|
            .step (.xHi 41) <|
            .missing 4 7))
          (.step (.primeLo 3 71) <|
          .step (.dropHi 4 44) <|
          .step (.xHi 41) <|
          .splitBase 2 37
            (.step (.dropLo 3 76) <|
            .step (.dropLo 4 40) <|
            .step (.primeLo 3 79) <|
            .step (.xLo 41) <|
            .missing 4 7)
            (.step (.primeLo 2 41) <|
            .step (.dropHi 4 39) <|
            .step (.xHi 37) <|
            .missing 4 19))))
      (.step (.primeLo 2 43) <|
      .step (.dropHi 4 42) <|
      .step (.xHi 41) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 4 36) <|
        .step (.xLo 33) <|
        .step (.xHi 33) <|
        .missing 4 17)
        (.step (.dropLo 4 32) <|
        .step (.xLo 33) <|
        .splitBase 3 67
          (.step (.dropLo 4 35) <|
          .step (.xLo 37) <|
          .splitBase 3 61
            (.splitBase 2 43
              (.step (.dropLo 4 40) <|
              .step (.xLo 41) <|
              .missing 4 7)
              (.step (.primeLo 2 47) <|
              .step (.dropHi 4 39) <|
              .step (.xHi 37) <|
              .missing 4 19))
            (.step (.primeLo 3 67) <|
            .step (.dropHi 2 45) <|
            .step (.dropHi 4 39) <|
            .step (.primeHi 2 43) <|
            .step (.xHi 37) <|
            .missing 4 19))
          (.step (.primeLo 3 71) <|
          .step (.dropHi 4 37) <|
          .splitBase 2 43
            (.step (.dropLo 4 34) <|
            .step (.xLo 37) <|
            .missing 4 19)
            (.step (.primeLo 2 47) <|
            .step (.dropHi 4 35) <|
            .step (.xHi 33) <|
            .missing 4 17)))))

theorem deficientFourPowerGeneralPart066 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,47,2,0⟩, ⟨false,54,79,2,0⟩, ⟨true,25,77,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart066Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart067Tree : Tree :=
  .step (.primeHi 2 47) <|
  .step (.dropLo 4 24) <|
  .step (.xLo 25) <|
  .splitBase 3 53
    (.step (.dropLo 4 28) <|
    .step (.xLo 29) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 4 35) <|
      .step (.xLo 37) <|
      .splitBase 2 41
        (.step (.dropLo 4 40) <|
        .step (.xLo 41) <|
        .splitBase 3 45
          (.step (.primeHi 3 43) <|
          .step (.dropLo 4 48) <|
          .step (.xLo 49) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 4 60) <|
            .step (.xLo 77) <|
            .reject)
            (.step (.dropLo 4 58) <|
            .step (.xLo 61) <|
            .splitBase 2 37
              (.step (.dropLo 4 69) <|
              .splitBase 3 41
                (.step (.dropLo 4 75) <|
                .step (.xLo 77) <|
                .missing 4 13)
                (.step (.primeLo 3 43) <|
                .step (.dropHi 4 73) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 71) <|
                  .step (.xLo 73) <|
                  .splitExp 1 4
                    (.missing 1 11)
                    (.reject))))
              (.step (.primeLo 2 41) <|
              .step (.primeLo 3 43) <|
              .step (.dropHi 4 61) <|
              .missing 4 31)))
          (.step (.primeLo 3 47) <|
          .step (.dropHi 4 64) <|
          .step (.xHi 61) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 4 46) <|
            .step (.xLo 49) <|
            .splitBase 2 37
              (.step (.dropLo 4 53) <|
              .splitBase 3 49
                (.step (.primeHi 3 47) <|
                .reject)
                (.step (.primeLo 3 53) <|
                .step (.dropHi 4 55) <|
                .step (.xHi 53) <|
                .reject))
              (.step (.primeLo 2 41) <|
              .step (.dropHi 3 52) <|
              .step (.dropHi 4 55) <|
              .step (.primeHi 3 47) <|
              .step (.xHi 53) <|
              .step (.dropLo 4 52) <|
              .step (.xLo 53) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject)))))
        (.step (.primeLo 2 43) <|
        .step (.primeLo 3 47) <|
        .step (.dropHi 4 51) <|
        .step (.xHi 49) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 4 40) <|
          .step (.xLo 41) <|
          .splitBase 3 49
            (.step (.primeHi 3 47) <|
            .step (.primeHi 2 43) <|
            .reject)
            (.step (.primeLo 3 53) <|
            .step (.dropHi 4 46) <|
            .step (.xHi 45) <|
            .splitBase 2 43
              (.step (.dropLo 4 44) <|
              .step (.xLo 45) <|
              .missing 4 23)
              (.step (.primeLo 2 47) <|
              .step (.dropHi 4 42) <|
              .step (.xHi 41) <|
              .missing 4 7))))))
    (.use 0)

private def deficientFourPowerGeneralPart067Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,47,2,0⟩, ⟨false,54,79,2,0⟩, ⟨true,25,77,5,0⟩], 1, deficientFourPowerGeneralPart066⟩]

theorem deficientFourPowerGeneralPart067 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,49,2,0⟩, ⟨false,41,79,2,0⟩, ⟨true,21,77,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart067Tree deficientFourPowerGeneralPart067Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart068Tree : Tree :=
  .splitBase 3 333
    (.step (.primeHi 3 331) <|
    .step (.dropLo 4 22) <|
    .step (.xLo 25) <|
    .splitBase 2 41
      (.splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 3 180) <|
        .step (.dropLo 4 27) <|
        .step (.primeLo 3 181) <|
        .step (.xLo 29) <|
        .splitBase 2 37
          (.reject)
          (.step (.primeLo 2 41) <|
          .step (.dropHi 3 210) <|
          .step (.primeHi 3 199) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 195) <|
            .step (.primeLo 3 197) <|
            .splitExp 1 4
              (.missing 1 11)
              (.reject)))))
      (.step (.primeLo 2 43) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 3 221
          (.step (.primeHi 3 211) <|
          .step (.dropLo 4 26) <|
          .step (.xLo 29) <|
          .step (.dropHi 2 43) <|
          .step (.dropHi 3 169) <|
          .step (.primeHi 3 167) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.splitExp 1 4
              (.missing 1 11)
              (.reject)))
          (.step (.primeLo 3 223) <|
          .step (.dropHi 4 27) <|
          .step (.xHi 25) <|
          .missing 4 13))))
    (.step (.primeLo 3 337) <|
    .splitBase 2 41
      (.step (.dropLo 4 23) <|
      .step (.xLo 25) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 3 673
          (.step (.dropLo 4 26) <|
          .step (.xLo 29) <|
          .step (.dropHi 2 38) <|
          .step (.dropHi 3 488) <|
          .step (.primeHi 3 487) <|
          .step (.primeHi 2 37) <|
          .step (.dropLo 3 351) <|
          .step (.primeLo 3 353) <|
          .splitBase 3 409
            (.splitExp 0 6
              (.missing 0 1093)
              (.reject))
            (.step (.primeLo 3 419) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 4
                (.missing 1 11)
                (.step (.dropLo 3 469) <|
                .step (.primeLo 3 479) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.splitBase 3 481
                    (.step (.primeHi 3 479) <|
                    .reject)
                    (.step (.primeLo 3 487) <|
                    .splitExp 2 2
                      (.missing 2 7)
                      (.splitExp 1 6
                        (.reject)
                        (.reject))))))))
          (.step (.primeLo 3 677) <|
          .step (.dropHi 4 28) <|
          .step (.xHi 25) <|
          .missing 4 13)))
      (.step (.primeLo 2 43) <|
      .step (.dropHi 4 26) <|
      .step (.xHi 25) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 4 23) <|
        .step (.xLo 25) <|
        .missing 4 13)))

theorem deficientFourPowerGeneralPart068 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,47,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,21,29,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart068Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart069Tree : Tree :=
  .step (.primeHi 2 47) <|
  .step (.dropLo 4 18) <|
  .step (.xLo 21) <|
  .splitBase 3 165
    (.step (.primeHi 3 163) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 4 24) <|
      .step (.xLo 25) <|
      .splitBase 3 109
        (.step (.dropLo 4 26) <|
        .step (.xLo 29) <|
        .splitBase 2 41
          (.splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 4 34) <|
            .step (.xLo 33) <|
            .step (.xHi 33) <|
            .missing 4 17)
            (.step (.dropLo 4 32) <|
            .step (.xLo 33) <|
            .splitBase 3 93
              (.step (.primeHi 3 89) <|
              .step (.dropLo 2 38) <|
              .step (.dropLo 4 34) <|
              .step (.primeLo 2 41) <|
              .step (.xLo 37) <|
              .missing 4 19)
              (.step (.primeLo 3 97) <|
              .splitBase 2 37
                (.step (.dropLo 4 35) <|
                .step (.xLo 37) <|
                .missing 4 19)
                (.step (.primeLo 2 41) <|
                .step (.dropHi 4 34) <|
                .step (.xHi 33) <|
                .missing 4 17))))
          (.step (.primeLo 2 43) <|
          .step (.dropHi 4 35) <|
          .step (.xHi 33) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 100) <|
            .step (.dropHi 4 30) <|
            .step (.primeHi 3 97) <|
            .step (.xLo 33) <|
            .reject)
            (.splitBase 3 93
              (.step (.primeHi 3 89) <|
              .step (.dropLo 4 31) <|
              .step (.xLo 33) <|
              .missing 4 17)
              (.step (.primeLo 3 97) <|
              .splitBase 2 43
                (.step (.dropLo 4 31) <|
                .step (.xLo 33) <|
                .missing 4 17)
                (.step (.primeLo 2 47) <|
                .step (.dropHi 4 31) <|
                .step (.xHi 29) <|
                .reject)))))
        (.step (.primeLo 3 113) <|
        .step (.dropHi 4 35) <|
        .step (.xHi 33) <|
        .splitBase 2 41
          (.step (.dropLo 4 26) <|
          .step (.xLo 29) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 162) <|
            .step (.dropHi 4 31) <|
            .step (.primeHi 3 157) <|
            .step (.xLo 33) <|
            .reject)
            (.splitBase 3 133
              (.step (.primeHi 3 131) <|
              .step (.dropLo 4 30) <|
              .step (.xLo 33) <|
              .missing 4 17)
              (.step (.primeLo 3 137) <|
              .splitBase 2 37
                (.step (.dropLo 3 140) <|
                .step (.dropLo 4 31) <|
                .step (.primeLo 3 149) <|
                .step (.xLo 33) <|
                .missing 4 17)
                (.step (.primeLo 2 41) <|
                .step (.dropHi 4 31) <|
                .step (.xHi 29) <|
                .reject))))
          (.step (.primeLo 2 43) <|
          .step (.dropHi 4 31) <|
          .step (.xHi 29) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 115) <|
            .step (.dropLo 4 27) <|
            .step (.primeLo 3 127) <|
            .step (.xLo 29) <|
            .step (.dropHi 2 46) <|
            .step (.primeHi 2 43) <|
            .step (.dropLo 3 149) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 3 159) <|
              .step (.primeLo 3 163) <|
              .splitExp 1 4
                (.missing 1 11)
                (.reject)))))))
    (.step (.primeLo 3 167) <|
    .step (.dropHi 4 32) <|
    .step (.xHi 29) <|
    .splitExp 1 2
      (.missing 1 31)
      (.use 0))

private def deficientFourPowerGeneralPart069Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,47,2,0⟩, ⟨false,167,0,2,0⟩, ⟨true,21,29,5,0⟩], 1, deficientFourPowerGeneralPart068⟩]

theorem deficientFourPowerGeneralPart069 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,37,49,2,0⟩, ⟨false,83,0,2,0⟩, ⟨true,17,37,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart069Tree deficientFourPowerGeneralPart069Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
