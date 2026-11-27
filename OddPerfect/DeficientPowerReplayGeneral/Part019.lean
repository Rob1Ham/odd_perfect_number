module

public import OddPerfect.DeficientPowerReplayGeneral.Part018

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart090Tree : Tree :=
  .splitExp 0 2
    (.step (.grow 0 13) <|
    .step (.dropHi 4 18) <|
    .step (.xLo 13) <|
    .step (.xHi 13) <|
    .step (.dropHi 2 27) <|
    .step (.dropHi 3 33) <|
    .step (.primeHi 3 31) <|
    .step (.primeHi 2 23) <|
    .step (.dropLo 3 20) <|
    .step (.primeLo 3 23) <|
    .step (.dropHi 2 21) <|
    .step (.primeHi 2 19) <|
    .step (.dropLo 3 25) <|
    .step (.primeLo 3 29) <|
    .step (.dropHi 2 18) <|
    .step (.primeHi 2 17) <|
    .step (.dropLo 3 30) <|
    .step (.primeLo 3 31) <|
    .splitExp 1 2
      (.missing 1 19)
      (.reject))
    (.step (.dropLo 4 12) <|
    .step (.xLo 13) <|
    .splitBase 2 21
      (.step (.primeHi 2 19) <|
      .step (.dropLo 4 17) <|
      .splitBase 3 25
        (.step (.primeHi 3 23) <|
        .step (.dropLo 4 24) <|
        .step (.xLo 25) <|
        .splitBase 3 19
          (.step (.primeHi 2 17) <|
          .step (.dropLo 4 38) <|
          .step (.xLo 41) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 4 44) <|
            .step (.xLo 45) <|
            .splitExp 1 2
              (.step (.dropHi 4 46) <|
              .step (.xHi 45) <|
              .missing 4 23)
              (.step (.dropLo 4 51) <|
              .step (.xLo 53) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 2 2
                  (.missing 2 307)
                  (.splitExp 3 2
                    (.missing 3 127)
                    (.reject))))))
          (.step (.primeLo 3 23) <|
          .step (.dropHi 4 35) <|
          .step (.xHi 33) <|
          .splitBase 2 17
            (.step (.dropLo 4 28) <|
            .step (.xLo 29) <|
            .splitExp 0 4
              (.step (.grow 0 11) <|
              .step (.dropHi 4 31) <|
              .step (.xLo 33) <|
              .reject)
              (.step (.dropLo 4 31) <|
              .step (.xLo 33) <|
              .splitExp 1 2
                (.missing 1 19)
                (.reject)))
            (.step (.primeLo 2 19) <|
            .step (.dropHi 4 29) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 4 26) <|
              .step (.xLo 29) <|
              .missing 4 5))))
        (.step (.primeLo 3 29) <|
        .step (.dropHi 4 26) <|
        .step (.xHi 25) <|
        .splitBase 3 31
          (.step (.dropLo 4 19) <|
          .step (.xLo 21) <|
          .splitBase 2 17
            (.splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 4 23) <|
              .step (.xLo 25) <|
              .missing 4 13))
            (.step (.primeLo 2 19) <|
            .step (.dropHi 4 23) <|
            .step (.xHi 21) <|
            .missing 4 11))
          (.step (.primeLo 3 37) <|
          .step (.dropHi 4 22) <|
          .step (.xHi 21) <|
          .splitBase 2 17
            (.step (.dropLo 4 19) <|
            .step (.xLo 21) <|
            .missing 4 11)
            (.step (.primeLo 2 19) <|
            .step (.dropHi 4 19) <|
            .step (.xHi 17) <|
            .reject))))
      (.step (.primeLo 2 23) <|
      .step (.primeLo 3 29) <|
      .step (.dropHi 4 19) <|
      .step (.xHi 17) <|
      .splitBase 2 25
        (.step (.primeHi 2 23) <|
        .step (.dropLo 4 15) <|
        .step (.xLo 17) <|
        .step (.dropHi 3 35) <|
        .step (.primeHi 3 31) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject))
        (.step (.primeLo 2 29) <|
        .step (.primeLo 3 31) <|
        .step (.dropHi 4 15) <|
        .step (.xHi 13) <|
        .step (.dropLo 2 30) <|
        .step (.dropLo 3 36) <|
        .step (.primeLo 2 31) <|
        .step (.primeLo 3 37) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject))))

theorem deficientFourPowerGeneralPart090 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,31,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,9,53,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart090Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart091Tree : Tree :=
  .step (.primeHi 3 79) <|
  .step (.dropLo 4 14) <|
  .step (.xLo 17) <|
  .splitBase 3 53
    (.splitBase 2 17
      (.splitBase 3 45
        (.step (.primeHi 3 43) <|
        .step (.dropLo 4 18) <|
        .step (.xLo 21) <|
        .missing 4 11)
        (.step (.primeLo 3 47) <|
        .step (.dropHi 4 19) <|
        .step (.xHi 17) <|
        .step (.dropLo 3 51) <|
        .step (.primeLo 3 53) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject)))
      (.step (.primeLo 2 19) <|
      .step (.dropHi 4 18) <|
      .step (.xHi 17) <|
      .splitBase 3 45
        (.step (.primeHi 3 43) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject))
        (.step (.primeLo 3 47) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitExp 1 2
            (.reject)
            (.step (.dropLo 3 51) <|
            .step (.primeLo 3 53) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 2 2
                (.missing 2 127)
                (.reject)))))))
    (.step (.primeLo 3 59) <|
    .step (.dropHi 2 18) <|
    .step (.dropHi 4 18) <|
    .step (.primeHi 2 17) <|
    .step (.xHi 17) <|
    .splitExp 0 4
      (.missing 0 11)
      (.step (.dropLo 3 63) <|
      .step (.primeLo 3 67) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 3 77) <|
        .step (.primeLo 3 79) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))))

theorem deficientFourPowerGeneralPart091 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,41,81,2,0⟩, ⟨true,13,21,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart091Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart092Tree : Tree :=
  .step (.primeLo 2 23) <|
  .step (.dropHi 4 16) <|
  .step (.xHi 13) <|
  .splitBase 3 81
    (.step (.primeHi 3 79) <|
    .step (.dropLo 4 11) <|
    .step (.xLo 13) <|
    .splitBase 3 53
      (.step (.dropLo 2 24) <|
      .step (.primeLo 2 29) <|
      .splitBase 3 45
        (.step (.primeHi 3 43) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 2 30) <|
          .step (.primeLo 2 31) <|
          .splitExp 1 2
            (.missing 1 19)
            (.reject)))
        (.step (.primeLo 3 47) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitExp 1 2
            (.missing 1 19)
            (.splitBase 3 49
              (.step (.primeHi 3 47) <|
              .reject)
              (.step (.primeLo 3 53) <|
              .step (.dropHi 2 29) <|
              .reject)))))
      (.step (.primeLo 3 59) <|
      .step (.dropHi 2 27) <|
      .step (.primeHi 2 23) <|
      .step (.dropLo 3 62) <|
      .step (.primeLo 3 67) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject)))
    (.step (.primeLo 3 83) <|
    .splitBase 4 9
      (.missing 4 5)
      (.step (.xLo 13) <|
      .step (.dropHi 2 24) <|
      .step (.dropHi 3 111) <|
      .step (.primeHi 3 109) <|
      .step (.primeHi 2 23) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitExp 1 2
          (.missing 1 19)
          (.step (.dropLo 3 104) <|
          .step (.primeLo 3 107) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 108) <|
            .step (.primeLo 3 109) <|
            .splitExp 2 2
              (.missing 2 79)
              (.reject))))))

theorem deficientFourPowerGeneralPart092 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,22,31,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,9,21,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart092Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart093Tree : Tree :=
  .step (.primeLo 2 17) <|
  .step (.primeLo 3 19) <|
  .splitBase 1 5
    (.use 0)
    (.step (.primeLo 1 7) <|
    .step (.dropHi 4 53) <|
    .splitBase 2 33
      (.step (.primeHi 2 31) <|
      .splitBase 3 37
        (.use 1)
        (.step (.primeLo 3 41) <|
        .step (.dropHi 4 21) <|
        .splitExp 0 2
          (.step (.grow 0 13) <|
          .step (.dropHi 4 12) <|
          .step (.xLo 13) <|
          .reject)
          (.splitBase 2 21
            (.step (.primeHi 2 19) <|
            .step (.dropLo 4 12) <|
            .step (.xLo 13) <|
            .splitBase 3 81
              (.use 2)
              (.step (.primeLo 3 83) <|
              .step (.dropHi 4 16) <|
              .step (.xHi 13) <|
              .step (.dropLo 3 151) <|
              .splitBase 3 301
                (.step (.primeHi 3 293) <|
                .step (.dropLo 2 18) <|
                .step (.primeLo 2 19) <|
                .splitExp 0 4
                  (.missing 0 11)
                  (.reject))
                (.step (.primeLo 3 307) <|
                .splitBase 2 17
                  (.step (.dropLo 3 8988) <|
                  .step (.primeLo 3 8999) <|
                  .splitExp 0 4
                    (.missing 0 11)
                    (.reject))
                  (.step (.primeLo 2 19) <|
                  .splitExp 0 4
                    (.missing 0 11)
                    (.step (.dropLo 3 340) <|
                    .step (.primeLo 3 347) <|
                    .splitExp 1 2
                      (.step (.dropHi 3 427) <|
                      .step (.primeHi 3 421) <|
                      .splitExp 0 6
                        (.missing 0 1093)
                        (.step (.dropLo 3 394) <|
                        .step (.primeLo 3 397) <|
                        .splitExp 2 2
                          (.missing 2 127)
                          (.step (.dropLo 3 418) <|
                          .step (.primeLo 3 419) <|
                          .splitExp 0 8
                            (.step (.grow 0 13) <|
                            .missing 0 757)
                            (.reject))))
                      (.step (.dropLo 3 11858) <|
                      .step (.primeLo 3 11863) <|
                      .splitExp 0 6
                        (.missing 0 1093)
                        (.reject)))))))
            (.use 3))))
      (.step (.primeLo 2 37) <|
      .step (.primeLo 3 41) <|
      .step (.dropHi 4 12) <|
      .step (.xHi 9) <|
      .missing 4 5))

private def deficientFourPowerGeneralPart093Refs : List Known := [
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,17,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,9,0,5,0⟩], 1, deficientFourPowerGeneralPart089⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,31,2,0⟩, ⟨false,19,37,2,0⟩, ⟨true,9,53,5,0⟩], 1, deficientFourPowerGeneralPart090⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,41,81,2,0⟩, ⟨true,13,21,5,0⟩], 1, deficientFourPowerGeneralPart091⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,22,31,2,0⟩, ⟨false,41,0,2,0⟩, ⟨true,9,21,5,0⟩], 1, deficientFourPowerGeneralPart092⟩]

theorem deficientFourPowerGeneralPart093 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,7,2,0⟩, ⟨false,14,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,9,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart093Tree deficientFourPowerGeneralPart093Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart094Tree : Tree :=
  .step (.primeHi 1 7) <|
  .splitBase 0 3
    (.step (.dropLo 4 6) <|
    .step (.xLo 9) <|
    .splitBase 2 13
      (.step (.dropLo 4 11) <|
      .step (.xLo 13) <|
      .splitBase 3 21
        (.step (.primeHi 3 19) <|
        .step (.dropLo 2 8) <|
        .step (.dropLo 4 25) <|
        .step (.primeLo 2 11) <|
        .step (.primeLo 3 13) <|
        .splitBase 1 5
          (.reject)
          (.step (.primeLo 1 7) <|
          .splitExp 0 2
            (.splitBase 3 15
              (.step (.primeHi 3 13) <|
              .step (.primeHi 2 11) <|
              .step (.dropLo 4 22021) <|
              .splitExp 1 2
                (.step (.grow 1 19) <|
                .splitExp 2 2
                  (.splitExp 3 2
                    (.step (.grow 3 61) <|
                    .step (.dropHi 4 22022) <|
                    .step (.xHi 22021) <|
                    .reject)
                    (.reject))
                  (.reject))
                (.reject))
              (.step (.primeLo 3 17) <|
              .step (.dropHi 4 65) <|
              .splitBase 2 11
                (.step (.grow 0 13) <|
                .step (.dropLo 4 39) <|
                .step (.xLo 65) <|
                .step (.dropHi 3 17) <|
                .splitExp 1 2
                  (.missing 1 19)
                  (.splitExp 2 2
                    (.missing 2 19)
                    (.splitExp 3 2
                      (.missing 3 307)
                      (.reject))))
                (.step (.primeLo 2 13) <|
                .step (.dropHi 4 33) <|
                .splitBase 3 17
                  (.step (.dropLo 4 29) <|
                  .splitExp 1 2
                    (.missing 1 19)
                    (.step (.dropLo 4 32) <|
                    .step (.xLo 33) <|
                    .splitExp 2 2
                      (.missing 2 61)
                      (.splitExp 3 2
                        (.missing 3 307)
                        (.reject))))
                  (.step (.primeLo 3 19) <|
                  .step (.dropHi 4 27) <|
                  .step (.xHi 25) <|
                  .reject))))
            (.use 0)))
        (.use 1))
      (.use 2))
    (.step (.primeLo 0 5) <|
    .step (.primeLo 1 7) <|
    .step (.primeLo 2 11) <|
    .step (.primeLo 3 13) <|
    .step (.dropHi 2 79) <|
    .step (.dropHi 4 7) <|
    .step (.xHi 5) <|
    .missing 4 3)

private def deficientFourPowerGeneralPart094Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,13,19,2,0⟩, ⟨true,25,0,5,0⟩], 1, deficientFourPowerGeneralPart000⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,5,7,2,0⟩, ⟨false,7,13,2,0⟩, ⟨false,22,0,2,0⟩, ⟨true,13,0,5,0⟩], 1, deficientFourPowerGeneralPart012⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,5,7,2,0⟩, ⟨false,14,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,9,0,5,0⟩], 1, deficientFourPowerGeneralPart093⟩]

theorem deficientFourPowerGeneralPart094 : Closed (#v[⟨false,3,5,2,0⟩, ⟨false,5,9,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,5,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart094Tree deficientFourPowerGeneralPart094Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
