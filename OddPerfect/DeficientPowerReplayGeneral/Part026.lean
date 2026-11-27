module

public import OddPerfect.DeficientPowerReplayGeneral.Part025

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFourPowerGeneralPart125Tree : Tree :=
  .step (.primeHi 2 53) <|
  .step (.dropLo 3 38) <|
  .step (.primeLo 3 41) <|
  .splitBase 3 81
    (.step (.primeHi 3 79) <|
    .step (.dropLo 1 27) <|
    .step (.dropLo 2 31) <|
    .step (.primeLo 1 29) <|
    .splitBase 2 39
      (.step (.primeHi 2 37) <|
      .step (.primeHi 1 31) <|
      .reject)
      (.step (.primeLo 2 41) <|
      .step (.primeLo 3 43) <|
      .splitBase 1 33
        (.step (.primeHi 1 31) <|
        .step (.dropLo 2 43) <|
        .step (.dropLo 3 59) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 1 30) <|
          .step (.dropLo 2 51) <|
          .step (.dropLo 3 75) <|
          .step (.primeLo 1 31) <|
          .step (.primeLo 2 53) <|
          .step (.primeLo 3 79) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.splitExp 1 2
                  (.missing 1 331)
                  (.reject))))))
        (.step (.primeLo 1 37) <|
        .splitBase 3 55
          (.step (.primeHi 3 53) <|
          .step (.primeHi 2 47) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 1 41) <|
            .step (.dropLo 2 44) <|
            .step (.dropLo 3 50) <|
            .step (.primeLo 2 47) <|
            .step (.primeLo 3 53) <|
            .step (.dropHi 1 42) <|
            .step (.primeHi 1 41) <|
            .reject))
          (.step (.primeLo 3 59) <|
          .step (.dropHi 2 50) <|
          .step (.primeHi 2 47) <|
          .splitExp 0 4
            (.missing 0 11)
            (.splitBase 3 67
              (.splitBase 1 39
                (.step (.primeHi 1 37) <|
                .step (.dropLo 2 44) <|
                .step (.dropLo 3 62) <|
                .step (.primeLo 2 47) <|
                .step (.primeLo 3 67) <|
                .reject)
                (.step (.primeLo 1 41) <|
                .step (.primeLo 2 43) <|
                .step (.dropHi 1 42) <|
                .step (.dropHi 2 44) <|
                .step (.dropHi 3 61) <|
                .step (.primeHi 2 43) <|
                .step (.primeHi 1 41) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject)))
              (.step (.primeLo 3 71) <|
              .step (.dropHi 1 39) <|
              .step (.dropHi 2 44) <|
              .step (.primeHi 2 43) <|
              .step (.primeHi 1 37) <|
              .splitBase 3 73
                (.step (.dropLo 2 42) <|
                .step (.primeLo 2 43) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject))
                (.step (.primeLo 3 79) <|
                .step (.dropHi 2 41) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject))))))))
    (.use 0)

private def deficientFourPowerGeneralPart125Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,53,2,0⟩, ⟨false,82,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart124⟩]

theorem deficientFourPowerGeneralPart125 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,57,2,0⟩, ⟨false,31,0,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart125Tree deficientFourPowerGeneralPart125Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart126Tree : Tree :=
  .step (.primeHi 3 157) <|
  .splitBase 2 69
    (.step (.primeHi 2 67) <|
    .splitExp 0 4
      (.missing 0 11)
      (.reject))
    (.step (.primeLo 2 71) <|
    .splitExp 0 4
      (.missing 0 11)
      (.splitBase 3 127
        (.step (.dropLo 2 78) <|
        .step (.primeLo 2 79) <|
        .splitBase 3 115
          (.step (.primeHi 3 113) <|
          .step (.dropLo 2 85) <|
          .step (.primeLo 2 89) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 111) <|
            .step (.primeLo 3 113) <|
            .splitExp 1 2
              (.missing 1 7)
              (.splitSpecial 5
                (.missing 4 7)
                (.reject))))
          (.step (.primeLo 3 127) <|
          .step (.dropHi 2 82) <|
          .step (.primeHi 2 79) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject)))
        (.step (.primeLo 3 131) <|
        .step (.dropHi 2 80) <|
        .step (.primeHi 2 79) <|
        .splitBase 2 73
          (.step (.dropLo 3 145) <|
          .step (.primeLo 3 149) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 2 72) <|
            .step (.dropLo 3 154) <|
            .step (.primeLo 2 73) <|
            .step (.primeLo 3 157) <|
            .splitExp 1 2
              (.missing 1 7)
              (.splitSpecial 5
                (.missing 4 7)
                (.reject))))
          (.step (.primeLo 2 79) <|
          .step (.dropHi 3 136) <|
          .step (.primeHi 3 131) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject)))))

theorem deficientFourPowerGeneralPart126 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,89,2,0⟩, ⟨false,107,161,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart126Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart127Tree : Tree :=
  .step (.primeLo 3 223) <|
  .step (.dropHi 2 64) <|
  .step (.primeHi 2 61) <|
  .step (.dropLo 3 240) <|
  .step (.primeLo 3 241) <|
  .splitBase 3 277
    (.splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 60) <|
      .step (.dropLo 3 266) <|
      .step (.primeLo 2 61) <|
      .step (.primeLo 3 269) <|
      .splitExp 1 2
        (.missing 1 7)
        (.step (.dropLo 3 272) <|
        .step (.primeLo 3 277) <|
        .splitSpecial 5
          (.missing 4 7)
          (.reject))))
    (.step (.primeLo 3 281) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitBase 2 59
        (.step (.dropLo 3 313) <|
        .splitBase 3 321
          (.step (.primeHi 3 317) <|
          .splitExp 1 2
            (.missing 1 7)
            (.reject))
          (.step (.primeLo 3 331) <|
          .splitExp 1 2
            (.missing 1 7)
            (.splitSpecial 5
              (.missing 4 7)
              (.splitExp 0 8
                (.missing 0 13)
                (.reject)))))
        (.step (.primeLo 2 61) <|
        .step (.dropHi 3 281) <|
        .splitExp 1 2
          (.missing 1 7)
          (.splitSpecial 5
            (.missing 4 7)
            (.splitExp 0 8
              (.missing 0 13)
              (.splitExp 0 10
                (.splitExp 2 2
                  (.missing 2 13)
                  (.reject))
                (.reject)))))))

theorem deficientFourPowerGeneralPart127 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,71,2,0⟩, ⟨false,218,331,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart127Tree [] _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart128Tree : Tree :=
  .step (.primeLo 3 107) <|
  .step (.dropHi 1 26) <|
  .step (.dropHi 2 93) <|
  .step (.primeHi 2 89) <|
  .step (.primeHi 1 23) <|
  .splitBase 3 161
    (.use 0)
    (.step (.primeLo 3 163) <|
    .step (.dropHi 2 72) <|
    .step (.primeHi 2 71) <|
    .splitExp 0 4
      (.missing 0 11)
      (.splitBase 3 217
        (.step (.primeHi 3 211) <|
        .step (.dropLo 2 63) <|
        .step (.primeLo 2 67) <|
        .step (.dropHi 3 198) <|
        .step (.primeHi 3 197) <|
        .splitBase 3 177
          (.step (.primeHi 3 173) <|
          .splitBase 2 67
            (.reject)
            (.step (.primeLo 2 71) <|
            .step (.dropHi 3 169) <|
            .step (.primeHi 3 167) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 3 164) <|
              .step (.primeLo 3 167) <|
              .splitExp 1 2
                (.missing 1 7)
                (.splitSpecial 5
                  (.missing 4 7)
                  (.reject)))))
          (.step (.primeLo 3 179) <|
          .step (.dropHi 2 69) <|
          .step (.primeHi 2 67) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 191) <|
            .splitBase 3 193
              (.splitExp 1 2
                (.missing 1 7)
                (.reject))
              (.step (.primeLo 3 197) <|
              .splitExp 1 2
                (.missing 1 7)
                (.splitSpecial 5
                  (.missing 4 7)
                  (.splitExp 0 8
                    (.missing 0 13)
                    (.reject)))))))
        (.use 1)))

private def deficientFourPowerGeneralPart128Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,89,2,0⟩, ⟨false,107,161,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart126⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,23,23,2,0⟩, ⟨false,59,71,2,0⟩, ⟨false,218,331,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart127⟩]

theorem deficientFourPowerGeneralPart128 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,59,97,2,0⟩, ⟨false,104,331,2,0⟩, ⟨true,5,5,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart128Tree deficientFourPowerGeneralPart128Refs _ _ (by decide +kernel)

private def deficientFourPowerGeneralPart129Tree : Tree :=
  .step (.primeLo 1 23) <|
  .step (.primeLo 2 29) <|
  .step (.primeLo 3 31) <|
  .step (.dropHi 4 6) <|
  .step (.xHi 5) <|
  .splitExp 0 2
    (.missing 0 13)
    (.splitBase 1 45
      (.step (.primeHi 1 43) <|
      .splitBase 2 57
        (.use 0)
        (.step (.primeLo 2 59) <|
        .step (.primeLo 3 61) <|
        .step (.dropHi 1 32) <|
        .step (.dropHi 2 281) <|
        .step (.dropHi 3 334) <|
        .step (.primeHi 3 331) <|
        .step (.primeHi 1 31) <|
        .splitBase 2 97
          (.splitBase 3 103
            (.splitBase 1 25
              (.step (.primeHi 1 23) <|
              .step (.dropLo 2 68) <|
              .step (.dropLo 3 71) <|
              .step (.primeLo 2 71) <|
              .step (.primeLo 3 73) <|
              .splitExp 0 4
                (.missing 0 11)
                (.step (.dropLo 2 91) <|
                .step (.dropLo 3 97) <|
                .step (.primeLo 2 97) <|
                .step (.primeLo 3 101) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.splitBase 3 101
                    (.reject)
                    (.step (.primeLo 3 103) <|
                    .splitExp 1 2
                      (.missing 1 7)
                      (.splitSpecial 5
                        (.missing 4 7)
                        (.splitExp 0 8
                          (.missing 0 13)
                          (.reject)))))))
              (.step (.primeLo 1 29) <|
              .step (.dropHi 2 77) <|
              .step (.dropHi 3 81) <|
              .step (.primeHi 3 79) <|
              .step (.primeHi 2 73) <|
              .splitExp 0 4
                (.missing 0 11)
                (.splitBase 3 67
                  (.step (.primeHi 2 61) <|
                  .step (.dropLo 1 30) <|
                  .step (.dropLo 3 63) <|
                  .step (.primeLo 1 31) <|
                  .step (.primeLo 3 67) <|
                  .step (.dropHi 2 60) <|
                  .step (.primeHi 2 59) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.reject))
                  (.step (.primeLo 3 71) <|
                  .step (.dropHi 1 30) <|
                  .step (.dropHi 2 66) <|
                  .step (.primeHi 2 61) <|
                  .step (.primeHi 1 29) <|
                  .step (.dropLo 3 74) <|
                  .step (.primeLo 3 79) <|
                  .step (.dropHi 2 60) <|
                  .step (.primeHi 2 59) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.reject)))))
            (.use 1))
          (.step (.primeLo 2 101) <|
          .step (.primeLo 3 103) <|
          .reject)))
      (.step (.primeLo 1 47) <|
      .step (.primeLo 2 53) <|
      .step (.primeLo 3 59) <|
      .reject))

private def deficientFourPowerGeneralPart129Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,57,2,0⟩, ⟨false,31,0,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart125⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,23,31,2,0⟩, ⟨false,59,97,2,0⟩, ⟨false,104,331,2,0⟩, ⟨true,5,5,5,0⟩], 1, deficientFourPowerGeneralPart128⟩]

theorem deficientFourPowerGeneralPart129 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,22,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,5,17,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFourPowerGeneralPart129Tree deficientFourPowerGeneralPart129Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
