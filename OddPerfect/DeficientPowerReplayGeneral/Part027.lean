module

public import OddPerfect.DeficientPowerReplayGeneral.Part026

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def closedPowerGeneralTree : Tree :=
  .step (.primeLo 1 5) <|
  .step (.primeLo 2 7) <|
  .step (.primeLo 3 11) <|
  .splitBase 0 5
    (.splitBase 1 9
      (.use 0)
      (.step (.primeLo 1 11) <|
      .step (.primeLo 2 13) <|
      .step (.primeLo 3 17) <|
      .step (.dropHi 0 4) <|
      .step (.dropHi 4 19) <|
      .step (.primeHi 0 3) <|
      .step (.xHi 17) <|
      .splitBase 1 21
        (.step (.primeHi 1 19) <|
        .splitBase 2 25
          (.step (.primeHi 2 23) <|
          .splitBase 3 33
            (.step (.primeHi 3 31) <|
            .splitExp 0 2
              (.step (.dropHi 4 11) <|
              .step (.xHi 9) <|
              .splitBase 1 13
                (.step (.dropLo 4 6) <|
                .step (.xLo 9) <|
                .missing 4 5)
                (.step (.primeLo 1 17) <|
                .step (.primeLo 2 19) <|
                .step (.primeLo 3 23) <|
                .missing 0 13))
              (.step (.dropLo 4 6) <|
              .step (.xLo 9) <|
              .splitBase 1 13
                (.splitBase 2 15
                  (.step (.primeHi 2 13) <|
                  .step (.primeHi 1 11) <|
                  .step (.dropLo 3 18) <|
                  .step (.dropLo 4 12) <|
                  .step (.primeLo 3 19) <|
                  .step (.xLo 13) <|
                  .splitBase 3 23
                    (.step (.dropLo 4 14) <|
                    .step (.xLo 17) <|
                    .step (.dropHi 3 19) <|
                    .splitExp 0 4
                      (.reject)
                      (.reject))
                    (.step (.primeLo 3 29) <|
                    .step (.dropHi 4 13) <|
                    .missing 4 7))
                  (.step (.primeLo 2 17) <|
                  .step (.primeLo 3 19) <|
                  .step (.dropHi 4 13) <|
                  .splitBase 3 23
                    (.step (.primeHi 2 19) <|
                    .splitBase 1 11
                      (.step (.dropLo 4 10) <|
                      .step (.xLo 13) <|
                      .missing 4 7)
                      (.step (.primeLo 1 13) <|
                      .step (.dropHi 4 11) <|
                      .step (.xHi 9) <|
                      .missing 4 5))
                    (.step (.primeLo 3 29) <|
                    .step (.dropHi 4 10) <|
                    .step (.xHi 9) <|
                    .missing 4 5)))
                (.step (.primeLo 1 17) <|
                .step (.primeLo 2 19) <|
                .step (.primeLo 3 23) <|
                .reject)))
            (.step (.primeLo 3 37) <|
            .step (.dropHi 4 12) <|
            .step (.xHi 9) <|
            .splitExp 0 2
              (.step (.dropHi 4 8) <|
              .step (.xHi 5) <|
              .step (.dropLo 1 17) <|
              .step (.dropLo 2 21) <|
              .step (.dropLo 3 247) <|
              .step (.primeLo 2 23) <|
              .step (.primeLo 3 251) <|
              .missing 0 13)
              (.splitBase 1 13
                (.step (.dropLo 4 6) <|
                .step (.xLo 9) <|
                .missing 4 5)
                (.step (.primeLo 1 17) <|
                .step (.primeLo 2 19) <|
                .step (.dropHi 4 7) <|
                .step (.xHi 5) <|
                .reject))))
          (.use 1))
        (.use 2)))
    (.step (.primeLo 0 7) <|
    .step (.primeLo 1 11) <|
    .step (.primeLo 2 13) <|
    .step (.primeLo 3 17) <|
    .reject)

private def closedPowerGeneralRefs : List Known := [
  ⟨#v[⟨false,3,5,2,0⟩, ⟨false,5,9,2,0⟩, ⟨false,7,0,2,0⟩, ⟨false,11,0,2,0⟩, ⟨true,5,0,5,0⟩], 1, deficientFourPowerGeneralPart094⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,26,0,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,5,17,5,0⟩], 1, deficientFourPowerGeneralPart121⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,22,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨false,17,0,2,0⟩, ⟨true,5,17,5,0⟩], 1, deficientFourPowerGeneralPart129⟩]

theorem closedPowerGeneral : Closed (#v[⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,5,0⟩] : Vector Slot 5) 1 :=
  Tree.sound closedPowerGeneralTree closedPowerGeneralRefs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
