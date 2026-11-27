module

public import OddPerfect.DeficientReplay5.Part014

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def closedSecond5Tree : Tree :=
  .step (.primeLo 2 7) <|
  .step (.primeLo 3 11) <|
  .step (.dropLo 2 9) <|
  .step (.dropLo 4 9) <|
  .step (.primeLo 2 11) <|
  .step (.primeLo 3 13) <|
  .splitBase 2 21
    (.step (.primeHi 2 19) <|
    .step (.dropLo 3 18) <|
    .step (.dropLo 4 18) <|
    .step (.primeLo 3 19) <|
    .step (.xLo 21) <|
    .splitBase 3 37
      (.step (.dropLo 2 12) <|
      .step (.dropLo 4 34) <|
      .step (.primeLo 2 13) <|
      .step (.xLo 37) <|
      .splitExp 0 2
        (.splitBase 3 25
          (.step (.primeHi 3 23) <|
          .step (.dropLo 2 15) <|
          .step (.dropLo 4 83) <|
          .step (.primeLo 2 17) <|
          .step (.xLo 85) <|
          .step (.grow 0 13) <|
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
          .splitBase 2 15
            (.step (.primeHi 2 13) <|
            .step (.dropLo 3 33) <|
            .step (.dropLo 4 299) <|
            .step (.primeLo 3 37) <|
            .step (.xLo 301) <|
            .splitExp 1 2
              (.step (.grow 1 31) <|
              .step (.dropHi 4 348) <|
              .step (.xLo 341) <|
              .step (.xHi 341) <|
              .missing 4 19)
              (.reject))
            (.step (.primeLo 2 17) <|
            .step (.grow 0 13) <|
            .step (.dropHi 4 151) <|
            .step (.xLo 65) <|
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
                  .step (.dropHi 3 30) <|
                  .step (.dropHi 4 75) <|
                  .step (.primeHi 3 29) <|
                  .step (.xHi 65) <|
                  .missing 4 11))
                (.step (.primeLo 3 37) <|
                .step (.dropHi 2 17) <|
                .step (.dropHi 4 69) <|
                .step (.xHi 65) <|
                .missing 4 11)))))
        (.reject))
      (.use 0))
    (.use 1)

private def closedSecond5Refs : List Known := [
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,38,0,2,0⟩, ⟨true,21,0,1,1⟩], 1, deficientFour5Part044⟩,
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,22,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,9,0,1,1⟩], 1, deficientFour5Part069⟩]

theorem closedSecond5 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound closedSecond5Tree closedSecond5Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
