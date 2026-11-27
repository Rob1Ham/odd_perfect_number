module

public import OddPerfect.DeficientReplay7.Part002

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def closedSecond7Tree : Tree :=
  .step (.primeLo 2 11) <|
  .step (.primeLo 3 13) <|
  .step (.dropLo 4 6) <|
  .step (.xLo 9) <|
  .splitBase 2 21
    (.use 0)
    (.step (.primeLo 2 23) <|
    .step (.primeLo 3 29) <|
    .step (.dropHi 4 18) <|
    .step (.xHi 17) <|
    .splitExp 0 2
      (.step (.grow 0 13) <|
      .step (.dropHi 2 32) <|
      .step (.dropHi 3 47) <|
      .step (.dropHi 4 10) <|
      .step (.primeHi 2 31) <|
      .step (.xLo 13) <|
      .reject)
      (.splitBase 2 45
        (.step (.primeHi 2 43) <|
        .splitBase 3 57
          (.use 1)
          (.step (.primeLo 3 59) <|
          .step (.dropHi 4 13) <|
          .splitBase 2 29
            (.splitBase 3 117
              (.step (.primeHi 3 113) <|
              .step (.dropLo 4 10) <|
              .step (.xLo 13) <|
              .step (.dropHi 2 24) <|
              .step (.dropHi 3 67) <|
              .step (.primeHi 2 23) <|
              .splitExp 0 4
                (.missing 0 11)
                (.splitExp 1 2
                  (.missing 1 19)
                  (.step (.dropLo 3 64) <|
                  .step (.primeLo 3 67) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.splitExp 2 2
                      (.missing 2 79)
                      (.splitExp 1 4
                        (.splitExp 0 8
                          (.step (.grow 0 13) <|
                          .missing 0 757)
                          (.splitExp 0 10
                            (.splitExp 3 2
                              (.missing 3 31)
                              (.reject))
                            (.reject)))
                        (.reject))))))
              (.step (.primeLo 3 127) <|
              .step (.dropHi 4 11) <|
              .step (.xHi 9) <|
              .missing 4 5))
            (.step (.primeLo 2 31) <|
            .step (.dropHi 4 11) <|
            .step (.xHi 9) <|
            .missing 4 5)))
        (.step (.primeLo 2 47) <|
        .step (.primeLo 3 53) <|
        .step (.dropHi 2 110) <|
        .step (.dropHi 3 150) <|
        .step (.dropHi 4 10) <|
        .step (.primeHi 3 149) <|
        .step (.primeHi 2 109) <|
        .step (.xHi 9) <|
        .missing 4 5)))

private def closedSecond7Refs : List Known := [
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,21,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,9,0,1,1⟩], 1, deficientFour7Part008⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,57,2,0⟩, ⟨true,9,17,1,1⟩], 1, deficientFour7Part009⟩]

theorem closedSecond7 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound closedSecond7Tree closedSecond7Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
