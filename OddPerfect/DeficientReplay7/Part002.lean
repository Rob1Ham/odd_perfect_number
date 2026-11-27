module

public import OddPerfect.DeficientReplay7.Part001

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour7Part005Tree : Tree :=
  .step (.dropLo 4 16) <|
  .step (.xLo 17) <|
  .splitBase 3 57
    (.step (.primeHi 3 53) <|
    .step (.dropLo 4 24) <|
    .step (.xLo 25) <|
    .splitBase 3 37
      (.step (.dropLo 4 30) <|
      .step (.xLo 33) <|
      .splitBase 2 11
        (.use 0)
        (.step (.primeLo 2 13) <|
        .step (.dropHi 4 53) <|
        .splitBase 3 31
          (.step (.dropLo 4 35) <|
          .step (.xLo 37) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 4 41) <|
            .splitExp 1 2
              (.missing 1 19)
              (.step (.dropLo 4 46) <|
              .step (.xLo 49) <|
              .step (.dropHi 3 30) <|
              .step (.primeHi 3 29) <|
              .step (.dropLo 4 52) <|
              .step (.xLo 53) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 2 2
                  (.missing 2 61)
                  (.reject)))))
          (.step (.primeLo 3 37) <|
          .step (.dropHi 4 37) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .reject)
            (.splitExp 1 2
              (.missing 1 19)
              (.step (.dropLo 4 37) <|
              .missing 4 19)))))
      (.use 1))
    (.step (.primeLo 3 59) <|
    .step (.dropHi 4 46) <|
    .step (.xHi 45) <|
    .splitBase 3 117
      (.step (.primeHi 3 113) <|
      .step (.dropLo 4 19) <|
      .step (.xLo 21) <|
      .splitBase 2 11
        (.use 2)
        (.step (.primeLo 2 13) <|
        .step (.dropHi 4 26) <|
        .step (.xHi 25) <|
        .splitBase 3 77
          (.step (.primeHi 3 73) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 4 23) <|
            .step (.xLo 25) <|
            .step (.dropHi 3 70) <|
            .step (.primeHi 3 67) <|
            .splitExp 1 2
              (.missing 1 19)
              (.step (.dropLo 3 66) <|
              .step (.primeLo 3 67) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))))
          (.step (.primeLo 3 79) <|
          .step (.dropHi 4 24) <|
          .step (.xHi 21) <|
          .missing 4 11)))
      (.step (.primeLo 3 127) <|
      .step (.dropHi 4 32) <|
      .step (.xHi 29) <|
      .splitBase 2 11
        (.step (.dropLo 4 22) <|
        .step (.xLo 25) <|
        .splitBase 3 253
          (.step (.primeHi 3 251) <|
          .splitExp 0 4
            (.step (.dropHi 4 28) <|
            .step (.xHi 25) <|
            .missing 4 13)
            (.step (.dropLo 4 26) <|
            .step (.xLo 29) <|
            .missing 4 5))
          (.step (.primeLo 3 257) <|
          .step (.dropHi 4 28) <|
          .step (.xHi 25) <|
          .missing 4 13))
        (.step (.primeLo 2 13) <|
        .step (.dropHi 4 21) <|
        .splitBase 3 253
          (.step (.primeHi 3 251) <|
          .step (.dropLo 4 18) <|
          .step (.xLo 21) <|
          .missing 4 11)
          (.step (.primeLo 3 257) <|
          .step (.dropHi 4 19) <|
          .step (.xHi 17) <|
          .step (.dropLo 3 261) <|
          .step (.primeLo 3 263) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 6150) <|
            .step (.primeLo 3 6151) <|
            .splitExp 1 2
              (.missing 1 19)
              (.reject))))))

private def deficientFour7Part005Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,33,317,1,1⟩], 1, deficientFour7Part002⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,38,53,2,0⟩, ⟨true,25,317,1,1⟩], 1, deficientFour7Part003⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,59,113,2,0⟩, ⟨true,21,45,1,1⟩], 1, deficientFour7Part004⟩]

theorem deficientFour7Part005 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,29,0,2,0⟩, ⟨true,13,317,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part005Tree deficientFour7Part005Refs _ _ (by decide +kernel)

private def deficientFour7Part006Tree : Tree :=
  .step (.primeLo 3 59) <|
  .step (.dropHi 4 17) <|
  .splitBase 3 117
    (.step (.primeHi 3 113) <|
    .splitBase 3 77
      (.step (.primeHi 3 73) <|
      .step (.dropLo 4 14) <|
      .step (.xLo 17) <|
      .step (.dropHi 2 17) <|
      .step (.dropHi 3 64) <|
      .step (.primeHi 3 61) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitExp 1 2
          (.missing 1 19)
          (.reject)))
      (.step (.primeLo 3 79) <|
      .step (.dropHi 4 16) <|
      .step (.xHi 13) <|
      .step (.dropLo 3 80) <|
      .step (.primeLo 3 83) <|
      .splitBase 2 17
        (.reject)
        (.step (.primeLo 2 19) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject))))
    (.step (.primeLo 3 127) <|
    .step (.dropHi 4 14) <|
    .step (.xHi 13) <|
    .splitBase 3 253
      (.step (.primeHi 3 251) <|
      .splitBase 2 17
        (.step (.dropLo 3 165) <|
        .step (.primeLo 3 167) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject))
        (.step (.primeLo 2 19) <|
        .step (.dropHi 3 187) <|
        .step (.primeHi 3 181) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitExp 1 2
            (.reject)
            (.step (.dropLo 3 166) <|
            .step (.primeLo 3 167) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 3 178) <|
              .step (.primeLo 3 179) <|
              .splitExp 2 2
                (.missing 2 127)
                (.reject))))))
      (.step (.primeLo 3 257) <|
      .step (.dropHi 2 18) <|
      .step (.primeHi 2 17) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 3 420) <|
        .step (.primeLo 3 421) <|
        .splitExp 1 2
          (.missing 1 19)
          (.reject))))

theorem deficientFour7Part006 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,58,0,2,0⟩, ⟨true,13,25,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part006Tree [] _ _ (by decide +kernel)

private def deficientFour7Part007Tree : Tree :=
  .step (.dropLo 4 12) <|
  .step (.xLo 13) <|
  .splitBase 2 13
    (.use 0)
    (.step (.primeLo 2 17) <|
    .step (.dropHi 4 25) <|
    .splitBase 3 57
      (.step (.primeHi 3 53) <|
      .step (.dropLo 4 15) <|
      .step (.xLo 17) <|
      .splitBase 3 37
        (.splitBase 3 31
          (.step (.dropLo 4 19) <|
          .step (.xLo 21) <|
          .splitBase 2 17
            (.splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 4 23) <|
              .step (.xLo 25) <|
              .missing 4 13))
            (.step (.primeLo 2 19) <|
            .step (.dropHi 3 30) <|
            .step (.dropHi 4 22) <|
            .step (.primeHi 3 29) <|
            .step (.xHi 21) <|
            .missing 4 11))
          (.step (.primeLo 3 37) <|
          .step (.dropHi 4 21) <|
          .splitBase 2 17
            (.step (.dropLo 4 19) <|
            .step (.xLo 21) <|
            .missing 4 11)
            (.step (.primeLo 2 19) <|
            .step (.dropHi 4 18) <|
            .step (.xHi 17) <|
            .splitExp 0 4
              (.missing 0 11)
              (.reject))))
        (.step (.primeLo 3 41) <|
        .step (.dropHi 4 20) <|
        .step (.xHi 17) <|
        .splitBase 2 17
          (.step (.dropLo 3 43) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 52) <|
            .step (.primeLo 3 53) <|
            .splitExp 1 2
              (.missing 1 19)
              (.reject)))
          (.step (.primeLo 2 19) <|
          .step (.dropHi 3 45) <|
          .step (.primeHi 3 43) <|
          .splitExp 0 4
            (.missing 0 11)
            (.splitExp 1 2
              (.reject)
              (.reject)))))
      (.use 1))

private def deficientFour7Part007Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,29,0,2,0⟩, ⟨true,13,317,1,1⟩], 1, deficientFour7Part005⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,17,19,2,0⟩, ⟨false,58,0,2,0⟩, ⟨true,13,25,1,1⟩], 1, deficientFour7Part006⟩]

theorem deficientFour7Part007 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,29,0,2,0⟩, ⟨true,9,317,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part007Tree deficientFour7Part007Refs _ _ (by decide +kernel)

private def deficientFour7Part008Tree : Tree :=
  .step (.primeHi 2 19) <|
  .splitBase 3 25
    (.step (.primeHi 3 23) <|
    .step (.dropLo 4 13) <|
    .splitExp 0 2
      (.splitBase 2 13
        (.step (.dropLo 4 20) <|
        .step (.xLo 21) <|
        .splitBase 3 15
          (.step (.primeHi 3 13) <|
          .step (.primeHi 2 11) <|
          .step (.dropLo 4 22021) <|
          .splitExp 1 2
            (.step (.grow 1 19) <|
            .splitExp 2 2
              (.splitExp 3 2
                (.step (.grow 3 61) <|
                .step (.dropHi 4 22021) <|
                .last 4)
                (.reject))
              (.reject))
            (.reject))
          (.step (.primeLo 3 17) <|
          .step (.dropHi 4 64) <|
          .step (.xHi 61) <|
          .step (.fix 0 13 2) <|
          .step (.dropHi 3 22) <|
          .step (.dropHi 4 32) <|
          .step (.primeHi 3 19) <|
          .step (.xHi 29) <|
          .step (.dropLo 4 25) <|
          .splitBase 3 17
            (.step (.dropLo 4 29) <|
            .missing 4 5)
            (.step (.primeLo 3 19) <|
            .step (.dropHi 4 26) <|
            .step (.xHi 25) <|
            .splitExp 1 2
              (.reject)
              (.reject))))
        (.step (.primeLo 2 17) <|
        .step (.primeLo 3 19) <|
        .step (.grow 0 13) <|
        .step (.dropHi 4 17) <|
        .step (.xHi 13) <|
        .step (.dropLo 2 18) <|
        .step (.dropLo 3 22) <|
        .step (.primeLo 2 19) <|
        .step (.primeLo 3 23) <|
        .splitExp 1 2
          (.reject)
          (.reject)))
      (.use 0))
    (.step (.primeLo 3 29) <|
    .step (.dropHi 4 319) <|
    .step (.xHi 317) <|
    .splitExp 0 2
      (.step (.dropHi 4 23) <|
      .step (.xHi 21) <|
      .splitBase 2 13
        (.step (.dropLo 4 11) <|
        .step (.xLo 13) <|
        .step (.dropHi 3 540) <|
        .step (.primeHi 3 523) <|
        .splitBase 3 53
          (.splitBase 3 37
            (.step (.dropLo 4 15) <|
            .step (.xLo 17) <|
            .step (.fix 0 13 2) <|
            .step (.dropHi 3 29) <|
            .step (.dropHi 4 17) <|
            .splitExp 1 2
              (.missing 1 19)
              (.reject))
            (.step (.primeLo 3 41) <|
            .step (.dropHi 4 19) <|
            .step (.xHi 17) <|
            .splitBase 2 11
              (.step (.grow 0 13) <|
              .step (.dropLo 3 44) <|
              .step (.dropLo 4 17) <|
              .step (.primeLo 3 47) <|
              .step (.xLo 65) <|
              .reject)
              (.step (.primeLo 2 13) <|
              .step (.dropHi 4 14) <|
              .step (.xHi 13) <|
              .step (.dropLo 3 49) <|
              .step (.primeLo 3 53) <|
              .splitExp 1 2
                (.missing 1 19)
                (.reject))))
          (.step (.primeLo 3 59) <|
          .step (.dropHi 2 12) <|
          .step (.dropHi 4 16) <|
          .step (.primeHi 2 11) <|
          .step (.xHi 13) <|
          .step (.grow 0 13) <|
          .step (.dropLo 3 181) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 3 375) <|
            .step (.primeLo 3 379) <|
            .splitExp 2 2
              (.missing 2 19)
              (.step (.dropLo 3 521) <|
              .splitExp 1 4
                (.splitExp 2 4
                  (.missing 2 5)
                  (.reject))
                (.reject)))))
        (.step (.primeLo 2 17) <|
        .step (.grow 0 13) <|
        .step (.dropHi 3 189) <|
        .step (.dropHi 4 12) <|
        .step (.primeHi 3 181) <|
        .step (.xLo 13) <|
        .reject))
      (.use 1))

private def deficientFour7Part008Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨true,13,0,1,1⟩], 1, deficientFour7Part001⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,29,0,2,0⟩, ⟨true,9,317,1,1⟩], 1, deficientFour7Part007⟩]

theorem deficientFour7Part008 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,21,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,9,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part008Tree deficientFour7Part008Refs _ _ (by decide +kernel)

private def deficientFour7Part009Tree : Tree :=
  .step (.primeHi 3 53) <|
  .step (.dropLo 4 10) <|
  .step (.xLo 13) <|
  .step (.dropHi 2 41) <|
  .splitBase 2 29
    (.splitBase 3 37
      (.splitBase 2 25
        (.step (.primeHi 2 23) <|
        .step (.dropLo 4 15) <|
        .step (.xLo 17) <|
        .step (.dropHi 3 31) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitExp 1 2
            (.missing 1 19)
            (.reject)))
        (.step (.primeLo 2 29) <|
        .step (.primeLo 3 31) <|
        .step (.dropHi 4 14) <|
        .step (.xHi 13) <|
        .step (.dropLo 3 32) <|
        .step (.primeLo 3 37) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitExp 1 2
            (.missing 1 19)
            (.reject))))
      (.step (.primeLo 3 41) <|
      .step (.dropHi 4 15) <|
      .step (.xHi 13) <|
      .splitBase 2 25
        (.step (.primeHi 2 23) <|
        .step (.dropLo 3 45) <|
        .step (.primeLo 3 47) <|
        .splitExp 0 4
          (.missing 0 11)
          (.reject))
        (.step (.primeLo 2 29) <|
        .step (.dropHi 3 41) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitExp 1 2
            (.missing 1 19)
            (.splitExp 0 6
              (.missing 0 1093)
              (.reject))))))
    (.step (.primeLo 2 31) <|
    .step (.primeLo 3 37) <|
    .step (.dropHi 2 31) <|
    .step (.dropHi 3 38) <|
    .step (.dropHi 4 13) <|
    .step (.primeHi 3 37) <|
    .splitExp 0 4
      (.missing 0 11)
      (.splitExp 1 2
        (.missing 1 19)
        (.reject)))

theorem deficientFour7Part009 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,23,43,2,0⟩, ⟨false,29,57,2,0⟩, ⟨true,9,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part009Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
