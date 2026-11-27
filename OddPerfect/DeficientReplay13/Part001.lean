module

public import OddPerfect.DeficientTree

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour13Part000Tree : Tree :=
  .step (.primeHi 3 131) <|
  .step (.dropLo 2 45) <|
  .step (.primeLo 2 47) <|
  .splitBase 3 87
    (.step (.primeHi 3 83) <|
    .step (.dropLo 2 56) <|
    .step (.primeLo 2 59) <|
    .splitExp 0 4
      (.missing 0 11)
      (.reject))
    (.step (.primeLo 3 89) <|
    .splitBase 2 55
      (.step (.primeHi 2 53) <|
      .step (.dropLo 3 92) <|
      .step (.primeLo 3 97) <|
      .splitExp 0 4
        (.missing 0 11)
        (.reject))
      (.step (.primeLo 2 59) <|
      .step (.dropHi 3 122) <|
      .step (.primeHi 3 113) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 2 63
          (.step (.primeHi 2 61) <|
          .step (.dropLo 3 103) <|
          .splitBase 3 107
            (.splitExp 0 6
              (.missing 0 1093)
              (.reject))
            (.step (.primeLo 3 109) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 2
                (.step (.fix 1 61 2) <|
                .reject)
                (.reject))))
          (.step (.primeLo 2 67) <|
          .step (.dropHi 3 97) <|
          .splitBase 3 91
            (.step (.primeHi 3 89) <|
            .splitBase 2 67
              (.reject)
              (.step (.primeLo 2 71) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 2
                  (.missing 1 61)
                  (.reject))))
            (.step (.primeLo 3 97) <|
            .step (.dropHi 2 67) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 2
                (.missing 1 61)
                (.reject)))))))

theorem deficientFour13Part000 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,37,71,2,0⟩, ⟨false,67,133,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour13Part000Tree [] _ _ (by decide +kernel)

private def deficientFour13Part001Tree : Tree :=
  .step (.primeLo 3 317) <|
  .splitExp 0 4
    (.missing 0 11)
    (.step (.dropLo 2 38) <|
    .step (.dropLo 3 369) <|
    .step (.primeLo 2 41) <|
    .step (.primeLo 3 373) <|
    .step (.dropHi 3 1600) <|
    .step (.primeHi 3 1597) <|
    .splitBase 3 603
      (.step (.primeHi 3 601) <|
      .splitBase 2 41
        (.reject)
        (.step (.primeLo 2 43) <|
        .step (.dropHi 3 560) <|
        .step (.primeHi 3 557) <|
        .splitBase 3 445
          (.step (.primeHi 3 443) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 3 434) <|
            .step (.primeLo 3 439) <|
            .splitExp 1 2
              (.missing 1 61)
              (.reject)))
          (.step (.primeLo 3 449) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.splitExp 1 2
              (.missing 1 61)
              (.step (.dropLo 3 540) <|
              .step (.primeLo 3 541) <|
              .splitExp 0 8
                (.missing 0 757)
                (.step (.dropLo 3 553) <|
                .step (.primeLo 3 557) <|
                .splitExp 2 2
                  (.missing 2 631)
                  (.reject)))))))
      (.step (.primeLo 3 607) <|
      .step (.dropHi 2 42) <|
      .step (.primeHi 2 41) <|
      .step (.dropLo 3 644) <|
      .step (.primeLo 3 647) <|
      .splitBase 3 919
        (.splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 873) <|
          .step (.primeLo 3 877) <|
          .splitExp 1 2
            (.missing 1 61)
            (.reject)))
        (.step (.primeLo 3 929) <|
        .splitExp 0 6
          (.step (.fix 0 1093 3) <|
          .reject)
          (.splitExp 1 2
            (.missing 1 61)
            (.step (.dropLo 3 1443) <|
            .step (.primeLo 3 1447) <|
            .splitExp 0 8
              (.missing 0 757)
              (.step (.dropLo 3 1543) <|
              .splitBase 3 1569
                (.step (.primeHi 3 1567) <|
                .splitExp 2 2
                  (.missing 2 1723)
                  (.reject))
                (.step (.primeLo 3 1571) <|
                .splitExp 2 2
                  (.missing 2 1723)
                  (.step (.dropLo 3 1578) <|
                  .step (.primeLo 3 1579) <|
                  .splitExp 0 10
                    (.missing 0 23)
                    (.step (.dropLo 3 1591) <|
                    .step (.primeLo 3 1597) <|
                    .splitExp 1 4
                      (.reject)
                      (.reject))))))))))

theorem deficientFour13Part001 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,37,43,2,0⟩, ⟨false,314,0,2,0⟩, ⟨true,5,5,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour13Part001Tree [] _ _ (by decide +kernel)

private def deficientFour13Part002Tree : Tree :=
  .step (.primeLo 2 37) <|
  .step (.primeLo 3 41) <|
  .step (.dropHi 2 1600) <|
  .step (.dropHi 4 5) <|
  .step (.primeHi 2 1597) <|
  .splitExp 0 2
    (.reject)
    (.splitBase 2 71
      (.step (.dropLo 3 64) <|
      .step (.primeLo 3 67) <|
      .splitBase 3 133
        (.use 0)
        (.step (.primeLo 3 137) <|
        .step (.dropHi 2 56) <|
        .step (.primeHi 2 53) <|
        .splitBase 2 43
          (.step (.dropLo 3 157) <|
          .splitBase 3 313
            (.splitExp 0 4
              (.missing 0 11)
              (.reject))
            (.use 1))
          (.step (.primeLo 2 47) <|
          .step (.dropHi 3 262) <|
          .step (.primeHi 3 257) <|
          .splitExp 0 4
            (.missing 0 11)
            (.step (.dropLo 3 139) <|
            .splitBase 3 179
              (.step (.dropLo 2 48) <|
              .step (.primeLo 2 53) <|
              .step (.dropHi 3 160) <|
              .step (.primeHi 3 157) <|
              .splitBase 3 147
                (.step (.primeHi 3 139) <|
                .reject)
                (.step (.primeLo 3 149) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.splitExp 1 2
                    (.missing 1 61)
                    (.reject))))
              (.step (.primeLo 3 181) <|
              .step (.dropHi 2 51) <|
              .step (.primeHi 2 47) <|
              .step (.dropLo 3 211) <|
              .splitBase 3 231
                (.step (.primeHi 3 229) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject))
                (.step (.primeLo 3 233) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.splitExp 1 2
                    (.missing 1 61)
                    (.reject))))))))
      (.step (.primeLo 2 73) <|
      .step (.primeLo 3 79) <|
      .step (.dropHi 2 80) <|
      .step (.dropHi 3 87) <|
      .step (.primeHi 3 83) <|
      .step (.primeHi 2 79) <|
      .splitExp 0 4
        (.missing 0 11)
        (.splitBase 2 75
          (.step (.primeHi 2 73) <|
          .step (.dropLo 3 80) <|
          .step (.primeLo 3 83) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject))
          (.step (.primeLo 2 79) <|
          .step (.primeLo 3 83) <|
          .reject))))

private def deficientFour13Part002Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,37,71,2,0⟩, ⟨false,67,133,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour13Part000⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,13,13,2,0⟩, ⟨false,37,43,2,0⟩, ⟨false,314,0,2,0⟩, ⟨true,5,5,1,1⟩], 1, deficientFour13Part001⟩]

theorem deficientFour13Part002 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,34,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,5,9,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour13Part002Tree deficientFour13Part002Refs _ _ (by decide +kernel)

private def closedSecond13Tree : Tree :=
  .step (.primeLo 2 17) <|
  .step (.primeLo 3 19) <|
  .step (.dropHi 4 10) <|
  .step (.xHi 9) <|
  .splitBase 2 33
    (.step (.primeHi 2 31) <|
    .splitBase 3 37
      (.splitExp 0 2
        (.step (.dropHi 4 7) <|
        .step (.xHi 5) <|
        .step (.dropLo 2 28) <|
        .step (.dropLo 3 33) <|
        .step (.primeLo 2 29) <|
        .step (.primeLo 3 37) <|
        .reject)
        (.step (.dropLo 4 7) <|
        .step (.xLo 9) <|
        .missing 4 5))
      (.step (.primeLo 3 41) <|
      .step (.dropHi 4 7) <|
      .step (.xHi 5) <|
      .splitExp 0 2
        (.step (.dropHi 2 26) <|
        .step (.dropHi 3 411) <|
        .step (.primeHi 3 409) <|
        .step (.primeHi 2 23) <|
        .step (.dropLo 3 52) <|
        .step (.primeLo 3 53) <|
        .splitBase 3 93
          (.step (.primeHi 3 89) <|
          .step (.dropLo 2 19) <|
          .splitBase 2 19
            (.reject)
            (.step (.primeLo 2 23) <|
            .step (.dropHi 3 54) <|
            .step (.primeHi 3 53) <|
            .splitExp 1 2
              (.missing 1 61)
              (.reject)))
          (.step (.primeLo 3 97) <|
          .step (.dropHi 2 19) <|
          .step (.dropLo 3 104) <|
          .step (.primeLo 3 107) <|
          .splitBase 3 169
            (.step (.primeHi 3 167) <|
            .splitBase 2 17
              (.reject)
              (.step (.primeLo 2 19) <|
              .step (.dropHi 3 111) <|
              .step (.primeHi 3 109) <|
              .splitExp 1 2
                (.missing 1 61)
                (.reject)))
            (.step (.primeLo 3 173) <|
            .step (.dropHi 2 17) <|
            .step (.dropLo 3 323) <|
            .step (.primeLo 3 331) <|
            .splitExp 1 2
              (.missing 1 61)
              (.step (.dropLo 3 379) <|
              .splitExp 2 2
                (.missing 2 307)
                (.reject)))))
        (.reject)))
    (.use 0)

private def closedSecond13Refs : List Known := [
  ⟨#v[⟨false,3,3,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,34,0,2,0⟩, ⟨false,19,0,2,0⟩, ⟨true,5,9,1,1⟩], 1, deficientFour13Part002⟩]

theorem closedSecond13 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,13,13,2,0⟩, ⟨false,3,0,2,0⟩, ⟨false,3,0,2,0⟩, ⟨true,5,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound closedSecond13Tree closedSecond13Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
