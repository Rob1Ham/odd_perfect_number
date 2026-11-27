module

public import OddPerfect.DeficientTree

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour7Part000Tree : Tree :=
  .step (.dropLo 2 12) <|
  .step (.dropLo 4 142) <|
  .step (.primeLo 2 13) <|
  .step (.xLo 145) <|
  .splitBase 3 17
    (.step (.dropLo 4 1766) <|
    .step (.xLo 1769) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.xLo 1793) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.xLo 1881) <|
        .splitExp 2 2
          (.step (.grow 2 61) <|
          .step (.dropHi 4 2756) <|
          .step (.xLo 12749) <|
          .reject)
          (.step (.dropLo 4 8792) <|
          .step (.xLo 9405) <|
          .splitExp 3 2
            (.step (.grow 3 307) <|
            .reject)
            (.reject)))
        (.reject))
      (.reject))
    (.step (.primeLo 3 19) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 4 281) <|
      .step (.xLo 165) <|
      .step (.xHi 253) <|
      .splitExp 1 2
        (.reject)
        (.step (.dropLo 4 238) <|
        .step (.xLo 253) <|
        .missing 4 127))
      (.step (.dropLo 4 294) <|
      .step (.xLo 297) <|
      .splitExp 1 2
        (.step (.dropHi 4 426) <|
        .step (.xHi 425) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 334) <|
          .step (.xLo 337) <|
          .splitExp 2 2
            (.missing 2 61)
            (.step (.dropLo 4 394) <|
            .step (.xLo 397) <|
            .splitExp 3 2
              (.missing 3 127)
              (.step (.dropLo 4 418) <|
              .step (.xLo 421) <|
              .splitExp 0 8
                (.missing 0 757)
                (.reject)))))
        (.step (.dropLo 4 1854) <|
        .step (.xLo 1857) <|
        .splitExp 0 6
          (.step (.grow 0 1093) <|
          .step (.xLo 5465) <|
          .splitExp 2 2
            (.step (.grow 2 61) <|
            .reject)
            (.step (.dropLo 4 11519) <|
            .step (.xLo 14209) <|
            .splitExp 3 2
              (.step (.grow 3 127) <|
              .step (.dropHi 4 40616) <|
              .step (.xLo 416433) <|
              .reject)
              (.reject)))
          (.step (.dropLo 4 7528) <|
          .step (.xLo 7529) <|
          .splitExp 2 2
            (.step (.grow 2 61) <|
            .step (.xLo 7625) <|
            .splitExp 3 2
              (.step (.grow 3 127) <|
              .step (.dropHi 4 44369) <|
              .step (.xLo 23241) <|
              .step (.xHi 23241) <|
              .splitExp 1 4
                (.reject)
                (.splitExp 0 8
                  (.missing 0 757)
                  (.reject)))
              (.reject))
            (.reject)))))

theorem deficientFour7Part000 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,61,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part000Tree [] _ _ (by decide +kernel)

private def deficientFour7Part001Tree : Tree :=
  .step (.dropLo 4 24) <|
  .step (.xLo 25) <|
  .splitBase 2 13
    (.step (.dropLo 3 16) <|
    .step (.dropLo 4 60) <|
    .step (.primeLo 3 17) <|
    .step (.xLo 61) <|
    .splitBase 3 19
      (.use 0)
      (.step (.primeLo 3 23) <|
      .splitBase 2 11
        (.step (.dropLo 4 607) <|
        .step (.xLo 609) <|
        .splitExp 0 4
          (.splitExp 1 2
            (.step (.grow 1 19) <|
            .step (.dropHi 4 1229) <|
            .step (.xLo 665) <|
            .step (.xHi 1197) <|
            .splitExp 2 2
              (.reject)
              (.step (.dropLo 4 1110) <|
              .step (.xLo 1121) <|
              .splitExp 3 2
                (.missing 3 79)
                (.reject)))
            (.reject))
          (.reject))
        (.step (.primeLo 2 13) <|
        .step (.dropHi 4 110) <|
        .step (.xHi 109) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 75) <|
          .step (.xLo 77) <|
          .reject)
          (.step (.dropLo 4 77) <|
          .splitExp 1 2
            (.missing 1 19)
            (.step (.dropLo 4 99) <|
            .step (.xLo 101) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 4 103) <|
              .step (.xLo 105) <|
              .splitExp 2 2
                (.missing 2 61)
                (.step (.dropLo 4 108) <|
                .step (.xLo 109) <|
                .missing 4 5)))))))
    (.step (.primeLo 2 17) <|
    .step (.primeLo 3 19) <|
    .step (.dropHi 4 52) <|
    .step (.xHi 49) <|
    .splitBase 3 19
      (.step (.primeHi 2 17) <|
      .step (.dropLo 4 38) <|
      .step (.xLo 41) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 4 44) <|
        .step (.xLo 45) <|
        .splitExp 1 2
          (.step (.dropHi 4 45) <|
          .missing 4 23)
          (.reject)))
      (.step (.primeLo 3 23) <|
      .step (.dropHi 4 34) <|
      .step (.xHi 33) <|
      .splitBase 2 17
        (.step (.dropLo 4 28) <|
        .step (.xLo 29) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 30) <|
          .step (.xLo 33) <|
          .reject)
          (.step (.dropLo 4 31) <|
          .step (.xLo 33) <|
          .splitExp 1 2
            (.missing 1 19)
            (.reject)))
        (.step (.primeLo 2 19) <|
        .step (.dropHi 4 28) <|
        .step (.xHi 25) <|
        .missing 4 13)))

private def deficientFour7Part001Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,17,19,2,0⟩, ⟨true,61,0,1,1⟩], 1, deficientFour7Part000⟩]

theorem deficientFour7Part001 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,19,2,0⟩, ⟨false,13,23,2,0⟩, ⟨true,13,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part001Tree deficientFour7Part001Refs _ _ (by decide +kernel)

private def deficientFour7Part002Tree : Tree :=
  .step (.dropLo 4 54) <|
  .step (.xLo 57) <|
  .splitBase 3 31
    (.step (.dropLo 4 75) <|
    .step (.xLo 77) <|
    .splitExp 0 4
      (.step (.dropHi 4 137) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 97) <|
        .step (.xLo 133) <|
        .reject)
        (.step (.dropLo 4 96) <|
        .step (.xLo 97) <|
        .splitBase 3 29
          (.step (.dropLo 4 123) <|
          .step (.xLo 125) <|
          .splitExp 2 2
            (.step (.grow 2 19) <|
            .reject)
            (.step (.dropLo 4 136) <|
            .step (.xLo 137) <|
            .missing 4 23))
          (.step (.primeLo 3 31) <|
          .step (.dropHi 4 104) <|
          .step (.xHi 101) <|
          .splitExp 2 2
            (.missing 2 19)
            (.reject))))
      (.step (.dropLo 4 104) <|
      .step (.xLo 105) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .step (.dropHi 4 164) <|
        .step (.xLo 133) <|
        .step (.xHi 133) <|
        .missing 4 67)
        (.step (.dropLo 4 149) <|
        .splitBase 3 29
          (.step (.dropLo 4 225) <|
          .splitExp 2 2
            (.step (.grow 2 19) <|
            .step (.dropHi 4 257) <|
            .step (.xLo 285) <|
            .reject)
            (.step (.dropLo 4 271) <|
            .step (.xLo 273) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 4 304) <|
              .step (.xLo 305) <|
              .splitExp 1 4
                (.step (.dropHi 4 313) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 4 308) <|
                  .step (.xLo 309) <|
                  .splitExp 3 2
                    (.missing 3 13)
                    (.step (.dropLo 4 312) <|
                    .step (.xLo 313) <|
                    .missing 4 157)))
                (.step (.dropLo 4 310) <|
                .step (.xLo 313) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 4 314) <|
                  .step (.xLo 317) <|
                  .missing 4 53)))))
          (.step (.primeLo 3 31) <|
          .step (.dropHi 4 183) <|
          .step (.xHi 181) <|
          .splitExp 2 2
            (.missing 2 19)
            (.step (.dropLo 4 167) <|
            .step (.xLo 169) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.step (.dropLo 4 179) <|
              .step (.xLo 181) <|
              .missing 4 13))))))
    (.step (.primeLo 3 37) <|
    .step (.dropHi 4 91) <|
    .step (.xHi 89) <|
    .splitExp 0 4
      (.step (.dropHi 4 66) <|
      .step (.xHi 65) <|
      .splitExp 1 2
        (.step (.grow 1 19) <|
        .reject)
        (.step (.dropLo 4 63) <|
        .step (.xLo 65) <|
        .splitExp 2 2
          (.missing 2 19)
          (.reject)))
      (.step (.dropLo 4 67) <|
      .step (.xLo 69) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 4 83) <|
        .step (.xLo 85) <|
        .splitExp 2 2
          (.missing 2 19)
          (.step (.dropLo 4 88) <|
          .step (.xLo 89) <|
          .missing 4 5))))

theorem deficientFour7Part002 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,29,37,2,0⟩, ⟨true,33,317,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part002Tree [] _ _ (by decide +kernel)

private def deficientFour7Part003Tree : Tree :=
  .step (.primeLo 3 41) <|
  .step (.dropHi 4 73) <|
  .splitBase 2 11
    (.step (.dropLo 4 37) <|
    .splitBase 3 45
      (.step (.primeHi 3 43) <|
      .step (.dropLo 4 44) <|
      .step (.xLo 45) <|
      .splitExp 0 4
        (.step (.dropHi 4 56) <|
        .step (.xHi 53) <|
        .splitExp 1 2
          (.missing 1 19)
          (.step (.dropLo 4 51) <|
          .step (.xLo 53) <|
          .step (.dropHi 3 42) <|
          .step (.primeHi 3 41) <|
          .reject))
        (.step (.dropLo 4 53) <|
        .splitExp 1 2
          (.step (.grow 1 19) <|
          .step (.dropHi 4 60) <|
          .step (.xLo 57) <|
          .step (.xHi 57) <|
          .missing 4 29)
          (.step (.dropLo 4 63) <|
          .step (.xLo 65) <|
          .splitBase 3 41
            (.step (.dropLo 4 68) <|
            .step (.xLo 69) <|
            .splitExp 2 2
              (.missing 2 19)
              (.step (.dropLo 4 71) <|
              .step (.xLo 73) <|
              .missing 4 37))
            (.step (.primeLo 3 43) <|
            .step (.dropHi 4 67) <|
            .step (.xHi 65) <|
            .splitExp 2 2
              (.missing 2 19)
              (.reject)))))
      (.step (.primeLo 3 47) <|
      .step (.dropHi 4 59) <|
      .step (.xHi 57) <|
      .splitExp 0 4
        (.step (.dropHi 4 47) <|
        .step (.xHi 45) <|
        .splitExp 1 2
          (.missing 1 19)
          (.step (.dropLo 4 41) <|
          .splitBase 3 49
            (.step (.primeHi 3 47) <|
            .reject)
            (.step (.primeLo 3 53) <|
            .step (.dropHi 4 42) <|
            .step (.xHi 41) <|
            .splitExp 2 2
              (.missing 2 19)
              (.reject))))
        (.step (.dropLo 4 43) <|
        .step (.xLo 45) <|
        .splitExp 1 2
          (.step (.grow 1 19) <|
          .step (.dropHi 3 52) <|
          .step (.dropHi 4 50) <|
          .step (.primeHi 3 47) <|
          .step (.xLo 57) <|
          .reject)
          (.step (.dropLo 4 49) <|
          .splitBase 3 49
            (.step (.primeHi 3 47) <|
            .step (.dropLo 4 56) <|
            .step (.xLo 57) <|
            .missing 4 29)
            (.step (.primeLo 3 53) <|
            .step (.dropHi 4 51) <|
            .step (.xHi 49) <|
            .missing 4 5)))))
    (.step (.primeLo 2 13) <|
    .step (.dropHi 4 34) <|
    .step (.xHi 33) <|
    .splitBase 3 45
      (.step (.primeHi 3 43) <|
      .step (.dropLo 4 27) <|
      .step (.xLo 29) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 3 42) <|
        .step (.dropHi 4 29) <|
        .step (.primeHi 3 41) <|
        .step (.xLo 33) <|
        .reject)
        (.step (.dropLo 4 30) <|
        .step (.xLo 33) <|
        .missing 4 17))
      (.step (.primeLo 3 47) <|
      .step (.dropHi 4 30) <|
      .step (.xHi 29) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 4 26) <|
        .step (.xLo 29) <|
        .missing 4 5)))

theorem deficientFour7Part003 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,13,2,0⟩, ⟨false,38,53,2,0⟩, ⟨true,25,317,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part003Tree [] _ _ (by decide +kernel)

private def deficientFour7Part004Tree : Tree :=
  .step (.dropLo 4 27) <|
  .step (.xLo 29) <|
  .splitBase 3 77
    (.step (.primeHi 3 73) <|
    .step (.dropLo 4 31) <|
    .step (.xLo 33) <|
    .splitExp 0 4
      (.step (.dropHi 4 39) <|
      .step (.xHi 37) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 3 61) <|
        .step (.dropLo 4 34) <|
        .step (.xLo 37) <|
        .missing 4 19))
      (.step (.dropLo 4 35) <|
      .step (.xLo 37) <|
      .splitExp 1 2
        (.missing 1 19)
        (.step (.dropLo 4 39) <|
        .step (.xLo 41) <|
        .step (.dropHi 3 71) <|
        .splitBase 3 63
          (.step (.primeHi 3 61) <|
          .step (.dropLo 4 44) <|
          .step (.xLo 45) <|
          .missing 4 23)
          (.step (.primeLo 3 67) <|
          .step (.dropHi 4 42) <|
          .step (.xHi 41) <|
          .splitExp 2 2
            (.missing 2 19)
            (.step (.dropLo 3 68) <|
            .step (.primeLo 3 71) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 4
                (.splitExp 0 8
                  (.missing 0 13)
                  (.splitExp 2 4
                    (.missing 2 5)
                    (.splitExp 0 10
                      (.missing 0 23)
                      (.splitExp 3 2
                        (.reject)
                        (.reject)))))
                (.splitExp 0 8
                  (.missing 0 13)
                  (.reject))))))))
    (.step (.primeLo 3 79) <|
    .step (.dropHi 4 38) <|
    .step (.xHi 37) <|
    .splitExp 0 4
      (.step (.dropHi 4 33) <|
      .splitExp 1 2
        (.missing 1 19)
        (.splitBase 3 91
          (.step (.primeHi 3 89) <|
          .step (.dropLo 4 31) <|
          .step (.xLo 33) <|
          .missing 4 17)
          (.step (.primeLo 3 97) <|
          .step (.dropHi 4 30) <|
          .step (.xHi 29) <|
          .missing 4 5)))
      (.step (.dropLo 4 30) <|
      .step (.xLo 33) <|
      .splitExp 1 2
        (.missing 1 19)
        (.splitBase 3 91
          (.step (.primeHi 3 89) <|
          .step (.dropLo 4 35) <|
          .step (.xLo 37) <|
          .missing 4 19)
          (.step (.primeLo 3 97) <|
          .step (.dropHi 4 35) <|
          .step (.xHi 33) <|
          .missing 4 17))))

theorem deficientFour7Part004 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,7,7,2,0⟩, ⟨false,11,11,2,0⟩, ⟨false,59,113,2,0⟩, ⟨true,21,45,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour7Part004Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
