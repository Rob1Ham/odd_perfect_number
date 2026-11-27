module

public import OddPerfect.DeficientReplay5.Part010

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part050Tree : Tree :=
  .step (.primeLo 3 79) <|
  .step (.dropHi 4 135) <|
  .step (.xHi 133) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 3 112) <|
    .step (.dropHi 4 86) <|
    .step (.primeHi 3 109) <|
    .step (.xLo 77) <|
    .step (.xHi 77) <|
    .missing 4 13)
    (.step (.dropLo 4 83) <|
    .step (.xLo 85) <|
    .splitBase 3 91
      (.step (.primeHi 3 89) <|
      .step (.dropLo 4 104) <|
      .step (.xLo 105) <|
      .splitBase 3 83
        (.step (.dropLo 4 113) <|
        .splitBase 3 79
          (.step (.dropLo 4 122) <|
          .step (.xLo 125) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 128) <|
            .step (.xLo 129) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 133) <|
              .missing 4 67)))
          (.step (.primeLo 3 83) <|
          .step (.dropHi 4 125) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 119) <|
            .step (.xLo 121) <|
            .splitExp 1 4
              (.step (.grow 1 11) <|
              .missing 1 71)
              (.step (.dropLo 4 123) <|
              .step (.xLo 125) <|
              .missing 4 7))))
        (.step (.primeLo 3 89) <|
        .step (.dropHi 4 113) <|
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
      .step (.dropHi 4 102) <|
      .step (.xHi 101) <|
      .splitBase 3 103
        (.step (.dropLo 4 89) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 93) <|
          .splitBase 3 99
            (.step (.primeHi 3 97) <|
            .step (.dropLo 4 98) <|
            .step (.xLo 101) <|
            .missing 4 17)
            (.step (.primeLo 3 101) <|
            .step (.dropHi 4 98) <|
            .step (.xHi 97) <|
            .splitExp 1 4
              (.missing 1 11)
              (.step (.dropLo 4 95) <|
              .step (.xLo 97) <|
              .missing 4 7))))
        (.step (.primeLo 3 107) <|
        .step (.dropHi 4 92) <|
        .step (.xHi 89) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 86) <|
          .step (.xLo 89) <|
          .step (.dropHi 3 112) <|
          .step (.primeHi 3 109) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject)))))

theorem deficientFour5Part050 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,78,113,2,0⟩, ⟨true,65,333,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part050Tree [] _ _ (by decide +kernel)

private def deficientFour5Part051Tree : Tree :=
  .step (.primeLo 2 29) <|
  .step (.dropHi 4 80) <|
  .step (.xHi 77) <|
  .splitBase 3 77
    (.step (.primeHi 3 73) <|
    .step (.dropLo 4 50) <|
    .step (.xLo 53) <|
    .splitExp 0 4
      (.step (.grow 0 11) <|
      .step (.dropHi 3 67) <|
      .step (.dropHi 4 60) <|
      .step (.xLo 77) <|
      .reject)
      (.step (.dropLo 4 61) <|
      .splitBase 3 65
        (.step (.primeHi 3 61) <|
        .step (.dropLo 4 73) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 75) <|
          .step (.xLo 77) <|
          .missing 4 13))
        (.step (.primeLo 3 67) <|
        .step (.dropHi 4 68) <|
        .step (.xHi 65) <|
        .splitBase 3 69
          (.step (.primeHi 3 67) <|
          .reject)
          (.step (.primeLo 3 71) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.step (.dropLo 4 62) <|
            .step (.xLo 65) <|
            .missing 4 11)))))
    (.step (.primeLo 3 79) <|
    .step (.dropHi 4 59) <|
    .step (.xHi 57) <|
    .splitExp 0 4
      (.missing 0 11)
      (.step (.dropLo 4 47) <|
      .step (.xLo 49) <|
      .step (.dropHi 3 108) <|
      .step (.primeHi 3 107) <|
      .splitBase 3 89
        (.step (.dropLo 4 53) <|
        .splitBase 3 83
          (.step (.dropLo 4 55) <|
          .step (.xLo 57) <|
          .splitBase 3 79
            (.splitExp 0 6
              (.missing 0 1093)
              (.reject))
            (.step (.primeLo 3 83) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 4
                (.missing 1 11)
                (.splitExp 0 8
                  (.missing 0 13)
                  (.reject)))))
          (.step (.primeLo 3 89) <|
          .step (.dropHi 4 54) <|
          .step (.xHi 53) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject)))
        (.step (.primeLo 3 97) <|
        .step (.dropHi 4 51) <|
        .step (.xHi 49) <|
        .step (.dropLo 3 99) <|
        .step (.primeLo 3 101) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 104) <|
          .step (.primeLo 3 107) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject)))))

theorem deficientFour5Part051 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,26,29,2,0⟩, ⟨false,59,113,2,0⟩, ⟨true,41,333,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part051Tree [] _ _ (by decide +kernel)

private def deficientFour5Part052Tree : Tree :=
  .step (.dropLo 4 48) <|
  .step (.xLo 49) <|
  .splitBase 3 513
    (.step (.primeHi 3 509) <|
    .step (.dropLo 4 53) <|
    .splitBase 3 341
      (.step (.primeHi 3 337) <|
      .step (.dropLo 4 56) <|
      .step (.xLo 57) <|
      .splitBase 3 291
        (.step (.primeHi 3 283) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 4 59) <|
          .step (.xLo 61) <|
          .missing 4 31))
        (.step (.primeLo 3 293) <|
        .step (.dropHi 4 59) <|
        .step (.xHi 57) <|
        .missing 4 29))
      (.step (.primeLo 3 347) <|
      .step (.dropHi 4 57) <|
      .splitBase 3 411
        (.step (.primeHi 3 409) <|
        .step (.dropLo 4 54) <|
        .step (.xLo 57) <|
        .missing 4 29)
        (.step (.primeLo 3 419) <|
        .step (.dropHi 4 56) <|
        .step (.xHi 53) <|
        .step (.dropLo 3 444) <|
        .step (.primeLo 3 449) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))))
    (.step (.primeLo 3 521) <|
    .step (.dropHi 4 54) <|
    .step (.xHi 53) <|
    .splitBase 3 1041
      (.step (.primeHi 3 1039) <|
      .step (.dropLo 4 50) <|
      .step (.xLo 53) <|
      .step (.dropHi 3 717) <|
      .step (.primeHi 3 709) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.step (.dropLo 3 541) <|
        .splitBase 3 613
          (.splitExp 1 4
            (.missing 1 11)
            (.reject))
          (.step (.primeLo 3 617) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 3 649) <|
            .step (.primeLo 3 653) <|
            .splitBase 3 679
              (.step (.primeHi 3 677) <|
              .splitExp 2 2
                (.missing 2 7)
                (.reject))
              (.step (.primeLo 3 683) <|
              .splitExp 2 2
                (.missing 2 7)
                (.step (.dropLo 3 686) <|
                .step (.primeLo 3 691) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.step (.dropLo 3 708) <|
                  .step (.primeLo 3 709) <|
                  .splitExp 1 6
                    (.splitExp 0 10
                      (.reject)
                      (.reject))
                    (.reject))))))))
      (.step (.primeLo 3 1049) <|
      .step (.dropHi 4 51) <|
      .step (.xHi 49) <|
      .step (.dropLo 3 1345) <|
      .step (.primeLo 3 1361) <|
      .splitBase 3 2721
        (.step (.primeHi 3 2719) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 3 2729) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 3 2966) <|
          .step (.primeLo 3 2969) <|
          .splitExp 1 4
            (.missing 1 11)
            (.step (.dropLo 3 33500) <|
            .step (.primeLo 3 33503) <|
            .splitExp 2 2
              (.step (.grow 2 7) <|
              .missing 2 79)
              (.reject))))))

theorem deficientFour5Part052 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,257,0,2,0⟩, ⟨true,41,61,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part052Tree [] _ _ (by decide +kernel)

private def deficientFour5Part053Tree : Tree :=
  .step (.primeLo 3 127) <|
  .step (.dropHi 4 81) <|
  .splitExp 1 2
    (.missing 1 31)
    (.step (.dropLo 4 29) <|
    .splitBase 2 25
      (.step (.primeHi 2 23) <|
      .step (.dropLo 4 41) <|
      .splitBase 3 253
        (.step (.primeHi 3 251) <|
        .step (.dropLo 4 48) <|
        .step (.xLo 49) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 3 250) <|
          .step (.dropHi 4 60) <|
          .step (.primeHi 3 241) <|
          .step (.xLo 77) <|
          .reject)
          (.step (.dropLo 4 59) <|
          .step (.xLo 61) <|
          .splitBase 3 167
            (.step (.dropLo 4 67) <|
            .step (.xLo 69) <|
            .splitBase 3 143
              (.step (.primeHi 3 139) <|
              .step (.dropLo 4 73) <|
              .splitBase 3 131
                (.step (.dropLo 4 75) <|
                .step (.xLo 77) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 78) <|
                  .step (.xLo 81) <|
                  .missing 4 41))
                (.step (.primeLo 3 137) <|
                .step (.dropHi 4 77) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 75) <|
                  .step (.xLo 77) <|
                  .missing 4 13)))
              (.step (.primeLo 3 149) <|
              .step (.dropHi 4 74) <|
              .step (.xHi 73) <|
              .splitBase 3 157
                (.splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 71) <|
                  .step (.xLo 73) <|
                  .missing 4 37))
                (.step (.primeLo 3 163) <|
                .step (.dropHi 4 71) <|
                .step (.xHi 69) <|
                .missing 4 7)))
            (.step (.primeLo 3 173) <|
            .step (.dropHi 4 69) <|
            .splitBase 3 203
              (.step (.primeHi 3 199) <|
              .step (.dropLo 4 63) <|
              .step (.xLo 65) <|
              .splitBase 3 185
                (.step (.primeHi 3 181) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 67) <|
                  .step (.xLo 69) <|
                  .missing 4 7))
                (.step (.primeLo 3 191) <|
                .step (.dropHi 4 66) <|
                .step (.xHi 65) <|
                .missing 4 11))
              (.step (.primeLo 3 211) <|
              .step (.dropHi 4 64) <|
              .step (.xHi 61) <|
              .missing 4 31))))
        (.step (.primeLo 3 257) <|
        .step (.dropHi 4 61) <|
        .splitExp 0 4
          (.missing 0 11)
          (.use 0)))
      (.step (.primeLo 2 29) <|
      .step (.dropHi 4 45) <|
      .splitBase 3 253
        (.step (.primeHi 3 251) <|
        .step (.dropLo 4 33) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 38) <|
          .step (.xHi 33) <|
          .missing 4 17)
          (.step (.dropLo 4 38) <|
          .step (.xLo 41) <|
          .step (.dropHi 3 187) <|
          .step (.primeHi 3 181) <|
          .splitBase 3 149
            (.step (.dropLo 4 42) <|
            .step (.xLo 45) <|
            .missing 4 23)
            (.step (.primeLo 3 151) <|
            .step (.dropHi 4 43) <|
            .step (.xHi 41) <|
            .missing 4 7)))
        (.step (.primeLo 3 257) <|
        .step (.dropHi 4 38) <|
        .step (.xHi 37) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 33) <|
          .step (.xLo 33) <|
          .missing 4 17)
          (.step (.dropLo 3 278) <|
          .step (.dropLo 4 33) <|
          .step (.primeLo 3 281) <|
          .splitBase 3 561
            (.step (.primeHi 3 557) <|
            .step (.dropLo 4 35) <|
            .step (.xLo 37) <|
            .missing 4 19)
            (.step (.primeLo 3 563) <|
            .step (.dropHi 4 35) <|
            .step (.xHi 33) <|
            .missing 4 17)))))

private def deficientFour5Part053Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,257,0,2,0⟩, ⟨true,41,61,1,1⟩], 1, deficientFour5Part052⟩]

theorem deficientFour5Part053 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,29,2,0⟩, ⟨false,118,0,2,0⟩, ⟨true,25,333,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part053Tree deficientFour5Part053Refs _ _ (by decide +kernel)

private def deficientFour5Part054Tree : Tree :=
  .step (.primeHi 3 113) <|
  .step (.dropLo 4 23) <|
  .step (.xLo 25) <|
  .splitExp 1 2
    (.step (.fix 1 31 2) <|
    .step (.dropLo 4 29) <|
    .step (.dropHi 4 43) <|
    .step (.xHi 41) <|
    .splitBase 3 77
      (.step (.primeHi 3 73) <|
      .step (.dropLo 4 33) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 3 71) <|
        .step (.dropHi 4 36) <|
        .step (.xHi 33) <|
        .missing 4 17)
        (.step (.dropLo 3 62) <|
        .step (.dropLo 4 38) <|
        .step (.primeLo 3 67) <|
        .step (.xLo 41) <|
        .missing 4 7))
      (.step (.primeLo 3 79) <|
      .step (.dropHi 4 36) <|
      .step (.xHi 33) <|
      .splitExp 0 4
        (.step (.grow 0 11) <|
        .step (.dropHi 3 100) <|
        .step (.dropHi 4 31) <|
        .step (.primeHi 3 97) <|
        .step (.xLo 33) <|
        .reject)
        (.step (.dropLo 3 96) <|
        .step (.dropLo 4 32) <|
        .step (.primeLo 3 97) <|
        .step (.xLo 33) <|
        .missing 4 17)))
    (.step (.dropLo 4 27) <|
    .step (.xLo 29) <|
    .splitBase 2 35
      (.step (.primeHi 2 31) <|
      .step (.dropLo 4 37) <|
      .splitBase 3 77
        (.step (.primeHi 3 73) <|
        .step (.dropLo 4 45) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 4 53) <|
          .splitBase 3 65
            (.step (.primeHi 3 61) <|
            .step (.dropLo 4 62) <|
            .step (.xLo 65) <|
            .missing 4 11)
            (.step (.primeLo 3 67) <|
            .step (.dropHi 4 59) <|
            .step (.xHi 57) <|
            .splitBase 3 69
              (.step (.primeHi 3 67) <|
              .step (.dropLo 4 57) <|
              .missing 4 29)
              (.step (.primeLo 3 71) <|
              .step (.dropHi 4 56) <|
              .step (.xHi 53) <|
              .step (.dropLo 3 72) <|
              .step (.primeLo 3 73) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject)))))
        (.step (.primeLo 3 79) <|
        .step (.dropHi 4 52) <|
        .step (.xHi 49) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 3 81) <|
          .step (.dropLo 4 42) <|
          .step (.primeLo 3 83) <|
          .step (.xLo 45) <|
          .step (.dropHi 3 102) <|
          .step (.primeHi 3 101) <|
          .splitBase 3 91
            (.step (.primeHi 3 89) <|
            .step (.dropLo 4 47) <|
            .step (.xLo 49) <|
            .step (.dropHi 3 87) <|
            .step (.primeHi 3 83) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.reject))
            (.step (.primeLo 3 97) <|
            .step (.dropHi 4 46) <|
            .step (.xHi 45) <|
            .missing 4 23))))
      (.step (.primeLo 2 37) <|
      .step (.dropHi 4 49) <|
      .splitBase 3 77
        (.step (.primeHi 3 73) <|
        .step (.dropLo 4 32) <|
        .step (.xLo 33) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 40) <|
          .step (.xHi 33) <|
          .missing 4 17)
          (.step (.dropLo 4 36) <|
          .step (.xLo 37) <|
          .splitBase 2 39
            (.step (.primeHi 2 37) <|
            .step (.dropLo 4 41) <|
            .splitBase 3 65
              (.step (.primeHi 3 61) <|
              .step (.dropLo 4 47) <|
              .step (.xLo 49) <|
              .step (.dropHi 3 59) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 4
                  (.missing 1 11)
                  (.reject)))
              (.step (.primeLo 3 67) <|
              .step (.dropHi 4 44) <|
              .step (.xHi 41) <|
              .missing 4 7))
            (.step (.primeLo 2 41) <|
            .step (.dropHi 4 43) <|
            .step (.xHi 41) <|
            .splitBase 3 65
              (.step (.primeHi 3 61) <|
              .step (.dropLo 4 40) <|
              .step (.xLo 41) <|
              .missing 4 7)
              (.step (.primeLo 3 67) <|
              .step (.dropHi 4 39) <|
              .step (.xHi 37) <|
              .missing 4 19))))
        (.step (.primeLo 3 79) <|
        .step (.dropHi 4 40) <|
        .step (.xHi 37) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 34) <|
          .step (.xLo 33) <|
          .step (.xHi 33) <|
          .missing 4 17)
          (.step (.dropLo 4 30) <|
          .step (.xLo 33) <|
          .splitBase 2 39
            (.step (.primeHi 2 37) <|
            .step (.dropLo 3 89) <|
            .step (.dropLo 4 34) <|
            .step (.xLo 37) <|
            .missing 4 19)
            (.step (.primeLo 2 41) <|
            .step (.dropHi 3 100) <|
            .step (.dropHi 4 36) <|
            .step (.primeHi 3 97) <|
            .step (.xHi 33) <|
            .missing 4 17)))))

theorem deficientFour5Part054 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,31,43,2,0⟩, ⟨false,59,117,2,0⟩, ⟨true,21,65,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part054Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
