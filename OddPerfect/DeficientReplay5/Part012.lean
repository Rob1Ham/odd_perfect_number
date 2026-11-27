module

public import OddPerfect.DeficientReplay5.Part011

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part055Tree : Tree :=
  .step (.primeHi 3 251) <|
  .splitExp 0 4
    (.step (.grow 0 11) <|
    .step (.dropHi 4 29) <|
    .step (.xLo 33) <|
    .reject)
    (.step (.dropLo 4 26) <|
    .step (.xLo 29) <|
    .splitBase 3 167
      (.splitBase 2 39
        (.step (.primeHi 2 37) <|
        .step (.dropLo 4 31) <|
        .step (.xLo 33) <|
        .missing 4 17)
        (.step (.primeLo 2 41) <|
        .step (.dropHi 4 30) <|
        .step (.xHi 29) <|
        .splitBase 3 143
          (.step (.primeHi 3 139) <|
          .splitBase 2 41
            (.reject)
            (.step (.primeLo 2 43) <|
            .splitBase 3 131
              (.splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.step (.primeLo 3 137) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 4
                  (.missing 1 11)
                  (.reject)))))
          (.step (.primeLo 3 149) <|
          .step (.dropHi 2 42) <|
          .step (.primeHi 2 41) <|
          .splitBase 3 157
            (.splitExp 0 6
              (.missing 0 1093)
              (.reject))
            (.step (.primeLo 3 163) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitExp 1 4
                (.missing 1 11)
                (.step (.dropLo 3 166) <|
                .step (.primeLo 3 167) <|
                .splitExp 0 8
                  (.missing 0 13)
                  (.reject)))))))
      (.step (.primeLo 3 173) <|
      .step (.dropHi 2 40) <|
      .step (.dropHi 4 31) <|
      .step (.primeHi 2 37) <|
      .step (.xHi 29) <|
      .step (.dropLo 3 248) <|
      .step (.primeLo 3 251) <|
      .splitExp 0 6
        (.missing 0 1093)
        (.reject)))

theorem deficientFour5Part055 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,43,2,0⟩, ⟨false,127,253,2,0⟩, ⟨true,25,33,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part055Tree [] _ _ (by decide +kernel)

private def deficientFour5Part056Tree : Tree :=
  .step (.primeLo 2 31) <|
  .step (.dropHi 4 67) <|
  .step (.xHi 65) <|
  .splitBase 3 117
    (.use 0)
    (.step (.primeLo 3 127) <|
    .step (.dropHi 4 41) <|
    .splitExp 1 2
      (.step (.fix 1 31 2) <|
      .step (.dropLo 4 23) <|
      .step (.dropHi 4 30) <|
      .step (.xLo 25) <|
      .step (.xHi 29) <|
      .step (.dropHi 3 1785) <|
      .step (.primeHi 3 1783) <|
      .splitBase 3 237
        (.step (.primeHi 3 233) <|
        .splitExp 0 4
          (.missing 0 11)
          (.step (.dropLo 3 157) <|
          .step (.dropLo 4 28) <|
          .step (.xLo 29) <|
          .step (.dropHi 3 170) <|
          .step (.primeHi 3 167) <|
          .splitExp 0 6
            (.missing 0 1093)
            (.reject)))
        (.step (.primeLo 3 239) <|
        .step (.dropHi 4 27) <|
        .step (.xHi 25) <|
        .missing 4 13))
      (.step (.dropLo 4 22) <|
      .step (.xLo 25) <|
      .splitBase 2 35
        (.step (.primeHi 2 31) <|
        .step (.dropLo 4 28) <|
        .step (.xLo 29) <|
        .splitBase 3 253
          (.step (.primeHi 3 251) <|
          .step (.dropLo 4 31) <|
          .step (.xLo 33) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 166) <|
            .step (.dropHi 4 35) <|
            .step (.primeHi 3 163) <|
            .step (.xHi 33) <|
            .missing 4 17)
            (.step (.dropLo 4 35) <|
            .step (.xLo 37) <|
            .step (.dropHi 3 197) <|
            .splitBase 3 153
              (.step (.primeHi 3 151) <|
              .step (.dropLo 4 39) <|
              .step (.xLo 41) <|
              .missing 4 7)
              (.step (.primeLo 3 157) <|
              .step (.dropHi 4 38) <|
              .step (.xHi 37) <|
              .missing 4 19)))
          (.step (.primeLo 3 257) <|
          .step (.dropHi 4 35) <|
          .step (.xHi 33) <|
          .splitExp 0 4
            (.step (.grow 0 11) <|
            .step (.dropHi 3 507) <|
            .step (.dropHi 4 30) <|
            .step (.primeHi 3 503) <|
            .step (.xLo 33) <|
            .reject)
            (.step (.dropLo 3 369) <|
            .step (.dropLo 4 31) <|
            .step (.primeLo 3 373) <|
            .step (.xLo 33) <|
            .missing 4 17)))
        (.step (.primeLo 2 37) <|
        .step (.dropHi 4 33) <|
        .splitBase 3 253
          (.use 1)
          (.step (.primeLo 3 257) <|
          .step (.dropHi 4 29) <|
          .splitExp 0 4
            (.missing 0 11)
            (.splitBase 3 513
              (.step (.primeHi 3 509) <|
              .splitBase 2 39
                (.step (.primeHi 2 37) <|
                .step (.dropLo 4 28) <|
                .step (.xLo 29) <|
                .step (.dropHi 3 309) <|
                .step (.primeHi 3 307) <|
                .splitBase 3 279
                  (.step (.primeHi 3 277) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.step (.dropLo 3 276) <|
                    .step (.primeLo 3 277) <|
                    .splitExp 1 4
                      (.missing 1 11)
                      (.reject)))
                  (.step (.primeLo 3 281) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.splitExp 1 4
                      (.missing 1 11)
                      (.step (.dropLo 3 301) <|
                      .step (.primeLo 3 307) <|
                      .splitExp 0 8
                        (.missing 0 13)
                        (.splitExp 2 2
                          (.missing 2 7)
                          (.reject))))))
                (.step (.primeLo 2 41) <|
                .step (.dropHi 4 27) <|
                .step (.xHi 25) <|
                .missing 4 13))
              (.step (.primeLo 3 521) <|
              .step (.dropHi 4 27) <|
              .step (.xHi 25) <|
              .missing 4 13))))))

private def deficientFour5Part056Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,31,43,2,0⟩, ⟨false,59,117,2,0⟩, ⟨true,21,65,1,1⟩], 1, deficientFour5Part054⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,37,43,2,0⟩, ⟨false,127,253,2,0⟩, ⟨true,25,33,1,1⟩], 1, deficientFour5Part055⟩]

theorem deficientFour5Part056 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,30,43,2,0⟩, ⟨false,59,0,2,0⟩, ⟨true,21,333,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part056Tree deficientFour5Part056Refs _ _ (by decide +kernel)

private def deficientFour5Part057Tree : Tree :=
  .step (.primeLo 3 59) <|
  .step (.dropHi 4 333) <|
  .splitBase 2 29
    (.step (.dropLo 4 24) <|
    .step (.xLo 25) <|
    .splitBase 3 117
      (.step (.primeHi 3 113) <|
      .step (.dropLo 4 31) <|
      .step (.xLo 33) <|
      .splitExp 1 2
        (.step (.grow 1 31) <|
        .step (.dropHi 4 90) <|
        .step (.xLo 93) <|
        .reject)
        (.step (.dropLo 4 40) <|
        .step (.xLo 41) <|
        .splitBase 2 25
          (.step (.primeHi 2 23) <|
          .step (.dropLo 4 64) <|
          .step (.xLo 65) <|
          .splitBase 3 77
            (.step (.primeHi 3 73) <|
            .step (.dropLo 4 92) <|
            .step (.xLo 93) <|
            .splitExp 0 4
              (.step (.grow 0 11) <|
              .step (.dropHi 4 140) <|
              .step (.xLo 121) <|
              .step (.xHi 121) <|
              .step (.fix 4 61 3) <|
              .reject)
              (.step (.dropLo 4 140) <|
              .step (.xLo 141) <|
              .splitBase 3 65
                (.step (.primeHi 3 61) <|
                .step (.dropLo 4 226) <|
                .step (.xLo 229) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.step (.dropLo 4 249) <|
                  .splitBase 3 59
                    (.step (.dropLo 4 290) <|
                    .step (.xLo 293) <|
                    .splitExp 1 4
                      (.step (.grow 1 11) <|
                      .missing 1 71)
                      (.step (.dropLo 4 318) <|
                      .step (.xLo 321) <|
                      .splitExp 2 2
                        (.step (.grow 2 7) <|
                        .missing 2 79)
                        (.step (.dropLo 4 327) <|
                        .step (.xLo 329) <|
                        .splitExp 0 8
                          (.missing 0 13)
                          (.step (.dropLo 4 332) <|
                          .step (.xLo 333) <|
                          .missing 4 167))))
                    (.step (.primeLo 3 61) <|
                    .step (.dropHi 4 280) <|
                    .step (.xHi 277) <|
                    .splitExp 1 4
                      (.step (.grow 1 11) <|
                      .missing 1 71)
                      (.step (.dropLo 4 270) <|
                      .step (.xLo 273) <|
                      .splitExp 2 2
                        (.step (.grow 2 7) <|
                        .missing 2 79)
                        (.step (.dropLo 4 276) <|
                        .step (.xLo 277) <|
                        .missing 4 139)))))
                (.step (.primeLo 3 67) <|
                .step (.dropHi 4 197) <|
                .splitBase 3 69
                  (.step (.primeHi 3 67) <|
                  .step (.dropLo 4 169) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.step (.dropLo 4 182) <|
                    .step (.xLo 185) <|
                    .splitExp 1 4
                      (.missing 1 11)
                      (.step (.dropLo 4 192) <|
                      .step (.xLo 193) <|
                      .splitExp 2 2
                        (.missing 2 7)
                        (.step (.dropLo 4 195) <|
                        .step (.xLo 197) <|
                        .missing 4 11))))
                  (.step (.primeLo 3 71) <|
                  .step (.dropHi 4 168) <|
                  .step (.xHi 165) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.step (.dropLo 4 148) <|
                    .step (.xLo 149) <|
                    .splitExp 1 4
                      (.step (.grow 1 11) <|
                      .step (.fix 1 71 3) <|
                      .step (.dropLo 4 157) <|
                      .step (.dropHi 4 160) <|
                      .step (.xLo 165) <|
                      .reject)
                      (.step (.dropLo 4 155) <|
                      .step (.xLo 157) <|
                      .splitBase 3 71
                        (.step (.dropLo 4 165) <|
                        .missing 4 83)
                        (.step (.primeLo 3 73) <|
                        .step (.dropHi 4 158) <|
                        .step (.xHi 157) <|
                        .missing 4 79)))))))
            (.use 0))
          (.use 1)))
      (.use 2))
    (.use 3)

private def deficientFour5Part057Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,23,23,2,0⟩, ⟨false,78,113,2,0⟩, ⟨true,65,333,1,1⟩], 1, deficientFour5Part050⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,26,29,2,0⟩, ⟨false,59,113,2,0⟩, ⟨true,41,333,1,1⟩], 1, deficientFour5Part051⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,29,2,0⟩, ⟨false,118,0,2,0⟩, ⟨true,25,333,1,1⟩], 1, deficientFour5Part053⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,30,43,2,0⟩, ⟨false,59,0,2,0⟩, ⟨true,21,333,1,1⟩], 1, deficientFour5Part056⟩]

theorem deficientFour5Part057 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,43,2,0⟩, ⟨false,58,0,2,0⟩, ⟨true,21,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part057Tree deficientFour5Part057Refs _ _ (by decide +kernel)

private def deficientFour5Part058Tree : Tree :=
  .step (.primeHi 3 103) <|
  .step (.dropLo 4 18) <|
  .step (.xLo 21) <|
  .splitExp 1 2
    (.missing 1 31)
    (.splitBase 2 61
      (.step (.dropLo 4 23) <|
      .step (.xLo 25) <|
      .splitBase 3 69
        (.step (.primeHi 3 67) <|
        .step (.dropLo 4 27) <|
        .step (.xLo 29) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 35) <|
          .step (.xLo 33) <|
          .step (.xHi 33) <|
          .missing 4 17)
          (.step (.dropLo 4 30) <|
          .step (.xLo 33) <|
          .splitBase 2 53
            (.splitBase 3 59
              (.step (.dropLo 4 34) <|
              .step (.xLo 37) <|
              .splitBase 2 49
                (.step (.primeHi 2 47) <|
                .splitBase 3 55
                  (.step (.primeHi 3 53) <|
                  .step (.dropLo 4 40) <|
                  .step (.xLo 41) <|
                  .missing 4 7)
                  (.step (.primeLo 3 59) <|
                  .step (.dropHi 4 38) <|
                  .step (.xHi 37) <|
                  .missing 4 19))
                (.step (.primeLo 2 53) <|
                .step (.primeLo 3 59) <|
                .reject))
              (.step (.primeLo 3 61) <|
              .step (.dropHi 4 37) <|
              .splitBase 2 49
                (.step (.primeHi 2 47) <|
                .step (.dropLo 4 35) <|
                .step (.xLo 37) <|
                .missing 4 19)
                (.step (.primeLo 2 53) <|
                .step (.dropHi 3 64) <|
                .step (.dropHi 4 34) <|
                .step (.primeHi 3 61) <|
                .step (.xHi 33) <|
                .missing 4 17)))
            (.step (.primeLo 2 59) <|
            .step (.primeLo 3 61) <|
            .reject)))
        (.step (.primeLo 3 71) <|
        .step (.dropHi 4 34) <|
        .step (.xHi 33) <|
        .splitExp 0 4
          (.step (.grow 0 11) <|
          .step (.dropHi 4 29) <|
          .step (.xLo 33) <|
          .reject)
          (.step (.dropLo 4 26) <|
          .step (.xLo 29) <|
          .splitBase 2 53
            (.splitBase 3 83
              (.splitBase 2 49
                (.step (.primeHi 2 47) <|
                .step (.dropLo 3 72) <|
                .step (.dropLo 4 32) <|
                .step (.primeLo 3 73) <|
                .step (.xLo 33) <|
                .missing 4 17)
                (.step (.primeLo 2 53) <|
                .step (.dropHi 4 31) <|
                .step (.xHi 29) <|
                .step (.dropLo 3 81) <|
                .step (.primeLo 3 83) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject)))
              (.step (.primeLo 3 89) <|
              .step (.dropHi 2 52) <|
              .step (.dropHi 4 31) <|
              .step (.primeHi 2 47) <|
              .step (.xHi 29) <|
              .step (.dropLo 3 101) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject)))
            (.step (.primeLo 2 59) <|
            .step (.dropHi 3 74) <|
            .step (.dropHi 4 29) <|
            .step (.primeHi 3 73) <|
            .splitExp 0 6
              (.missing 0 1093)
              (.splitBase 2 59
                (.step (.dropLo 3 72) <|
                .step (.primeLo 3 73) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.reject))
                (.step (.primeLo 2 61) <|
                .step (.dropHi 3 71) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.reject)))))))
      (.step (.primeLo 2 67) <|
      .step (.primeLo 3 71) <|
      .step (.dropHi 4 27) <|
      .step (.xHi 25) <|
      .splitExp 0 4
        (.missing 0 11)
        (.step (.dropLo 4 23) <|
        .step (.xLo 25) <|
        .missing 4 13)))

theorem deficientFour5Part058 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,47,89,2,0⟩, ⟨false,53,105,2,0⟩, ⟨true,17,41,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part058Tree [] _ _ (by decide +kernel)

private def deficientFour5Part059Tree : Tree :=
  .splitExp 0 6
    (.missing 0 1093)
    (.splitBase 2 181
      (.step (.dropLo 3 452) <|
      .step (.primeLo 3 457) <|
      .splitExp 1 4
        (.missing 1 11)
        (.reject))
      (.step (.primeLo 2 191) <|
      .step (.dropHi 3 469) <|
      .step (.primeHi 3 467) <|
      .splitExp 1 4
        (.missing 1 11)
        (.splitBase 3 457
          (.splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 2 192) <|
            .step (.dropLo 3 454) <|
            .step (.primeLo 2 193) <|
            .step (.primeLo 3 457) <|
            .splitExp 1 6
              (.reject)
              (.splitExp 0 10
                (.missing 0 23)
                (.reject))))
          (.step (.primeLo 3 461) <|
          .step (.dropHi 2 192) <|
          .step (.primeHi 2 191) <|
          .splitExp 0 8
            (.missing 0 13)
            (.step (.dropLo 3 465) <|
            .step (.primeLo 3 467) <|
            .splitExp 1 6
              (.splitExp 0 10
                (.missing 0 23)
                (.splitExp 0 12
                  (.reject)
                  (.splitExp 2 2
                    (.missing 2 7)
                    (.splitExp 0 14
                      (.missing 0 11)
                      (.reject)))))
              (.reject))))))

theorem deficientFour5Part059 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,173,193,2,0⟩, ⟨false,449,523,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part059Tree [] _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
