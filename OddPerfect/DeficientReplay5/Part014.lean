module

public import OddPerfect.DeficientReplay5.Part013

public section

namespace OddPerfect.DeficientSlots
open OddPerfect.SpoofBox (Slot)

set_option maxRecDepth 16000
set_option maxHeartbeats 0

private def deficientFour5Part065Tree : Tree :=
  .splitBase 3 201
    (.step (.primeHi 3 199) <|
    .splitExp 0 4
      (.missing 0 11)
      (.step (.dropLo 4 18) <|
      .step (.xLo 21) <|
      .missing 4 11))
    (.step (.primeLo 3 211) <|
    .step (.dropHi 4 19) <|
    .step (.xHi 17) <|
    .splitExp 0 4
      (.missing 0 11)
      (.step (.dropLo 2 123) <|
      .step (.dropLo 3 338) <|
      .step (.primeLo 2 127) <|
      .step (.primeLo 3 347) <|
      .splitBase 3 693
        (.use 0)
        (.step (.primeLo 3 701) <|
        .step (.dropHi 2 168) <|
        .step (.primeHi 2 167) <|
        .splitBase 2 143
          (.use 1)
          (.step (.primeLo 2 149) <|
          .step (.dropHi 3 1548) <|
          .step (.primeHi 3 1543) <|
          .splitBase 3 963
            (.step (.primeHi 3 953) <|
            .splitBase 2 157
              (.splitExp 0 6
                (.missing 0 1093)
                (.step (.dropLo 3 735) <|
                .step (.primeLo 3 739) <|
                .splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 2 156) <|
                  .step (.dropLo 3 949) <|
                  .step (.primeLo 2 157) <|
                  .step (.primeLo 3 953) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.reject))))
              (.step (.primeLo 2 163) <|
              .step (.dropHi 3 816) <|
              .step (.primeHi 3 811) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 4
                  (.missing 1 11)
                  (.splitBase 3 751
                    (.step (.dropLo 2 164) <|
                    .step (.primeLo 2 167) <|
                    .step (.dropHi 3 728) <|
                    .step (.primeHi 3 727) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.step (.dropLo 3 718) <|
                      .step (.primeLo 3 719) <|
                      .splitExp 1 6
                        (.step (.dropHi 3 721) <|
                        .step (.primeHi 3 719) <|
                        .splitExp 0 10
                          (.missing 0 23)
                          (.reject))
                        (.step (.dropLo 3 724) <|
                        .step (.primeLo 3 727) <|
                        .splitExp 0 10
                          (.missing 0 23)
                          (.reject))))
                    (.step (.primeLo 3 757) <|
                    .step (.dropHi 2 165) <|
                    .step (.primeHi 2 163) <|
                    .step (.dropLo 3 775) <|
                    .step (.primeLo 3 787) <|
                    .splitExp 0 8
                      (.missing 0 13)
                      (.step (.dropLo 3 803) <|
                      .step (.primeLo 3 809) <|
                      .splitExp 1 6
                        (.reject)
                        (.reject)))))))
            (.use 2)))))

private def deficientFour5Part065Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,127,193,2,0⟩, ⟨false,347,693,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part060⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,127,143,2,0⟩, ⟨false,701,0,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part063⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,149,167,2,0⟩, ⟨false,964,1543,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part064⟩]

theorem deficientFour5Part065 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,97,193,2,0⟩, ⟨false,101,0,2,0⟩, ⟨true,17,21,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part065Tree deficientFour5Part065Refs _ _ (by decide +kernel)

private def deficientFour5Part066Tree : Tree :=
  .step (.primeLo 2 227) <|
  .splitBase 3 303
    (.step (.primeHi 3 293) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.step (.dropLo 2 231) <|
      .step (.primeLo 2 233) <|
      .splitBase 2 247
        (.step (.primeHi 2 241) <|
        .step (.dropLo 3 278) <|
        .step (.primeLo 3 281) <|
        .splitExp 1 4
          (.missing 1 11)
          (.reject))
        (.step (.primeLo 2 251) <|
        .splitExp 1 4
          (.missing 1 11)
          (.splitBase 3 283
            (.step (.dropLo 2 256) <|
            .step (.primeLo 2 257) <|
            .splitBase 2 259
              (.step (.primeHi 2 257) <|
              .step (.dropLo 3 282) <|
              .step (.primeLo 3 283) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject))
              (.step (.primeLo 2 263) <|
              .step (.dropHi 3 280) <|
              .step (.primeHi 3 277) <|
              .splitExp 0 8
                (.missing 0 13)
                (.reject)))
            (.step (.primeLo 3 293) <|
            .step (.dropHi 2 252) <|
            .step (.primeHi 2 251) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))))
    (.step (.primeLo 3 307) <|
    .step (.dropHi 2 243) <|
    .step (.primeHi 2 241) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitExp 1 4
        (.missing 1 11)
        (.splitBase 3 321
          (.step (.primeHi 3 317) <|
          .step (.dropLo 2 233) <|
          .splitBase 2 235
            (.step (.primeHi 2 233) <|
            .reject)
            (.step (.primeLo 2 239) <|
            .step (.dropHi 3 314) <|
            .step (.primeHi 3 313) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 309) <|
              .step (.primeLo 3 311) <|
              .step (.dropHi 2 240) <|
              .step (.primeHi 2 239) <|
              .step (.dropLo 3 312) <|
              .step (.primeLo 3 313) <|
              .splitExp 1 6
                (.reject)
                (.reject))))
          (.step (.primeLo 3 331) <|
          .step (.dropHi 2 230) <|
          .step (.primeHi 2 229) <|
          .splitExp 0 8
            (.missing 0 13)
            (.splitBase 3 333
              (.step (.primeHi 3 331) <|
              .reject)
              (.step (.primeLo 3 337) <|
              .step (.dropHi 2 227) <|
              .splitExp 1 6
                (.reject)
                (.reject)))))))

theorem deficientFour5Part066 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,226,263,2,0⟩, ⟨false,277,337,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part066Tree [] _ _ (by decide +kernel)

private def deficientFour5Part067Tree : Tree :=
  .step (.primeLo 3 277) <|
  .step (.dropHi 2 266) <|
  .step (.primeHi 2 263) <|
  .splitBase 3 337
    (.splitBase 2 225
      (.step (.primeHi 2 223) <|
      .splitBase 3 303
        (.step (.primeHi 3 293) <|
        .step (.dropLo 2 211) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.reject))
        (.step (.primeLo 3 307) <|
        .splitExp 0 6
          (.missing 0 1093)
          (.step (.dropLo 2 209) <|
          .step (.primeLo 2 211) <|
          .splitExp 1 4
            (.missing 1 11)
            (.reject))))
      (.use 0))
    (.step (.primeLo 3 347) <|
    .step (.dropHi 2 223) <|
    .splitExp 0 6
      (.missing 0 1093)
      (.splitBase 2 209
        (.step (.primeHi 2 199) <|
        .step (.dropLo 3 369) <|
        .step (.primeLo 3 373) <|
        .splitExp 1 4
          (.missing 1 11)
          (.step (.dropLo 3 416) <|
          .step (.primeLo 3 419) <|
          .splitBase 3 425
            (.step (.primeHi 3 421) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))
            (.step (.primeLo 3 431) <|
            .step (.dropHi 2 198) <|
            .step (.primeHi 2 197) <|
            .splitExp 0 8
              (.missing 0 13)
              (.reject))))
        (.step (.primeLo 2 211) <|
        .step (.dropHi 3 380) <|
        .step (.primeHi 3 379) <|
        .splitExp 1 4
          (.missing 1 11)
          (.splitBase 2 215
            (.step (.primeHi 2 211) <|
            .step (.dropLo 3 371) <|
            .step (.primeLo 3 373) <|
            .splitExp 0 8
              (.missing 0 13)
              (.step (.dropLo 3 378) <|
              .step (.primeLo 3 379) <|
              .splitExp 1 6
                (.reject)
                (.reject)))
            (.step (.primeLo 2 223) <|
            .step (.dropHi 3 347) <|
            .splitExp 0 8
              (.missing 0 13)
              (.splitExp 1 6
                (.reject)
                (.splitExp 0 10
                  (.missing 0 23)
                  (.splitExp 0 12
                    (.reject)
                    (.splitExp 1 8
                      (.missing 1 19)
                      (.reject))))))))))

private def deficientFour5Part067Refs : List Known := [
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,226,263,2,0⟩, ⟨false,277,337,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part066⟩]

theorem deficientFour5Part067 : Closed (#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,197,421,2,0⟩, ⟨false,272,433,2,0⟩, ⟨true,17,17,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part067Tree deficientFour5Part067Refs _ _ (by decide +kernel)

private def deficientFour5Part068Tree : Tree :=
  .step (.primeLo 2 47) <|
  .step (.primeLo 3 53) <|
  .step (.dropHi 4 41) <|
  .splitBase 2 93
    (.step (.primeHi 2 89) <|
    .step (.dropLo 4 15) <|
    .step (.xLo 17) <|
    .splitBase 3 105
      (.use 0)
      (.step (.primeLo 3 107) <|
      .step (.dropHi 4 29) <|
      .splitExp 1 2
        (.missing 1 31)
        (.splitBase 2 61
          (.step (.dropLo 4 19) <|
          .step (.xLo 21) <|
          .splitBase 3 213
            (.step (.primeHi 3 211) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 4 23) <|
              .step (.xLo 25) <|
              .splitBase 2 53
                (.splitBase 3 141
                  (.step (.primeHi 3 139) <|
                  .step (.dropLo 4 26) <|
                  .step (.xLo 29) <|
                  .step (.dropHi 2 47) <|
                  .step (.dropHi 3 110) <|
                  .step (.primeHi 3 109) <|
                  .splitExp 0 6
                    (.missing 0 1093)
                    (.splitExp 1 4
                      (.missing 1 11)
                      (.reject)))
                  (.step (.primeLo 3 149) <|
                  .step (.dropHi 4 27) <|
                  .step (.xHi 25) <|
                  .missing 4 13))
                (.step (.primeLo 2 59) <|
                .step (.dropHi 3 122) <|
                .step (.dropHi 4 25) <|
                .step (.primeHi 3 113) <|
                .missing 4 13)))
            (.step (.primeLo 3 223) <|
            .step (.dropHi 4 25) <|
            .splitExp 0 4
              (.missing 0 11)
              (.splitBase 2 53
                (.step (.dropLo 4 22) <|
                .step (.xLo 25) <|
                .missing 4 13)
                (.step (.primeLo 2 59) <|
                .step (.dropHi 3 1082) <|
                .step (.dropHi 4 22) <|
                .step (.primeHi 3 1069) <|
                .step (.xHi 21) <|
                .missing 4 11))))
          (.step (.primeLo 2 67) <|
          .step (.dropHi 4 24) <|
          .step (.xHi 21) <|
          .splitBase 3 213
            (.step (.primeHi 3 211) <|
            .step (.dropLo 4 19) <|
            .step (.xLo 21) <|
            .missing 4 11)
            (.step (.primeLo 3 223) <|
            .splitExp 0 4
              (.missing 0 11)
              (.step (.dropLo 4 19) <|
              .step (.xLo 21) <|
              .missing 4 11))))))
    (.step (.primeLo 2 97) <|
    .step (.primeLo 3 101) <|
    .step (.dropHi 4 22) <|
    .step (.xHi 21) <|
    .splitExp 1 2
      (.missing 1 31)
      (.step (.dropLo 4 15) <|
      .step (.xLo 17) <|
      .splitBase 2 193
        (.use 1)
        (.step (.primeLo 2 197) <|
        .step (.primeLo 3 199) <|
        .step (.dropHi 2 427) <|
        .step (.dropHi 3 436) <|
        .step (.dropHi 4 17) <|
        .step (.primeHi 3 433) <|
        .step (.primeHi 2 421) <|
        .splitExp 0 4
          (.missing 0 11)
          (.splitBase 3 271
            (.step (.primeHi 2 269) <|
            .step (.dropLo 2 224) <|
            .step (.dropLo 3 226) <|
            .step (.primeLo 2 227) <|
            .step (.primeLo 3 229) <|
            .splitBase 2 245
              (.step (.primeHi 2 241) <|
              .step (.dropLo 3 250) <|
              .step (.primeLo 3 251) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.reject))
              (.step (.primeLo 2 251) <|
              .step (.primeLo 3 257) <|
              .splitExp 0 6
                (.missing 0 1093)
                (.splitExp 1 4
                  (.missing 1 11)
                  (.step (.dropLo 2 267) <|
                  .step (.dropLo 3 269) <|
                  .step (.primeLo 2 269) <|
                  .step (.primeLo 3 271) <|
                  .splitExp 0 8
                    (.missing 0 13)
                    (.reject)))))
            (.use 2)))))

private def deficientFour5Part068Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,47,89,2,0⟩, ⟨false,53,105,2,0⟩, ⟨true,17,41,1,1⟩], 1, deficientFour5Part058⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,97,193,2,0⟩, ⟨false,101,0,2,0⟩, ⟨true,17,21,1,1⟩], 1, deficientFour5Part065⟩,
  ⟨#v[⟨false,3,3,6,0⟩, ⟨false,5,5,4,0⟩, ⟨false,197,421,2,0⟩, ⟨false,272,433,2,0⟩, ⟨true,17,17,1,1⟩], 1, deficientFour5Part067⟩]

theorem deficientFour5Part068 : Closed (#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,46,0,2,0⟩, ⟨false,29,0,2,0⟩, ⟨true,13,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part068Tree deficientFour5Part068Refs _ _ (by decide +kernel)

private def deficientFour5Part069Tree : Tree :=
  .step (.primeLo 2 23) <|
  .step (.primeLo 3 29) <|
  .splitExp 0 2
    (.step (.grow 0 13) <|
    .step (.dropHi 4 43) <|
    .step (.xLo 13) <|
    .step (.xHi 13) <|
    .missing 4 7)
    (.step (.dropLo 4 13) <|
    .splitBase 2 45
      (.step (.primeHi 2 43) <|
      .step (.dropLo 4 19) <|
      .step (.xLo 21) <|
      .splitBase 3 57
        (.step (.primeHi 3 53) <|
        .step (.dropLo 4 29) <|
        .splitBase 2 29
          (.use 0)
          (.step (.primeLo 2 31) <|
          .step (.primeLo 3 37) <|
          .step (.dropHi 4 229) <|
          .splitExp 1 2
            (.step (.dropHi 4 80) <|
            .step (.xHi 77) <|
            .step (.fix 1 31 2) <|
            .step (.dropLo 4 40) <|
            .step (.xLo 41) <|
            .splitBase 3 43
              (.step (.dropLo 4 49) <|
              .splitExp 0 4
                (.step (.grow 0 11) <|
                .step (.dropHi 3 42) <|
                .step (.dropHi 4 60) <|
                .step (.primeHi 3 41) <|
                .step (.xLo 77) <|
                .reject)
                (.step (.dropLo 4 60) <|
                .step (.xLo 61) <|
                .splitBase 3 39
                  (.step (.primeHi 3 37) <|
                  .reject)
                  (.step (.primeLo 3 41) <|
                  .step (.dropHi 4 65) <|
                  .splitBase 3 41
                    (.step (.dropLo 4 64) <|
                    .step (.xLo 65) <|
                    .missing 4 11)
                    (.step (.primeLo 3 43) <|
                    .step (.dropHi 4 61) <|
                    .splitExp 0 6
                      (.missing 0 1093)
                      (.splitExp 0 8
                        (.missing 0 13)
                        (.splitExp 2 2
                          (.missing 2 331)
                          (.splitExp 3 2
                            (.missing 3 631)
                            (.reject))))))))
              (.step (.primeLo 3 47) <|
              .step (.dropHi 4 54) <|
              .step (.xHi 53) <|
              .splitExp 0 4
                (.missing 0 11)
                (.step (.dropLo 4 47) <|
                .step (.xLo 49) <|
                .step (.dropHi 3 51) <|
                .step (.primeHi 3 47) <|
                .step (.dropLo 4 53) <|
                .splitExp 0 6
                  (.missing 0 1093)
                  (.reject))))
            (.use 1)))
        (.use 2))
      (.use 3))

private def deficientFour5Part069Refs : List Known := [
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,29,2,0⟩, ⟨false,29,53,2,0⟩, ⟨true,29,0,1,1⟩], 1, deficientFour5Part047⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,4,0⟩, ⟨false,31,43,2,0⟩, ⟨false,37,53,2,0⟩, ⟨true,29,229,1,1⟩], 1, deficientFour5Part049⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,23,43,2,0⟩, ⟨false,58,0,2,0⟩, ⟨true,21,0,1,1⟩], 1, deficientFour5Part057⟩,
  ⟨#v[⟨false,3,3,4,0⟩, ⟨false,5,5,2,0⟩, ⟨false,46,0,2,0⟩, ⟨false,29,0,2,0⟩, ⟨true,13,0,1,1⟩], 1, deficientFour5Part068⟩]

theorem deficientFour5Part069 : Closed (#v[⟨false,3,3,2,0⟩, ⟨false,5,5,2,0⟩, ⟨false,22,0,2,0⟩, ⟨false,13,0,2,0⟩, ⟨true,9,0,1,1⟩] : Vector Slot 5) 1 :=
  Tree.sound deficientFour5Part069Tree deficientFour5Part069Refs _ _ (by decide +kernel)

end OddPerfect.DeficientSlots
